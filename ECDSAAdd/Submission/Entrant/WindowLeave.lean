import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.PairFrameUnique
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Arithmetic.NarrowSignedRecord
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ExactBorrowErase
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.DisjointPrograms
import ECDSAAdd.Challenge.Contract
import Mathlib.Tactic.FinCases
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof
import ECDSAAdd.Arithmetic.SignedWordBits
import ECDSAAdd.Arithmetic.SignedHalf
import ECDSAAdd.Arithmetic.BalancedCoreLayoutProof
import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Math.SkywalkTerminationBudget
import ECDSAAdd.Math.SkywalkTrace
import ECDSAAdd.Arithmetic.RecordedRailRippleCertificate
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Arithmetic.RecordedRailVentedProof
import ECDSAAdd.Framework.WireRenameComposition
import ECDSAAdd.Framework.Cost
import ECDSAAdd.Framework.PacketSequenceFrame
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Framework.WireRenameEquivalence
import ECDSAAdd.Submission.Entrant.Window

namespace ECDSAAdd.Entrant.StairPacket
/-- The shadow window's blocks 1..22 start between ticks 90 and 405. -/
theorem start_win7 (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 22) : 90 ≤ start j ∧ start j ≤ 405 := by
  unfold start; omega
theorem start_win75 (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : 75 ≤ start j ∧ start j ≤ 405 := by
  unfold start; omega
end ECDSAAdd.Entrant.StairPacket

/- Inlined from ShadowParts; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket GateMirror Partial LeaveSelector


def forward (j : Fin 24) := IntegerPacket.seq (Shadow7.shape j) 0 15

def reverse (j : Fin 24) := IntegerPacket.back (Shadow7.shape j) 0 15

def onRails (j:Fin 24) (i:Nat) (z:SkywalkRails.State) (b:BasisState) :=
  ready (Shadow7.shape j) i z (mappedBasis j b)

def leaveJoin (s : Nat) : List Gate :=
  digitsG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) (Shadow7.e0P s + 6) 1613 0 16 ++ wordGM 1614 (Shadow7.columnsP s)

def lowSign (s : Nat) : List Gate := [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559]

def lowRest (s : Nat) : List Gate :=
  (List.range (Shadow7.lowsP s)).map (fun i => .make 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ++
  addG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ((List.range (Shadow7.lowsP s - 1)).map (1559 + ·)) 1558 ++
  xsG ((List.range (Shadow7.lowsP s)).map (Shadow7.b0P s + ·)) ++
  [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557]

def leaveHeadOps (s : Nat) : List Gate :=
  Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ leaveFix5 s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.leaveJoin s ++ Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.lowSign s

def leaveMidOps (s : Nat) : List Gate := Shadow7.lowRest s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s

def leaveOps (s : Nat) : List Gate :=
  Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ leaveFix5 s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.leaveJoin s ++ Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def leaveP (j : Fin 24) : Program := GateMirror.forward (Shadow7.leaveOps (start j))

def leaveInvP (j : Fin 24) : Program := inverse (Shadow7.leaveOps (start j))

def moveA (s : Nat) : List Gate :=
  Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ (leaveFix5 s (Shadow7.sbP s)).take 27

def moveMux (s : Nat) : List Gate := ((leaveFix5 s (Shadow7.sbP s)).drop 27).take 16

def moveB (s : Nat) : List Gate :=
  (leaveFix5 s (Shadow7.sbP s)).drop 43 ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++ Shadow7.fix8P s (Shadow7.sbP s)

def moveDig (s : Nat) : List Gate := digitsG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) (Shadow7.e0P s + 6) 1613 0 16

def moveKept (s : Nat) : List Gate := keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) 1613 0 16

def moveC (s : Nat) : List Gate :=
  wordGM 1614 (Shadow7.columnsP s) ++ Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def body (j:Fin 24) (admin:Program) := Shadow7.routed j 0 1 ++ (admin ++ Shadow7.routed j 1 14)

def unbody (j:Fin 24) (reverse:Program) := Shadow7.unrouted j 1 14 ++ (reverse ++ Shadow7.unrouted j 0 1)

def physicalCells (j:Fin 24) (s:State) := readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis)

def leaveBox2 (s q : Nat) : Prop :=
  ((s+15 ≤ q ∧ q ≤ min (s + 30 + railP (s+14)) 529) ∨ (786 ≤ q ∧ q ≤ 785 + railP s) ∨ (1556 ≤ q ∧ q ≤ min 1812 (2069 - s)) ∨ (1044+s ≤ q ∧ q < 1059+s)) ∧
  ¬ (s+31 ≤ q ∧ q < Shadow7.a0P s - 1) ∧ ¬ (786 ≤ q ∧ q < Shadow7.b0P s - 1) ∧ ¬ (Shadow7.a0P s + 17 + min 3 (Shadow7.wpP s + s - 448) ≤ q ∧ q ≤ 785) ∧ q ≠ s + 15 ∧
  ¬ (1301 ≤ q ∧ q ≤ 1058 + s) ∧ ¬ (2070 ≤ q + s ∧ q ≤ 1812)

/-- A record reads only the low bit and the history wire, both fixed by the start tick. -/
theorem readCells_eq (j : Fin 24) (i n : Nat) (s : BasisState) :
    readCells (Shadow7.shape j) i n s = readCells (StairPacket.shape j) i n s := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    change cell (Shadow7.shape j) i s :: _ = cell (StairPacket.shape j) i s :: _
    exact congrArg₂ List.cons rfl (ih (i+1))

theorem physicalCells_eq (j : Fin 24) (s : State) :
    Shadow7.physicalCells j s = StairPacket.physicalCells j s :=
  Shadow7.readCells_eq j 0 15 (mappedBasis j s.basis)

theorem native_raw_read (j : Fin 24) (s : State) (q : Nat) (h : q < 20) :
    let cells := readCells (Shadow7.shape j) 0 15 (mappedBasis j s.basis)
    s.basis (nativeRawPort j q) =
      StairArchiveRaw.letterBit (StairArchiveRaw.read (cells.drop 5) (q/2)) q := by
  simpa only [Shadow7.readCells_eq] using StairPacket.native_raw_read j s q h

end ECDSAAdd.Entrant.StairPacket.Shadow7

end


/- Inlined from ShadowRoute; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic
set_option maxHeartbeats 3500000

theorem stable {j : Fin 24} {a q : Nat} (ha : a < 15)
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

/-! Measured receiver untick (kaankolcu, decf4047): the Shadow7 window's reverse ticks run the measured
`W.ReverseCarry.receiverUntick` at full width, one Toffoli cheaper per tick than `skywalkIntegerUntick`. -/
namespace ECDSAAdd.Entrant.IntegerPacket
open Arithmetic
set_option maxHeartbeats 2000000

/-- At full width the receiver untick inverts the integer tick on every odd-parity `SkywalkIntegerInput` state: there
the narrow tick is the integer tick (`narrowSkywalkTick_eq`, bounds from the decode range) and `receiverTick_roundtrip`
inverts the narrow tick. -/
theorem receiverUntick_int_roundtrip (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int) (G : Bool)
    (hp : (A+B)%2=1) (s : State) (m₁ m₂ : List Bool) (hin : SkywalkIntegerInput L A B G s.basis) :
    run (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick L L.half.length) m₂ (run (skywalkIntegerTick L) m₁ s) = s := by
  have hn : 0 < L.half.length := by simp [SkywalkIntegerLayout.half]
  have la : L.a.length = L.half.length := by
    simp [SkywalkIntegerLayout.a, SkywalkIntegerLayout.half, SkywalkIntegerLayout.ah]
  have lb : L.b.length = L.half.length := by
    have := hv.mids
    simp [SkywalkIntegerLayout.b, SkywalkIntegerLayout.half, SkywalkIntegerLayout.ah, SkywalkIntegerLayout.bh, this]
  have rA := signedDecode_range L.a.length (regValue L.a s.basis) (by simp [SkywalkIntegerLayout.a])
    (regValue_lt _ _)
  have rB := signedDecode_range L.b.length (regValue L.b s.basis) (by simp [SkywalkIntegerLayout.b])
    (regValue_lt _ _)
  have eA : signedDecode L.a.length (regValue L.a s.basis) = A := hin.1
  have eB : signedDecode L.b.length (regValue L.b s.basis) = B := hin.2.1
  rw [eA, la] at rA
  rw [eB, lb] at rB
  have hb : ∀ X : Int, -((2^(L.half.length-1):Nat):Int) ≤ X → X < ((2^(L.half.length-1):Nat):Int) →
      -((2^(L.half.length-1):Nat):Int) ≤ X/2 ∧ X/2 < ((2^(L.half.length-1):Nat):Int) := by
    intro X h1 h2
    constructor <;> omega
  have hr : (-((2^(L.half.length-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2 ∧
      (SkywalkRails.route A B).1/2 < ((2^(L.half.length-1):Nat):Int)) ∧
      (-((2^(L.half.length-1):Nat):Int) ≤ (SkywalkRails.route A B).2 ∧
      (SkywalkRails.route A B).2 < ((2^(L.half.length-1):Nat):Int)) := by
    unfold SkywalkRails.route
    split
    · exact ⟨hb B rB.1 rB.2, rA⟩
    · exact ⟨hb A rA.1 rA.2, rB⟩
  have heq := narrowSkywalkTick_eq L hv L.half.length hn le_rfl A B G hp hr.1.1 hr.1.2 hr.2.1 hr.2.2 s m₁ hin
  rw [← heq]
  exact ECDSAAdd.Entrant.W.ReverseCarry.receiverTick_roundtrip L hv L.half.length hn le_rfl s m₁ m₂
    hin.2.2.2.2.1 hin.2.2.2.2.2

/-- `back` with the full-width receiver untick. -/
def backR (p : Shape) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => backR p (i+1) n ++
    ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (ports p i) (ports p i).half.length

theorem metricsR (p : Shape) (i n : Nat) (hi : i+n≤p.length) :
    toffoliCount (backR p i n) = n*(2*(p.mid+1)-1) ∧ measurementCount (backR p i n) = n*(p.mid+1) := by
  induction n generalizing i with
  | zero => simp [backR,toffoliCount,measurementCount]
  | succ n ih =>
    have valid := ok p ⟨i,by omega⟩
    change (ports p i).Valid at valid
    have hn : 0 < (ports p i).half.length := by simp [SkywalkIntegerLayout.half]
    obtain ⟨t,m⟩ := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_counts (ports p i) _ valid hn le_rfl
    obtain ⟨c,d⟩ := ih (i+1) (by omega)
    have eq : (ports p i).ah.length=p.mid+1 := by simp [ports,SkywalkIntegerLayout.ah]
    have hl : (ports p i).half.length=p.mid+2 := by simp [SkywalkIntegerLayout.half,eq]
    have e1 : toffoliCount (backR p i (n+1)) = toffoliCount (backR p (i+1) n) +
        toffoliCount (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (ports p i) (ports p i).half.length) := by
      rw [backR, toffoliCount_append]
    have e2 : measurementCount (backR p i (n+1)) = measurementCount (backR p (i+1) n) +
        measurementCount (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (ports p i) (ports p i).half.length) := by
      rw [backR, measurementCount_append]
    have s1 : (n+1)*(2*(p.mid+1)-1) = n*(2*(p.mid+1)-1)+(2*(p.mid+1)-1) := Nat.succ_mul _ _
    have s2 : (n+1)*(p.mid+1) = n*(p.mid+1)+(p.mid+1) := Nat.succ_mul _ _
    rw [e1, e2, s1, s2, c, d, t, m]
    constructor <;> omega

attribute [local irreducible] run seq backR ports skywalkIntegerTick skywalkIntegerUntick measurementCount

private theorem composeR {P Q : BasisState → Prop} {A B I J : Program}
    (stage : Triple P A Q) (left : Restores P A I) (right : Restores Q B J) :
    Restores P (A++B) (J++I) := by
  intro s enc dec p
  rw [run_append J I,run_append A B]
  rw [right _ _ _ (stage _ _ p).2]
  exact left _ _ _ p

theorem singleR (p : Shape) (i : Fin p.length) (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (ready p i z) (skywalkIntegerTick (ports p i))
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (ports p i) (ports p i).half.length) := by
  intro s a b h
  have clean := h.2.2.2.2 i (Nat.le_refl _) i.isLt
  exact receiverUntick_int_roundtrip (ports p i) (ok p i) z.a z.b z.g odd s a b
    ⟨h.1, h.2.1, h.2.2.1, clean.1, clean.2, h.2.2.2.1⟩

theorem roundtripR (p : Shape) (i n : Nat) (bound : i+n≤p.length) (z : SkywalkRails.State)
    (odd : (z.a+z.b)%2=1) : Restores (ready p i z) (seq p i n) (backR p i n) := by
  induction n generalizing i z with
  | zero =>
    intro s a b h
    simp [backR,seq,run]
  | succ n ih =>
    rw [seq,backR]
    apply composeR (one p (j:=i) (by omega) z odd)
    · exact singleR p ⟨i,by omega⟩ z odd
    · exact ih (i+1) (by omega) (SkywalkTrace.next z) (nextOdd z odd)

end ECDSAAdd.Entrant.IntegerPacket

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic

theorem fixed_route (j : Fin 24) (a n : Nat) (bound:a+n≤15) :
    Shadow7.routed j a n=renameProgram (windowNet j) (IntegerPacket.seq (Shadow7.shape j) a n) ∧
    Shadow7.unrouted j a n=renameProgram (windowNet j) (IntegerPacket.backR (Shadow7.shape j) a n) := by
  induction n generalizing a with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have ha : a < 15 := by omega
    have h:=(skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (Shadow7.shape j) ⟨a,ha⟩))
    have hn : 0 < (IntegerPacket.ports (Shadow7.shape j) a).half.length := by simp [SkywalkIntegerLayout.half]
    have u:=ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support (IntegerPacket.ports (Shadow7.shape j) a) _
      (IntegerPacket.ok (Shadow7.shape j) ⟨a,ha⟩) hn le_rfl
    obtain ⟨f,r⟩:=ih (a+1) (by omega)
    have app (g : Wire → Wire) (P Q : Program) : renameProgram g (P++Q)=renameProgram g P++renameProgram g Q := List.map_append
    simp only [Shadow7.routed,Shadow7.unrouted,IntegerPacket.seq,IntegerPacket.backR,app,f,r]
    constructor
    · exact congrArg (fun P=>P++_) (renameProgram_congr_support _ _ _ (fun q hq=>
        Shadow7.stable ha (List.mem_toFinset.mp (h.1 hq))))
    · have cong (P : Program) (hp : wires P ⊆ (IntegerPacket.ports (Shadow7.shape j) a).wires.toFinset) :
          renameProgram (net j a) P = renameProgram (windowNet j) P :=
        renameProgram_congr_support _ _ _ (fun q hq => Shadow7.stable ha (List.mem_toFinset.mp (hp hq)))
      exact congrArg (fun P=>_++P) (cong _ u)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem pull_routed (j:Fin 24) (i n:Nat) (bound:i+n≤15) (m:List Bool) (s:State) :
    pullState (windowNet j) (run (Shadow7.routed j i n) m s)=run (seq (Shadow7.shape j) i n) m (pullState (windowNet j) s) := by
  rw [(Shadow7.fixed_route j i n bound).1,run_rename _ (netInjective j)]

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_frame (j:Fin 24) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) :
    Triple (Shadow7.onRails j i z) (Shadow7.routed j i n) (Shadow7.onRails j (i+n) (SkywalkTrace.next^[n] z)) := by
  intro s m ready
  have h:=IntegerPacket.semantic (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m ready
  rw [←Shadow7.pull_routed j i n bound m s] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_records (j:Fin 24) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (s:State) (m:List Bool) (h:Shadow7.onRails j i z s.basis) :
    readCells (Shadow7.shape j) i n (mappedBasis j (run (Shadow7.routed j i n) m s).basis)=SkywalkTrace.trace n z ∧
    ∀ d < i, cell (Shadow7.shape j) d (mappedBasis j (run (Shadow7.routed j i n) m s).basis)=cell (Shadow7.shape j) d (mappedBasis j s.basis) := by
  have hh:=records (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m h
  rw [←Shadow7.pull_routed j i n bound m s] at hh
  exact hh

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

theorem route_undo (j:Fin 24) (i n:Nat) (bound:i+n≤15) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) :
    Restores (Shadow7.onRails j i z) (Shadow7.routed j i n) (Shadow7.unrouted j i n) := by
  intro s m t ready
  have forward:=Shadow7.pull_routed j i n bound m s
  let actual:=run (Shadow7.routed j i n) m s
  have bk:pullState (windowNet j) (run (Shadow7.unrouted j i n) t actual)=run (backR (Shadow7.shape j) i n) t (pullState (windowNet j) actual):=by
    rw [(Shadow7.fixed_route j i n bound).2,run_rename _ (netInjective j)]
  have fin:=IntegerPacket.roundtripR (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m t ready
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

theorem split_run (j:Fin 24) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (s:State) (m n:List Bool)
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

def watch (j:Fin 24) :=
  let p:=Shadow7.shape j
  let L:=ports p 1
  (L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket
set_option linter.unusedSimpArgs false

theorem watch_congr (j:Fin 24) (s t:State) (agree:∀q∈Shadow7.watch j,t.basis q=s.basis q)
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

structure AdminResult (j:Fin 24) (reverse:Program) (src out:State) : Prop where
  phase : out.phase=src.phase
  unchanged : ∀q∈Shadow7.watch j,out.basis q=src.basis q
  undo : ∀m,run reverse m out=src

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run Shadow7.unrouted Shadow7.onRails

theorem body_run (j:Fin 24) (admin reverse:Program) (s:State) (m:List Bool)
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

theorem ready_after_head (j:Fin 24) (P:Program) (s:State) (a b:List Bool) (z:SkywalkRails.State)
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

def tickSites (j:Fin 24) (a:Nat) := ((ports (Shadow7.shape j) a).wires.map (windowNet j))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

def spanSites (j:Fin 24) (a n:Nat) := (List.range' a n).flatMap (Shadow7.tickSites j)

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem route_sites (j:Fin 24) (a n:Nat) (lim:a+n≤15) (q:Wire) (inP:q∈wires (Shadow7.routed j a n)) :
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

theorem route_outside (j:Fin 24) (a n:Nat) (lim:a+n≤15) (q:Wire) (free:q∉Shadow7.spanSites j a n) (s:State) (m:List Bool) :
    (run (Shadow7.routed j a n) m s).basis q=s.basis q :=
  run_preserves_outside _ _ _ _ (fun used=>free (Shadow7.route_sites j a n lim q used))

end ECDSAAdd.Entrant.StairPacket.Shadow7

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000

theorem old_clear {j:Fin 24} {a n q:Nat} (lim:a+n≤15)
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

theorem native_carry (j:Fin 24) (z:SkywalkRails.State) (s:State) (ready:Shadow7.onRails j 15 z s.basis) (q:Wire)
    (mem:q∈((ports (Shadow7.shape j) 15).carry.map (windowNet j))) : s.basis q=false:=by
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp mem
  exact (regValue_zero _ _).mp ready.2.2.2.1 _ hw

end ECDSAAdd.Entrant.StairPacket.Shadow7

end


/- Inlined from ShadowRouteCover; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket

def MayTouch (j : Fin 24) (w : Wire) : Prop :=
  (start j + 15 ≤ w ∧ w ≤ start j + 14 + 16 + (Shadow7.shape j).mid + 2) ∨
  (786 ≤ w ∧ w ≤ 787 + (Shadow7.shape j).mid) ∨
  (1556 ≤ w ∧ w ≤ 1556 + (Shadow7.shape j).mid) ∨
  (1044 + start j ≤ w ∧ w < 1044 + start j + 15)

instance (j : Fin 24) (w : Wire) : Decidable (Shadow7.MayTouch j w) := by
  unfold Shadow7.MayTouch
  infer_instance

theorem named_range (j : Fin 24) (a n q : Nat) (lim : a + n ≤ 15)
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

theorem through_body (j : Fin 24) (P : Program) (s : State) (m : List Bool) (q : Nat)
    (free : ¬Shadow7.MayTouch j (windowNet j q))
    (admin : let a := run (Shadow7.routed j 0 1) m s
      (run P (m.drop (measurementCount (Shadow7.routed j 0 1))) a).basis q = a.basis q) :
    (run (Shadow7.body j P) m s).basis q = s.basis q := by
  simp only [Shadow7.body, run_append, run_take]
  exact (Shadow7.route_outside j 1 14 (by decide) q (Shadow7.named_range j 1 14 q (by decide) free) _ _).trans
    (admin.trans (Shadow7.route_outside j 0 1 (by decide) q (Shadow7.named_range j 0 1 q (by decide) free) s m))

theorem body_cover (j : Fin 24) (P : Program) (controls effects : List Wire)
    (clean : ∀ q ∈ controls, ¬Shadow7.MayTouch j (windowNet j q))
    (apart : ∀ q ∈ controls, q ∉ effects) (cover : wires P ⊆ effects.toFinset)
    (s : State) (m : List Bool) (q : Wire) (hit : q ∈ controls) :
    (run (Shadow7.body j P) m s).basis q = s.basis q :=
  Shadow7.through_body j P s m q (clean q hit) (run_preserves_outside P _ _ q
    (fun used => apart q hit (List.mem_toFinset.mp (cover used))))

theorem ext_head (P : Program) (j : Fin 24) (Q : Program) (effects : List Wire)
    (s : State) (m n : List Bool) (q : Wire) (native : ¬Shadow7.MayTouch j (windowNet j q))
    (enter : q ∉ wires P) (admin : q ∉ effects) (cover : wires Q ⊆ effects.toFinset) :
    (run (Shadow7.body j Q) n (run P m s)).basis q = s.basis q :=
  (Shadow7.through_body j Q _ n q native (run_preserves_outside Q _ _ q
    (fun used => admin (List.mem_toFinset.mp (cover used))))).trans (run_preserves_outside P _ _ q enter)

theorem sig_tail (j : Fin 24) (h21 : j.val ≤ 22) (q : Wire)
    (lo : Shadow7.e0P (start j) + 6 ≤ q) (hi : q + start j ≤ 2054)
    (i : Nat) (ile : i ≤ start j + 14) : OB5.sig i q = q := by
  have top : start j ≤ 405 := by simp only [start]; omega
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

def firstUnchanged (j : Fin 24) (q : Wire) : Prop :=
  let r := windowNet j q
  r = (ports (Shadow7.shape j) 0).previous ∨ r ∉ (ports (Shadow7.shape j) 0).wires

instance (j : Fin 24) (q : Wire) : Decidable (Shadow7.firstUnchanged j q) := by
  unfold Shadow7.firstUnchanged
  infer_instance

theorem first_preserves (j : Fin 24) (z : SkywalkRails.State) (odd : (z.a + z.b) % 2 = 1)
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

theorem body_keeps (j : Fin 24) (P : Program) (ps : Ports) (d : Bool) (row : Nat)
    (s : State) (m : List Bool) (off : ∀ i : Fin 16, ps ⟨i.val, by omega⟩ ∉ Shadow7.spanSites j 1 14)
    (hold : Frame ps (code d) row (run P (m.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) m s))) : Kept ps d row (run (Shadow7.body j P) m s) := by
  intro i
  simp only [Shadow7.body, run_append, run_take]
  exact (Shadow7.route_outside j 1 14 (by decide) _ (off i) _ _).trans (hold ⟨i.val, by omega⟩)

theorem after_encoded (j : Fin 24) (P : Program) (outPorts : Ports) (d : Bool) (row : Nat)
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

end


/- Inlined from ShadowBounds; provenance retained from022799f6. -/
section
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open SkywalkNat

/-- The far branch alone needs the smaller word to fit the narrowed cutoff. -/
def SmallIfFar (b k : Nat) (z : SkywalkNat.State) : Prop :=
  Shadow.far b k z → min z.u z.v < 2^b

/-- At the end of a block the smaller true word fits the entry cutoff in both branches. -/
def EndSmall (b : Nat) (z : SkywalkNat.State) : Prop :=
  min (step^[15] z).u (step^[15] z).v < 2^b

namespace Envelope

private theorem half_lt {u n : Nat} (h : u < 2^n) : u/2 < 2^(n-1) := by
  rcases n with _ | n
  · have z : u = 0 := by simpa using h
    subst z
    simp
  · have e : 2^(n+1) = 2*2^n := by rw [pow_succ]; ring
    rw [e] at h
    rw [Nat.add_sub_cancel]
    omega

/-- One tick halves one of the two bounds. -/
theorem budget_step (z : SkywalkNat.State) (a b : Nat) (hu : z.u < 2^(256-a)) (hv : z.v < 2^(256-b)) :
    ((step z).u < 2^(256-(a+1)) ∧ (step z).v < 2^(256-b)) ∨
    ((step z).u < 2^(256-(b+1)) ∧ (step z).v < 2^(256-a)) := by
  have e1 : 256-(a+1) = (256-a)-1 := by omega
  have e2 : 256-(b+1) = (256-b)-1 := by omega
  have ha := half_lt hu
  have hb := half_lt hv
  rw [← e1] at ha
  rw [← e2] at hb
  by_cases h0 : z.u = 0
  · left
    have s : step z = z := by simp [step, h0]
    rw [s, h0]
    exact ⟨Nat.two_pow_pos _, hv⟩
  · by_cases he : z.u % 2 = 0
    · left
      have s : step z = ⟨z.u/2, z.v⟩ := by simp [step, h0, he]
      rw [s]
      exact ⟨ha, hv⟩
    · by_cases hle : z.v ≤ z.u
      · left
        have s : step z = ⟨(z.u-z.v)/2, z.v⟩ := by simp [step, h0, he, hle]
        rw [s]
        exact ⟨lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) ha, hv⟩
      · right
        have s : step z = ⟨(z.v-z.u)/2, z.u⟩ := by simp [step, h0, he, hle]
        rw [s]
        exact ⟨lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le _ _)) hb, hu⟩

/-- After `t` ticks the two words obey `u < 2^(256-a)`, `v < 2^(256-b)` with `a+b = t`. -/
theorem budget (x p : Nat) (hx : x < 2^256) (hp : p < 2^256) (t : Nat) :
    ∃ a b, a + b = t ∧ (step^[t] (init x p)).u < 2^(256-a) ∧ (step^[t] (init x p)).v < 2^(256-b) := by
  induction t with
  | zero => exact ⟨0, 0, rfl, hx, hp⟩
  | succ t ih =>
    obtain ⟨a, b, hab, hu, hv⟩ := ih
    rw [Function.iterate_succ_apply']
    rcases budget_step _ a b hu hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a+1, b, by omega, h1, h2⟩
    · exact ⟨b+1, a, by omega, h1, h2⟩

theorem min_lt (x p : Nat) (hx : x < 2^256) (hp : p < 2^256) (t : Nat) :
    min (step^[t] (init x p)).u (step^[t] (init x p)).v < 2^(256-(t+1)/2) := by
  obtain ⟨a, b, hab, hu, hv⟩ := budget x p hx hp t
  by_cases h : a ≤ b
  · exact lt_of_le_of_lt (min_le_right _ _)
      (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
  · exact lt_of_le_of_lt (min_le_left _ _)
      (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega)))

theorem inputs_through (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 512) :
    let b := sbP t
    let z := step^[t] (init x p)
    SmallIfFar b 15 z ∧ EndSmall b z := by
  intro b z
  have hb : b = (498 - t - (1 - (91 - t) - t / 391))/2 := rfl
  refine ⟨?_, ?_⟩
  · intro hfar
    have pos : 0 < Shadow.limb b 15 := by unfold Shadow.limb; exact Nat.two_pow_pos _
    have hf := (Nat.le_div_iff_mul_le pos).mp hfar
    have he : Shadow.limb b 15 = 2^(b+16) := by unfold Shadow.limb; rfl
    rw [he] at hf
    obtain ⟨a, c, hac, hu, hv⟩ := budget x p hx hp t
    have hbig : 2^(b+16) ≤ z.u ∨ 2^(b+16) ≤ z.v := by omega
    rcases hbig with h | h
    · have ex : b+16 < 256-a := (Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt h hu)
      exact lt_of_le_of_lt (min_le_right _ _)
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
    · have ex : b+16 < 256-c := (Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt h hv)
      exact lt_of_le_of_lt (min_le_left _ _)
        (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega)))
  · have h := min_lt x p hx hp (15+t)
    rw [Function.iterate_add_apply] at h
    have e : 256 - (15+t+1)/2 ≤ b := by omega
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) e)

theorem inputs (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 420) :
    let b := sbP t
    let z := step^[t] (init x p)
    SmallIfFar b 15 z ∧ EndSmall b z :=
  inputs_through x p t hx hp (by omega)

/-- The hand-off uses the next cutoff only when the next state is far. -/
theorem nextFarSmall (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : t ≤ 420) :
    SmallIfFar (sbP (t+15)) 15 (step^[15] (step^[t] (init x p))) := by
  rw [← Function.iterate_add_apply, Nat.add_comm 15 t]
  exact (inputs_through x p (t+15) hx hp (by omega)).1

end Envelope
end ECDSAAdd.Entrant.StairPacket.Shadow7

end


/- Inlined from ShadowLeaveFacts; provenance retained from022799f6. -/
section

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
    (crossing p k).read v=(if far b 15 z then !cross17 d else false) ∧
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
      change X.testBit (place b z)=!cross17 d
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (d%2=1)=!cross17 d
      have digit : d+1=(cross17 d).toNat+2*_ := val.1
      cases e : cross17 d
      · rw [e] at digit
        simp only [Bool.toNat_false] at digit
        simp only [Bool.not_false,decide_eq_true_eq]
        omega
      · rw [e] at digit
        simp only [Bool.toNat_true] at digit
        simp only [Bool.not_true,decide_eq_false_iff_not]
        omega
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
    min a.u a.v<2^b ∧ (a.u+a.v)/2^b<2^18 := by
  by_cases f : far b 15 z
  · exact inputFit b z (small f)
  · simp only [reduced,if_neg f]
    refine ⟨endSmall,?_⟩
    have upper : z.u+z.v < 2*limb b 15 :=
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

end


/- T2 (margin 17): threshold-2 portal gadgets. `PortalAnd.flags2` is `PortalAnd.flags` without the `A0 ∧ A1`
   make/pop: the latch over `a :: as.fst` (`a = A1`) is `[H ≥ 2]`. The stock threshold-3 gadgets are untouched. -/
section

namespace ECDSAAdd.Entrant.StairPacket.PortalAnd
open Arithmetic

def flags2 (a temp far long mag : Wire) (as bs : List (Wire×Wire)) : Program :=
  latch true none temp a as ++ [.CX temp far,.CX far temp] ++ latch false (some far) long mag bs

def flagsBack2 (a temp far long mag:Wire) (as bs:List (Wire×Wire)):Program :=
  backwardLatch false (some far) long mag bs ++ [.CX far temp,.CX temp far] ++ backwardLatch true none temp a as

theorem flags2_run (a temp far long mag : Wire) (as bs : List (Wire×Wire))
    (lA:(temp::a::sites as).Nodup)
    (lB:(far::long::mag::sites bs).Nodup) (ft:far≠temp)
    (s:State) (m:List Bool) (hf:s.basis far=false) (ht:s.basis temp=false)
    (hj:s.basis long=false)
    (ca:∀p∈as,s.basis p.2=false) (cb:∀p∈bs,s.basis p.2=false) :
    let f:=(digits a as).any s.basis
    let u:=f && (digits mag bs).any s.basis
    run (flags2 a temp far long mag as bs) m s=
      ⟨s.phase,writeBit (writeBit s.basis far f) long u⟩ := by
  let f:=(digits a as).any s.basis
  let v:State:=⟨s.phase,writeBit s.basis far f⟩
  have first:=run_latch true none temp a as lA (by simp) s m ca
  rw [ht,Bool.false_xor] at first
  simp only [active,Option.elim_none,Bool.true_and] at first
  have copy (m':List Bool) : run [.CX temp far,.CX far temp] m'
      ⟨s.phase,writeBit s.basis temp f⟩=v:= by
    simp [run,writeBit,Function.update,v,ft,ft.symm,hf]
    funext q
    by_cases qt:q=temp <;> by_cases qf:q=far <;> simp_all [Function.update]
  obtain ⟨fl,fm,fr,n⟩ : far≠long ∧ far≠mag ∧ far∉sites bs ∧ (long::mag::sites bs).Nodup := by
    have c:=List.nodup_cons.mp lB
    simpa [and_assoc] using c
  have fresh (p:Wire×Wire) (hp:p∈bs): v.basis p.2=false:=by
    have inside:p.2∈sites bs:=List.mem_flatMap.mpr ⟨p,hp,by simp⟩
    have eq:p.2≠far:=fun e=>fr (e ▸ inside)
    simp [v,writeBit,eq,cb p hp]
  have away (q:Wire) (hq:q∈digits mag bs):q≠far:=by
    intro eq; subst q
    rcases List.mem_cons.mp hq with h|h
    · exact fm h
    · obtain ⟨p,hp,h⟩:=List.mem_map.mp h
      exact fr (h ▸ List.mem_flatMap.mpr ⟨p,hp,by simp⟩)
  have anyEq:(digits mag bs).any v.basis=(digits mag bs).any s.basis:=by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨q,hq,h⟩ <;> exact ⟨q,hq,by simpa [v,writeBit,away q hq] using h⟩
  simp only [flags2,run_append,run_take,first]
  change run (latch false (some far) long mag bs) _ (run [.CX temp far,.CX far temp] _ ⟨s.phase,writeBit s.basis temp f⟩)=_
  rw [copy,run_latch _ _ _ _ _ n (by intro c h; obtain rfl:=Option.mem_some_iff.mp h;exact (List.nodup_cons.mp lB).1) _ _ fresh]
  rw [anyEq]
  simp [active,v,writeBit,fl.symm,hj,f]

theorem flags2_undo (a temp far long mag : Wire) (as bs : List (Wire×Wire))
    (lA:(temp::a::sites as).Nodup)
    (lB:(far::long::mag::sites bs).Nodup) (ft:far≠temp)
    (s:State) (m tape:List Bool) (hf:s.basis far=false) (ht:s.basis temp=false)
    (hj:s.basis long=false)
    (ca:∀p∈as,s.basis p.2=false) (cb:∀p∈bs,s.basis p.2=false) :
    run (flagsBack2 a temp far long mag as bs) tape
      (run (flags2 a temp far long mag as bs) m s)=s := by
  let f:=(digits a as).any s.basis
  let u:=f && (digits mag bs).any s.basis
  let v:State:=⟨s.phase,writeBit s.basis far f⟩
  let w:State:=⟨s.phase,writeBit v.basis long u⟩
  let k:State:=⟨s.phase,writeBit s.basis temp f⟩
  have input:run (flags2 a temp far long mag as bs) m s=w :=
    flags2_run _ _ _ _ _ _ _ lA lB ft _ _ hf ht hj ca cb
  have detail (p:Wire×Wire) (ps:List (Wire×Wire)) (h:p∈ps) : p.1∈sites ps ∧ p.2∈sites ps:=by
    constructor <;> exact List.mem_flatMap.mpr ⟨p,h,by simp⟩
  obtain ⟨fl,fm,fr,lm,lr,mr,nb⟩:far≠long ∧ far≠mag ∧ far∉sites bs ∧ long≠mag ∧
      long∉sites bs ∧ mag∉sites bs ∧ (sites bs).Nodup:=by simpa [and_assoc] using lB
  obtain ⟨ta,tr,ar,na⟩:temp≠a ∧ temp∉sites as ∧ a∉sites as ∧ (sites as).Nodup:=by simpa [and_assoc] using lA
  have stableW (q:Wire) (qf:q≠far) (ql:q≠long):w.basis q=s.basis q:=by simp [w,v,writeBit,qf,ql]
  have src (q:Wire) (hq:q∈digits mag bs):w.basis q=s.basis q:=by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact stableW _ fm.symm lm.symm
    · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hq
      exact stableW _ (fun eq=>fr (eq ▸ (detail _ _ hp).1)) (fun eq=>lr (eq ▸ (detail _ _ hp).1))
  have anyEq:(digits mag bs).any w.basis=(digits mag bs).any s.basis:=by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨q,h,hq⟩ <;> exact ⟨q,h,by simpa [src _ h] using hq⟩
  have cbw (p:Wire×Wire) (hp:p∈bs):w.basis p.2=false:=
    (stableW _ (fun eq=>fr (eq ▸ (detail _ _ hp).2)) (fun eq=>lr (eq ▸ (detail _ _ hp).2))).trans (cb _ hp)
  have reset (ms:List Bool):run (backwardLatch false (some far) long mag bs) ms w=v:=by
    rw [backward_latch _ _ _ _ _ (List.nodup_cons.mp lB).2 (by
      intro c hc; obtain rfl:=Option.mem_some_iff.mp hc; exact (List.nodup_cons.mp lB).1) _ _ cbw,anyEq]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases qf:q=far <;> by_cases ql:q=long <;> simp_all [active,w,v,u,writeBit,Function.update]
  have exchange (ms:List Bool):run [.CX far temp,.CX temp far] ms v=k:=by
    apply congrArg (State.mk s.phase)
    funext q
    by_cases qf:q=far <;> by_cases qt:q=temp <;> simp_all [v,writeBit,Function.update,ft.symm]
  have kskip (q:Wire) (ne:q≠temp):k.basis q=s.basis q:=by simp [k,writeBit,ne]
  have ka (q:Wire) (h:q∈digits a as):k.basis q=s.basis q:=by
    rcases List.mem_cons.mp h with rfl | h
    · exact kskip _ ta.symm
    · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp h
      exact kskip _ (fun eq=>tr (eq ▸ (detail _ _ hp).1))
  have anyA:(digits a as).any k.basis=(digits a as).any s.basis:=by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨q,h,hq⟩ <;> exact ⟨q,h,by simpa [ka _ h] using hq⟩
  have ktemp:k.basis temp=f:=by simp [k,writeBit]
  have clearK (ms:List Bool):run (backwardLatch true none temp a as) ms k=s:=by
    rw [backward_latch _ _ _ _ _ lA (by simp) k ms (fun p hp=>
       (kskip _ (fun eq=>tr (eq ▸ (detail _ _ hp).2))).trans (ca _ hp)),anyA,ktemp]
    apply congrArg (State.mk s.phase)
    funext q; by_cases qt:q=temp <;> simp_all [k,f,active,writeBit,Function.update]
  simp only [input,flagsBack2,run_append,run_take,reset,exchange,clearK]

end ECDSAAdd.Entrant.StairPacket.PortalAnd

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

/-- `[2 ≤ value]` of a register is the OR of its digits above the first. -/
theorem aboveFirst (a:Wire) (rest:List Wire) (s:BasisState) :
    rest.any s=decide (2≤regValue (a::rest) s) := by
  rw [nonzero]
  change decide (0<regValue rest s)=decide (2≤(if s a then 1 else 0)+2*regValue rest s)
  cases s a <;> simp <;> omega

theorem secondBit (a b:Wire) (rest:List Wire) (s:BasisState) :
    s b=true ↔ 2≤regValue (a::b::rest) s%4 := by
  change s b=true ↔ 2≤((if s a then 1 else 0)+2*((if s b then 1 else 0)+2*regValue rest s))%4
  cases s a <;> cases s b <;> simp <;> omega

theorem wideSecond (a b:Wire) (rest:List Wire) (s:BasisState) (U W:Nat)
    (hp:0<U) (eq:regValue (a::b::rest) s=W/U) :
    s b=true ↔ 2*U≤W%(4*U) := by
  rw [secondBit a b rest s,eq,Nat.mul_comm 4 U,Nat.mod_mul]
  have rem:=Nat.mod_lt W hp
  constructor
  · intro h
    have big:=Nat.mul_le_mul_left U h
    omega
  · intro h
    by_contra not
    have ub:(W/U%4)+1≤2:=by omega
    have p:=Nat.mul_le_mul_left U ub
    rw [Nat.mul_add,Nat.mul_one] at p
    omega

theorem upper2 (a b:Wire) (rest:List Wire) (s:BasisState) (U W:Nat)
    (eq:regValue (a::b::rest) s=W/U) :
    regValue rest s=W/(4*U) := by
  have z:=shiftedValue (a::b::rest) 2 (by simp) s
  rw [eq,Nat.div_div_eq_div_mul,Nat.mul_comm U] at z
  exact z

end ECDSAAdd.Entrant.StairPacket.PortalValues

end

/- Inlined from ShadowPortalFacts; provenance retained from022799f6. Restated for threshold 2 (margin 17). -/
section

namespace ECDSAAdd.Entrant.StairPacket.PortalCut


theorem orientation_shadow7 (b U u v e : Nat) (unit : 2*b≤U) (positive:0<b)
    (small : 2*U ≤ u+v → min u v < b) (en:e≤1) :
    (2*U≤u+v ∧ U≤u-e) ↔ (2*U≤u+v ∧ b≤u) := by
  by_cases f : 2*U ≤ u+v
  · have sm := small f
    omega
  · simp [f]

end ECDSAAdd.Entrant.StairPacket.PortalCut

namespace ECDSAAdd.Entrant.StairPacket.PortalCut


/-- Borrow into bit 2 of the high word (was bit 3): `M = u-e`, `X = u+v`, half limb `2U` of the quad limb `4U`. -/
theorem clear_value_shadow7 (b U u v e : Nat) (unit:2*b≤U) (positive:0<b)
    (small : 2*U ≤ u+v → min u v < b) (en:e≤1) (eu:e≤u) :
    let M:=u-e
    let X:=u+v
    let w:=if 2*U≤M%(4*U) ∧ X%(4*U)<2*U then 1 else 0
    M/(4*U)+w=if 2*U≤X ∧ b≤u then X/(4*U) else 0 := by
  dsimp only
  by_cases h:2*U≤u+v ∧ b≤u
  · rw [if_pos h]
    have sm := small h.1
    have g:v+e≤2*U:=by omega
    have z:=half_limb_borrow (2*U) (u-e) (v+e) (by omega) g
    rw [show u-e+(v+e)=u+v by omega,show 2*(2*U)=4*U by omega] at z
    exact z.symm
  · rw [if_neg h]
    have lo:u-e<2*U:=by
      by_cases f:2*U≤u+v
      · have sm := small f
        omega
      · omega
    rw [Nat.mod_eq_of_lt (show u-e<4*U by omega),Nat.div_eq_of_lt (show u-e<4*U by omega)]
    simp [show ¬ 2*U≤u-e by omega]

end ECDSAAdd.Entrant.StairPacket.PortalCut

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem actual_flags_shadow7 (a b:Wire) (as bs:List (Wire×Wire)) (mag:Wire) (A B:List Wire)
    (aShape:a::b::as.map Prod.fst=A) (bShape:PortalAnd.digits mag bs=B)
    (s:BasisState) (U small u v e:Nat) (ub:2*small≤U) (bp:0<small)
    (sz : 2*U ≤ u+v → min u v < small) (en:e≤1) (x:regValue A s=(u+v)/U) (y:regValue B s=(u-e)/U) :
    (PortalAnd.digits b as).any s=decide (2*U≤u+v) ∧
    ((PortalAnd.digits b as).any s && (PortalAnd.digits mag bs).any s)=decide (2*U≤u+v ∧ small≤u) := by
  have up:0<U:=by omega
  have far:(PortalAnd.digits b as).any s=decide (2*U≤u+v):=by
    have two:(PortalAnd.digits b as).any s=decide (2≤regValue (a::b::as.map Prod.fst) s):=
      aboveFirst a (b::as.map Prod.fst) s
    rw [two,aShape,x]
    apply Bool.eq_iff_iff.mpr; simpa only [decide_eq_true_eq] using (Nat.le_div_iff_mul_le up : 2≤(u+v)/U ↔ _)
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

theorem input_eq_shadow7 (a0 a1 b0 b1 long:Wire) (xs ys:List Wire) (s:BasisState)
    (U small u v e:Nat) (unit:2*small≤U) (bp:0<small) (sz : 2*U ≤ u+v → min u v < small) (en:e≤1) (eu:e≤u)
    (a:regValue (a0::a1::xs) s=(u+v)/U)
    (b:regValue (b0::b1::ys) s=(u-e)/U)
    (orient:s long=decide (2*U≤u+v ∧ small≤u)) (same:xs.length=ys.length) :
    (regValue ys s+(s b1 && !s a1).toNat)%2^ys.length=copyValue (some long) s (regValue xs s) := by
  have hp:0<U:=by omega
  have ax:=wideSecond _ _ _ _ U _ hp a
  have by':=wideSecond _ _ _ _ U _ hp b
  have bits:(s b1 && !s a1).toNat =
      if 2*U≤(u-e)%(4*U) ∧ (u+v)%(4*U)<2*U then 1 else 0 := by
    cases bbit:s b1 <;> cases abit:s a1 <;> simp_all
  have v':=PortalCut.clear_value_shadow7 small U u v e unit bp sz en eu
  rw [upper2 _ _ _ _ U _ b,bits,v',copyValue,orient,upper2 _ _ _ _ U _ a]
  by_cases cond:2*U≤u+v ∧ small≤u
  · simp only [cond]
    apply Nat.mod_eq_of_lt
    rw [←upper2 _ _ _ _ U _ a,←same]
    exact regValue_lt _ _
  · simp [cond]

end ECDSAAdd.Entrant.StairPacket.PortalValues

end


/- Inlined from ShadowEntryFacts; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open SkywalkNat

theorem reduced_values_shadow7 (b k : Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let T:=reduced b k z
    let f:=far b k z
    let h:=limb b k
    let d:=if f then gap b k z else 0
    let lu:=decide (f ∧ 2^b≤z.u)
    T.u=z.u-(if lu then d else 0) ∧ (T.u+T.v=z.u+z.v-d) ∧ T.u+T.v<2*h ∧
    PortalValues.negative sg T.u=PortalValues.negative sg z.u ∧
    (T.u-(PortalValues.negative sg T.u).toNat)=
      (z.u-(PortalValues.negative sg z.u).toNat)-(if lu then d else 0) := by
  by_cases f : far b k z
  · exact reduced_values b k z sg (small f)
  · have hu : 0 < limb b k := by simp [limb]
    have lt : z.u+z.v < 2*limb b k := (Nat.div_lt_iff_lt_mul hu).mp (Nat.lt_of_not_ge f)
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


theorem actual_residue_limb_shadow7 (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let T:=reduced b k z;let e:=PortalValues.negative sg z.u
    (T.u+T.v)%limb b k=(z.u+z.v)%limb b k ∧ (T.u-e.toNat)%limb b k=(z.u-e.toNat)%limb b k := by
  by_cases f : far b k z
  · exact actual_residue_limb b k z sg (small f)
  · simp [reduced,f]
end ECDSAAdd.Entrant.StairPacket.Shadow

/- T3 (item A, register margin 17): the Shadow7 window enter on the two aperture rows `sb+16`, `sb+17`
(`enterFix17`, 8 Toffoli). Port order: A rows, B rows, g n f u, the parked B wire of row `sb+18`, `e0..e0+2`, `1556`.
Generated by wA/T3/apply.py (programs, columns and row parts by wA/T3/enter17_gen.py). It replaces the
`EnterProof.*_shadow7` copies of the four-row enter on the Shadow7 path. -/
namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 8192
def input : Cols := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0x0,
  0x0,
  0x0,
  0x0]
def output : Cols := [0xa5a5ffffa5a5ffff5555aaaa5555aaaaaaaaffffaaaaffffaaaaaaaaaaaaaaaaa5a5ffffa5a5ffff5555aaaa5555aaaaaaaaffffaaaaffffaaaaaaaaaaaaaaaa,
  0x36c9000039c600006699000099660000cccc0000cccc0000cccc0000cccc000036c9000039c600006699000099660000cccc0000cccc0000cccc0000cccc0000,
  0xffffa5a5ffffa5a5f0f00f0ff0f00f0ffffff0f0fffff0f0f0f0f0f0f0f0f0f0ffffa5a5ffffa5a5f0f00f0ff0f00f0ffffff0f0fffff0f0f0f0f0f0f0f0f0f0,
  0x36c90000639c00003cc30000c33c0000ff000000ff000000ff000000ff00000036c90000639c00003cc30000c33c0000ff000000ff000000ff000000ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xc936c93639c6639c9966c33c9966c33c333300ffccccff00333300ffccccff00c936c93639c6639c9966c33c9966c33c333300ffccccff00333300ffccccff00,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0x0,
  0xf0f0aaaaf0f0aaaa0000000000000000f0f0aaaaf0f0aaaa0000000000000000f0f0aaaaf0f0aaaa0000000000000000f0f0aaaaf0f0aaaa0000000000000000,
  0xff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00ccccff00cccc,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0x0]
def mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def forward : Program := [.CX 0 2,
.CCX 4 2 0,
.CX 0 2,
.CX 1 3,
.CCX 4 3 1,
.CX 1 3,
.CX 5 2,
.CX 5 3,
.CCX 6 0 9,
.CX 9 0,
.CX 6 0,
.CX 1 10,
.CX 10 1,
.X 9,
.CCX 7 9 12,
.X 9,
.CCX 12 2 3,
.CCX 7 10 3,
.CX 12 2,
.X 9,
.measureX 12 [] [.CZ 7 9],
.X 9,
.CX 5 2,
.CX 5 3,
.CX 0 2,
.CCX 4 2 0,
.CX 0 2,
.CCX 4 3 1,
.CX 1 3,
.CX 1 5,
.CX 3 5,
.CX 8 11,
.CX 11 8]
theorem forward_checked : eval mask forward input=(true,output) := by decide +kernel
def backward : Program := [.CX 11 8,
.CX 8 11,
.CX 3 5,
.CX 1 5,
.CX 1 3,
.CCX 4 3 1,
.CX 0 2,
.CCX 4 2 0,
.CX 0 2,
.CX 5 3,
.CX 5 2,
.X 9,
.CCX 7 9 12,
.X 9,
.CX 12 2,
.CCX 7 10 3,
.CCX 12 2 3,
.X 9,
.measureX 12 [] [.CZ 7 9],
.X 9,
.CX 10 1,
.CX 1 10,
.CX 6 0,
.CX 9 0,
.measureX 9 [] [.CZ 6 0],
.CX 5 3,
.CX 5 2,
.CX 1 3,
.CCX 4 3 1,
.CX 1 3,
.CX 0 2,
.CCX 4 2 0,
.CX 0 2]
theorem backward_checked : eval mask backward output=(true,input) := by decide +kernel
def result (r : Nat) : Nat :=
  let ra:=r%4; let rb:=r/4%4; let g:=r.testBit 4; let neg:=r.testBit 5
  let f:=r.testBit 6; let u:=r.testBit 7; let p:=r.testBit 8
  let a:=if g then rb else ra; let m:=(if g then ra else rb) ^^^ (if neg then 3 else 0)
  let s0:=f && a.testBit 0; let s1:=a.testBit 1
  let x:=if f then 1 else a%2
  let sm:=if u then (m+(5-(s0.toNat+2*s1.toNat))%4)%4 else m
  let y:=sm ^^^ (if neg then 3 else 0)
  let l:=if g then y else x; let b:=if g then x else y
  l+4*b+16*g.toNat+32*(neg ^^ l.testBit 1 ^^ b.testBit 1).toNat+
    64*f.toNat+128*u.toNat+512*s0.toNat+1024*s1.toNat+2048*p.toNat
def width : Nat := 13

def Formula (r : Nat) : Prop :=
  ∀ q:Fin width,(get input q).testBit r=r.testBit q ∧ (get output q).testBit r=(result r).testBit q
instance (r:Nat) : Decidable (Formula r) := inferInstanceAs (Decidable (∀_:Fin width,_))

def Interval (lo n : Nat) : Prop := ∀ j : Fin n, Formula (lo+j)
instance (lo n:Nat) : Decidable (Interval lo n) := inferInstanceAs (Decidable (∀_:Fin n,_))

theorem combine (lo n : Nat) (a:Interval lo n) (b:Interval (lo+n) n) : Interval lo (n+n) := by
  intro j
  by_cases h:j.val<n
  · exact a ⟨j,h⟩
  · have hj:=j.isLt
    have rhs:=b ⟨j.val-n,by omega⟩
    change Formula (lo+n+(j.val-n)) at rhs
    change Formula (lo+j.val)
    rwa [show lo+n+(j.val-n)=lo+j.val by omega] at rhs
end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
private theorem part0_16 : Interval 0 16 := by decide +kernel
private theorem part16_16 : Interval 16 16 := by decide +kernel
private theorem part32_16 : Interval 32 16 := by decide +kernel
private theorem part48_16 : Interval 48 16 := by decide +kernel
private theorem part64_16 : Interval 64 16 := by decide +kernel
private theorem part80_16 : Interval 80 16 := by decide +kernel
private theorem part96_16 : Interval 96 16 := by decide +kernel
private theorem part112_16 : Interval 112 16 := by decide +kernel
private theorem part128_16 : Interval 128 16 := by decide +kernel
private theorem part144_16 : Interval 144 16 := by decide +kernel
private theorem part160_16 : Interval 160 16 := by decide +kernel
private theorem part176_16 : Interval 176 16 := by decide +kernel
private theorem part192_16 : Interval 192 16 := by decide +kernel
private theorem part208_16 : Interval 208 16 := by decide +kernel
private theorem part224_16 : Interval 224 16 := by decide +kernel
private theorem part240_16 : Interval 240 16 := by decide +kernel
private theorem part256_16 : Interval 256 16 := by decide +kernel
private theorem part272_16 : Interval 272 16 := by decide +kernel
private theorem part288_16 : Interval 288 16 := by decide +kernel
private theorem part304_16 : Interval 304 16 := by decide +kernel
private theorem part320_16 : Interval 320 16 := by decide +kernel
private theorem part336_16 : Interval 336 16 := by decide +kernel
private theorem part352_16 : Interval 352 16 := by decide +kernel
private theorem part368_16 : Interval 368 16 := by decide +kernel
private theorem part384_16 : Interval 384 16 := by decide +kernel
private theorem part400_16 : Interval 400 16 := by decide +kernel
private theorem part416_16 : Interval 416 16 := by decide +kernel
private theorem part432_16 : Interval 432 16 := by decide +kernel
private theorem part448_16 : Interval 448 16 := by decide +kernel
private theorem part464_16 : Interval 464 16 := by decide +kernel
private theorem part480_16 : Interval 480 16 := by decide +kernel
private theorem part496_16 : Interval 496 16 := by decide +kernel
theorem allRows : Interval 0 512 := (combine 0 256 (combine 0 128 (combine 0 64 (combine 0 32 (combine 0 16 part0_16 part16_16) (combine 32 16 part32_16 part48_16)) (combine 64 32 (combine 64 16 part64_16 part80_16) (combine 96 16 part96_16 part112_16))) (combine 128 64 (combine 128 32 (combine 128 16 part128_16 part144_16) (combine 160 16 part160_16 part176_16)) (combine 192 32 (combine 192 16 part192_16 part208_16) (combine 224 16 part224_16 part240_16)))) (combine 256 128 (combine 256 64 (combine 256 32 (combine 256 16 part256_16 part272_16) (combine 288 16 part288_16 part304_16)) (combine 320 32 (combine 320 16 part320_16 part336_16) (combine 352 16 part352_16 part368_16))) (combine 384 64 (combine 384 32 (combine 384 16 part384_16 part400_16) (combine 416 16 part416_16 part432_16)) (combine 448 32 (combine 448 16 part448_16 part464_16) (combine 480 16 part480_16 part496_16)))))
end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic CodecBitSliceVerify ArchiveFieldScratch StairArchiveHandoff
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 8192

def step (inv:Bool) := if inv then backward else forward
def source (inv:Bool) := if inv then output else input
def destination (inv:Bool) := if inv then input else output
def initial (inv:Bool) (r:Nat) := if inv then result r else r
def finalValue (inv:Bool) (r:Nat) := if inv then r else result r

private theorem width_bound (inv:Bool) : wires (step inv) ⊆ Finset.range width := by
  apply bounded
  cases inv <;> decide +kernel

private theorem lookup (inv : Bool) (r : Fin 512) (q:Fin width) :
    (get (source inv) q).testBit r=(initial inv r).testBit q ∧
    (get (destination inv) q).testBit r=(finalValue inv r).testBit q := by
  have h:=allRows r q
  simp only [Nat.zero_add] at h
  cases inv
  · exact h
  · exact ⟨h.2,h.1⟩

theorem apply_guard (f:Wire→Wire) (inv:Bool) (r:Fin 512)
    (inj:∀a b : Fin width, f a=f b → a=b) (m:List Bool) (s:State)
    (entry:∀q∈wires (step inv),s.basis (f q)=(initial inv r).testBit q) :
    (run (renameProgram f (step inv)) m s).phase=s.phase ∧
    (∀q∈wires (step inv),(run (renameProgram f (step inv)) m s).basis (f q)=(finalValue inv r).testBit q) ∧
    ∀q∉wires (renameProgram f (step inv)),(run (renameProgram f (step inv)) m s).basis q=s.basis q := by
  have targetOK:∀g∈step inv,target g < (source inv).length := by cases inv <;> decide +kernel
  have active:mask.testBit r=true := by
    change (2^512-1:Nat).testBit r=true
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true r.isLt
  let v:=value (source inv) r
  have rel:Rel (source inv) v r:=value_rel _ _
  have bound:=width_bound inv
  have finInj:∀a∈Finset.range width,∀b∈Finset.range width,f a=f b → a=b := by
    intro a ha b hb eq
    exact congrArg Fin.val (inj ⟨a,Finset.mem_range.mp ha⟩ ⟨b,Finset.mem_range.mp hb⟩ eq)
  have data:∀q∈wires (step inv),(pullState f s).basis q=v.testBit q := by
    intro q h
    exact ((entry q h).trans (lookup inv r ⟨q,Finset.mem_range.mp (bound h)⟩).1.symm).trans (rel q).symm
  have checked:eval mask (step inv) (source inv)=(true,destination inv) := by
    cases inv
    · exact forward_checked
    · exact backward_checked
  have logical:=StairArchiveRows.run_row (step inv) mask r v m (pullState f s)
    (source inv) (destination inv) active targetOK rel checked data
  have phys:=run_rename_pool f _ finInj _ bound m (pullState f s) s rfl (fun _ _=>rfl)
  exact ⟨phys.1.trans logical.1,
    fun q h=>((phys.2 q (bound h)).trans (logical.2.1 q h)).trans (lookup inv r ⟨q,Finset.mem_range.mp (bound h)⟩).2,
    fun q h=>run_preserves_outside _ _ _ q h⟩

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- A two-row slice of the signed rail is the one's complement of its magnitude when the rail is negative. -/
def signedPair (n:Bool) (m:Nat) := m ^^^ (if n then 3 else 0)

def encodedPair (g neg:Bool) (a m:Nat) := if g then signedPair neg m+4*a else a+4*signedPair neg m

def rowOf (a m:Nat) (g neg f u p:Bool) :=
  encodedPair g neg a m+16*g.toNat+32*neg.toNat+64*f.toNat+128*u.toNat+256*p.toNat

/-- Sum rail rows `sb+16, sb+17` after the enter: `1` when far, unchanged (below 2) otherwise. -/
def updateA (a:Nat) : Bool→Nat
  | true => 1
  | false => a%2
/-- Bit 0 of the saved high word: the sum rail's row `sb+16` under the far flag. -/
def saveLow (a:Nat) : Bool→Nat
  | true => a%2
  | false => 0
/-- Signed rail rows `sb+16, sb+17` (as a magnitude): `m+(1-H) mod 4` under the long flag. -/
def updateM (a m:Nat) (f:Bool) : Bool→Nat
  | true => (m+(5-(saveLow a f+2*(a/2%2)))%4)%4
  | false => m

def expected (a m:Nat) (g neg f u p:Bool) :=
  encodedPair g neg (updateA a f) (updateM a m f u)+16*g.toNat+
    32*(neg ^^ (updateA a f).testBit 1 ^^ (signedPair neg (updateM a m f u)).testBit 1).toNat+
    64*f.toNat+128*u.toNat+512*(saveLow a f+2*(a/2%2)+4*p.toNat)

def RowSpec (x:Nat) : Prop :=
  ∀ y:Fin 4,∀g n f u p:Bool,rowOf x y g n f u p<512 ∧ result (rowOf x y g n f u p)=expected x y g n f u p
instance (x:Nat):Decidable (RowSpec x):=inferInstanceAs (Decidable (∀_:Fin 4,∀ _ _ _ _ _:Bool,_))

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
theorem row0 : RowSpec 0 := by decide +kernel
theorem row1 : RowSpec 1 := by decide +kernel
theorem row2 : RowSpec 2 := by decide +kernel
theorem row3 : RowSpec 3 := by decide +kernel

theorem shape (a m:Fin 4) (g n f u p:Bool) :
    rowOf a m g n f u p<512 ∧ result (rowOf a m g n f u p)=expected a m g n f u p := by
  apply (show RowSpec a from ?_) m g n f u p
  fin_cases a
  · exact row0
  · exact row1
  · exact row2
  · exact row3

theorem small_top : ∀ a:Fin 2,a.val.testBit 1=false := by decide +kernel
theorem signed_top : ∀ e:Bool,∀ m:Fin 2,(signedPair e m.val).testBit 1=e := by decide +kernel
theorem xor_cancel (e:Bool) : (e ^^ false ^^ e)=false := by cases e <;> rfl

theorem expected_small (a m:Nat) (g neg f u p:Bool) {x y S:Nat}
    (hx:updateA a f=x) (hy:updateM a m f u=y) (x2:x<2) (y2:y<2)
    (hs:saveLow a f+2*(a/2%2)+4*p.toNat=S) :
    expected a m g neg f u p=encodedPair g neg x y+16*g.toNat+64*f.toNat+128*u.toNat+512*S := by
  subst hx
  subst hy
  subst hs
  have t1:(updateA a f).testBit 1=false:=small_top ⟨_,x2⟩
  have t2:(signedPair neg (updateM a m f u)).testBit 1=neg:=signed_top neg ⟨_,y2⟩
  unfold expected
  rw [t1,t2,xor_cancel]
  simp only [Bool.toNat_false,Nat.mul_zero,Nat.add_zero]

theorem bit_toNat (q:Nat) : (decide (q%2=1)).toNat=q%2 := by
  rcases Nat.mod_two_eq_zero_or_one q with h|h <;> rw [h] <;> rfl

/-- Removing `c` whole units below the quotient. -/
theorem div_sub (W U c:Nat) (pos:0<U) (le:c≤W/U) : (W-c*U)/U=W/U-c ∧ (W-c*U)%U=W%U := by
  have h:=Nat.div_add_mod W U
  obtain ⟨d,hd⟩:∃d,W/U=c+d:=⟨W/U-c,by omega⟩
  have m:U*(W/U)=c*U+U*d:=by rw [hd];ring
  have e:W-c*U=W%U+U*d:=by omega
  rw [e,Nat.add_mul_div_left _ _ pos,Nat.add_mul_mod_self_left,Nat.mod_mod,Nat.div_eq_of_lt (Nat.mod_lt _ pos),hd]
  omega

/-- The long far case in numbers: `X = M+j` with `j ≤ U` and `X/U = c+1`; the gap is `c*U`. -/
theorem far_long_nat (U X M j c:Nat) (pos:0<U) (hX:X=M+j) (hj:j≤U) (hH:X/U=c+1) :
    c*U≤M ∧ c*U+U≤X ∧ (X-c*U)/U=1 ∧ (X-c*U)%U=X%U ∧ (M-c*U)%U=M%U ∧
    (M-c*U)/U%4=(M/U%4+(5-(c+1)%4)%4)%4 ∧ (M-c*U)/U<2 := by
  have hx:=Nat.div_add_mod X U
  rw [hH] at hx
  have xr:=Nat.mod_lt X pos
  have e1:U*(c+1)=c*U+U:=by ring
  have e2:(c+2)*U=c*U+U+U:=by ring
  have dM:c*U≤M:=by omega
  have q1:c≤M/U:=by
    by_contra hlt
    have lt:M/U<c:=by omega
    have:=(Nat.div_lt_iff_lt_mul pos).mp lt
    omega
  have q2:M/U<c+2:=(Nat.div_lt_iff_lt_mul pos).mpr (by omega)
  have a:=div_sub X U c pos (by omega)
  have b:=div_sub M U c pos q1
  refine ⟨dM,by omega,?_,a.2,b.2,?_,?_⟩
  · rw [a.1,hH];omega
  · rw [b.1];omega
  · rw [b.1];omega

def pair (W U:Nat):Nat:=W/U%4

/-- Row algebra of the two-row enter on a block state (`U = limb`, far means `2 ≤ H`, gap `(H-1)U`). -/
theorem shadow_digits (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small:Shadow7.SmallIfFar b k z) :
    updateA (pair (z.u+z.v) (Shadow.limb b k)) (decide (Shadow.far b k z))=pair ((Shadow.reduced b k z).u+(Shadow.reduced b k z).v) (Shadow.limb b k) ∧
    updateM (pair (z.u+z.v) (Shadow.limb b k)) (pair (z.u-(PortalValues.negative sg z.u).toNat) (Shadow.limb b k)) (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u))=
      pair ((Shadow.reduced b k z).u-(PortalValues.negative sg z.u).toNat) (Shadow.limb b k) ∧
    pair ((Shadow.reduced b k z).u+(Shadow.reduced b k z).v) (Shadow.limb b k)<2 ∧ pair ((Shadow.reduced b k z).u-(PortalValues.negative sg z.u).toNat) (Shadow.limb b k)<2 ∧
    saveLow (pair (z.u+z.v) (Shadow.limb b k)) (decide (Shadow.far b k z))+2*(pair (z.u+z.v) (Shadow.limb b k)/2%2)+
        4*(decide ((z.u+z.v)/Shadow.limb b k/4%2=1)).toNat=
      (if Shadow.far b k z then Shadow.high b k z%8 else 0) ∧
    ((Shadow.reduced b k z).u+(Shadow.reduced b k z).v)%Shadow.limb b k=(z.u+z.v)%Shadow.limb b k ∧ ((Shadow.reduced b k z).u-(PortalValues.negative sg z.u).toNat)%Shadow.limb b k=(z.u-(PortalValues.negative sg z.u).toNat)%Shadow.limb b k ∧
    (Shadow.reduced b k z).u+(Shadow.reduced b k z).v<2*Shadow.limb b k ∧
    PortalValues.negative sg (Shadow.reduced b k z).u=PortalValues.negative sg z.u := by
  have pos:0<Shadow.limb b k:=by unfold Shadow.limb;exact Nat.two_pow_pos _
  have light:2^b≤Shadow.limb b k:=by
    unfold Shadow.limb
    apply Nat.pow_le_pow_right (by decide)
    omega
  have e1:(PortalValues.negative sg z.u).toNat≤1:=by cases PortalValues.negative sg z.u <;> decide
  have eu:(PortalValues.negative sg z.u).toNat≤z.u:=by
    by_cases hz:0<z.u
    · omega
    · have z0:PortalValues.negative sg z.u=false:=by
        unfold PortalValues.negative
        rw [decide_eq_false hz,Bool.and_false]
      rw [z0]
      exact Nat.zero_le _
  by_cases hf:Shadow.far b k z
  · have sm:=small hf
    have hH:2≤(z.u+z.v)/Shadow.limb b k:=hf
    obtain ⟨c,hc⟩:∃c,(z.u+z.v)/Shadow.limb b k=c+1:=⟨(z.u+z.v)/Shadow.limb b k-1,by omega⟩
    have gapEq:Shadow.gap b k z=c*Shadow.limb b k:=by
      show ((z.u+z.v)/Shadow.limb b k-1)*Shadow.limb b k=_
      rw [hc,Nat.add_sub_cancel]
    have fT:decide (Shadow.far b k z)=true:=decide_eq_true hf
    have hi8:(if Shadow.far b k z then Shadow.high b k z%8 else 0)=(z.u+z.v)/Shadow.limb b k%8:=
      (if_pos hf).trans rfl
    by_cases hl:2^b≤z.u
    · have lT:decide (Shadow.far b k z ∧ 2^b≤z.u)=true:=decide_eq_true ⟨hf,hl⟩
      have hv:z.v<2^b:=by omega
      have red:Shadow.reduced b k z=⟨z.u-c*Shadow.limb b k,z.v⟩:=by
        unfold Shadow.reduced
        rw [if_pos hf,if_pos hl,gapEq]
      have hX:z.u+z.v=(z.u-(PortalValues.negative sg z.u).toNat)+(z.v+(PortalValues.negative sg z.u).toNat):=by omega
      have hj:z.v+(PortalValues.negative sg z.u).toNat≤Shadow.limb b k:=by omega
      obtain ⟨dM,dX,x1,xr,mr,md,m2⟩:=far_long_nat (Shadow.limb b k) (z.u+z.v) (z.u-(PortalValues.negative sg z.u).toNat) (z.v+(PortalValues.negative sg z.u).toNat) c pos hX hj hc
      have s1:z.u-c*Shadow.limb b k+z.v=z.u+z.v-c*Shadow.limb b k:=by omega
      have s2:z.u-c*Shadow.limb b k-(PortalValues.negative sg z.u).toNat=z.u-(PortalValues.negative sg z.u).toNat-c*Shadow.limb b k:=by omega
      rw [red,fT,lT]
      dsimp only
      rw [s1,s2]
      refine ⟨?_,?_,?_,?_,?_,xr,mr,?_,?_⟩
      · show 1=(z.u+z.v-c*Shadow.limb b k)/Shadow.limb b k%4
        omega
      · show ((z.u-(PortalValues.negative sg z.u).toNat)/Shadow.limb b k%4+(5-((z.u+z.v)/Shadow.limb b k%4%2+2*((z.u+z.v)/Shadow.limb b k%4/2%2)))%4)%4=
          (z.u-(PortalValues.negative sg z.u).toNat-c*Shadow.limb b k)/Shadow.limb b k%4
        rw [md]
        omega
      · show (z.u+z.v-c*Shadow.limb b k)/Shadow.limb b k%4<2
        omega
      · show (z.u-(PortalValues.negative sg z.u).toNat-c*Shadow.limb b k)/Shadow.limb b k%4<2
        exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) m2
      · rw [hi8,bit_toNat]
        show (z.u+z.v)/Shadow.limb b k%4%2+2*((z.u+z.v)/Shadow.limb b k%4/2%2)+4*((z.u+z.v)/Shadow.limb b k/4%2)=(z.u+z.v)/Shadow.limb b k%8
        omega
      · exact (Nat.div_lt_iff_lt_mul pos).mp (by omega)
      · have tp:0<z.u-c*Shadow.limb b k:=by omega
        have zp:0<z.u:=by omega
        unfold PortalValues.negative
        rw [decide_eq_true tp,decide_eq_true zp]
    · have lF:decide (Shadow.far b k z ∧ 2^b≤z.u)=false:=decide_eq_false (fun h=>hl h.2)
      have red:Shadow.reduced b k z=⟨z.u,z.v-c*Shadow.limb b k⟩:=by
        unfold Shadow.reduced
        rw [if_pos hf,if_neg hl,gapEq]
      have hx:=Nat.div_add_mod (z.u+z.v) (Shadow.limb b k)
      rw [hc] at hx
      have e1':Shadow.limb b k*(c+1)=c*Shadow.limb b k+Shadow.limb b k:=by ring
      have a:=div_sub (z.u+z.v) (Shadow.limb b k) c pos (by omega)
      have s1:z.u+(z.v-c*Shadow.limb b k)=z.u+z.v-c*Shadow.limb b k:=by omega
      have mz:(z.u-(PortalValues.negative sg z.u).toNat)/Shadow.limb b k=0:=Nat.div_eq_of_lt (by omega)
      rw [red,fT,lF]
      dsimp only
      rw [s1]
      refine ⟨?_,rfl,?_,?_,?_,a.2,rfl,?_,rfl⟩
      · show 1=(z.u+z.v-c*Shadow.limb b k)/Shadow.limb b k%4
        rw [a.1,hc]
        omega
      · show (z.u+z.v-c*Shadow.limb b k)/Shadow.limb b k%4<2
        rw [a.1,hc]
        omega
      · show (z.u-(PortalValues.negative sg z.u).toNat)/Shadow.limb b k%4<2
        omega
      · rw [hi8,bit_toNat]
        show (z.u+z.v)/Shadow.limb b k%4%2+2*((z.u+z.v)/Shadow.limb b k%4/2%2)+4*((z.u+z.v)/Shadow.limb b k/4%2)=(z.u+z.v)/Shadow.limb b k%8
        omega
      · exact (Nat.div_lt_iff_lt_mul pos).mp (by rw [a.1,hc];omega)
  · have hlt:(z.u+z.v)/Shadow.limb b k<2:=by
      have nf:¬2≤(z.u+z.v)/Shadow.limb b k:=hf
      omega
    have fF:decide (Shadow.far b k z)=false:=decide_eq_false hf
    have lF:decide (Shadow.far b k z ∧ 2^b≤z.u)=false:=decide_eq_false (fun h=>hf h.1)
    have red:Shadow.reduced b k z=z:=by
      unfold Shadow.reduced
      rw [if_neg hf]
    have xl:z.u+z.v<2*Shadow.limb b k:=(Nat.div_lt_iff_lt_mul pos).mp hlt
    have ml:(z.u-(PortalValues.negative sg z.u).toNat)/Shadow.limb b k<2:=(Nat.div_lt_iff_lt_mul pos).mpr (by omega)
    rw [red,fF,lF,if_neg hf]
    refine ⟨?_,rfl,?_,?_,?_,rfl,rfl,xl,rfl⟩
    · show (z.u+z.v)/Shadow.limb b k%4%2=(z.u+z.v)/Shadow.limb b k%4
      generalize (z.u+z.v)/Shadow.limb b k = q at hlt ⊢
      omega
    · show (z.u+z.v)/Shadow.limb b k%4<2
      generalize (z.u+z.v)/Shadow.limb b k = q at hlt ⊢
      omega
    · show (z.u-(PortalValues.negative sg z.u).toNat)/Shadow.limb b k%4<2
      generalize (z.u-(PortalValues.negative sg z.u).toNat)/Shadow.limb b k = q at ml ⊢
      omega
    · rw [bit_toNat]
      show 0+2*((z.u+z.v)/Shadow.limb b k%4/2%2)+4*((z.u+z.v)/Shadow.limb b k/4%2)=0
      generalize (z.u+z.v)/Shadow.limb b k = q at hlt ⊢
      omega

def initialRow (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) :=
  rowOf (pair (z.u+z.v) (Shadow.limb b k)) (pair (z.u-(PortalValues.negative sg z.u).toNat) (Shadow.limb b k)) g (PortalValues.negative sg z.u)
    (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u)) (decide ((z.u+z.v)/Shadow.limb b k/4%2=1))

def shadowRow (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) :=
  encodedPair g (PortalValues.negative sg z.u) (pair ((Shadow.reduced b k z).u+(Shadow.reduced b k z).v) (Shadow.limb b k))
      (pair ((Shadow.reduced b k z).u-(PortalValues.negative sg z.u).toNat) (Shadow.limb b k))+16*g.toNat+
    64*(decide (Shadow.far b k z)).toNat+128*(decide (Shadow.far b k z ∧ 2^b≤z.u)).toNat+
    512*(if Shadow.far b k z then Shadow.high b k z%8 else 0)

theorem rows (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) (small:Shadow7.SmallIfFar b k z) :
    initialRow b k z g sg<512 ∧ result (initialRow b k z g sg)=shadowRow b k z g sg := by
  obtain ⟨dA,dM,a0,m0,hb,_,_,_,_⟩:=shadow_digits b k z sg small
  have sh:=shape ⟨pair (z.u+z.v) (Shadow.limb b k),Nat.mod_lt _ (by decide)⟩
    ⟨pair (z.u-(PortalValues.negative sg z.u).toNat) (Shadow.limb b k),Nat.mod_lt _ (by decide)⟩ g (PortalValues.negative sg z.u)
    (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u)) (decide ((z.u+z.v)/Shadow.limb b k/4%2=1))
  refine ⟨sh.1,sh.2.trans ?_⟩
  have ex:=expected_small (pair (z.u+z.v) (Shadow.limb b k)) (pair (z.u-(PortalValues.negative sg z.u).toNat) (Shadow.limb b k)) g (PortalValues.negative sg z.u)
    (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u)) (decide ((z.u+z.v)/Shadow.limb b k/4%2=1)) dA dM a0 m0 hb
  exact ex

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 10000

def rowBefore (inv:Bool) (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :=
  if inv then shadowRow b k z g s else initialRow b k z g s

def rowAfter (inv:Bool) (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :=
  if inv then initialRow b k z g s else shadowRow b k z g s

theorem actual_shadow (map:Wire→Wire) (P:Program) (inv:Bool) (b k:Nat) (z:SkywalkNat.State)
    (g s:Bool) (small : Shadow7.SmallIfFar b k z)
    (injective:∀a c:Fin width,map a=map c→a=c) (emitted:P=renameProgram map (step inv))
    (origin:State) (tape:List Bool)
    (data:∀q∈wires (step inv),origin.basis (map q)=(rowBefore inv b k z g s).testBit q) :
    (run P tape origin).phase=origin.phase ∧
    (∀q∈wires (step inv),(run P tape origin).basis (map q)=(rowAfter inv b k z g s).testBit q) ∧
    ∀q∉wires P,(run P tape origin).basis q=origin.basis q := by
  have h:=rows b k z g s small
  let row:Fin 512:=⟨initialRow b k z g s,h.1⟩
  have each (q:Wire) (hq:q∈wires (step inv)):origin.basis (map q)=(initial inv row).testBit q:=by
    cases inv <;> simpa [initial,row,h.2,rowBefore] using data q hq
  rw [emitted]
  have act:=apply_guard map inv row injective tape origin each
  refine ⟨act.1,?_,act.2.2⟩
  intro q hq
  have value:=act.2.1 q hq
  cases inv <;> simpa [finalValue,row,h.2,rowAfter] using value

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic

theorem slice_value (r:List Wire) (k:Nat) (hi:k+2≤r.length) (s:BasisState) :
    regValue ((r.drop k).take 2) s=pair (regValue r s) (2^k) := by
  rw [EnterProof.takeValue _ _ (by simp;omega),PortalValues.shiftedValue _ _ (by omega)]
  rfl

private theorem pair_inverse : ∀x:Fin 4,(3-x.val) ^^^ 3=x.val := by decide +kernel

theorem sign_digits (r:List Wire) (size:r.length=2) (s:BasisState) (neg:Bool) :
    regValue r s=signedPair neg (regValue r (fun q=>s q ^^ neg)) := by
  cases neg
  · simp [signedPair]
  · simp only [Bool.xor_true,regValue_complement,size,signedPair,ite_true]
    exact (pair_inverse ⟨regValue r s,by simpa [size] using regValue_lt r s⟩).symm

structure Ports (A B:List Wire) (g n f u pk:Wire) (rs:List Wire) where
  a : A.length=2
  b : B.length=2
  clear : List Wire
  list : rs=A++B++[g,n,f,u,pk]++clear

theorem read_ports {A B g n f u pk rs} (ports:Ports A B g n f u pk rs) (z:SkywalkNat.State) (k b:Nat) (G S:Bool)
    (s:BasisState) (G0:s g=G) (N:s n=PortalValues.negative S z.u)
    (F:s f=decide (Shadow.far b k z)) (U:s u=decide (Shadow.far b k z ∧ 2^b≤z.u))
    (PK:s pk=decide ((z.u+z.v)/Shadow.limb b k/4%2=1))
    (zero:∀q∈ports.clear,s q=false)
    (x:regValue (if G then B else A) s=pair (z.u+z.v) (Shadow.limb b k))
    (y:regValue (if G then A else B) (fun q=>s q ^^ PortalValues.negative S z.u)=
      pair (z.u-(PortalValues.negative S z.u).toNat) (Shadow.limb b k)) :
    regValue rs s=initialRow b k z G S := by
  have h0:regValue ports.clear s=0:=(regValue_zero _ _).mpr zero
  have controlValue:regValue [g,n,f,u,pk] s=
      (s g).toNat+2*((s n).toNat+2*((s f).toNat+2*((s u).toNat+2*(s pk).toNat))):=by
    show (if s g then 1 else 0)+2*((if s n then 1 else 0)+2*((if s f then 1 else 0)+
      2*((if s u then 1 else 0)+2*((if s pk then 1 else 0)+2*0))))=_
    cases s g <;> cases s n <;> cases s f <;> cases s u <;> cases s pk <;> rfl
  rw [ports.list,regValue_append,regValue_append,regValue_append,h0,Nat.mul_zero,Nat.add_zero,
    List.length_append,ports.a,ports.b,controlValue,G0,N,F,U,PK]
  cases G <;> simp only [Bool.false_eq_true,ite_false,ite_true] at x y
  · have y0:=sign_digits B ports.b s (PortalValues.negative S z.u)
    rw [y] at y0
    rw [x,y0];simp only [initialRow,rowOf,encodedPair,Bool.false_eq_true,ite_false,Bool.toNat_false];omega
  · have y0:=sign_digits A ports.a s (PortalValues.negative S z.u)
    rw [y] at y0
    rw [x,y0];simp only [initialRow,rowOf,encodedPair,ite_true,Bool.toNat_true];omega

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic
set_option maxRecDepth 16000

theorem forward_all : wires forward=Finset.range width:=by decide +kernel

def leftWord (g e:Bool) (A M:Nat) := if g then signedPair e M else A
def rightWord (g e:Bool) (A M:Nat) := if g then A else signedPair e M

private theorem signedSmall (e:Bool) (M:Fin 4) : signedPair e M<4 := by
  have t:∀b:Bool,∀m:Fin 4,signedPair b m<4:=by decide +kernel
  exact t e M

theorem projected (b k:Nat) (z:SkywalkNat.State) (G S:Bool) :
    let T:=Shadow.reduced b k z;let V:=Shadow.limb b k;let e:=PortalValues.negative S z.u
    let A:=pair (T.u+T.v) V;let M:=pair (T.u-e.toNat) V;let W:=shadowRow b k z G S
    W%4=leftWord G e A M ∧ (W/4)%4=rightWord G e A M ∧ W/4096=0 := by
  dsimp only
  let T:=Shadow.reduced b k z;let V:=Shadow.limb b k;let e:=PortalValues.negative S z.u
  let A:=pair (T.u+T.v) V;let M:=pair (T.u-e.toNat) V
  have ar:A<4:=Nat.mod_lt _ (by decide)
  have mr:M<4:=Nat.mod_lt _ (by decide)
  have sn:signedPair e M<4:=signedSmall e ⟨M,mr⟩
  have gr:G.toNat≤1:=by cases G <;> decide
  let f:=decide (Shadow.far b k z)
  let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  have fb:f.toNat≤1:=by cases f <;> decide
  have ub:u.toNat≤1:=by cases u <;> decide
  let h:=(if Shadow.far b k z then Shadow.high b k z%8 else 0)
  have hh:h<8:=by dsimp [h];split <;> omega
  let X:=encodedPair G e A M+16*G.toNat+64*f.toNat+128*u.toNat+512*h
  have val:shadowRow b k z G S=X:=rfl
  rw [val]
  change X%4=leftWord G e A M ∧ X/4%4=rightWord G e A M ∧ X/4096=0
  dsimp only [X,encodedPair,leftWord,rightWord]
  cases G <;> simp only [ite_true,Bool.false_eq_true,ite_false,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem output_values (ports:List Wire) (s:BasisState) (b k:Nat) (z:SkywalkNat.State) (G S:Bool)
    (plen:ports.length=width)
    (data:∀q∈wires forward,s (ports.getD q 0)=(shadowRow b k z G S).testBit q) :
    let T:=Shadow.reduced b k z;let V:=Shadow.limb b k;let e:=PortalValues.negative S z.u
    let A:=pair (T.u+T.v) V;let M:=pair (T.u-e.toNat) V
    regValue (ports.take 2) s=leftWord G e A M ∧
    regValue ((ports.drop 2).take 2) s=rightWord G e A M ∧ regValue (ports.drop 12) s=0 := by
  let W:=shadowRow b k z G S
  have p:=projected b k z G S
  have N:ports.length=13:=plen
  have whole:=EnterProof.value_of_bits ports s W (fun q h=>data q (forward_all ▸ Finset.mem_range.mpr (plen ▸ h)))
  rw [N,Nat.mod_eq_of_lt (show W<2^13 by have h:W/4096=0:=p.2.2;omega)] at whole
  rw [EnterProof.takeValue _ _ (by omega),whole,EnterProof.takeValue _ _ (by simp [N]),
    PortalValues.shiftedValue _ 2 (by omega),whole,PortalValues.shiftedValue _ 12 (by omega),whole]
  exact p

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic RailPair

namespace EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-- The aperture of the two-row enter: rows `cut`, `cut+1` of both rails, and the pair of row `cut+2`, which is
the first pair of the parked bank (`park ∈ hi`): its B wire is the enter's parked port. -/
structure Aperture (lo hi:List (Wire×Wire)) (g n f u:Wire) (ports:List Wire) (L:SkywalkIntegerLayout)
    (net:Wire→Wire) (cut:Nat) where
  a : List Wire
  b : List Wire
  park : Wire×Wire
  spec : Ports a b g n f u park.2 ports
  g0 : net g=L.previous
  xa : a.map net=(L.a.drop cut).take 2
  xb : b.map net=(L.b.drop cut).take 2
  na : cut+3≤L.a.length
  nb : cut+3≤L.b.length
  parked : park∈hi
  pa : net park.1=L.a.getD (cut+2) 0
  pb : net park.2=L.b.getD (cut+2) 0
  protected0 : ∀q∈g::(a++b++spec.clear),q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi
  temps : ∀q∈spec.clear,net q∈L.carry

theorem read_packed {lo hi g n f u rs L net b k} (A:Aperture lo hi g n f u rs L net (b+k+1))
    (raw result:State) (z:SkywalkNat.State) (G S:Bool)
    (P:PackedCut lo hi g n f u (PortalValues.negative S z.u)
      (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) result)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue rs result.basis=initialRow b k z G S:=by
  let neg:=PortalValues.negative S z.u
  have eq (q:Wire) (hq:q∈g::(A.a++A.b++A.spec.clear)):result.basis q=raw.basis (net q):=by
    obtain ⟨h0,h1,h2,hi⟩:=A.protected0 _ hq
    exact P.unchanged q h0 h1 h2 hi
  have math:=PortalValues.mathematical _ _ _ _ _ _ input
  have gOk:result.basis g=G:=(eq _ (by simp)).trans ((congrArg raw.basis A.g0).trans math.1)
  have clean:∀q∈A.spec.clear,result.basis q=false:=fun q h=>(eq _ (by simp [h])).trans
    ((regValue_zero _ _).mp input.2.2.2.2.2 _ (A.temps _ h))
  have view (ns full:List Wire) (ok:∀q∈ns,q∈g::(A.a++A.b++A.spec.clear))
      (shape:ns.map net=(full.drop (b+k+1)).take 2) (sz:b+k+1+2≤full.length) (flip:Bool) :
      regValue ns (fun q=>result.basis q ^^ flip)=
        pair (regValue full (fun q=>raw.basis q ^^ flip)) (Shadow.limb b k) := by
    calc
      _=regValue ns (fun q=>raw.basis (net q) ^^ flip):=regValue_congr _ _ _ (fun q h=>congrArg (· ^^ flip) (eq q (ok q h)))
      _=regValue (ns.map net) (fun q=>raw.basis q ^^ flip):=(PortalValues.unroute net ns (fun q=>raw.basis q ^^ flip)).symm
      _=_:=by rw [shape,slice_value _ _ sz];rfl
  have left (s:Bool):=view A.a L.a (by intro q h;simp [h]) A.xa (by have h:=A.na;omega) s
  have right (s:Bool):=view A.b L.b (by intro q h;simp [h]) A.xb (by have h:=A.nb;omega) s
  have tag:(pullState net raw).basis g=G:=(congrArg raw.basis A.g0).trans math.1
  have sel:result.basis A.park.2=if G then raw.basis (net A.park.2) else raw.basis (net A.park.1):=by
    have e:=(P.upper A.park A.parked).2
    rw [tag] at e;exact e
  have bitX:(if G then raw.basis (net A.park.2) else raw.basis (net A.park.1))=(z.u+z.v).testBit (b+k+1+2):=by
    cases G
    · show raw.basis (net A.park.1)=_
      rw [A.pa,EnterProof.bitAt L.a raw.basis (b+k+1+2) (by have h:=A.na;omega),
        show regValue L.a raw.basis=z.u+z.v from math.2.2.1]
    · show raw.basis (net A.park.2)=_
      rw [A.pb,EnterProof.bitAt L.b raw.basis (b+k+1+2) (by have h:=A.nb;omega),
        show regValue L.b raw.basis=z.u+z.v from math.2.2.1]
  have pw:(z.u+z.v)/2^(b+k+1+2)=(z.u+z.v)/Shadow.limb b k/4:=by
    rw [Nat.div_div_eq_div_mul,pow_add] <;> rfl
  have pk:result.basis A.park.2=decide ((z.u+z.v)/Shadow.limb b k/4%2=1):=by
    rw [sel,bitX,Nat.testBit_eq_decide_div_mod_eq,pw]
  apply read_ports A.spec z k b G S result.basis gOk P.sign P.mode P.orientation pk clean
  · cases G
    · exact (by simpa using left false : regValue A.a result.basis=_).trans
        (congrArg (fun x=>pair x (Shadow.limb b k)) math.2.2.1)
    · exact (by simpa using right false : regValue A.b result.basis=_).trans
        (congrArg (fun x=>pair x (Shadow.limb b k)) math.2.2.1)
  · cases G
    · exact (right neg).trans (congrArg (fun x=>pair x (Shadow.limb b k)) math.2.2.2)
    · exact (left neg).trans (congrArg (fun x=>pair x (Shadow.limb b k)) math.2.2.2)

end EnterProof17
end ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic

theorem join (lo hi:List Wire) (cut W:Nat) (s:BasisState) (size:lo.length=cut)
    (low:regValue lo s=W%2^cut) (high:regValue hi s=pair W (2^cut)) (bound:W/(2^cut)<4) :
    regValue (lo++hi) s=W := by
  rw [regValue_append,size,low,high,pair,Nat.mod_eq_of_lt bound,Nat.mod_add_div]

theorem norm_pair (r:List Wire) (size:r.length=2) (s:BasisState) (e:Bool) (Y:Nat)
    (v:regValue r s=signedPair e Y) : regValue r (fun q=>s q ^^ e)=Y := by
  have eq: signedPair e (regValue r (fun q=>s q ^^ e))=signedPair e Y:=(sign_digits _ size s e).symm.trans v
  exact Nat.xor_left_inj.mp eq

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic
set_option maxRecDepth 12000

theorem tags (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :
    let W:=shadowRow b k z g s
    W.testBit 4=g ∧ W.testBit 5=false ∧ W.testBit 6=decide (Shadow.far b k z) ∧
    W.testBit 7=decide (Shadow.far b k z ∧ 2^b≤z.u) ∧ W.testBit 8=false ∧ W/512=
      (if Shadow.far b k z then Shadow.high b k z%8 else 0) := by
  let T:=Shadow.reduced b k z;let V:=Shadow.limb b k;let e:=PortalValues.negative s z.u
  let A:=pair (T.u+T.v) V;let M:=pair (T.u-e.toNat) V
  have ar:A<4:=Nat.mod_lt _ (by decide)
  have mr:M<4:=Nat.mod_lt _ (by decide)
  have small:∀x:Fin 4,∀n:Bool,signedPair n x<4:=by decide +kernel
  have sn:signedPair e M<4:=small ⟨_,mr⟩ e
  let f:=decide (Shadow.far b k z);let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  let h:=(if Shadow.far b k z then Shadow.high b k z%8 else 0)
  let W:=encodedPair g e A M+16*g.toNat+64*f.toNat+128*u.toNat+512*h
  have w:shadowRow b k z g s=W:=rfl
  have base:encodedPair g e A M<16:=by cases g <;> dsimp [encodedPair] <;> omega
  dsimp only
  rw [w]
  change W.testBit 4=g ∧ W.testBit 5=false ∧ W.testBit 6=f ∧ W.testBit 7=u ∧ W.testBit 8=false ∧ W/512=h
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  change decide (W/16%2=1)=g ∧ decide (W/32%2=1)=false ∧ decide (W/64%2=1)=f ∧
    decide (W/128%2=1)=u ∧ decide (W/256%2=1)=false ∧ W/512=h
  dsimp only [W]
  cases g <;> cases f <;> cases u <;> simp only [Bool.toNat_true,Bool.toNat_false,decide_eq_true_eq,decide_eq_false_iff_not] <;> omega

theorem actual_tags (ports:List Wire) (s:BasisState) (b k:Nat) (z:SkywalkNat.State) (G S:Bool)
    (h:∀q∈wires forward,s (ports.getD q 0)=(shadowRow b k z G S).testBit q) :
    s (ports.getD 4 0)=G ∧ s (ports.getD 5 0)=false ∧ s (ports.getD 6 0)=decide (Shadow.far b k z) ∧
    s (ports.getD 7 0)=decide (Shadow.far b k z ∧ 2^b≤z.u) := by
  rw [h 4 (by decide +kernel),h 5 (by decide +kernel),h 6 (by decide +kernel),h 7 (by decide +kernel)]
  have ⟨a,b,c,d,_⟩:=tags b k z G S
  exact ⟨a,b,c,d⟩

/-- The parked port is clean after the enter. -/
theorem actual_parked (ports:List Wire) (s:BasisState) (b k:Nat) (z:SkywalkNat.State) (G S:Bool)
    (h:∀q∈wires forward,s (ports.getD q 0)=(shadowRow b k z G S).testBit q) :
    s (ports.getD 8 0)=false := by
  rw [h 8 (by decide +kernel)]
  exact (tags b k z G S).2.2.2.2.1

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic RailPair
set_option maxRecDepth 12000

structure WordPlacement {lo hi g n f u rs L net b k}
    (A:Aperture lo hi g n f u rs L net (b+k+1)) (P:Program) where
  lowA : List Wire
  lowB : List Wire
  al : lowA.length=b+k+1
  bl : lowB.length=b+k+1
  xa : lowA.map net=L.a.take (b+k+1)
  xb : lowB.map net=L.b.take (b+k+1)
  aTop : rs.take 2=A.a
  bTop : (rs.drop 2).take 2=A.b
  protected0 : ∀q∈lowA++lowB,q∉wires P ∧ q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi
  portsCount : rs.length=width

theorem short_rails {lo hi g n f u rs L net b k} {A:Aperture lo hi g n f u rs L net (b+k+1)}
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
  let T:=Shadow.reduced b k z;let V:=Shadow.limb b k;let e:=PortalValues.negative S z.u
  let X:=T.u+T.v;let M:=T.u-e.toNat
  have num:=PortalValues.mathematical _ _ _ _ _ _ input
  obtain ⟨_,_,_,_,_,resX,resM,pos,neg⟩:=shadow_digits b k z S small
  have residue:X%V=(z.u+z.v)%V ∧ M%V=(z.u-e.toNat)%V:=⟨resX,resM⟩
  change PortalValues.negative S T.u=e at neg
  change X<2*V at pos
  have pv:0<V:=by simp [V,Shadow.limb]
  have bounded (v:Nat) (h:v≤X):v/V<4:=(Nat.div_lt_iff_lt_mul pv).mpr (by omega)
  have Xbound:X<2^(b+k+1+1):=by rw [pow_succ]; change X<V*2; omega
  have high:=output_values rs post.basis b k z G S place.portsCount data
  rw [place.aTop,place.bTop] at high
  have same (q:Wire) (h:q∈place.lowA++place.lowB):post.basis q=raw.basis (net q):=by
    obtain ⟨hp,hn,hf,hu,hh⟩:=place.protected0 q h
    exact (outside q hp).trans (cut.unchanged q hn hf hu hh)
  have valueLo (w full:List Wire) (sub:∀q∈w,q∈place.lowA++place.lowB)
      (shape:w.map net=full.take (b+k+1)) (size:b+k+1≤full.length) (flip:Bool) :
      regValue w (fun q=>post.basis q ^^ flip)=regValue full (fun q=>raw.basis q ^^ flip)%V:=by
    calc
      _=regValue w (fun q=>raw.basis (net q) ^^ flip):=regValue_congr _ _ _ (fun q h=>congrArg (· ^^ flip) (same q (sub q h)))
      _=regValue (w.map net) (fun q=>raw.basis q ^^ flip):=(PortalValues.unroute net w (fun q=>raw.basis q ^^ flip)).symm
      _=_:=by rw [shape,EnterProof.takeValue _ _ size];rfl
  have lowA (flag:Bool):=valueLo _ L.a (fun _ h=>List.mem_append_left _ h) place.xa (by have h:=A.na;omega) flag
  have lowB (flag:Bool):=valueLo _ L.b (fun _ h=>List.mem_append_right _ h) place.xb (by have h:=A.nb;omega) flag
  have ds:=high
  change regValue A.a post.basis=leftWord G e (pair X V) (pair M V) ∧
    regValue A.b post.basis=rightWord G e (pair X V) (pair M V) ∧ _ at ds
  have ybound:T.u≤X:=by simp [X]
  have mbound:M≤X:=Nat.le_trans (Nat.sub_le _ _) ybound
  obtain ⟨_,_,wpos,wmag⟩:=num
  have la:(place.lowA++A.a).length=(b+k+1+1)+1:=by
    have h1:=place.al
    have h2:=A.spec.a
    rw [List.length_append]
    omega
  have lb:(place.lowB++A.b).length=(b+k+1+1)+1:=by
    have h1:=place.bl
    have h2:=A.spec.b
    rw [List.length_append]
    omega
  cases G
  · have pl:regValue place.lowA post.basis=X%V:=by
      have v:=lowA false
      simpa only [Bool.xor_false,show regValue L.a raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowB (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowB e,show regValue L.b (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.al pl ds.1 (bounded _ (le_refl _))
    have mh:=norm_pair _ A.spec.b _ e _ ds.2.1
    have py:=join _ _ _ M _ place.bl ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨EnterProof.ordinary _ _ la _ X Xbound px,
      EnterProof.signed _ _ lb _ _ S (lt_of_le_of_lt ybound Xbound) py⟩
  · have pl:regValue place.lowB post.basis=X%V:=by
      have v:=lowB false
      simpa only [Bool.xor_false,show regValue L.b raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowA (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowA e,show regValue L.a (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.bl pl ds.2.1 (bounded _ (le_refl _))
    have mh:=norm_pair _ A.spec.a _ e _ ds.1
    have py:=join _ _ _ M _ place.al ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨EnterProof.signed _ _ la _ _ S (lt_of_le_of_lt ybound Xbound) py,
      EnterProof.ordinary _ _ lb _ X Xbound px⟩

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic MappedCompressed RailPair IntegerPacket
set_option maxRecDepth 16000

structure FramePorts {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k+1)}
    (place:WordPlacement A P) (j:Fin 24) : Prop where
  a : ((ports (Shadow7.shape j) 0).a.map (windowNet j))=place.lowA++A.a
  bSites : ((ports (Shadow7.shape j) 0).b.map (windowNet j))=place.lowB++A.b
  prev : windowNet j (ports (Shadow7.shape j) 0).previous=rs.getD 4 0
  carry : ∀q∈(ports (Shadow7.shape j) 0).carry,let v:=windowNet j q
    v∈rs.drop 12 ∨ (v∉wires P ∧ net v∈L.carry ∧ v≠n ∧ v≠f ∧ v≠u ∧ v∉sites hi)
  ext : ∀r:Fin 15,let q:=windowNet j (ports (Shadow7.shape j) r).ext
    q∉wires P ∧ q∈hi.map Prod.fst
  hist : ∀r:Fin 15,let q:=windowNet j (ports (Shadow7.shape j) r).history
    q∉wires P ∧ q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi

theorem complete {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k+1)}
    {place:WordPlacement A P} {j:Fin 24} (frame:FramePorts place j)
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
  have values:=short_rails P place z G S small raw pre post cut input data save
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

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

theorem return_packed {lo hi g n f u rs L net b k} (A:Aperture lo hi g n f u rs L net (b+k+1))
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
    have hv:=EnterProof.bitAt rs cut.basis q (sz ▸ Finset.mem_range.mp (lim hq))
    rwa [src] at hv
  have first:=actual_shadow map p false b k z G S small inj pf cut m initial
  have last:=actual_shadow map r true b k z G S small inj pr (run p m cut) t
    (fun q hq=>first.2.1 q (sup ▸ hq))
  apply congrArg₂ State.mk (last.1.trans first.1)
  funext q
  have pp:wires p=(wires forward).image map:=pf ▸ JointForward1588.wires_rename_image _ _
  have rr:wires r=wires p:=by rw [pr,JointForward1588.wires_rename_image,←sup,pp]
  by_cases mem:q∈wires p
  · obtain ⟨v,vh,rfl⟩:=Finset.mem_image.mp (pp ▸ mem)
    exact (last.2.1 _ (sup ▸ vh)).trans (initial _ vh).symm
  · exact (last.2.2 q (rr ▸ mem)).trans (first.2.2 _ mem)

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.EnterProof17
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
open Arithmetic MappedCompressed
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000

/-- `SavedHigh.stored` for a sublist of the parked bank (the saved word skips the bank's first pair). -/
theorem stored_sub {lo hi g n f u neg far long} {L:SkywalkIntegerLayout} {net:Wire→Wire}
    (sub:List (Wire×Wire)) (inc:∀p∈sub,p∈hi) (bits:Nat)
    (raw cut:State) (z:SkywalkNat.State) (G S:Bool)
    (packed:PackedCut lo hi g n f u neg far long (pullState net raw) cut)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (gate:net g=L.previous) (left:(sub.map Prod.fst).map net=L.a.drop bits)
    (right:(sub.map Prod.snd).map net=L.b.drop bits)
    (la:bits≤L.a.length) (lb:bits≤L.b.length) : regValue (sub.map Prod.snd) cut.basis=(z.u+z.v)/2^bits:=by
  have math:=PortalValues.mathematical _ _ _ _ _ _ input
  have tag:(pullState net raw).basis g=G:=(congrArg raw.basis gate).trans math.1
  have select (p:Wire×Wire) (h:p∈sub):cut.basis p.2=if G then raw.basis (net p.2) else raw.basis (net p.1):=by
    have e:=(packed.upper p (inc p h)).2
    rw [tag] at e;exact e
  cases G with
  | false=>
    rw [SavedHigh.mapped sub Prod.snd Prod.fst _ (fun q=>raw.basis (net q)) (fun p h=>by simpa using select p h),
      ←PortalValues.unroute net _ _,left,PortalValues.shiftedValue _ _ la,
      show regValue L.a raw.basis=z.u+z.v from math.2.2.1]
  | true=>
    rw [SavedHigh.mapped sub Prod.snd Prod.snd _ (fun q=>raw.basis (net q)) (fun p h=>by simpa using select p h),
      ←PortalValues.unroute net _ _,right,PortalValues.shiftedValue _ _ lb,
      show regValue L.b raw.basis=z.u+z.v from math.2.2.1]

theorem three (a b c:Wire) (s:BasisState) (row:Nat)
    (ha:s a=row.testBit 9) (hb:s b=row.testBit 10) (hc:s c=row.testBit 11) :
    regValue [a,b,c] s=row/512%8:=by
  simp only [regValue,List.foldr_cons,List.foldr_nil,ha,hb,hc,Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
  split <;> split <;> split <;> simp_all <;> omega

theorem assemble (b k:Nat) (z:SkywalkNat.State) (G S:Bool) (s:BasisState) (a c e:Wire) (rest:List Wire)
    (ha:s a=(shadowRow b k z G S).testBit 9) (hc:s c=(shadowRow b k z G S).testBit 10)
    (he:s e=(shadowRow b k z G S).testBit 11)
    (high:regValue rest s=(z.u+z.v)/2^(b+k+1+3)) :
    regValue ([a,c,e]++rest) s=(if Shadow.far b k z then Shadow.high b k z else 0):=by
  rw [regValue_append,three _ _ _ _ _ ha hc he,(tags b k z G S).2.2.2.2.2, high]
  have div:(z.u+z.v)/2^(b+k+1+3)=Shadow.high b k z/8:=by
    unfold Shadow.high Shadow.limb;rw [Nat.div_div_eq_div_mul,pow_add 2 (b+k+1) 3];rfl
  rw [div]
  change (if Shadow.far b k z then Shadow.high b k z%8 else 0)%8+8*(Shadow.high b k z/8)=_
  by_cases h:Shadow.far b k z
  · simp only [h,if_true];omega
  · simp only [h,if_false];unfold Shadow.far at h;omega

end ECDSAAdd.Entrant.StairPacket.EnterProof17

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem scanRouted_shadow7 (j : Fin 24) (k a b g n : Nat) (ps : List (Wire×Wire))
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

end


/- Inlined from ShadowEnterJ; provenance retained from022799f6. -/
section
/-! build-chain: Shadow7 renders of the stock window families EnterJ (helpers/build-chain/shadow/render7.py). -/

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic IntegerPacket MappedCompressed
def zeroSites (j:Fin 24) :=
  let p:=Shadow7.shape j
  let L:=ports p 0
  (L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

set_option linter.unusedSimpArgs false in
theorem zero_congr (j:Fin 24) (s t:State) (agree:∀q∈Shadow7.zeroSites j,t.basis q=s.basis q)
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

/-- The two A-rail ports `s+h+32, s+h+33` (rows `sb+16`, `sb+17`). -/
def railA (j : Fin 24) : List Wire :=
  [start j+Shadow7.sbP (start j)+32, start j+Shadow7.sbP (start j)+33]
/-- The two B-rail ports `h+802, h+803`. -/
def railB (j : Fin 24) : List Wire :=
  [Shadow7.sbP (start j)+802, Shadow7.sbP (start j)+803]
/-- Orientation gate `s+15` and the three flags `n f u` (`e0+5, e0+3, e0+4`). -/
def gate (j : Fin 24) : Wire := start j+15
def flagN (j : Fin 24) : Wire := Shadow7.sbP (start j)+1579
def flagF (j : Fin 24) : Wire := Shadow7.sbP (start j)+1577
def flagU (j : Fin 24) : Wire := Shadow7.sbP (start j)+1578
/-- The parked B wire of row `sb+18` (bit 2 of the high word); the enter moves it to `e0+2`. -/
def parked (j : Fin 24) : Wire := Shadow7.sbP (start j)+804
/-- Clean ports: `e0..e0+2` and the one carry wire `1556` the enter uses. -/
def clear (j : Fin 24) : List Wire :=
  [Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576, 1556]
/-- The 13 ports of the enter program. -/
def ports (j : Fin 24) : List Wire :=
  [start j+Shadow7.sbP (start j)+32, start j+Shadow7.sbP (start j)+33,
   Shadow7.sbP (start j)+802, Shadow7.sbP (start j)+803, start j+15,
   Shadow7.sbP (start j)+1579, Shadow7.sbP (start j)+1577, Shadow7.sbP (start j)+1578, Shadow7.sbP (start j)+804,
   Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576, 1556]
def map (j : Fin 24) (q : Wire) : Wire := (ports j).getD q 0
/-- The parked bank: two low pairs (rows `sb+16`, `sb+17`), then `Wp-2` upper pairs from row `sb+18` up to the
B rail's top `785+R`. `upperTail` is the bank without its first pair (rows from `sb+19`). -/
def lowerPairs (j : Fin 24) : List (Wire×Wire) :=
  [(start j+Shadow7.sbP (start j)+32, Shadow7.sbP (start j)+802), (start j+Shadow7.sbP (start j)+33, Shadow7.sbP (start j)+803)]
def upperPairs (j : Fin 24) : List (Wire×Wire) :=
  (List.range (Shadow7.wpP (start j)-2)).map (fun i => (start j+Shadow7.sbP (start j)+34+i, Shadow7.sbP (start j)+804+i))
def upperTail (j : Fin 24) : List (Wire×Wire) :=
  (List.range (Shadow7.wpP (start j)-3)).map (fun i => (start j+Shadow7.sbP (start j)+35+i, Shadow7.sbP (start j)+805+i))
/-- Saved high word (`Enter{s}.saved`) and the three pending flags written by the previous leave. -/
def saved (j : Fin 24) : List Wire :=
  [Shadow7.sbP (start j)+1574, Shadow7.sbP (start j)+1575, Shadow7.sbP (start j)+1576]++(upperTail j).map Prod.snd
def pending (j : Fin 24) : List Wire := [Shadow7.sbP (start j)+1580, Shadow7.sbP (start j)+1581, Shadow7.sbP (start j)+1582]
/-- Low rails `s+16..` and `786..` (`h+16` wires each) and the guard predicate. -/
def lowA (j : Fin 24) : List Wire := List.range' (start j+16) (Shadow7.sbP (start j)+15+1)
def lowB (j : Fin 24) : List Wire := List.range' 786 (Shadow7.sbP (start j)+15+1)
def safe (j : Fin 24) (q : Wire) : Prop :=
  (q<start j+16 ∨ start j+Shadow7.sbP (start j)+32≤q) ∧ (q<786 ∨ Shadow7.sbP (start j)+802≤q)
instance (j : Fin 24) (q : Wire) : Decidable (safe j q) := by unfold safe; infer_instance
/-- Stock layout of tick `s` and the frame of tick `s-1`. -/
def lay (j : Fin 24) : SkywalkIntegerLayout := W.compactSkywalkTickLayout base (start j)
def pull (j : Fin 24) : Wire → Wire := OB5.sig (start j-1)
def carryPorts (j : Fin 24) : List Wire := ((IntegerPacket.ports (Shadow7.shape j) 0).carry).map (windowNet j)
def rest (j : Fin 24) : List Wire := (carryPorts j).drop 1
def guarded (j : Fin 24) : List Wire := ports j++[flagN j, flagF j, flagU j]++RailPair.sites (upperPairs j)

theorem ports_length (j : Fin 24) : (ports j).length=EnterProof17.width := rfl

/-- `inc{s}` for every block. -/
theorem inc_all : ∀ j : Fin 24, ∀ a b : Fin EnterProof17.width, map j a=map j b → a=b := by decide +kernel
theorem inc (j : Fin 24) : ∀ a b : Fin EnterProof17.width, map j a=map j b → a=b := inc_all j
/-- `emitted{s}` / `emitted{s}Inv`: definitional for every block. -/
theorem emitted (j : Fin 24) : Shadow7.enterP j=renameProgram (map j) EnterProof17.forward := rfl
theorem emittedInv (j : Fin 24) : Shadow7.enterInvP j=renameProgram (map j) EnterProof17.backward := rfl

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof17
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
theorem frame (j : Fin 24) : start j=75+15*j.val ∧ j.val<24 ∧ 2*Shadow7.sbP (start j)+start j≤499 ∧
    496≤2*Shadow7.sbP (start j)+start j ∧ 3<Shadow7.wpP (start j) ∧ Shadow7.wpP (start j)+Shadow7.sbP (start j)≤242 := by
  have arith : ∀ k : Fin 24, 2*Shadow7.sbP (start k)+start k≤499 ∧ 496≤2*Shadow7.sbP (start k)+start k ∧
      3<Shadow7.wpP (start k) ∧ Shadow7.wpP (start k)+Shadow7.sbP (start k)≤242 := by decide +kernel
  exact ⟨rfl,j.isLt,arith j⟩

theorem upperSites (j : Fin 24) {q : Wire} (h : q∈RailPair.sites (upperPairs j)) :
    (start j+Shadow7.sbP (start j)+34≤q ∧ q+2<start j+Shadow7.sbP (start j)+34+Shadow7.wpP (start j)) ∨
    (Shadow7.sbP (start j)+804≤q ∧ q+2<Shadow7.sbP (start j)+804+Shadow7.wpP (start j)) := by
  simp only [RailPair.sites,upperPairs,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false] at h
  obtain ⟨p,⟨i,hi,rfl⟩,hp⟩:=h
  simp only [Wire] at *
  rcases hp with rfl|rfl <;> omega

theorem portsRegion (j : Fin 24) {q : Wire} (h : q∈ports j) :
    (start j+Shadow7.sbP (start j)+32≤q ∧ q≤start j+Shadow7.sbP (start j)+33) ∨ (Shadow7.sbP (start j)+802≤q ∧ q≤Shadow7.sbP (start j)+804) ∨
    q=start j+15 ∨ (Shadow7.sbP (start j)+1574≤q ∧ q≤Shadow7.sbP (start j)+1579) ∨ (1556≤q ∧ q≤1563) := by
  simp only [ports,List.mem_cons,List.not_mem_nil,or_false] at h
  simp only [Wire] at *
  omega

theorem g0_all : ∀ j : Fin 24, pull j (gate j)=(lay j).previous := by decide +kernel
theorem xa_all : ∀ j : Fin 24, (railA j).map (pull j)=((lay j).a.drop (Shadow7.sbP (start j)+15+1)).take 2 := by decide +kernel
theorem xb_all : ∀ j : Fin 24, (railB j).map (pull j)=((lay j).b.drop (Shadow7.sbP (start j)+15+1)).take 2 := by decide +kernel
theorem na_all : ∀ j : Fin 24, Shadow7.sbP (start j)+15+1+3≤(lay j).a.length := by decide +kernel
theorem nb_all : ∀ j : Fin 24, Shadow7.sbP (start j)+15+1+3≤(lay j).b.length := by decide +kernel
/-- The pair of row `sb+18` is the first pair of the parked bank; its wires in the stock frame. -/
theorem park_mem (j : Fin 24) : (start j+Shadow7.sbP (start j)+34, Shadow7.sbP (start j)+804)∈upperPairs j := by
  have f:=frame j
  unfold upperPairs
  exact List.mem_map.mpr ⟨0,List.mem_range.mpr (by omega),rfl⟩
theorem pa_all : ∀ j : Fin 24, pull j (start j+Shadow7.sbP (start j)+34)=(lay j).a.getD (Shadow7.sbP (start j)+15+1+2) 0 := by decide +kernel
theorem pb_all : ∀ j : Fin 24, pull j (Shadow7.sbP (start j)+804)=(lay j).b.getD (Shadow7.sbP (start j)+15+1+2) 0 := by decide +kernel
theorem temps_all : ∀ j : Fin 24, ∀q∈clear j, pull j q∈(lay j).carry := by decide +kernel

theorem protected0 (j : Fin 24) : ∀q∈gate j::(railA j++railB j++clear j),
    q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉RailPair.sites (upperPairs j) := by
  have f:=frame j
  intro q hq
  simp only [gate,railA,railB,clear,flagN,flagF,flagU,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  refine ⟨by simp only [Wire] at *;omega,by simp only [Wire] at *;omega,by simp only [Wire] at *;omega,fun hs=>?_⟩
  have u:=upperSites j hs
  simp only [Wire] at *
  omega

/-- `Enter{s}.layout`. -/
def layout (j : Fin 24) : EnterProof17.Aperture (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (ports j)
    (lay j) (pull j) (Shadow7.sbP (start j)+15+1) where
  a:=railA j
  b:=railB j
  park:=(start j+Shadow7.sbP (start j)+34,Shadow7.sbP (start j)+804)
  spec:=⟨rfl,rfl,clear j,rfl⟩
  g0:=g0_all j
  xa:=xa_all j
  xb:=xb_all j
  na:=na_all j
  nb:=nb_all j
  parked:=park_mem j
  pa:=pa_all j
  pb:=pb_all j
  protected0:=protected0 j
  temps:=temps_all j

/-- `Enter{s}.from_full` for every block. -/
theorem from_full (j : Fin 24) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (p:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (PortalValues.negative S z.u)
        (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
        (pullState (pull j) raw) v)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    let next:=run (Shadow7.enterP j) m v
    next.phase=v.phase ∧ (∀q∈wires EnterProof17.forward,next.basis (map j q)=(EnterProof17.shadowRow (Shadow7.sbP (start j)) 15 z G S).testBit q) ∧
      ∀q∉wires (Shadow7.enterP j),next.basis q=v.basis q := by
  have src:=EnterProof17.read_packed (layout j) raw v z G S p input
  apply EnterProof17.actual_shadow (map j) (Shadow7.enterP j) false (Shadow7.sbP (start j)) 15 z G S small (inc j) (emitted j) v m
  intro q h
  have lim:wires EnterProof17.forward ⊆ Finset.range 13 := by apply ArchiveFieldScratch.bounded;decide +kernel
  have hv:=EnterProof.bitAt (ports j) v.basis q ((show (ports j).length=13 from rfl) ▸ Finset.mem_range.mp (lim h))
  rw [src] at hv
  exact hv

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed Partial EnterProof17 RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- Every wire of `Shadow7.enterP j` is one of its 13 ports (from `emitted`, no evaluation). -/
theorem programCover (j : Fin 24) : wires (Shadow7.enterP j) ⊆ (ports j).toFinset := by
  rw [emitted j,renameProgram_support,EnterProof17.forward_all]
  intro q hq
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
  have lt:w<(ports j).length:=Finset.mem_range.mp hw
  rw [List.mem_toFinset,map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,Option.getD_some]
  exact List.getElem_mem lt
theorem notWire (j : Fin 24) {q : Wire} (h : q∉ports j) : q∉wires (Shadow7.enterP j) :=
  fun m=>h (List.mem_toFinset.mp (programCover j m))

theorem noLow (j : Fin 24) : ∀q∈guarded j, safe j q := by
  have f:=frame j
  intro q hq
  simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  unfold safe
  rcases hq with (hp|hn)|hs
  · have r:=portsRegion j hp; simp only [Wire] at *; omega
  · simp only [flagN,flagF,flagU,Wire] at *; omega
  · have u:=upperSites j hs; simp only [Wire] at *; omega
theorem lowUnsafe (j : Fin 24) : ∀w∈lowA j++lowB j, ¬safe j w := by
  intro w h
  simp only [lowA,lowB,safe,List.mem_append,List.mem_range'_1,Wire] at *
  omega
theorem lowXa_all : ∀ j : Fin 24, (lowA j).map (pull j)=(lay j).a.take (Shadow7.sbP (start j)+15+1) := by decide +kernel
theorem lowXb_all : ∀ j : Fin 24, (lowB j).map (pull j)=(lay j).b.take (Shadow7.sbP (start j)+15+1) := by decide +kernel

theorem protects (j : Fin 24) (q:Wire) (h:q∈lowA j++lowB j) :
    q∉wires (Shadow7.enterP j) ∧ q≠flagN j ∧ q≠flagF j ∧ q≠flagU j ∧ q∉sites (upperPairs j) := by
  have bad:=lowUnsafe j q h
  have gone:q∉guarded j:=fun mem=>bad (noLow j q mem)
  simp only [guarded,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at gone
  exact ⟨notWire j gone.1.1,gone.1.2.1,gone.1.2.2.1,gone.1.2.2.2,gone.2⟩

/-- `Enter{s}.placement`. -/
def placement (j : Fin 24) : EnterProof17.WordPlacement (b:=Shadow7.sbP (start j)) (k:=15) (layout j) (Shadow7.enterP j) where
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
open Arithmetic MappedCompressed Partial EnterProof17 RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- The carry ports of the block's first tick are fixed by the window frame: `1556..1573+h`. -/
theorem carryPorts_eq (j : Fin 24) : carryPorts j=List.range' 1556 (Shadow7.sbP (start j)+17) := by
  have hj:=j.isLt
  have hc:(IntegerPacket.ports (Shadow7.shape j) 0).carry=List.range' 1556 (Shadow7.sbP (start j)+17) := rfl
  unfold carryPorts
  rw [hc]
  conv => rhs; rw [← List.map_id (List.range' 1556 _)]
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range'_1] at hq
  simp only [windowNet,net,OB5.sig,start,Shadow7.sbP,id,Wire] at hq ⊢
  split <;> omega
theorem rest_eq (j : Fin 24) : rest j=List.range' 1557 (Shadow7.sbP (start j)+16) := by
  rw [rest,carryPorts_eq,List.drop_range']
  congr 1
theorem parts (j : Fin 24) : carryPorts j=((ports j).drop 12)++rest j := by
  rw [rest_eq,carryPorts_eq]
  have e:Shadow7.sbP (start j)+17=1+(Shadow7.sbP (start j)+16):=by omega
  rw [e,← List.range'_append_1]
  rfl
theorem layCarry_all : ∀ j : Fin 24,
    (lay j).carry=List.range' 1556 (W.compactSkywalkTickPreWidth (start j)-1) := by decide +kernel
theorem layWidth_all : ∀ j : Fin 24, Shadow7.sbP (start j)+19≤W.compactSkywalkTickPreWidth (start j) := by decide +kernel
theorem guardedBound_all : ∀ j : Fin 24, ∀q∈guarded j, q<1557 ∨ Shadow7.sbP (start j)+1574≤q := by decide +kernel
theorem clearCover (j : Fin 24) : ∀q∈guarded j, q∉rest j := by
  intro q hq mem
  rw [rest_eq,List.mem_range'_1] at mem
  have:=guardedBound_all j q hq
  simp only [Wire] at *
  omega
theorem sourceCover (j : Fin 24) : ∀q∈rest j, pull j q∈(lay j).carry := by
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

theorem frameA_all : ∀ j : Fin 24,
    (IntegerPacket.ports (Shadow7.shape j) 0).a.map (windowNet j)=lowA j++railA j := by decide +kernel
theorem frameB_all : ∀ j : Fin 24,
    (IntegerPacket.ports (Shadow7.shape j) 0).b.map (windowNet j)=lowB j++railB j := by decide +kernel
theorem framePrev_all : ∀ j : Fin 24,
    windowNet j (IntegerPacket.ports (Shadow7.shape j) 0).previous=(ports j).getD 4 0 := by decide +kernel
theorem frameExt_all : ∀ j : Fin 24, ∀r:Fin 15, let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).ext
    q∉ports j ∧ q∈(upperPairs j).map Prod.fst := by decide +kernel

/-- History ports of the block's ticks in the window frame: raw `s+r+1044`, or its mirror `2069-s-r`. -/
theorem histPort (j : Fin 24) (r : Fin 15) :
    let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history
    (q=start j+r.val+1044 ∧ start j+r.val+1044<1301) ∨ (q=2069-start j-r.val ∧ 1301≤start j+r.val+1044) := by
  have hr:=r.isLt
  have f:=frame j
  simp only [windowNet,net,OB5.sig,IntegerPacket.ports,Shadow7.shape]
  simp only [Wire] at *
  split <;> omega
theorem frameHist (j : Fin 24) : ∀r:Fin 15, let q:=windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history
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
theorem live (j : Fin 24) : EnterProof17.FramePorts (placement j) j where
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
open Arithmetic MappedCompressed Partial EnterProof17 RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-- `Enter{s}.ready_from_cut`, with the history cells of ticks `s..s+14` given in the pulled frame
(every block; the stock-frame form below holds for `s ≤ 255`). -/
theorem ready_from_cut_at (j : Fin 24) (raw v:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
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
  exact ⟨ph,EnterProof17.complete (live j) _ G S small raw v _ p input body outer hist⟩

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

theorem avoid_enter (j : Fin 24) : ∀q∈pending j,q∉wires (Shadow7.enterP j) := by
  have f:=frame j
  intro q hq
  apply notWire j
  intro hp
  have r:=portsRegion j hp
  simp only [pending,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Wire] at *
  omega
theorem zeroBand_all : ∀ j : Fin 24,
    (Shadow7.zeroSites j).all (fun q=>decide (q<Shadow7.sbP (start j)+1580 ∨ Shadow7.sbP (start j)+1583≤q)) := by decide +kernel
theorem avoid_live (j : Fin 24) : ∀q∈pending j,q∉Shadow7.zeroSites j := by
  intro q hq hz
  have b:=of_decide_eq_true (List.all_eq_true.mp (zeroBand_all j) q hz)
  simp only [pending,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Wire] at *
  omega

/-- `Enter{s}.ready_pending` with the history sources in the pulled frame (every block). -/
theorem ready_pending_at (j : Fin 24) (raw pre:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
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

end EnterJ7
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ7
open Arithmetic MappedCompressed EnterProof17 PortalValues Partial
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

theorem highA_all : ∀ j : Fin 24,
    ((upperTail j).map Prod.fst).map (pull j)=(lay j).a.drop (Shadow7.sbP (start j)+19) := by decide +kernel
theorem highB_all : ∀ j : Fin 24,
    ((upperTail j).map Prod.snd).map (pull j)=(lay j).b.drop (Shadow7.sbP (start j)+19) := by decide +kernel
theorem highLa_all : ∀ j : Fin 24, Shadow7.sbP (start j)+19≤(lay j).a.length := by decide +kernel
theorem highLb_all : ∀ j : Fin 24, Shadow7.sbP (start j)+19≤(lay j).b.length := by decide +kernel
theorem tail_sub (j : Fin 24) : ∀p∈upperTail j,p∈upperPairs j := by
  intro p hp
  unfold upperTail at hp
  unfold upperPairs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hp
  rw [List.mem_range] at hi
  refine List.mem_map.mpr ⟨i+1,List.mem_range.mpr (by omega),?_⟩
  exact congrArg₂ Prod.mk (by (try simp only [Wire] at *); omega) (by (try simp only [Wire] at *); omega)
theorem savedLive (j : Fin 24) : ∀q∈(upperTail j).map Prod.snd,q∉ports j := by
  have f:=frame j
  intro q hq hp
  simp only [upperTail,List.map_map,List.mem_map,List.mem_range,Function.comp] at hq
  obtain ⟨i,hi,rfl⟩:=hq
  have r:=portsRegion j hp
  simp only [Wire] at *
  omega

/-- `Enter{s}.high_from_cut` for every block. -/
theorem high_from_cut (j : Fin 24) (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (m:List Bool)
    (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (packed:PackedCut (lowerPairs j) (upperPairs j) (gate j) (flagN j) (flagF j) (flagU j) (negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (pull j) raw) cut)
    (input:SkywalkIntegerInput (lay j) (SkywalkRails.encode G S z.u z.v).a
      (SkywalkRails.encode G S z.u z.v).b G raw.basis) :
    regValue (saved j) (run (Shadow7.enterP j) m cut).basis=
      if Shadow.far (Shadow7.sbP (start j)) 15 z then Shadow.high (Shadow7.sbP (start j)) 15 z else 0 :=by
  have high:=EnterProof17.stored_sub (upperTail j) (tail_sub j) (Shadow7.sbP (start j)+19) raw cut z G S packed input (layout j).g0
    (highA_all j) (highB_all j) (highLa_all j) (highLb_all j)
  obtain ⟨_,bits,outer⟩:=from_full j raw cut z G S m small packed input
  have bulk:=regValue_congr ((upperTail j).map Prod.snd) (run (Shadow7.enterP j) m cut).basis cut.basis
    (fun q hit=>outer q (notWire j (savedLive j q hit)))
  apply EnterProof17.assemble (Shadow7.sbP (start j)) 15 z G S _ (Shadow7.sbP (start j)+1574) (Shadow7.sbP (start j)+1575) (Shadow7.sbP (start j)+1576) _
  · exact bits 9 (by rw [EnterProof17.forward_all];decide)
  · exact bits 10 (by rw [EnterProof17.forward_all];decide)
  · exact bits 11 (by rw [EnterProof17.forward_all];decide)
  · exact bulk.trans high

end ECDSAAdd.Entrant.StairPacket.EnterJ7

end

end


/- Inlined from ShadowGeometry; provenance retained from022799f6. -/
section

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

theorem scratchS_cases (t k : Nat) (ht : t < 512) (hk : k < 134) :
    (scratchS t k = scratchW t k ∧ 1556 ≤ scratchS t k ∧ scratchS t k ≤ 1699 ∧ scratchS t k + t < 2068) ∨
    (369 ≤ t ∧ 1302 ≤ scratchS t k + t ∧ scratchS t k ≤ 933) := by
  have b := scratchW_bounds t k
  have l := scratchW_le t k hk
  by_cases h : scratchW t k + t < 2068
  · left; rw [scratchS_eq t k ht h]; omega
  · right; rw [scratchS_high t k ht hk (by omega)]; omega

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
theorem counts_fix0P (s h : Nat) : Counts (fix0P s h) 18 0 0 74 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_fix2P (s h : Nat) : Counts (fix2P s h) 0 34 50 141 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_fix8P (s h : Nat) : Counts (fix8P s h) 0 0 0 4 := ⟨rfl, rfl, rfl, rfl⟩
theorem counts_fix10P (s h : Nat) : Counts (fix10P s h) 0 0 0 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem counts_leaveAdjust (s : Nat) (hw : 1 ≤ wpP s) :
    Counts (leaveAdjust s) 0 (wpP s - 1) (wpP s - 1) (5*wpP s - 1) :=
  ((⟨rfl, rfl, rfl, rfl⟩ : Counts [Gate.cx (e0P s + 6) (e0P s + 3)] 0 0 0 1).app
    ((counts_cxsG _ _).app ((counts_addG _ _ _ (by first | omega | (simp <;> omega))).app (counts_cxsG _ _)))).congr
    (by simp) (by simp) (by simp) (by first | omega | (simp <;> omega))

theorem counts_leaveBarrel (s : Nat) : Counts (leaveBarrel s) (4*wpP s + 11) 0 0 (12*wpP s + 97) :=
  ((((counts_stageG _ _ _ _ _).app (counts_stageG _ _ _ _ _)).app (counts_stageG _ _ _ _ _)).app
    (counts_stageG _ _ _ _ _)).congr (by omega) rfl rfl
    (by simp only [controlsP0, controlsP1, controlsP2, controlsP3, List.length_cons, List.length_nil]; omega)

theorem counts_leaveJoin (s : Nat) (hL : lowsP s ≤ 17) : Counts (leaveJoin s) 32 0 17 (115 - lowsP s) := by
  have hw := counts_wordGM 1614 (columnsP s)
  have e1 : (columnsP s).length = 17 := by simp [columnsP]
  have e2 : (columnsP s).countP (fun r => r.hot.isSome) = 16 := by
    simp only [columnsP, List.countP_map]
    show (List.range 17).countP (fun i => (if i < 16 then some (tagsP.getD i 0) else none : Option Wire).isSome) = 16
    decide
  have e3 : (columnsP s).countP (fun r => r.low) = lowsP s := by
    simp only [columnsP, List.countP_map]
    show (List.range 17).countP (fun i => decide (i < lowsP s)) = lowsP s
    rw [countP_range_lt]; omega
  rw [e1, e2, e3] at hw
  exact ((counts_digitsG _ _ _ _ _ _).app hw).congr (by omega) (by omega) (by omega) (by omega)

theorem counts_leaveLowStore (s : Nat) (hL : 1 ≤ lowsP s) :
    Counts (leaveLowStore s) 0 (2*lowsP s - 1) (lowsP s + 1) (6*lowsP s + 4) := by
  have a := counts_mapG (List.range (lowsP s)) (fun i => Gate.make 1556 (a0P s + i) (b0P s + i)) false true false
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have b := counts_xsG ((List.range (lowsP s)).map (b0P s + ·))
  have c := counts_addG ((List.range (lowsP s - 1)).map (1559 + ·)) ((List.range (lowsP s)).map (b0P s + ·)) 1558
    (by first | omega | (simp <;> omega))
  exact ((((((⟨rfl, rfl, rfl, rfl⟩ :
      Counts [.cx (e0P s + 3) 1560, .cx 1559 1560, .pop (e0P s + 3) (e0P s + 4) 1559] 0 0 1 3).app a).app b).app c).app
    b).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop (b0P s - 1) 1557 1558, .cx (a0P s - 1) 1557, .x 1557] 0 0 1 3)).congr
    (by simp) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega)) (by first | omega | (simp <;> omega))

theorem counts_leaveStoreMapped (s : Nat) (hL : lowsP s ≤ wpP s + 15) :
    Counts (leaveStoreMapped s) 0 (wpP s + 18) (wpP s + 17) (4*wpP s + 77) := by
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
  exact ((((((((((⟨rfl, rfl, rfl, rfl⟩ : Counts [.x 1558, .x top] 0 0 0 2).app
    x1).app c1).app x2).app (⟨rfl, rfl, rfl, rfl⟩ :
      Counts [.x top, .x 1558, .make 1556 1557 1558, .x 1558] 0 1 0 4)).app
    x3).app c2).app x4).app (⟨rfl, rfl, rfl, rfl⟩ : Counts [.x 1558] 0 0 0 1))).congr
    (by simp) (by simp [H, L]; omega) (by simp [H, L]; omega) (by simp [hi, seq2, H, L]; omega)

theorem counts_leaveLowClose (s : Nat) : Counts (leaveLowClose s) (lowsP s + 1) 0 0 (4*lowsP s + 19) := by
  have a := counts_xsG ((List.range 15).map (s+16+·))
  have b := counts_mapG (List.range (lowsP s + 1)) (fun i => Gate.cx (e0P s + 5) (b0P s - 1 + i)) false false false
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have c := counts_flatCswap (lowsP s + 1) (s+30) (fun i => b0P s - 1 + i) (fun i => a0P s - 1 + i)
  exact ((a.app b).app c).congr (by simp) (by simp) (by simp) (by first | omega | (simp <;> omega))

theorem counts_leaveClose (s : Nat) (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveClose s) 0 5 5 (21 + 3*(wpP (s+15) + 4)) := by
  have a := counts_eventsG (e0P s + 7) (e0P s + 4)
    [(OB5.sig (s+14) (s+1044), 1556), (OB5.sig (s+14) (s+1045), 1559), (OB5.sig (s+14) (s+1046), 1560),
     (OB5.sig (s+14) (s+1047), 1561), (OB5.sig (s+14) (s+1048), 1562)]
  have b := counts_swapsG (movesP s)
  exact (a.app b).congr (by simp) (by simp) (by simp) (by simp [movesP]; omega)

/-- The whole leave, for every block start `s` with a sane geometry. -/
theorem counts_leaveOps (s : Nat) (hw : 4 ≤ wpP s) (hL1 : 1 ≤ lowsP s) (hL2 : lowsP s ≤ 17)
    (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveOps s) (4*wpP s + lowsP s + 78) (2*wpP s + 2*lowsP s + 91) (2*wpP s + lowsP s + 124)
      (21*wpP s + 9*lowsP s + 741 + 3*wpP (s+15)) := by
  have := ((((((((((((((((Shadow7.counts_fix0P s (sbP s)).app (counts_leaveFix1 s (sbP s))).app
    (Shadow7.counts_fix2P s (sbP s))).app (counts_leaveFix3 s (sbP s))).app (counts_leaveFix4 s (sbP s))).app
    (counts_leaveFix5 s (sbP s))).app (counts_leaveAdjust s (by omega))).app (counts_leaveBarrel s)).app
    (Shadow7.counts_fix8P s (sbP s))).app (counts_leaveJoin s hL2)).app (Shadow7.counts_fix10P s (sbP s))).app
    (counts_leaveFix11 s (sbP s))).app (counts_leaveFix12 s (sbP s))).app (counts_leaveLowStore s hL1)).app
    (counts_leaveStoreMapped s (by omega))).app (counts_leaveLowClose s)).app (counts_leaveClose s hn)
  exact this.congr (by omega) (by omega) (by omega) (by omega)

/-- The portal at tick `t` (threshold 2, store from bit 2). Same totals as the threshold-3 portal:
the dropped `make/pop` of `A0 ∧ A1` and the third low exchange pay for the one extra bulk pair. -/
theorem counts_portalOps (t : Nat) (hw : 5 ≤ wpP t) :
    Counts (portalOps t) (2*wpP t + 1) (3*wpP t - 5) (3*wpP t - 5) (18*wpP t - 2) := by
  let w := wpP t; let aBot := a0P t; let bBot := 802 + sbP t
  let rA := (List.range w).map (aBot + ·); let rB := (List.range w).map (bBot + ·)
  let bA := (List.range (w-2)).map (aBot + 2 + ·); let bB := (List.range (w-2)).map (bBot + 2 + ·)
  let sgn := e0P t + 5; let G := t + 15; let f3 := e0P t + 3; let f4 := e0P t + 4
  have zAB : (rA.zip rB).length = w := by simp [rA, rB]
  have zb : (bA.zip bB).length = w - 2 := by simp [bA, bB]
  have p1 := counts_exchangeG G (rA.zip rB)
  have p2 := counts_cxsG sgn rB
  have p3 := counts_latchG true none 1556 (aBot+1) ((List.range (w-2)).map (fun i => (aBot+2+i, 1558+i)))
  have p4 := counts_latchG false (some f3) f4 bBot ((List.range (w-1)).map (fun i => (bBot+1+i, 1556+i)))
  have p5 := counts_addG ((List.range (w-3)).map (1557 + ·)) bB 1556 (by simp [bB, w]; omega)
  have p6 := counts_mapG (bA.zip bB) (fun p => Gate.ccx f4 p.1 p.2) true false false (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  have p7 := counts_transferG (bA.zip bB)
  have p8 := counts_cxsG sgn [bBot, bBot+1]
  have p9 := counts_exchangeG G [(aBot, bBot), (aBot+1, bBot+1)]
  exact (((((((((((((⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx (aBot + w - 1) sgn, .cx (bTopP t) sgn] 0 0 0 2).app
    p1).app p2).app p3).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.cx 1556 f3, .cx f3 1556] 0 0 0 2)).app p4).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.x (aBot+1), .make (bBot+1) (aBot+1) 1556] 0 1 0 2)).app p5).app p6).app
    (⟨rfl, rfl, rfl, rfl⟩ : Counts [.pop (bBot+1) (aBot+1) 1556, .x (aBot+1)] 0 0 1 2)).app p7).app p8).app p9).congr
    (by simp [zAB, zb, w] at *; omega) (by simp [zAB, zb, w] at *; omega) (by simp [zAB, zb, w] at *; omega)
    (by simp [zAB, zb, rB, w] at *; omega)

theorem counts_parkOps (e : Nat) : Counts (parkOps e) 0 0 0 9 := (counts_swapsG _).congr rfl rfl rfl rfl

theorem window_geom : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    31 ≤ wpP (start j) ∧ 9 ≤ lowsP (start j) ∧ lowsP (start j) ≤ 10 ∧ 37 ≤ wpP (start j + 15) := by
  decide

theorem enter_counts (j : Fin 24) :
    toffoliCount (enterP j) = 8 ∧ toffoliCount (enterInvP j) = 7 ∧
    measurementCount (enterP j) = 1 ∧ measurementCount (enterInvP j) = 2 ∧
    gateSlots (enterP j) = 34 ∧ gateSlots (enterInvP j) = 35 :=
  (counts_enterFix17 _ _).programs

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

theorem counts_leaveJoinMove (s : Nat) (hL : lowsP s ≤ 17) : Counts (leaveJoinMove s) 16 0 17 (99 - lowsP s) := by
  have hw := counts_wordGM 1614 (columnsP s)
  have e1 : (columnsP s).length = 17 := by simp [columnsP]
  have e2 : (columnsP s).countP (fun r => r.hot.isSome) = 16 := by
    simp only [columnsP, List.countP_map]
    show (List.range 17).countP (fun i => (if i < 16 then some (tagsP.getD i 0) else none : Option Wire).isSome) = 16
    decide
  have e3 : (columnsP s).countP (fun r => r.low) = lowsP s := by
    have hl := (counts_leaveJoin s hL).len
    have hd := (counts_digitsG (tagsP.getD · 0) (fun i => a0P s + i) (e0P s + 6) 1613 0 16).len
    have hw' := hw.len
    simp only [leaveJoin, List.length_append] at hl
    rw [e1, e2] at hw'
    omega
  rw [e1, e2, e3] at hw
  exact ((counts_keptG _ _ 1613 0 16).app hw).congr (by omega) (by omega) (by omega) (by omega)

theorem counts_leaveMoveOps (s : Nat) (hw : 4 ≤ wpP s) (hL1 : 1 ≤ lowsP s) (hL2 : lowsP s ≤ 17)
    (hn : 3 ≤ wpP (s+15)) :
    Counts (leaveMoveOps s) (4*wpP s + lowsP s + 62) (2*wpP s + 2*lowsP s + 91) (2*wpP s + lowsP s + 124)
      (21*wpP s + 9*lowsP s + 757 + 3*wpP (s+15)) := by
  have := ((((((((((((((((Shadow7.counts_fix0P s (sbP s)).app (counts_leaveFix1 s (sbP s))).app
    (Shadow7.counts_fix2P s (sbP s))).app (counts_leaveFix3 s (sbP s))).app (counts_leaveFix4 s (sbP s))).app
    (counts_leaveFix5Move s (sbP s))).app (counts_leaveAdjust s (by omega))).app (counts_leaveBarrel s)).app
    (Shadow7.counts_fix8P s (sbP s))).app (counts_leaveJoinMove s hL2)).app (Shadow7.counts_fix10P s (sbP s))).app
    (counts_leaveFix11 s (sbP s))).app (counts_leaveFix12 s (sbP s))).app (counts_leaveLowStore s hL1)).app
    (counts_leaveStoreMapped s (by omega))).app (counts_leaveLowClose s)).app (counts_leaveClose s hn)
  have base := counts_leaveOps s hw hL1 hL2 hn
  exact this.congr (by omega) (by omega) (by omega) (by omega)

theorem leaveMove_counts (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    toffoliCount (leaveMoveP j) = 6*wpP (start j) + 3*lowsP (start j) + 153 ∧
    toffoliCount (leaveMoveInvP j) = 6*wpP (start j) + 2*lowsP (start j) + 186 ∧
    measurementCount (leaveMoveP j) = 2*wpP (start j) + lowsP (start j) + 124 ∧
    measurementCount (leaveMoveInvP j) = 2*wpP (start j) + 2*lowsP (start j) + 91 ∧
    gateSlots (leaveMoveP j) = 23*wpP (start j) + 10*lowsP (start j) + 881 + 3*wpP (start j + 15) ∧
    gateSlots (leaveMoveInvP j) = 23*wpP (start j) + 11*lowsP (start j) + 848 + 3*wpP (start j + 15) := by
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
theorem rail_facts (s : Nat) (h0 : 75 ≤ s) (h1 : s ≤ 405) :
    sbP s + 46 ≤ railP s ∧ railP s ≤ 258 ∧ sbP s = (498 - s - (1 - (91 - s) - s / 391))/2 ∧ (s ≤ 255 ∨ railP s = 513 - s) := by
  unfold railP sbP; split_ifs <;> omega

theorem enter_proper (s : Nat) (h0 : 75 ≤ s) (h1 : s ≤ 405) : ∀ g ∈ enterOps s, proper g = true := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts s h0 h1
  unfold enterOps enterFix17
  simp only [List.forall_mem_cons, List.forall_mem_nil, proper, decide_eq_true_eq, and_true, ne_eq]
  and_intros <;> first | trivial | (intro x hx; cases hx) | omega | exact Nat.ne_of_gt (by omega) | exact Nat.ne_of_lt (by omega)

private instance dec_enter_instr (i : Instr) : Decidable (RecordedQuantum.PhysicalInstr (.gate i)) := by
  cases i <;> simp only [RecordedQuantum.PhysicalInstr, ProperGate] <;> infer_instance
private instance dec_enter_physical (P : Program) : Decidable (GatePhysical P) := by
  unfold GatePhysical
  infer_instance

theorem enterP_physical (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    GatePhysical (enterP j) ∧ GatePhysical (enterInvP j) :=
  physical_of_proper _ (enter_proper (start j) (by simp [start] <;> omega) (by simp [start] <;> omega))

theorem park_proper (e : Nat) (h0 : 75 ≤ e) (h1 : e ≤ 420) : ∀ g ∈ parkOps e, proper g = true := by
  have f1 : sbP e + 46 ≤ railP e := by unfold railP sbP; split_ifs <;> omega
  have f2 : railP e ≤ 258 := by unfold railP; split_ifs <;> omega
  have f3 : sbP e = (498 - e - (1 - (91 - e) - e / 391))/2 := rfl
  have f4 : e ≤ 255 ∨ railP e = 513 - e := by unfold railP; split_ifs <;> omega
  have he : e0P e = 1574 + sbP e := rfl
  have hb : bTopP e = 785 + railP e := rfl
  unfold parkOps swapsG swapG
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.forall_mem_nil, proper, decide_eq_true_eq, and_true, ne_eq]
  and_intros <;> first | trivial | (intro x hx; cases hx) | omega | exact Nat.ne_of_gt (by omega) | exact Nat.ne_of_lt (by omega)

theorem parkP_physical (e : Nat) (h0 : 75 ≤ e) (h1 : e ≤ 420) :
    GatePhysical (parkP e) ∧ GatePhysical (parkInvP e) :=
  physical_of_proper _ (park_proper e h0 h1)

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
theorem archive_counts (j : Fin 24) (e : Nat) (d : Bool) :
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
def far1M (s : Nat) : Nat := interval 1598 (e0P s - 1598) ||| interval (e0P s + 10) (min (wpP s - 1 - (e0P s - 1598)) (2045 - s - e0P s)) |||
  interval (a0P s + 17) (min 3 (wpP s + s - 448))

/-- Far zeros from the barrel on: `1615 .. e0-1` and the pool above the anchored block, `e0+10 ..` (the corrected
StoreMapped chain takes its top carries there; the adjust leaves the pool clean). -/
def far2M (s : Nat) : Nat := interval 1615 (e0P s - 1615) ||| interval (e0P s + 10) (min (wpP s - 1 - (e0P s - 1598)) (2045 - s - e0P s)) |||
  interval (a0P s + 17) (min 3 (wpP s + s - 448))

theorem far1_iff (s : Nat) (q : Nat) :
    Zm (far1M s) q ↔ (1598 ≤ q ∧ q < e0P s) ∨ (e0P s + 10 ≤ q ∧ q < e0P s + 10 + min (wpP s - 1 - (e0P s - 1598)) (2045 - s - e0P s)) ∨
      (a0P s + 17 ≤ q ∧ q < a0P s + 17 + min 3 (wpP s + s - 448)) := by
  unfold far1M; rw [zm_or, zm_or]; unfold Zm; rw [testBit_interval, testBit_interval, testBit_interval]
  constructor
  · rintro ((⟨a, b⟩|⟨a, b⟩)|⟨a, b⟩)
    · left; constructor <;> ((try unfold Wire at *); omega)
    · right; left; constructor <;> ((try unfold Wire at *); omega)
    · right; right; constructor <;> ((try unfold Wire at *); omega)
  · rintro (⟨a, b⟩|⟨a, b⟩|⟨a, b⟩)
    · left; left; constructor <;> ((try unfold Wire at *); omega)
    · left; right; constructor <;> ((try unfold Wire at *); omega)
    · right; constructor <;> ((try unfold Wire at *); omega)

theorem far2_iff (s : Nat) (q : Nat) : Zm (far2M s) q ↔
    (1615 ≤ q ∧ q < e0P s) ∨ (e0P s + 10 ≤ q ∧ q < e0P s + 10 + min (wpP s - 1 - (e0P s - 1598)) (2045 - s - e0P s)) ∨
      (a0P s + 17 ≤ q ∧ q < a0P s + 17 + min 3 (wpP s + s - 448)) := by
  unfold far2M; rw [zm_or, zm_or]; unfold Zm; rw [testBit_interval, testBit_interval, testBit_interval]
  constructor
  · rintro ((⟨a, b⟩|⟨a, b⟩)|⟨a, b⟩)
    · left; constructor <;> ((try unfold Wire at *); omega)
    · right; left; constructor <;> ((try unfold Wire at *); omega)
    · right; right; constructor <;> ((try unfold Wire at *); omega)
  · rintro (⟨a, b⟩|⟨a, b⟩|⟨a, b⟩)
    · left; left; constructor <;> ((try unfold Wire at *); omega)
    · left; right; constructor <;> ((try unfold Wire at *); omega)
    · right; constructor <;> ((try unfold Wire at *); omega)

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
theorem fix0_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (Shadow7.fix0P (start j) (sbP (start j))) (maskSites cC ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel

theorem fix1_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (leaveFix1 (start j) (sbP (start j))) (maskSites cC ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel

theorem fix2_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (Shadow7.fix2P (start j) (sbP (start j))) (maskSites cK ||| far1M (start j)) = some (maskSites cC ||| far1M (start j)) := by
  decide +kernel

theorem fix3_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (leaveFix3 (start j) (sbP (start j))) (maskSites cA ||| far1M (start j)) = some (maskSites cK ||| far1M (start j)) := by
  decide +kernel

theorem fix4_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (leaveFix4 (start j) (sbP (start j))) (maskSites cB ||| far1M (start j)) = some (maskSites cA ||| far1M (start j)) := by
  decide +kernel

theorem fix5_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (leaveFix5 (start j) (sbP (start j))) (far1M (start j)) = some (maskSites cB ||| far1M (start j)) := by
  decide +kernel

theorem fix8_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (Shadow7.fix8P (start j) (sbP (start j))) (far2M (start j)) = some (far2M (start j)) := by
  decide +kernel

theorem fix10_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (Shadow7.fix10P (start j) (sbP (start j))) (far2M (start j)) = some (far2M (start j)) := by
  decide +kernel

theorem fix11_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (leaveFix11 (start j) (sbP (start j))) (maskSites cB ||| far2M (start j)) = some (far2M (start j)) := by
  decide +kernel

theorem fix12_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    bitCheck (leaveFix12 (start j) (sbP (start j))) (maskSites cA ||| far2M (start j)) = some (maskSites cB ||| far2M (start j)) := by
  decide +kernel

theorem lowSign_bit : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
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
/-- The window's rail and register facts at the Shadow7 widths (`sbP = (498-s)/2`, one lower at the even ticks 120..360): the stock statement with the
constants moved by the seven-bit reduction (`61 ≤ sbP ≤ 211` -> `54 ≤ sbP ≤ 204`, `railP ≤ 2 sbP + 1` -> `+ 15`,
`512 ≤ 2 sbP + s ≤ 513` -> `498 ≤ 2 sbP + s ≤ 499`, `sbP + 47 ≤ railP` -> `+ 46`, `sbP(s+15) + 50` -> `+ 53`; valid on [75,405]). -/
theorem rail_win {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
    railP s ≤ 258 ∧ sbP s + 46 ≤ railP s ∧ railP s ≤ 2 * sbP s + 17 ∧ 46 ≤ sbP s ∧ sbP s ≤ 211 ∧
    sbP (s+15) + 7 ≤ sbP s ∧ sbP s ≤ sbP (s+15) + 8 ∧ railP (s+15) ≤ railP s ∧
    railP (s+15) ≤ 2 * sbP (s+15) + 17 ∧ sbP (s+15) + 53 ≤ railP (s+15) ∧
    wpP s + sbP s + 16 = railP s ∧ wpP (s+15) + sbP (s+15) + 16 = railP (s+15) ∧
    e0P s = 1574 + sbP s ∧ e0P (s+15) = 1574 + sbP (s+15) ∧ bTopP s = 785 + railP s ∧
    bTopP (s+15) = 785 + railP (s+15) ∧ a0P s = s + sbP s + 32 ∧ b0P s = 787 + sbP s ∧
    lowsP s = 17 + sbP (s+15) - sbP s ∧ 2 * sbP s + s ≤ 499 ∧ 496 ≤ 2 * sbP s + s := by
  unfold wpP e0P bTopP a0P b0P lowsP railP sbP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try split_ifs) <;> omega

/-- The bank wires `bankW s i`, `i < wp+15`: three disjoint runs. -/
theorem bank_cases {s i : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (hi : i < wpP s + 15) :
    (i < 3 ∧ (bankW s i : Nat) = e0P s + i) ∨ (3 ≤ i ∧ i < wpP s ∧ (bankW s i : Nat) = bTopP s + 1 + i - wpP s ∧
      (bankW s i : Nat) ≤ 1043 ∧ 790 ≤ (bankW s i : Nat)) ∨
    (wpP s ≤ i ∧ (bankW s i : Nat) = 1598 + i - wpP s ∧ (bankW s i : Nat) ≤ 1612) := by
  have r := rail_win h1 h2
  unfold bankW; unfold wpP bTopP e0P at *
  split_ifs <;> ((try unfold Wire at *); omega)

theorem bank_inj {s i k : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (hi : i < wpP s + 15) (hk : k < wpP s + 15)
    (e : bankW s i = bankW s k) : i = k := by
  have r := rail_win h1 h2
  have a := bank_cases h1 h2 hi; have b := bank_cases h1 h2 hk
  unfold wpP bTopP e0P at *
  ((try unfold Wire at *); omega)

/-- On the window, `wpP s + s ≤ 451`: at most three carries leave the mirror-free run (block 22). -/
theorem pool_top {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) : wpP s + s ≤ 451 := by
  unfold wpP railP sbP; split_ifs <;> omega

theorem pool_cases {s i : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
    (1598 + i < e0P s ∧ (poolW s i : Nat) = 1598 + i) ∨ (e0P s ≤ 1598 + i ∧ 1608 + i + s < 2055 ∧ (poolW s i : Nat) = 1608 + i) ∨
    (e0P s ≤ 1598 + i ∧ 2055 ≤ 1608 + i + s ∧ (poolW s i : Nat) = a0P s + 17 + (1608 + i + s - 2055)) := by
  unfold poolW; split_ifs <;> ((try unfold Wire at *); omega)

theorem pool_nodup (s n : Nat) (h1 : 75 ≤ s) (h2 : s ≤ 405) (hn : n ≤ wpP s - 1) : ((List.range n).map (poolW s)).Nodup := by
  refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
  rw [List.mem_range] at hx hy
  have r := rail_win h1 h2
  have a := pool_cases (i := x) h1 h2; have b := pool_cases (i := y) h1 h2
  ((try unfold Wire at *); omega)

/-- The corrected StoreMapped carry sites: the stock pool `1558..` (skipping `1598..1612`), moved up by ten from the
anchored block `e0..e0+9` on. -/
theorem storeW_cases {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (k : Nat) :
    (1558 + k < 1598 ∧ (storeW s k : Nat) = 1558 + k) ∨
    (1598 ≤ 1558 + k ∧ 1573 + k < e0P s ∧ (storeW s k : Nat) = 1573 + k) ∨
    (1598 ≤ 1558 + k ∧ e0P s ≤ 1573 + k ∧ (storeW s k : Nat) = 1583 + k) := by
  have r := rail_win h1 h2
  simp only [storeW, Partial.storeW]; split_ifs <;> ((try unfold Wire at *); omega)

theorem adjust_ok {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
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
    have pt := pool_top h1 h2
    rw [far1_iff]; unfold wpP e0P at *; ((try unfold Wire at *); omega)
  refine ⟨?_, ?_⟩
  · unfold leaveAdjust leaveAdjustCore adjustG
    have c3 : ¬ Zm (far1M s) (e0P s + 3) := by rw [far1_iff]; ((try unfold Wire at *); omega)
    exact safe_append (a := [Gate.cx (e0P s + 6) (e0P s + 3)])
      (safe_frame' (fun g hg => by rw [List.mem_singleton] at hg; subst hg; rfl) (allAT_cons (ok_cx (A := fun _ => True) (T := fun q => ¬ Zm (far1M s) q) trivial c3) allAT_nil))
      (safe_append (safe_frame' (noMake_cxsG _ _) (allAT_cxsG _ _ trivial ys_far))
      (safe_append (safe_addG _ _ _ _ cs_in (pool_nodup s _ h1 h2 (le_refl _)) ys_far)
        (safe_frame' (noMake_cxsG _ _) (allAT_cxsG _ _ trivial ys_far))))
  · unfold leaveAdjust leaveAdjustCore
    refine proper_append (a := [Gate.cx (e0P s + 6) (e0P s + 3)])
      (proper_cons (pr_cx (by ((try unfold Wire at *); omega))) proper_nil) ?_
    refine proper_adjustG _ _ _ _ (fun y hy => ?_) (fun hc => ?_) (pool_nodup s _ h1 h2 (le_refl _))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_range] at hi
      have b := bank_cases h1 h2 (i := i) (by ((try unfold Wire at *); omega))
      refine ⟨fun hc => ?_, ?_, ?_⟩
      · obtain ⟨k, hk, e⟩ := List.mem_map.mp hc
        rw [List.mem_range] at hk
        have p := pool_cases (i := k) h1 h2; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
      · unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)
    · obtain ⟨k, hk, e⟩ := List.mem_map.mp hc
      rw [List.mem_range] at hk
      have p := pool_cases (i := k) h1 h2; unfold e0P at *; ((try unfold Wire at *); omega)

theorem bank_far2 {s i : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (hi : i < wpP s + 15) : ¬ Zm (far2M s) (bankW s i) := by
  have r := rail_win h1 h2
  have b := bank_cases h1 h2 hi
  rw [far2_iff]; unfold wpP bTopP e0P at *; ((try unfold Wire at *); omega)

theorem barrel_ok {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
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

theorem join_ok {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
    Safe (leaveJoin s) (Zm (far2M s)) (Zm (far2M s)) ∧ Proper (leaveJoin s) := by
  have r := rail_win h1 h2
  have a_far : ∀ i, i ≤ 16 → ¬ Zm (far2M s) (a0P s + i) := by
    intro i hi; rw [far2_iff]; unfold a0P e0P; ((try unfold Wire at *); omega)
  have rows : ∀ r ∈ columnsP s, ∃ i, i < 17 ∧ r.shadow = a0P s + i ∧ r.tube = bankW s i ∧
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
      (safe_frame' (noMake_wordGM _ _) (allAT_wordGM _ ⟨trivial, ?_⟩ _ (fun r hr => ?_)))
    · rw [far2_iff]; ((try unfold Wire at *); omega)
    · obtain ⟨i, hi, hs, ht, _⟩ := rows r hr
      exact ⟨fun _ _ => trivial, ⟨trivial, hs ▸ a_far i (by ((try unfold Wire at *); omega))⟩, ⟨trivial, ht ▸ bank_far2 h1 h2 (by ((try unfold Wire at *); omega))⟩⟩
  · unfold leaveJoin
    refine proper_append (proper_digitsG _ _ _ _ _ _ (fun i _ hi => ?_)) (proper_wordGM _ _ (fun r hr => ?_))
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
theorem far2_sub {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Wire) (h : Zm (far2M s) q) : Zm (far1M s) q := by
  rw [far2_iff] at h; rw [far1_iff]; ((try unfold Wire at *); omega)

theorem head_ok (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    Safe (leaveHeadOps (start j)) (Zm (maskSites cC ||| far1M (start j))) (Zm (maskSites cK ||| far2M (start j))) ∧
    Proper (leaveHeadOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 h1
  have f0 := safe_bit (fix0_bit j h0 h1); have f1 := safe_bit (fix1_bit j h0 h1)
  have f2 := safe_bit (fix2_bit j h0 h1); have f3 := safe_bit (fix3_bit j h0 h1)
  have f4 := safe_bit (fix4_bit j h0 h1); have f5 := safe_bit (fix5_bit j h0 h1)
  have f8 := safe_bit (fix8_bit j h0 h1); have f10 := safe_bit (fix10_bit j h0 h1)
  have f11 := safe_bit (fix11_bit j h0 h1); have f12 := safe_bit (fix12_bit j h0 h1)
  have fl := safe_bit (lowSign_bit j h0 h1)
  have ad := adjust_ok (by omega) w2; have ba := barrel_ok w1 w2; have jo := join_ok w1 w2
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
  (1559 ≤ q ∧ q ≤ 1597) ∨ (1613 ≤ q ∧ q < e0P s) ∨ (e0P s + 10 ≤ q ∧ q < e0P s + 10 + min (wpP s - 1 - (e0P s - 1598)) (2045 - s - e0P s)) ∨
  (a0P s + 17 ≤ q ∧ q < a0P s + 17 + min 3 (wpP s + s - 448))

theorem to_mid {s : Nat} (st : State) (hz : ZeroOn st (Zm (maskSites cK ||| far2M s)))
    (hc : ∀ q ∈ coreW, st.basis q = false) : ZeroOn st (midZ s) := by
  intro q hq
  by_cases hk : q ∈ cK
  · exact hz q ((zm_or _ _ _).mpr (Or.inl ((zm_sites _ _).mpr hk)))
  by_cases hw : q ∈ coreW
  · exact hc q hw
  · apply hz q; apply (zm_or _ _ _).mpr; right; rw [far2_iff]
    rw [mem_cK] at hk; rw [mem_coreW] at hw; unfold midZ at hq; ((try unfold Wire at *); omega)

theorem lowRest_ok {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
    Safe (lowRest s) (fun q => midZ s q ∨ ∃ i, i < lowsP s ∧ q = b0P s + i) (fun q => q = 1558 ∨ midZ s q) ∧ Proper (lowRest s) := by
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
    refine safe_append (Z1 := midZ s) (safe_append (Z1 := midZ s) (safe_append (Z1 := midZ s)
      (safe_append (Z1 := midZ s) ?_ ?_) ?_) ?_) tail
    · exact safe_mono (safe_makes 1556 (fun i => a0P s + i) (fun i => b0P s + i) (List.range (lowsP s))
          (fun q => midZ s q ∨ ∃ i, i < lowsP s ∧ q = b0P s + i)
          (List.Nodup.map (fun a b e => by ((try unfold Wire at *); omega)) List.nodup_range)
          (fun i hi => Or.inr ⟨i, List.mem_range.mp hi, rfl⟩))
        (fun q h => h) (fun q hq => ⟨fun hm => bs_out q hm hq, Or.inl hq⟩)
    · exact safe_frame' (noMake_xsG _) (allAT_xsG _ bs_out)
    · exact safe_addG _ _ _ _ cs_in cs_nd bs_out
    · exact safe_frame' (noMake_xsG _) (allAT_xsG _ bs_out)
  · unfold lowRest
    refine proper_append (proper_append (proper_append (proper_append ?_ (proper_xsG _)) ?_) (proper_xsG _)) ?_
    · exact proper_map _ _ (fun i hi => by rw [List.mem_range] at hi; exact pr_make (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
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
/-- Gates that never target `t` leave it alone. -/
theorem run_forward_keep (t : Wire) : ∀ (gs : List Gate) (s : State), (∀ g ∈ gs, target g ≠ t) →
    (run (GateMirror.forward gs) [] s).basis t = s.basis t
  | [], _, _ => rfl
  | g :: gs, s, h => by
    have e : run (GateMirror.forward (g :: gs)) [] s = run (GateMirror.forward gs) [] (transition g s) :=
      run_forward_append [g] gs s
    obtain ⟨v, hv⟩ := transition_basis g s
    have ne : t ≠ target g := Ne.symm (h g (List.mem_cons.mpr (Or.inl rfl)))
    rw [e, run_forward_keep t gs _ (fun k hk => h k (List.mem_cons_of_mem _ hk)), hv]
    simp only [writeBit, Function.update_of_ne ne]

/-- An `x t` sandwich around a block that never targets `t` returns the zero wire `t` to zero (margin 17: the pending
latch of `leaveStoreMapped` starts its chain on `1558` itself instead of on `row(top-2) ∧ row(top-1)`). -/
theorem safe_xx {t : Wire} {gs : List Gate} {Z : Wire → Prop} (hgs : Safe gs Z Z)
    (nt : ∀ g ∈ gs, target g ≠ t) (zt : ¬ Z t) :
    Safe ([Gate.x t] ++ gs ++ [Gate.x t]) (fun q => q = t ∨ Z q) (fun q => q = t ∨ Z q) := by
  intro s hs
  have z1 : ZeroOn (transition (Gate.x t) s) Z := by
    intro q hq
    have ne : q ≠ t := fun e => zt (e ▸ hq)
    show writeBit s.basis t (!s.basis t) q = false
    simp only [writeBit, Function.update_of_ne ne]
    exact hs q (Or.inr hq)
  obtain ⟨r1, z2⟩ := hgs _ z1
  have k2 : (run (GateMirror.forward gs) [] (transition (Gate.x t) s)).basis t = !s.basis t := by
    rw [run_forward_keep t gs _ nt]
    show writeBit s.basis t (!s.basis t) t = !s.basis t
    simp only [writeBit, Function.update_self]
  have step1 : run (GateMirror.forward ([Gate.x t] ++ gs)) [] s =
      run (GateMirror.forward gs) [] (transition (Gate.x t) s) := run_forward_append [Gate.x t] gs s
  refine ⟨ready_append _ _ _ (ready_append _ _ _ ⟨trivial, trivial⟩ r1) ⟨trivial, trivial⟩, ?_⟩
  rw [run_forward_append, step1]
  generalize run (GateMirror.forward gs) [] (transition (Gate.x t) s) = s2 at z2 k2
  intro q hq
  show writeBit s2.basis t (!s2.basis t) q = false
  by_cases e : q = t
  · rw [e]
    simp only [writeBit, Function.update_self, k2, Bool.not_not]
    exact hs t (Or.inl rfl)
  · simp only [writeBit, Function.update_of_ne e]
    rcases hq with h|h
    · exact absurd h e
    · exact z2 q h

theorem storeMapped_ok {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
    Safe (leaveStoreMapped s) (fun q => q = 1558 ∨ midZ s q) (midZ s) ∧ Proper (leaveStoreMapped s) := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, _, ee, _, et, _, ea, eb, el, _, _⟩ := r
  have hL : 9 ≤ lowsP s ∧ lowsP s ≤ 10 := by ((try unfold Wire at *); omega)
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
    have p2b : Safe [.x 1558] (fun q => q ≠ 1558 ∧ (q = 1558 ∨ midZ s q)) (midZ s) :=
      safe_mono (Z := midZ s) (safe_lit (fun g hg => by simp at hg; subst hg; rfl)
          (fun g hg => by simp at hg; subst hg; simp only [target]; unfold midZ; ((try unfold Wire at *); omega)))
        (fun q hq => ⟨fun e => by subst e; unfold midZ at hq; ((try unfold Wire at *); omega), Or.inr hq⟩) (fun _ h => h)
    have xtop : Safe [GateMirror.Gate.x (a0P s + lowsP s - 1)] (midZ s) (midZ s) :=
      safe_lit (fun g hg => by simp at hg; subst hg; rfl) (fun g hg => by simp at hg; subst hg; simp only [target]; exact top_out)
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
    have i1 := safe_then (midZ s) xtop (safe_frame' (noMake_xsG _) (allAT_xsG _ hi_out))
    have i2 := safe_then (midZ s) i1 ch1
    have i3 := safe_then (midZ s) i2 (safe_frame' (noMake_xsG _) (allAT_xsG _ hir_out))
    have i4 := safe_then (midZ s) i3 xtop
    have n57 : (1557 : Wire) ≠ 1558 := by decide
    have ntop : (a0P s + lowsP s - 1 : Wire) ≠ 1558 := by ((try unfold Wire at *); omega)
    have hiN : ∀ y ∈ ((List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i))), y ≠ (1558 : Wire) := by
      intro y hy; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi
      exact (bank_out _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))).2.1
    have hAT : AllAT (fun _ => True) (fun q => q ≠ (1558 : Wire))
        ([GateMirror.Gate.x (a0P s + lowsP s - 1)] ++ xsG ((List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i))) ++
        chainG (storeW s) (fun i => if i = 0 then a0P s + lowsP s - 1 else bankW s (lowsP s + i - 1))
        [.cx (storeW s (wpP s + 15 - lowsP s + 1)) 1557, .x 1557] 0 (wpP s + 15 - lowsP s + 1) ++
        xsG ((List.range (wpP s + 15 - lowsP s)).map (fun i => bankW s (lowsP s + i))).reverse ++ [GateMirror.Gate.x (a0P s + lowsP s - 1)]) :=
      allAT_append (allAT_append (allAT_append (allAT_append
        (allAT_cons (ok_x (A := fun _ => True) (T := fun q => q ≠ (1558 : Wire)) ntop) allAT_nil) (allAT_xsG _ hiN))
        (allAT_chainG (A := fun _ => True) (T := fun q => q ≠ (1558 : Wire)) _ _ _
          (allAT_cons (ok_cx (A := fun _ => True) (T := fun q => q ≠ (1558 : Wire)) trivial n57)
            (allAT_cons (ok_x (A := fun _ => True) (T := fun q => q ≠ (1558 : Wire)) n57) allAT_nil)) _ _
          (fun k _ _ => ⟨trivial, fun pos => by have sc := storeW_cases h1 h2 k; ((try unfold Wire at *); omega)⟩)
          (fun _ _ _ => trivial)))
        (allAT_xsG _ (fun y hy => hiN y (List.mem_reverse.mp hy))))
        (allAT_cons (ok_x (A := fun _ => True) (T := fun q => q ≠ (1558 : Wire)) ntop) allAT_nil)
    have sand := safe_xx i4 (fun g hg => (hAT g hg).2) (fun h => by unfold midZ at h; ((try unfold Wire at *); omega))
    have mk : Safe [GateMirror.Gate.make 1556 1557 1558] (fun q => q = 1558 ∨ midZ s q)
        (fun q => q ≠ 1558 ∧ (q = 1558 ∨ midZ s q)) := safe_make (Or.inl rfl)
    have q4 := safe_append (safe_append sand mk) p2b
    have q5 := safe_then (midZ s) q4 (safe_frame' (noMake_xsG _) (allAT_xsG _ s2_out))
    have q6 := safe_then (midZ s) q5 ch2
    have q7 := safe_then (midZ s) q6 (safe_frame' (noMake_xsG _) (allAT_xsG _ s2r_out))
    have key := safe_then (midZ s) q7 x58
    simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using key
  · simp only [leaveStoreMapped]
    refine proper_append (proper_append (proper_append (proper_append (proper_append (proper_append (proper_append
      (proper_append ?_ (proper_xsG _)) ?_) (proper_xsG _)) ?_) (proper_xsG _)) ?_) (proper_xsG _)) (proper_cons rfl proper_nil)
    · exact proper_cons rfl (proper_cons rfl proper_nil)
    · refine proper_chainG _ _ _ (proper_cons (pr_cx ?_) (proper_cons rfl proper_nil)) _ _ (fun k _ hk => ⟨?_, ?_⟩)
      · have sc := storeW_cases h1 h2 (wpP s + 15 - lowsP s + 1); ((try unfold Wire at *); omega)
      · intro e; have := st_inj k (k+1) ; have a := storeW_cases h1 h2 k; have b := storeW_cases h1 h2 (k+1); ((try unfold Wire at *); omega)
      · dsimp only
        split
        · have sc := storeW_cases h1 h2 (k+1); ((try unfold Wire at *); omega)
        · exact Ne.symm ((bank_out (lowsP s + k - 1) (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))).2.2.2.2 (k+1))
    · exact proper_cons rfl (proper_cons rfl (proper_cons (pr_make (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil)))
    · exact proper_chainG _ _ _ (proper_cons (pr_cx (by ((try unfold Wire at *); omega))) (proper_cons rfl proper_nil)) _ _
        (fun k _ hk => ⟨by ((try unfold Wire at *); omega), by ((try unfold Wire at *); omega)⟩)

theorem lowClose_ok {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
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
theorem sig_hist {s c : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
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
theorem moves_ne {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) : ∀ p ∈ movesP s, p.1 ≠ p.2 := by
  have r := rail_win h1 h2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  intro p hp
  rcases List.mem_append.mp hp with hp|hp
  · obtain ⟨i, hi, e⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    have bc := bank_cases (i := lowsP s + i) h1 h2 (by ((try unfold Wire at *); omega))
    rw [← e]; show (bankW s (lowsP s + i) : Nat) ≠ bTopP (s+15) + 3 + i - wpP (s+15)
    ((try unfold Wire at *); omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with e|e|e|e|e|e <;> rw [e] <;> show (_ : Nat) ≠ _ <;> ((try unfold Wire at *); omega)

set_option maxHeartbeats 1000000 in
theorem close_ok {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) :
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
theorem leave_ready (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q →
      q < e0P (start j) + 10 + min (wpP (start j) - 1 - (e0P (start j) - 1598)) (2045 - start j - e0P (start j)) →
      s.basis q = false)
    (up : ∀ q, a0P (start j) + 17 ≤ q → q < a0P (start j) + 17 + min 3 (wpP (start j) + start j - 448) → s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (low : ∀ i : Nat, i < 17 → (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis (b0P (start j) + i) = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false) :
    Ready s (leaveOps (start j)) ∧ (∀ g ∈ leaveOps (start j), proper g = true) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 h1
  have hd := head_ok j h0 h1
  have lr := lowRest_ok (by omega) w2; have sm := storeMapped_ok w1 w2; have lc := lowClose_ok w1 w2
  have cl := close_ok w1 w2
  have z0 : ZeroOn s (Zm (maskSites cC ||| far1M (start j))) := by
    intro q hq
    rcases (zm_or _ _ _).mp hq with h|h
    · rw [zm_sites, mem_cC] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ee, _⟩ := rail_win w1 w2
      exact initial q (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
    · rw [far1_iff] at h
      rcases h with ⟨a, b⟩|⟨a, b⟩|⟨a, b⟩
      · exact initial q (by ((try unfold Wire at *); omega)) b
      · exact extra q a b
      · exact up q a b
  obtain ⟨r1, z1⟩ := hd.1 s z0
  have mid : Safe (leaveMidOps (start j)) (fun q => midZ (start j) q ∨ ∃ i, i < lowsP (start j) ∧ q = b0P (start j) + i)
      (midZ (start j)) := by
    rw [leaveMidOps_eq]; exact safe_append (Z1 := midZ (start j)) (safe_append (Z1 := fun q => q = 1558 ∨ midZ (start j) q) lr.1 sm.1) lc.1
  have zin : ZeroOn (run (GateMirror.forward (leaveHeadOps (start j))) [] s)
      (fun q => midZ (start j) q ∨ ∃ i, i < lowsP (start j) ∧ q = b0P (start j) + i) := by
    intro q hq
    rcases hq with hq | ⟨i, hi, rfl⟩
    · exact to_mid _ z1 core q hq
    · exact low i (by have rr := rail_win w1 w2; (try unfold Wire at *); omega)
  obtain ⟨r2, z2⟩ := mid _ zin
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

/-- Block 22's relocated carries `a0P+17 ..` are clean again once the head and the mid part have run (the far-mask
chain of `leave_ready`). -/
theorem relocated_clean (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q →
      q < e0P (start j) + 10 + min (wpP (start j) - 1 - (e0P (start j) - 1598)) (2045 - start j - e0P (start j)) →
      s.basis q = false)
    (up : ∀ q, a0P (start j) + 17 ≤ q → q < a0P (start j) + 17 + min 3 (wpP (start j) + start j - 448) → s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (low : ∀ i : Nat, i < 17 → (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis (b0P (start j) + i) = false)
    (q : Nat) (a : a0P (start j) + 17 ≤ q) (b : q < a0P (start j) + 17 + min 3 (wpP (start j) + start j - 448)) :
    (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis q = false := by
  obtain ⟨w1, w2⟩ := start_win75 j (by omega) h1
  have hd := head_ok j (by omega) h1
  have lr := lowRest_ok (by omega) w2; have sm := storeMapped_ok (by omega) w2; have lc := lowClose_ok (by omega) w2
  have z0 : ZeroOn s (Zm (maskSites cC ||| far1M (start j))) := by
    intro q hq
    rcases (zm_or _ _ _).mp hq with h|h
    · rw [zm_sites, mem_cC] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ee, _⟩ := rail_win w1 w2
      exact initial q (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
    · rw [far1_iff] at h
      rcases h with ⟨a, b⟩|⟨a, b⟩|⟨a, b⟩
      · exact initial q (by ((try unfold Wire at *); omega)) b
      · exact extra q a b
      · exact up q a b
  obtain ⟨_, z1⟩ := hd.1 s z0
  have mid : Safe (leaveMidOps (start j)) (fun q => midZ (start j) q ∨ ∃ i, i < lowsP (start j) ∧ q = b0P (start j) + i)
      (midZ (start j)) := by
    rw [leaveMidOps_eq]; exact safe_append (Z1 := midZ (start j)) (safe_append (Z1 := fun q => q = 1558 ∨ midZ (start j) q) lr.1 sm.1) lc.1
  have zin : ZeroOn (run (GateMirror.forward (leaveHeadOps (start j))) [] s)
      (fun q => midZ (start j) q ∨ ∃ i, i < lowsP (start j) ∧ q = b0P (start j) + i) := by
    intro q hq
    rcases hq with hq | ⟨i, hi, rfl⟩
    · exact to_mid _ z1 core q hq
    · exact low i (by have rr := rail_win w1 w2; (try unfold Wire at *); omega)
  obtain ⟨_, z2⟩ := mid _ zin
  rw [run_forward_append]
  exact z2 q (Or.inr (Or.inr (Or.inr ⟨a, b⟩)))

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
theorem cell_lt {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) : a0P s + 16 ≤ 500 ∧ 1626 ≤ e0P s + 6 := by
  have r := rail_win w1 w2
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  omega

theorem calm_of {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) {r : MoveChain.Row} (hr : r ∈ moveRows s) (g : Gate)
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
theorem moveB_away {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) : AllAT (MoveA s) (MoveT s) (moveB s) := by
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
  · unfold leaveAdjust leaveAdjustCore
    refine allAT_append (a := [Gate.cx (e0P s + 6) (e0P s + 3)])
      (allAT_cons (ok_cx (far _ (by omega)) (farT _ (by omega) (by omega) (by omega))) allAT_nil) ?_
    refine allAT_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (far _ (by omega)) (far _ (by omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by omega)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      rcases pool_cases (i := i) w1 w2 with p | p | p
      · exact ⟨far _ (by unfold Wire at *; omega), farT _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)
          (by unfold Wire at *; omega)⟩
      · exact ⟨far _ (by unfold Wire at *; omega), farT _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)
          (by unfold Wire at *; omega)⟩
      · have ma : MoveA s (poolW s i) := by unfold MoveA; unfold Wire at *; omega
        exact ⟨ma, ma, Or.inl (by unfold Wire at *; omega), by unfold Wire at *; omega⟩
  · unfold leaveBarrel
    have c13 : MoveA s 1613 ∧ MoveT s 1613 := ⟨far _ (by omega), farT _ (by omega) (by omega) (by omega)⟩
    have st : ∀ (xs : List Wire) (d n : Nat), n + d ≤ wpP s + 15 → (∀ x ∈ xs, 1556 ≤ x) →
        AllAT (MoveA s) (MoveT s) (stageG 1613 (bankW s) xs d n) :=
      fun xs d n hn hx => allAT_stageG _ _ _ _ _ c13 (ctl xs hx)
        (fun i hi => ⟨bank i (by omega), bank (i+d) (by omega)⟩)
    refine allAT_append ?_ (st _ _ _ (by omega) (by decide))
    refine allAT_append ?_ (st _ _ _ (by omega) (by decide))
    exact allAT_append (st _ _ _ (by omega) (by decide)) (st _ _ _ (by omega) (by decide))
  · show AllAT (MoveA s) (MoveT s) [.cx (e0P s + 3) 1613, .cx 1596 1613, .cx 1597 1613, .cx (e0P s + 6) (e0P s + 3)]
    have t13 : MoveT s 1613 := farT _ (by omega) (by omega) (by omega)
    exact allAT_cons (ok_cx (far _ (by omega)) t13) (allAT_cons (ok_cx (far _ (by omega)) t13)
      (allAT_cons (ok_cx (far _ (by omega)) t13)
        (allAT_cons (ok_cx (far _ (by omega)) (farT _ (by omega) (by omega) (by omega))) allAT_nil)))

theorem calmB {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) :
    (moveRows s).all (fun r => (moveB s).all (calmGate (e0P s + 6) r)) = true := by
  have h := moveB_away w1 w2
  rw [List.all_eq_true]; intro r hr
  rw [List.all_eq_true]; intro g hg
  exact calm_of w1 w2 hr g (h g hg)

theorem stillB {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) :
    (moveRows s).all (fun r => (GateMirror.forward (moveB s)).all (MoveChain.quiet (e0P s + 6) r)) = true := by
  have h := moveB_away w1 w2
  rw [List.all_eq_true]; intro r hr
  rw [List.all_eq_true]; intro i hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
  exact (Bool.and_eq_true_iff.mp (calm_of w1 w2 hr g (h g hg))).1

theorem apart_move {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) : MoveChain.apart (e0P s + 6) (moveRows s) = true := by
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

theorem woven_move {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) :
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
theorem leaveMove_same {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) (v : State) (m : List Bool) (a0 : Wire)
    (clean : (run (GateMirror.forward (moveA s)) m v).basis (e0P s + 6) = false)
    (sel : ∀ r ∈ moveRows s, (run (GateMirror.forward (moveA s)) m v).basis r.1 = true → r.2 = a0) :
    run (GateMirror.forward (leaveMoveOps s)) m v = run (GateMirror.forward (leaveOps s)) m v := by
  rw [leaveMoveOps_shape, leaveOps_shape]
  simp only [forward_app]
  rw [rowGates_forward, mux_forward, dig_forward]
  exact MoveChain.splice (e0P s + 6) (moveRows s) (GateMirror.forward (moveA s)) (GateMirror.forward (moveB s))
    (GateMirror.forward (moveC s)) (GateMirror.forward (moveKept s)) v m a0 (apart_move w1 w2) (lone_move s)
    (stillB w1 w2) (woven_move w1 w2) clean sel

theorem kept_proper {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) : ∀ g ∈ moveKept s, proper g = true := by
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
theorem leaveMove_proper_of {s : Nat} (w1 : 75 ≤ s) (w2 : s ≤ 405) (p : ∀ g ∈ leaveOps s, proper g = true) :
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
theorem leaveMove_inverts (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State)
    (phase : ∀ m, (run (leaveP j) m s).phase = s.phase)
    (initial : ∀ q, 1556 ≤ q → q < e0P (start j) → s.basis q = false)
    (extra : ∀ q, e0P (start j) + 10 ≤ q →
      q < e0P (start j) + 10 + min (wpP (start j) - 1 - (e0P (start j) - 1598)) (2045 - start j - e0P (start j)) →
      s.basis q = false)
    (up : ∀ q, a0P (start j) + 17 ≤ q → q < a0P (start j) + 17 + min 3 (wpP (start j) + start j - 448) → s.basis q = false)
    (core : ∀ q ∈ coreW, (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis q = false)
    (low : ∀ i : Nat, i < 17 → (run (GateMirror.forward (leaveHeadOps (start j))) [] s).basis (b0P (start j) + i) = false)
    (post : (run (GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j))) [] s).basis 1556 = false)
    (a0 : Wire)
    (hot : ∀ o, (run (GateMirror.forward (moveA (start j))) o s).basis (e0P (start j) + 6) = false ∧
      ∀ r ∈ moveRows (start j), (run (GateMirror.forward (moveA (start j))) o s).basis r.1 = true → r.2 = a0)
    (m n : List Bool) :
    run (leaveMoveInvP j) n (run (leaveMoveP j) m s) = s := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 h1
  obtain ⟨ready, phys⟩ := leave_ready j h0 h1 s initial extra up core low post
  generalize hs : start j = t at *
  have same (o : List Bool) : run (GateMirror.forward (leaveMoveOps t)) o s = run (GateMirror.forward (leaveOps t)) o s :=
    leaveMove_same (by omega) w2 s o a0 (hot o).1 (hot o).2
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
theorem fixed_box : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    segBox (start j) (Shadow7.fix0P (start j) (sbP (start j)) ++ leaveFix1 (start j) (sbP (start j)) ++
      Shadow7.fix2P (start j) (sbP (start j)) ++ leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j)) ++
      leaveFix5 (start j) (sbP (start j)) ++ Shadow7.fix8P (start j) (sbP (start j)) ++ Shadow7.fix10P (start j) (sbP (start j)) ++
      leaveFix11 (start j) (sbP (start j)) ++ leaveFix12 (start j) (sbP (start j)) ++ lowSign (start j)) = true := by
  decide +kernel

/-- `Partial.sig_box` on the shadow window, through block 22 (start 405). -/
theorem sig_box7 {s c : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
    leaveBox s (OB5.sig (s+14) (s+c)) := by
  have e := sig_hist (by omega) h2 hc1 hc2
  unfold leaveBox; ((try unfold Wire at *); omega)

theorem leaveOps_box (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    AllW (leaveBox (start j)) (leaveOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 h1
  have fb := allW_of_segBox (fixed_box j h0 h1)
  simp only [allW_append_iff] at fb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f8⟩, f10⟩, f11⟩, f12⟩, fl⟩ := fb
  generalize hs : start j = s at *
  have r := rail_win (by omega) w2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ew, ew', ee, ee', et, et', ea, eb, el, _, _⟩ := r
  have hL : 9 ≤ lowsP s ∧ lowsP s ≤ 10 := by ((try unfold Wire at *); omega)
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
    unfold leaveAdjust leaveAdjustCore
    refine allW_append (a := [Gate.cx (e0P s + 6) (e0P s + 3)])
      (allW_of_allAT (allAT_cons (ok_cx (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))) allAT_nil)) ?_
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      rcases pool_cases (i := i) w1 w2 with p | p | p
      · exact scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
      · exact scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))
      · have r := rail_win w1 w2; unfold leaveBox; ((try unfold Wire at *); omega)
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
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordGM _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
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
        exact ⟨sig_box7 w1 w2 (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)), scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))⟩
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
theorem portal_foot (t : Nat) (h0 : 75 ≤ t) (h1 : t ≤ 420) : AllW (footP t) (portalOps t) := by
  have f2 : railP t ≤ 258 := by unfold railP; split_ifs <;> omega
  have f3 : sbP t = (498 - t - (1 - (91 - t) - t / 391))/2 := rfl
  have f4 : t ≤ 255 ∨ railP t = 513 - t := by unfold railP; split_ifs <;> omega
  have f1 : sbP t + 46 ≤ railP t := by unfold railP sbP; split_ifs <;> omega
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
  have mA3 : ∀ x ∈ (List.range (wpP t - 2)).map (a0P t + 2 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show a0P t + 2 + i = a0P t + (2+i) by omega]; exact pA _ (by omega)
  have mB3 : ∀ x ∈ (List.range (wpP t - 2)).map (802 + sbP t + 2 + ·), footP t x := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; have := List.mem_range.mp hi
    rw [show 802 + sbP t + 2 + i = 802 + sbP t + (2+i) by omega]; exact pB _ (by omega)
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
  have car : ∀ x ∈ (List.range (wpP t - 3)).map (1557 + ·), footP t x := by
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
  refine allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append (allW_append ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl <;> assumption
  · exact allW_exchangeG _ _ pG (zip _ _ mA mB)
  · exact allW_cxsG _ _ e5 mB
  · exact allW_latchG _ _ _ _ _ (fun w h => by cases h) c56 p1 thr
  · intro g hg q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl <;> assumption
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
    rcases hx with rfl | rfl <;> assumption
  · refine allW_exchangeG _ _ pG ?_
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨by assumption, by assumption⟩

theorem park_foot (e : Nat) (h0 : 75 ≤ e) (h1 : e ≤ 420) : AllW (parkFootP e) (parkOps e) := by
  have f2 : railP e ≤ 258 := by unfold railP; split_ifs <;> omega
  have f3 : sbP e = (498 - e - (1 - (91 - e) - e / 391))/2 := rfl
  have f4 : e ≤ 255 ∨ railP e = 513 - e := by unfold railP; split_ifs <;> omega
  have f1 : sbP e + 46 ≤ railP e := by unfold railP sbP; split_ifs <;> omega
  have he : e0P e = 1574 + sbP e := rfl
  have hb : bTopP e = 785 + railP e := rfl
  apply allW_swapsG
  intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> constructor <;> unfold parkFootP <;> omega

theorem enter_foot (s : Nat) (h0 : 75 ≤ s) (h1 : s ≤ 405) : AllW (footP s) (enterOps s) := by
  obtain ⟨f1, f2, f3, f4⟩ := rail_facts s h0 h1
  unfold enterOps enterFix17 AllW
  simp only [List.forall_mem_cons, List.forall_mem_nil, Gate.wires, and_true, implies_true]
  and_intros <;> first | (intro x hx; cases hx) | (unfold footP; omega)

private instance dec_footP (s q : Nat) : Decidable (footP s q) :=
  inferInstanceAs (Decidable ((s+15 ≤ q ∧ q ≤ s+15+railP s) ∨ (786 ≤ q ∧ q ≤ 785+railP s) ∨
    (s+1044 ≤ q ∧ q ≤ 1300) ∨ (1556 ≤ q ∧ q ≤ 1812)))

/-- Every enter port lies in the block's footprint: one kernel decision over all blocks. -/


theorem enter_wires (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    (∀ q ∈ wires (enterP j), footP (start j) q) ∧ (∀ q ∈ wires (enterInvP j), footP (start j) q) :=
  allW_programs (enter_foot (start j) (by simp [start] <;> omega) (by simp [start] <;> omega))

/-- Wires of the parametric programs (portal, park), for `Covered`. -/
theorem portal_wires (t : Nat) (h0 : 75 ≤ t) (h1 : t ≤ 420) :
    (∀ q ∈ wires (portalP t), footP t q) ∧ (∀ q ∈ wires (portalInvP t), footP t q) :=
  allW_programs (portal_foot t h0 h1)

theorem park_wires (e : Nat) (h0 : 75 ≤ e) (h1 : e ≤ 420) :
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
attribute [local irreducible] ReducedWindowArchives.load0 ReducedWindowArchives.load1 ReducedWindowArchives.restore0 ReducedWindowArchives.restore1
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
theorem archiveLoadP_wiresW (j : Fin 24) (d : Bool) (hj : j.val ≤ 22) :
    ∀ q ∈ wires (archiveLoadP j d), archFootW (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start] <;> omega
  intro q hq
  rw [archiveLoadP, wires_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact renamed_footW _ _ 155 _ _ (by cases d <;> first | exact load0_ports | exact load1_ports)
      (fun p hp => loadPortsWP_footW _ _ p ht hp) q hq
  · exact (allW_programs (moves_footW _ (e0P (start j + 15) + 6) (by omega)).1).1 q hq

theorem archiveRestoreP_wiresW (j : Fin 24) (d : Bool) (hj : j.val ≤ 22) :
    ∀ q ∈ wires (archiveRestoreP j d), archFootW (start j + 15) (e0P (start j + 15) + 6) q := by
  have ht : start j + 15 < 512 := by simp [start] <;> omega
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
theorem routed_counts (j : Fin 24) (a n : Nat) (bound : a+n≤15) :
    toffoliCount (Shadow7.routed j a n)=n*(2*(Shadow7.smallBits j+17)) ∧
    measurementCount (Shadow7.routed j a n)=n*(Shadow7.smallBits j+17) ∧
    toffoliCount (Shadow7.unrouted j a n)=n*(2*(Shadow7.smallBits j+17)-1) ∧
    measurementCount (Shadow7.unrouted j a n)=n*(Shadow7.smallBits j+17) := by
  obtain ⟨f,r⟩ := Shadow7.fixed_route j a n bound
  have hs := IntegerPacket.metrics (Shadow7.shape j) a n bound
  have hr := IntegerPacket.metricsR (Shadow7.shape j) a n bound
  have mid : (Shadow7.shape j).mid+1=Shadow7.smallBits j+17 := rfl
  rw [mid] at hs hr
  rw [f,r,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2]
  exact ⟨hs.1,hs.2.1,hr.1,hr.2⟩

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
def rawHead (i : Fin 24) : List Wire := cellsLoadP (start i+15)++[Shadow7.e0P (start i+15)+6,Shadow7.e0P (start i+15)+6+1,Shadow7.e0P (start i+15)+6+2]

def scratch (i : Fin 24) : List Wire := (List.range 134).map (Shadow7.scratchS (start i+15))

def rawPortsList (i : Fin 24) : List Wire :=
  Shadow7.loadPortsWP (start i+15) (Shadow7.e0P (start i+15)+6)++[Shadow7.scratchS (start i+15) 132,Shadow7.scratchS (start i+15) 133]

def rawPorts (i : Fin 24) (q : Fin 157) : Wire := (rawPortsList i).getD q 0

def codeTail (i : Fin 24) : List Wire :=
  [OB5.sig (start i+15) (start i+15+1036),OB5.sig (start i+15) (start i+15+1038),OB5.sig (start i+15) (start i+15+1041),
   OB5.sig (start i+15) (start i+15+1043),Shadow7.e0P (start i+15)+6,Shadow7.e0P (start i+15)+7,Shadow7.e0P (start i+15)+8]

def codePortsList (i : Fin 24) : List Wire := Shadow7.restorePortsWP (start i+15)++codeTail i

def codePorts (i : Fin 24) (q : Fin 157) : Wire := (codePortsList i).getD q 0

def loadMap (i : Fin 24) (q : Wire) : Wire := (Shadow7.loadPortsWP (start i+15) (Shadow7.e0P (start i+15)+6)).getD q 0

def restoreMap (i : Fin 24) (q : Wire) : Wire := (Shadow7.restorePortsWP (start i+15)).getD q 0

def restoreMoves (i : Fin 24) : List (Wire×Wire) := (moveRestorePairs (start i+15) (Shadow7.e0P (start i+15)+6)).map Prod.swap

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

theorem rawLength (i : Fin 24) : (rawPortsList i).length=157 := by
  simp only [rawPortsList,List.length_append,Shadow7.loadPortsWP_length,List.length_cons,List.length_nil]

theorem codeLength (i : Fin 24) : (codePortsList i).length=157 := by
  simp only [codePortsList,List.length_append,Shadow7.restorePortsWP_length,codeTail,List.length_cons,List.length_nil]

theorem raw_split (i : Fin 24) : rawPortsList i=rawHead i++scratch i := by
  simp only [rawPortsList,rawHead,scratch,Shadow7.loadPortsWP,List.append_assoc]
  rw [range_two]

theorem code_split (i : Fin 24) : codePortsList i=cellsRestoreP (start i+15)++scratch i++codeTail i := by
  simp only [codePortsList,Shadow7.restorePortsWP,scratch]

theorem raw_scratch (i : Fin 24) {k : Nat} (hk : k<134) : (rawPortsList i).getD (23+k) 0=Shadow7.scratchS (start i+15) k := by
  rw [raw_split,List.getD_append_right _ _ _ _ (by simp [rawHead,cellsLoadP]),scratch]
  have e:23+k-(rawHead i).length=k:=by simp [rawHead,cellsLoadP]
  rw [e,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem code_scratch (i : Fin 24) {k : Nat} (hk : k<134) : (codePortsList i).getD (16+k) 0=Shadow7.scratchS (start i+15) k := by
  rw [codePortsList,List.getD_append _ _ _ _ (by rw [Shadow7.restorePortsWP_length]; omega),Shadow7.restorePortsWP_scratch _ _ hk]

theorem rawIndex (i : Fin 24) {q : Wire} (h : q∈rawPortsList i) : ∃k:Fin 157, rawPorts i k=q := by
  obtain ⟨n,hn,eq⟩:=List.getElem_of_mem h
  refine ⟨⟨n,(rawLength i) ▸ hn⟩,?_⟩
  rw [rawPorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact eq

theorem codeIndex (i : Fin 24) {q : Wire} (h : q∈codePortsList i) : ∃k:Fin 157, codePorts i k=q := by
  obtain ⟨n,hn,eq⟩:=List.getElem_of_mem h
  refine ⟨⟨n,(codeLength i) ▸ hn⟩,?_⟩
  rw [codePorts,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact eq

theorem scratch_mem (i : Fin 24) {k : Nat} (hk : k<134) : Shadow7.scratchS (start i+15) k∈scratch i :=
  List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩

theorem scratch_nodup (i : Fin 24) : (scratch i).Nodup :=
  List.Nodup.map_on (fun a ha b hb h=>Shadow7.scratchS_inj _ a b (tick_lt i) (List.mem_range.mp ha) (List.mem_range.mp hb) h)
    List.nodup_range

/-- Head facts, one `decide` over the window archives `i ≤ 18` (short lists only). -/
theorem heads_all : ∀ i : Fin 24, i.val≤22 →
    (rawHead i).Nodup ∧ (∀q∈rawHead i, Band (start i+15) q) ∧
    (cellsRestoreP (start i+15)++codeTail i).Nodup ∧ (∀q∈cellsRestoreP (start i+15)++codeTail i, Band (start i+15) q) ∧
    (∀q∈cellsRestoreP (start i+15)++codeTail i, q∈rawHead i) ∧
    (∀p∈loadMoves i, p.1∈rawHead i ∧ p.2∈rawHead i ∧ p.1≠p.2) ∧
    (∀p∈restoreMoves i, p.1≠p.2 ∧ (p.1∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, p.1=Shadow7.scratchS (start i+15) c) ∧
      (p.2∈cellsRestoreP (start i+15)++codeTail i ∨ ∃c<7, p.2=Shadow7.scratchS (start i+15) c)) := by
  decide +kernel

theorem routes_head_all : ∀ i : Fin 24, i.val≤22 → ∀k:Fin 157,
    ((k.val<16 ∨ 150≤k.val) → backMap (loadMoves i) (codePorts i k)=rawPorts i (loadRoute k)) ∧
    (k.val<30 → backMap (restoreMoves i) (rawPorts i k)=codePorts i (restoreRoute k)) := by
  decide +kernel

theorem rawNodup (i : Fin 24) (hi : i.val≤22) : (rawPortsList i).Nodup := by
  obtain ⟨hn,hb,-⟩:=heads_all i hi
  rw [raw_split,List.nodup_append]
  refine ⟨hn,scratch_nodup i,?_⟩
  intro a ha b hb' eq
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hb'
  exact band_off _ (tick_lt i) (List.mem_range.mp hk) (hb a ha) eq.symm

theorem codeNodup (i : Fin 24) (hi : i.val≤22) : (codePortsList i).Nodup := by
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

theorem load_unique (i : Fin 24) (hi : i.val≤22) : Function.Injective (rawPorts i) :=
  injective_list (rawPortsList i) (rawLength i) (rawNodup i hi)

theorem restore_unique (i : Fin 24) (hi : i.val≤22) : Function.Injective (codePorts i) :=
  injective_list (codePortsList i) (codeLength i) (codeNodup i hi)

theorem load_map (i : Fin 24) : ∀q:Fin 155, loadMap i q=rawPorts i ⟨q,by omega⟩ := by
  intro q
  simp only [loadMap,rawPorts,rawPortsList]
  rw [List.getD_append _ _ _ _ (by rw [Shadow7.loadPortsWP_length]; exact q.isLt)]

theorem restore_map (i : Fin 24) : ∀q:Fin 150, restoreMap i q=codePorts i ⟨q,by omega⟩ := by
  intro q
  simp only [restoreMap,codePorts,codePortsList]
  rw [List.getD_append _ _ _ _ (by rw [Shadow7.restorePortsWP_length]; exact q.isLt)]

theorem load_route (i : Fin 24) (hi : i.val≤22) : ∀k,backMap (loadMoves i) (codePorts i k)=rawPorts i (loadRoute k) := by
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

theorem restore_route (i : Fin 24) (hi : i.val≤22) :
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

theorem load_scope (i : Fin 24) (hi : i.val≤22) : ∀p∈loadMoves i,(∃k,rawPorts i k=p.1) ∧ (∃k,rawPorts i k=p.2) := by
  intro p hp
  obtain ⟨h1,h2,-⟩:=(heads_all i hi).2.2.2.2.2.1 p hp
  exact ⟨rawIndex i (raw_split i ▸ List.mem_append_left _ h1),rawIndex i (raw_split i ▸ List.mem_append_left _ h2)⟩

theorem restore_scope (i : Fin 24) (hi : i.val≤22) : ∀p∈restoreMoves i,(∃k,codePorts i k=p.1) ∧ (∃k,codePorts i k=p.2) := by
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

theorem restore_proper (i : Fin 24) (hi : i.val≤22) : ∀p∈restoreMoves i,p.1≠p.2 :=
  fun p hp=>((heads_all i hi).2.2.2.2.2.2 p hp).1
theorem load_proper7 (i : Fin 24) (hi : i.val≤22) : ∀p∈loadMoves i,p.1≠p.2 :=
  fun p hp=>((heads_all i hi).2.2.2.2.2.1 p hp).2.2

theorem load_program (i : Fin 24) (d : Bool) : Shadow7.archiveLoadP i d=placed (loadMap i) (op true d)++moves (loadMoves i) := by
  cases d <;> rfl

theorem restore_program (i : Fin 24) (d : Bool) :
    Shadow7.archiveRestoreP i d=placed (restoreMap i) (op false d)++moves (restoreMoves i) := by
  cases d <;> rfl

theorem load_run (i : Fin 24) (hi : i.val≤22) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame (rawPorts i) (startCols true d) row s) :
    let t:=run (Shadow7.archiveLoadP i d) m s
    t.phase=s.phase ∧ Frame (codePorts i) (endCols true d) row t ∧ ∀q,(∀k,rawPorts i k≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d (rawPorts i) (codePorts i) (loadMap i) (loadMoves i) loadRoute (load_unique i hi) _
    (load_proper7 i hi) (load_route i hi) load_sort (load_scope i hi) row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map i ⟨q,lim⟩⟩

theorem restore_run (i : Fin 24) (hi : i.val≤22) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m:List Bool)
    (ready:Frame (codePorts i) (startCols false d) row s) :
    let t:=run (Shadow7.archiveRestoreP i d) m s
    t.phase=s.phase ∧ Frame (rawPorts i) (endCols false d) row t ∧ ∀q,(∀k,codePorts i k≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d (codePorts i) (rawPorts i) (restoreMap i) (restoreMoves i) restoreRoute (restore_unique i hi) _
    (restore_proper i hi) (restore_route i hi) restore_sort (restore_scope i hi) row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map i ⟨q,lim⟩⟩

theorem code_from_raw (i : Fin 24) (hi : i.val≤22) : ∀k,∃m,rawPorts i m=codePorts i k := by
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

theorem roundtrip (i : Fin 24) (hi : i.val≤22) (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
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

end ECDSAAdd.Entrant.StairPacket.Shadow7
end


end


/- Inlined from ShadowBox2; provenance retained from022799f6. -/
section

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
theorem box2_S {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Nat) (a : 1556 ≤ q) (b : q ≤ 1812) (c : q + s ≤ 2069) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega
/-- The relocated carries `a0P s + 17 ..` (block 22 only). -/
theorem box2_P {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Nat) (a : Shadow7.a0P s + 17 ≤ q)
    (b : q < Shadow7.a0P s + 17 + min 3 (Shadow7.wpP s + s - 448)) : Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  have r14 := rail14 s
  unfold Shadow7.leaveBox2
  omega

/-- The A columns `a0-1 .. a0+16`. -/
theorem box2_A {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Nat) (a : Shadow7.a0P s ≤ q + 1) (b : q ≤ Shadow7.a0P s + 16) :
    Shadow7.leaveBox2 s q := by
  have r14 := rail14 s
  unfold Shadow7.leaveBox2 Shadow7.a0P Shadow7.sbP railP at *
  split_ifs at * <;> omega
/-- The B rail from the low columns up: `b0-1 .. 785 + R`. -/
theorem box2_B {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Nat) (a : Shadow7.b0P s ≤ q + 1) (b : q ≤ 785 + railP s) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega
/-- The history letters `s+16 .. s+30`. -/
theorem box2_H {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Nat) (a : s + 16 ≤ q) (b : q ≤ s + 30) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  have r14 := rail14 s
  unfold Shadow7.leaveBox2; omega
/-- The history cells that the frame does not move: `s+1044 .. s+1058`, at most 1300. -/
theorem box2_C {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Nat) (a : 1044 + s ≤ q) (b : q ≤ 1058 + s) (c : q ≤ 1300) :
    Shadow7.leaveBox2 s q := by
  have r := Shadow7.rail_win h1 h2
  unfold Shadow7.leaveBox2; omega

/-- Boolean test of the five intervals (scratch first: most wires of the fixed segments are there). -/
def inBox2B (s q : Nat) : Bool :=
  (Nat.ble 1556 q && (Nat.ble q 1812 && Nat.ble (q + s) 2069)) ||
  ((Nat.ble (Shadow7.a0P s) (q + 1) && Nat.ble q (Shadow7.a0P s + 16)) ||
  ((Nat.ble (Shadow7.b0P s) (q + 1) && Nat.ble q (785 + railP s)) ||
  ((Nat.ble (s + 16) q && Nat.ble q (s + 30)) ||
  (Nat.ble (1044 + s) q && (Nat.ble q (1058 + s) && Nat.ble q 1300)))))

theorem inBox2B_sound {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (q : Nat) (h : Shadow7.inBox2B s q = true) : Shadow7.leaveBox2 s q := by
  unfold Shadow7.inBox2B at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  rcases h with h | h | h | h | h
  · exact Shadow7.box2_S h1 h2 q h.1 h.2.1 h.2.2
  · exact Shadow7.box2_A h1 h2 q h.1 h.2
  · exact Shadow7.box2_B h1 h2 q h.1 h.2
  · exact Shadow7.box2_H h1 h2 q h.1 h.2
  · exact Shadow7.box2_C h1 h2 q h.1 h.2.1 h.2.2

def segBox2 (s : Nat) (gs : List Gate) : Bool := gs.all (fun g => g.wires.all (Shadow7.inBox2B s))
theorem allW_of_segBox2 {s : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) {gs : List Gate} (h : Shadow7.segBox2 s gs = true) :
    AllW (Shadow7.leaveBox2 s) gs := by
  intro g hg q hq
  unfold Shadow7.segBox2 at h; rw [List.all_eq_true] at h
  have := h g hg; rw [List.all_eq_true] at this
  exact Shadow7.inBox2B_sound h1 h2 q (this q hq)

theorem sig_box2 {s c : Nat} (h1 : 75 ≤ s) (h2 : s ≤ 405) (hc1 : 1044 ≤ c) (hc2 : c ≤ 1058) :
    Shadow7.leaveBox2 s (OB5.sig (s+14) (s+c)) := by
  have e := Shadow7.sig_hist h1 h2 hc1 hc2
  have r := Shadow7.rail_win h1 h2
  rcases e with ⟨e, le⟩ | ⟨e, lo, hi⟩
  · rw [e]; exact Shadow7.box2_C h1 h2 _ (by omega) (by omega) le
  · rw [e]; exact Shadow7.box2_S h1 h2 _ (by omega) hi (by omega)

theorem fixed_box2 : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    Shadow7.segBox2 (start j) (Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      Shadow7.fix2P (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix8P (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix10P (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) = true := by
  decide +kernel

section Main
attribute [local irreducible] Shadow7.leaveBox2

theorem leaveOps_box2 (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    AllW (Shadow7.leaveBox2 (start j)) (Shadow7.leaveOps (start j)) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 h1
  have fb := Shadow7.allW_of_segBox2 (by omega) w2 (Shadow7.fixed_box2 j h0 h1)
  simp only [allW_append_iff] at fb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩, f8⟩, f10⟩, f11⟩, f12⟩, fl⟩ := fb
  generalize hs : start j = s at *
  have r := Shadow7.rail_win w1 w2
  have r14 := rail14 s
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hL : 9 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 10 := by ((try unfold Wire at *); omega)
  have boxS : ∀ q : Nat, 1556 ≤ q → q ≤ 1812 → q + s ≤ 2069 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_S w1 w2 q
  have boxA : ∀ q : Nat, Shadow7.a0P s ≤ q + 1 → q ≤ Shadow7.a0P s + 16 → Shadow7.leaveBox2 s q := fun q => Shadow7.box2_A w1 w2 q
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
  have aside : ∀ i, i ≤ 17 → Shadow7.leaveBox2 s (Shadow7.a0P s - 1 + i) := by intro i hi; apply boxA <;> omega
  have bside : ∀ i, i ≤ 12 → Shadow7.leaveBox2 s (Shadow7.b0P s - 1 + i) := by intro i hi; apply boxB <;> omega
  have scr : ∀ q, 1556 ≤ q → q ≤ Shadow7.e0P s + 20 → Shadow7.leaveBox2 s q := by intro q a b; apply boxS <;> ((try unfold Wire at *); omega)
  have ctl : ∀ (xs : List Wire), (∀ x ∈ xs, 1556 ≤ x ∧ x ≤ 1614) → ∀ x ∈ xs, Shadow7.leaveBox2 s x :=
    fun xs h x hx => scr x (h x hx).1 (by have := (h x hx).2; (try unfold Wire at *); omega)
  have adj : AllW (Shadow7.leaveBox2 s) (Shadow7.leaveAdjust s) := by
    unfold Shadow7.leaveAdjust Shadow7.leaveAdjustCore
    refine allW_append (a := [Gate.cx (Shadow7.e0P s + 6) (Shadow7.e0P s + 3)])
      (allW_of_allAT (allAT_cons (ok_cx (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))) allAT_nil)) ?_
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      rcases Shadow7.pool_cases (i := i) w1 w2 with p | p | p
      · apply boxS <;> ((try unfold Wire at *); omega)
      · apply boxS <;> ((try unfold Wire at *); omega)
      · have pt := Shadow7.pool_top w1 w2
        apply Shadow7.box2_P w1 w2 <;> ((try unfold Wire at *); omega)
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
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordGM _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
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

theorem gadgets_free (s : Nat) (w1 : 75 ≤ s) (w2 : s ≤ 405) :
    AllW (hfree s) (Shadow7.leaveAdjust s) ∧ AllW (hfree s) (Shadow7.leaveBarrel s) ∧ AllW (hfree s) (Shadow7.leaveJoin s) ∧
    AllW (hfree s) (Shadow7.lowRest s) ∧ AllW (hfree s) (Shadow7.leaveStoreMapped s) ∧ AllW (hfree s) (Shadow7.leaveLowClose s) ∧
    AllW (hfree s) (swapsG (Shadow7.movesP s)) := by
  have e0b : Shadow7.e0P s + 20 + s < 2055 := by unfold Shadow7.e0P Shadow7.sbP; omega
  have e1b : Shadow7.e0P (s+15) + 8 + s < 2055 := by unfold Shadow7.e0P Shadow7.sbP; omega
  have r := Shadow7.rail_win w1 w2
  have r14 : railP (s+15) ≤ railP (s+14) := by unfold railP; split_ifs <;> omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := r
  have hL : 9 ≤ Shadow7.lowsP s ∧ Shadow7.lowsP s ≤ 10 := by ((try unfold Wire at *); omega)
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
    unfold Shadow7.leaveAdjust Shadow7.leaveAdjustCore
    refine allW_append (a := [Gate.cx (Shadow7.e0P s + 6) (Shadow7.e0P s + 3)])
      (allW_of_allAT (allAT_cons (ok_cx (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))) allAT_nil)) ?_
    refine allW_adjustG _ _ _ _ (fun y hy => ?_) (fun c hc => ?_) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega)))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; exact bank i (by ((try unfold Wire at *); omega))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2; have r := Shadow7.rail_win w1 w2
      ((try unfold hfree); (try unfold leaveBox)); ((try unfold Wire at *); omega)
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
      (fun i _ hi => ⟨tags i (by ((try unfold Wire at *); omega)), ?_, ?_⟩)) (allW_wordGM _ (scr _ (by ((try unfold Wire at *); omega)) (by ((try unfold Wire at *); omega))) _ (fun r hr => ?_))
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

theorem fixed_targets : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    segT (start j) (Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      Shadow7.fix2P (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix8P (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix10P (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j)) = true := by
  decide +kernel

/-- The event chain of the close flips each of the first five swap cells twice and targets no other. -/
theorem events_parity : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 → ∀ i : Fin 15,
    LeaveSelector.parityAt (OB5.sig (start j+14) (start j+1044+i.val))
      (GateMirror.forward (eventsG (Shadow7.e0P (start j) + 7) (Shadow7.e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)])) = some false := by
  decide +kernel
theorem swap_not_free7 (s i : Nat) (w1 : 75 ≤ s) (w2 : s ≤ 405) (hi : i < 15) : ¬ hfree s (OB5.sig (s+14) (s+1044+i)) := by
  unfold hfree OB5.sig; intro h; split at h <;> ((try unfold Wire at *); omega)
theorem swap_not_ok7 (s i : Nat) (w1 : 75 ≤ s) (w2 : s ≤ 405) (hi : i < 15) : tgtOK s (OB5.sig (s+14) (s+1044+i)) = false := by
  unfold tgtOK OB5.sig
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  split <;> ((try unfold Wire at *); omega)
theorem notarget_of_free7 {s : Nat} {gs : List Gate} (h : AllW (hfree s) gs) (w1 : 75 ≤ s) (w2 : s ≤ 405) (i : Nat) (hi : i < 15) :
    ∀ ins ∈ GateMirror.forward gs, CodecBitSliceVerify.target ins ≠ OB5.sig (s+14) (s+1044+i) := by
  intro ins hins e
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hins
  exact swap_not_free7 s i w1 w2 hi (e ▸ h g hg _ (front_target_mem g))

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
attribute [local irreducible] run measurementCount Shadow7.fix0P leaveFix1 Shadow7.fix2P leaveFix3 leaveFix4 leaveFix5 Shadow7.fix8P
  Shadow7.fix10P leaveFix11 leaveFix12 Shadow7.lowSign Shadow7.leaveAdjust Shadow7.leaveBarrel Shadow7.leaveJoin Shadow7.lowRest
  Shadow7.leaveStoreMapped Shadow7.leaveLowClose eventsG swapsG Shadow7.movesP

/-- The leave keeps every swap cell. -/
theorem swaps_kept (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i : Nat) (hi : i < 15) (s : State) (m : List Bool) :
    (run (Shadow7.leaveP j) m s).basis (OB5.sig (start j+14) (start j+1044+i)) = s.basis (OB5.sig (start j+14) (start j+1044+i)) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 h1
  obtain ⟨adj, bar, joi, lr, sm, lc, mv⟩ := Shadow7.gadgets_free (start j) (by omega) w2
  have fx := Shadow7.fixed_targets j h0 h1
  have ev := Shadow7.events_parity j h0 h1 ⟨i, hi⟩
  generalize hq : OB5.sig (start j+14) (start j+1044+i) = q at *
  have fixNo : ∀ g ∈ Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++ leaveFix1 (start j) (Shadow7.sbP (start j)) ++
      Shadow7.fix2P (start j) (Shadow7.sbP (start j)) ++ leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix8P (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix10P (start j) (Shadow7.sbP (start j)) ++
      leaveFix11 (start j) (Shadow7.sbP (start j)) ++ leaveFix12 (start j) (Shadow7.sbP (start j)) ++ Shadow7.lowSign (start j),
      CodecBitSliceVerify.target (front g) ≠ q := by
    intro g hg e
    have t := List.all_eq_true.mp fx g hg
    rw [e, ←hq, swap_not_ok7 (start j) i w1 w2 hi] at t
    exact Bool.false_ne_true t
  have gad : ∀ {gs : List Gate}, AllW (hfree (start j)) gs → ∀ g ∈ gs, CodecBitSliceVerify.target (front g) ≠ q := by
    intro gs h g hg e
    exact notarget_of_free7 h w1 w2 i hi _ (List.mem_map.mpr ⟨g, hg, rfl⟩) (e.trans hq.symm)
  -- head ++ mid: no target is q
  have nt_app : ∀ {a b : List Gate}, (∀ g ∈ a, CodecBitSliceVerify.target (front g) ≠ q) →
      (∀ g ∈ b, CodecBitSliceVerify.target (front g) ≠ q) → ∀ g ∈ a ++ b, CodecBitSliceVerify.target (front g) ≠ q := by
    intro a b ha hb g hg
    rcases List.mem_append.mp hg with h|h
    · exact ha g h
    · exact hb g h
  have f0 : ∀ g ∈ Shadow7.fix0P (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f1 : ∀ g ∈ leaveFix1 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f2 : ∀ g ∈ Shadow7.fix2P (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f3 : ∀ g ∈ leaveFix3 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f4 : ∀ g ∈ leaveFix4 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f5 : ∀ g ∈ leaveFix5 (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f8 : ∀ g ∈ Shadow7.fix8P (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
  have f10 : ∀ g ∈ Shadow7.fix10P (start j) (Shadow7.sbP (start j)), CodecBitSliceVerify.target (front g) ≠ q := fun g h => fixNo g (by simp [h])
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

end


/- Inlined from ShadowLeave; provenance retained from022799f6. -/
section

/-! Shadow7 leave families: the generic leave proofs (`LeaveJ` and its companions) for the seven-bit shadow.
Generated from the stock families by build-leaves (helpers/shadow-leave/scripts/port.py), then edited where
smallness enters (far-only at the entry cutoff, `Shadow7.SmallIfFar` / `Shadow7.EndSmall`). -/

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
/-- Entry-cutoff smallness at the seven-bit shadow: far-only at entry, both branches at the end of the block. -/
def Small7 (b : Nat) (z : SkywalkNat.State) : Prop := Shadow7.SmallIfFar b 15 z ∧ Shadow7.EndSmall b z
end ECDSAAdd.Entrant.StairPacket.LeaveJ7
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace
theorem orient (b : Nat) (z : SkywalkNat.State) (small : LeaveJ7.Small7 b z) (far : Shadow.far b 15 z) :
    decide (2^b≤z.u)=decide (z.v<z.u) :=
  LeaveTraceHistory.orient b z (small.1 far) far
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace
theorem certifiedChain (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : LeaveJ7.Small7 b z) (odd : z.v%2=1) (far : Shadow.far b 15 z) :
    chain (decide (2^b≤z.u)) (SkywalkTrace.trace 15 (encode g s z.u z.v)) :=
  LeaveTraceHistory.certifiedChain b z g s (small.1 far) odd far
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace
theorem firstSwap (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : LeaveJ7.Small7 b z) (odd : z.v%2=1) (far : Shadow.far b 15 z)
    (side : decide (2^b≤z.u)=false) :
    let xs:=SkywalkTrace.trace 15 (encode g s z.u z.v)
    ∀ i (hi : i<xs.length), i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u) :=
  LeaveTraceHistory.firstSwap b z g s (small.1 far) odd far side
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far
open SkywalkNat IntegerHigh Shadow HighBankSum
theorem far_result (b w : Nat) (z : SkywalkNat.State) (small : LeaveJ7.Small7 b z)
    (far : Shadow.far b 15 z) (odd : z.v%2=1) (enough : high b 15 z+1<2^w) :
    let r:=reduced b 15 z
    let S:=total (step^[15] r)
    let F:=total (step^[15] z)
    let t:=if 2^b≤z.u then 0 else wait 15 z.u
    let d:=S/2^(b+1)/2^t
    let neg:=cross17 d && (!(decide (2^b≤z.u)) && negative (oddBits (letters 15 r)))
    d+1=(cross17 d).toNat+2*(!neg).toNat ∧
      F/2^(b+1)=2^t*HighBankAdjust.adjusted (high b 15 z) w (cross17 d) neg+S/2^(b+1)%2^t :=
  LeaveShadowRails.far_result b w z (small.1 far) far odd enough
end ECDSAAdd.Entrant.StairPacket.LeaveJ7.Far

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror HighBankJoin HighBankReassemble
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

/-- The bank register read by the adjust (dadon's `Leave{s}High.ys`). -/
def ys (j : Fin 24) : List Wire := (List.range (Shadow7.wpP (start j))).map (Shadow7.bankW (start j))
/-- The adjust's carry pool (dadon's `Leave{s}High.carries`). -/
def carries (j : Fin 24) : List Wire := (List.range (Shadow7.wpP (start j) - 1)).map (Shadow7.poolW (start j))
theorem tags_mem (i : Nat) (hi : i < 16) : tagsP.getD i 0 ∈ tagsP := by
  rw [List.getD_eq_getElem _ _ (show i < tagsP.length by simp [tagsP]; omega)]; exact List.getElem_mem _
theorem tags_range' : ∀ q ∈ tagsP, 1556 ≤ q ∧ q ≤ 1576 := by decide

theorem layout (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : HighBankShift.Layout 1613 (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  refine ⟨fun i hi k hk e => Shadow7.bank_inj (by omega) w2 hi hk e, fun i hi e => ?_⟩
  have r := Shadow7.rail_win w1 w2; have b := Shadow7.bank_cases w1 w2 hi
  unfold Shadow7.wpP bTopP Shadow7.e0P at *; unfold Wire at *; omega

/-! Control: the one-hot tag parity selects the key bits (constant lists, decided once). -/

theorem selection0 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP0 = key.val.testBit 0 := by
  revert key; decide +kernel
theorem selection1 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP1 = key.val.testBit 1 := by
  revert key; decide +kernel
theorem selection2 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP2 = key.val.testBit 2 := by
  revert key; decide +kernel
theorem selection3 (key : Fin 16) :
    HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) controlsP3 = key.val.testBit 3 := by
  revert key; decide +kernel

theorem controls_range : ∀ xs ∈ [controlsP0, controlsP1, controlsP2, controlsP3], 1613 ∉ xs ∧
    (∀ q ∈ xs, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ xs, q ∈ tagsP := by decide +kernel

theorem controls_out (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (xs : List Wire) (hx : ∀ q ∈ xs, 1556 ≤ q ∧ q ≤ 1576) :
    ∀ q ∈ xs, HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  intro q hq i hi e
  have r := Shadow7.rail_win (by omega) w2; have b := Shadow7.bank_cases w1 w2 hi; have := hx q hq
  unfold Shadow7.wpP bTopP Shadow7.e0P at *; unfold Wire at *; omega

/-! Barrel: four stages shift the bank by the key (dadon's `Leave{s}Barrel.value`). -/

theorem barrel_shape (s : Nat) : GateMirror.forward (Shadow7.leaveBarrel s) =
    HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP0 1 (Shadow7.wpP s) ++ HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP1 2 (Shadow7.wpP s + 1) ++
    HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP2 4 (Shadow7.wpP s + 3) ++ HighBankBarrel.stage 1613 (Shadow7.bankW s) controlsP3 8 (Shadow7.wpP s + 7) := by
  simp only [Shadow7.leaveBarrel, forward_app, forward_stageG]

/-- dadon's `Leave{s}BarrelBits.byDigits`: the four stages shift by the key read from the control parities. -/
theorem barrel_bits (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (key : Fin 16) (x : Nat) (s : State) (m : List Bool)
    (small : x < 2^(Shadow7.wpP (start j))) (h : HighBankBarrel.holds (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) x s) (clean : s.basis 1613 = false)
    (bit0 : HighBankControl.parity s.basis controlsP0 = key.val.testBit 0)
    (bit1 : HighBankControl.parity s.basis controlsP1 = key.val.testBit 1)
    (bit2 : HighBankControl.parity s.basis controlsP2 = key.val.testBit 2)
    (bit3 : HighBankControl.parity s.basis controlsP3 = key.val.testBit 3) :
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) m s) := by
  rw [barrel_shape]
  have L := layout j h0 (by omega)
  obtain ⟨c0, c1, c2, c3⟩ : (1613 ∉ controlsP0 ∧ (∀ q ∈ controlsP0, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP0, q ∈ tagsP) ∧
      (1613 ∉ controlsP1 ∧ (∀ q ∈ controlsP1, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP1, q ∈ tagsP) ∧
      (1613 ∉ controlsP2 ∧ (∀ q ∈ controlsP2, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP2, q ∈ tagsP) ∧
      (1613 ∉ controlsP3 ∧ (∀ q ∈ controlsP3, 1556 ≤ q ∧ q ≤ 1576) ∧ ∀ q ∈ controlsP3, q ∈ tagsP) :=
    ⟨controls_range _ (by simp), controls_range _ (by simp), controls_range _ (by simp), controls_range _ (by simp)⟩
  have beginPass : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< 0) s (run [] m s) := HighBankBarrel.start h
  have p1 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< (key.val % 2)) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j))) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c0.1 (controls_out j h0 (by omega) _ c0.2.1) clean
      (HighBankBarrel.room small (by omega)) _ beginPass
    rw [bit0]
    exact (by decide +kernel : ∀ key : Fin 16, 0 + (if key.val.testBit 0 then 1 else 0) = (key.val % 2)) key
  have p2 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< (key.val % 4)) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j)) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP1 2 (Shadow7.wpP (start j) + 1)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c1.1 (controls_out j h0 (by omega) _ c1.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 2 by decide); omega)) _ p1
    rw [bit1]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 2) + (if key.val.testBit 1 then 2 else 0) = (key.val % 4)) key
  have p3 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< (key.val % 8)) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j)) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP1 2 (Shadow7.wpP (start j) + 1) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP2 4 (Shadow7.wpP (start j) + 3)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c2.1 (controls_out j h0 (by omega) _ c2.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 4 by decide); omega)) _ p2
    rw [bit2]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 4) + (if key.val.testBit 2 then 4 else 0) = (key.val % 8)) key
  have p4 : ∀ m, HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s
      (run ([] ++ HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP0 1 (Shadow7.wpP (start j)) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP1 2 (Shadow7.wpP (start j) + 1) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP2 4 (Shadow7.wpP (start j) + 3) ++
        HighBankBarrel.stage 1613 (Shadow7.bankW (start j)) controlsP3 8 (Shadow7.wpP (start j) + 7)) m s) := by
    apply HighBankBarrel.next L (by decide) (by omega) c3.1 (controls_out j h0 (by omega) _ c3.2.1) clean
      (HighBankBarrel.room small (by have := Nat.mod_lt key.val (show 0 < 8 by decide); omega)) _ p3
    rw [bit3]
    exact (by decide +kernel : ∀ key : Fin 16, (key.val % 8) + (if key.val.testBit 3 then 8 else 0) = key.val) key
  simpa only [List.nil_append] using p4 m

theorem controls_tags : (∀ q ∈ controlsP0, q ∈ tagsP) ∧ (∀ q ∈ controlsP1, q ∈ tagsP) ∧ (∀ q ∈ controlsP2, q ∈ tagsP) ∧
    (∀ q ∈ controlsP3, q ∈ tagsP) := by decide +kernel

theorem ys_length (j : Fin 24) : (ys j).length = Shadow7.wpP (start j) := by simp [ys]
theorem ys_getD (j : Fin 24) (i : Nat) (hi : i < Shadow7.wpP (start j)) : (ys j).getD i 0 = Shadow7.bankW (start j) i := by
  simp [ys, List.getD_eq_getElem?_getD, hi]

theorem adjust_nodup (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    ((Shadow7.e0P (start j) + 3) :: (ys j ++ carries j)).Nodup := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, ?_, Shadow7.pool_nodup _ _ w1 w2 (le_refl _), ?_⟩
  · intro hm; rcases List.mem_append.mp hm with hm|hm
    · obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
    · obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have p := Shadow7.pool_cases (i := i) w1 w2; unfold Wire at *; omega
  · exact List.Nodup.map_on (fun a ha b hb e => Shadow7.bank_inj w1 w2 (by rw [List.mem_range] at ha; omega)
      (by rw [List.mem_range] at hb; omega) e) List.nodup_range
  · intro a ha b hb e
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hi hk
    have bb := Shadow7.bank_cases w1 w2 (i := i) (by omega); have p := Shadow7.pool_cases (i := k) w1 w2
    unfold Wire at *; omega

theorem high_bits (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (bit0 : HighBankControl.parity s.basis controlsP0 = key.val.testBit 0)
    (bit1 : HighBankControl.parity s.basis controlsP1 = key.val.testBit 1)
    (bit2 : HighBankControl.parity s.basis controlsP2 = key.val.testBit 2)
    (bit3 : HighBankControl.parity s.basis controlsP3 = key.val.testBit 3) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 3)) (s.basis 1596)
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s
      (run (GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))) m s) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  let p := HighBankAdjust.adjust (ys j) (carries j) (Shadow7.e0P (start j) + 3) 1596
  have pe : GateMirror.forward (Shadow7.leaveAdjustCore (start j)) = p := by
    simp only [Shadow7.leaveAdjustCore, forward_adjustG, p, ys, carries]
  let t := run p m s
  let x := regValue (ys j) t.basis
  have negOut : (1596:Wire) ∉ ys j := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
  have size : (carries j).length + 1 = (ys j).length := by simp [ys, carries]; omega
  have ht := HighBankAdjust.correct (ys j) (carries j) (Shadow7.e0P (start j) + 3) 1596 (adjust_nodup j h0 (by omega)) negOut size s m clean
  have small : x < 2^(Shadow7.wpP (start j)) := by have := regValue_lt (ys j) t.basis; rwa [ys_length] at this
  have notYs : ∀ i, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → Shadow7.bankW (start j) i ∉ ys j := by
    intro i a b hm; obtain ⟨k, hk, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hk
    have := Shadow7.bank_inj w1 w2 (i := k) (k := i) (by omega) b e; omega
  have data : HighBankBarrel.holds (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) x t := by
    intro i hi
    by_cases lo : i < Shadow7.wpP (start j)
    · rw [← ys_getD j i lo]
      exact HighBankAdjust.bit_read (ys j) i t.basis (by rw [ys_length]; exact lo)
    · rw [Nat.testBit_lt_two_pow (small.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
      exact (ht.2.1 _ (notYs i (by omega) hi)).trans (padding i (by omega) hi)
  have t1613 : (1613:Wire) ∉ ys j := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega
  have cold : t.basis 1613 = false := (ht.2.1 _ t1613).trans selectZero
  have untouched : ∀ q ∈ tagsP, q ∉ ys j := by
    intro q hq hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    have tr := tags_range' q hq
    unfold Wire at *; omega
  have same : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity t.basis xs = HighBankControl.parity s.basis xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => ht.2.1 q (untouched q (hx q hq)))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  have action := barrel_bits j h0 (by omega) key x t (m.drop (measurementCount p)) small data cold
    ((same _ t0).trans bit0) ((same _ t1).trans bit1) ((same _ t2).trans bit2) ((same _ t3).trans bit3)
  have initial : x = HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 3))
      (s.basis 1596) := by rw [← ys_length j]; exact ht.2.2
  dsimp only
  rw [forward_app, pe, run_append, run_take, ← initial]
  refine ⟨action.bits, action.phase.trans ht.1, fun q h => (action.frame q h).trans (ht.2.1 q ?_)⟩
  intro member
  obtain ⟨i, hi, e⟩ := List.mem_map.mp member; rw [List.mem_range] at hi
  exact h i (by omega) e.symm

/-- dadon's `Leave{s}High.result`. -/
theorem high_result (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (key : Fin 16) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (one : ∀ q ∈ tagsP, s.basis q = decide (q = tagsP.getD key 0)) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 3)) (s.basis 1596)
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) (x <<< key.val) s
      (run (GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))) m s) := by
  have par : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) →
      HighBankControl.parity s.basis xs = HighBankControl.parity (fun q => decide (q = tagsP.getD key 0)) xs :=
    fun xs hx => HighBankBarrel.parity_congr (fun q hq => one q (hx q hq))
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  exact high_bits j h0 (by omega) key s m clean selectZero padding ((par _ t0).trans (selection0 key))
    ((par _ t1).trans (selection1 key)) ((par _ t2).trans (selection2 key)) ((par _ t3).trans (selection3 key))

/-- dadon's `Leave{s}NearHigh.result`: all tags off, no shift. -/
theorem nearHigh_result (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (off : ∀ q ∈ tagsP, s.basis q = false) :
    let x := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (s.basis (Shadow7.e0P (start j) + 3)) (s.basis 1596)
    HighBankBarrel.Result (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) x s
      (run (GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))) m s) := by
  have quiet : ∀ (xs : List Wire), (∀ q ∈ xs, q ∈ tagsP) → HighBankControl.parity s.basis xs = false := by
    intro xs sub
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      simp only [HighBankControl.parity, off q (sub _ (by simp)), Bool.false_xor,
        ih (fun z h => sub _ (List.mem_cons_of_mem _ h))]
  obtain ⟨t0, t1, t2, t3⟩ := controls_tags
  have h := high_bits j h0 (by omega) 0 s m clean selectZero padding (quiet _ t0) (quiet _ t1) (quiet _ t2) (quiet _ t3)
  simpa only [Fin.val_zero, Nat.shiftLeft_zero] using h

/-! Join and Word: the digit pass and the word reassembly (dadon's `Leave{s}Join` / `Leave{s}Word.combine`). -/

def hot (key : Fin 16) (q : Wire) := decide (q = tagsP.getD key 0)
abbrev cols (j : Fin 24) : List Column := Shadow7.columnsP (start j)
theorem cols_length (j : Fin 24) : (cols j).length = 17 := by simp [cols, Shadow7.columnsP]
/-- dadon's `Leave{s}Word.row`. -/
abbrev row (j : Fin 24) (i : Fin 17) : Column := (cols j)[i.val]'(by rw [cols_length]; exact i.isLt)

theorem row_eq (j : Fin 24) (i : Fin 17) : (row j i).shadow = Shadow7.a0P (start j) + i.val ∧ (row j i).tube = Shadow7.bankW (start j) i.val ∧
    (row j i).low = decide (i.val < Shadow7.lowsP (start j)) ∧ (row j i).hot = if i.val < 16 then some (tagsP.getD i.val 0) else none := by
  simp [row, cols, Shadow7.columnsP]

/-- The schedule only reads the `hot` fields (identical at every block). -/
theorem schedule_hot (ref : BasisState) (key : Nat) : ∀ (a : Bool) (k : Nat) (rs rs' : List Column),
    rs.map (·.hot) = rs'.map (·.hot) → schedule ref key a k rs = schedule ref key a k rs'
  | _, _, [], [], _ => rfl
  | _, _, [], _::_, h => by simp at h
  | _, _, _::_, [], h => by simp at h
  | a, k, r::rs, r'::rs', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [schedule, h.1, schedule_hot ref key _ (k+1) rs rs' h.2]

theorem hots (j : Fin 24) : (cols j).map (·.hot) = (Shadow7.columnsP 225).map (·.hot) := by
  simp only [cols, Shadow7.columnsP, List.map_map]; rfl

theorem schedule_ok (j : Fin 24) (key : Fin 16) : schedule (hot key) key false 0 (cols j) = true := by
  rw [schedule_hot _ _ _ _ _ (Shadow7.columnsP 225) (hots j)]
  revert key; decide +kernel

theorem digitSites (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    DigitLayout (tagsP.getD · 0) (fun i => Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6) 1613 0 16 := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  refine ⟨fun i _ hi => ?_, fun i _ hi k _ hk => ?_⟩
  · have t := tags_range' _ (tags_mem i hi)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or, not_false_eq_true]
    unfold Wire at *; omega
  · have t := tags_range' _ (tags_mem i hi); unfold Wire at *; omega

theorem colSites (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : WellPlaced 1614 (cols j) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  refine ⟨fun c hc => ?_, fun c hc h hh => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    dsimp only
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or, not_false_eq_true]
    unfold Wire at *; omega
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    have th : 1556 ≤ h ∧ h ≤ 1576 := by
      simp only at hh; split at hh
      · simp only [Option.mem_def, Option.some.injEq] at hh; subst hh; exact tags_range' _ (tags_mem i (by omega))
      · simp at hh
    refine ⟨by unfold Wire at *; omega, fun v hv => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv; rw [List.mem_range] at hk
    have b := Shadow7.bank_cases w1 w2 (i := k) (by omega)
    dsimp only; unfold Wire at *; omega

theorem disjoint (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : (cols j).Pairwise Apart := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  unfold cols Shadow7.columnsP
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) (List.pairwise_lt_range (n := 17))
  rw [List.mem_range] at ha hb
  have ba := Shadow7.bank_cases w1 w2 (i := a) (by omega); have bb := Shadow7.bank_cases w1 w2 (i := b) (by omega)
  have ne : Shadow7.bankW (start j) a ≠ Shadow7.bankW (start j) b := fun e => by have := Shadow7.bank_inj w1 w2 (by omega) (by omega) e; omega
  unfold Apart; dsimp only
  refine ⟨?_, ?_, ?_, ne⟩ <;> unfold Wire at * <;> omega

theorem join_shape (s : Nat) : GateMirror.forward (Shadow7.leaveJoin s) =
    digits (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) (Shadow7.e0P s + 6) 1613 0 16 ++ wordM 1614 (Shadow7.columnsP s) := by
  simp only [Shadow7.leaveJoin, forward_app, forward_digitsG, forward_wordGM]

theorem combine (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (key : Fin 16) (X H : Nat) (s : State) (m : List Bool)
    (tagsOn : ∀ q ∈ tagsP, s.basis q = hot key q)
    (shadow : ∀ i < 17, s.basis (Shadow7.a0P (start j) + i) = X.testBit i)
    (tube : ∀ i < 17, s.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i)
    (digit : X/2^key.val = (s.basis (Shadow7.e0P (start j) + 6)).toNat + 2*(s.basis 1613).toNat)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (Shadow7.leaveJoin (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 17, out.basis (row j i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row j i).free = false) ∧
      ∀ q, (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  let ref := hot key
  let dp := digits (tagsP.getD · 0) (fun i => Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6) 1613 0 16
  let u := run dp m s
  have unique : ∀ i t : Fin 16, hot t (tagsP.getD i 0) = decide (i.val = t.val) := by decide +kernel
  have sel (i : Nat) (_ : 0 ≤ i) (hi : i < 0+16) : s.basis (tagsP.getD i 0) = decide (i = key.val) :=
    (tagsOn _ (tags_mem i hi)).trans (unique ⟨i, hi⟩ key)
  have z := digits_remainder (digitSites j h0 (by omega)) s m key.val (by omega) key.isLt sel X 17 (by decide)
    (fun i _ k _ eq => Nat.add_left_cancel eq) shadow digit
  have hits : ∀ c ∈ cols j, ∀ q ∈ c.hot, q ∈ tagsP := by
    intro c hc q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    simp only at hq; split at hq
    · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact tags_mem i (by omega)
    · simp at hq
  have members : ∀ q ∈ tagsP, ∀ i : Nat, i ≤ 17 → q ≠ Shadow7.a0P (start j) + i := by
    intro q hq i hi; have := tags_range' q hq; unfold Wire at *; omega
  have ctrl : ∀ c ∈ cols j, ∀ q ∈ c.hot, u.basis q = ref q := by
    intro c hc q hq
    have mem := hits c hc q hq
    exact (z.2.2 q (members q mem key.val (by omega)) (members q mem (key.val+1) (by omega))).trans (tagsOn q mem)
  have inputs : columnsRead (cols j) u.basis X H key.val 0 := by
    intro i hi
    rw [cols_length] at hi
    have g := row_eq j ⟨i, hi⟩
    change u.basis (row j ⟨i, hi⟩).shadow = _ ∧ u.basis (row j ⟨i, hi⟩).tube = _
    rw [g.1, g.2.1]
    simp only [Nat.zero_add]
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    refine ⟨z.2.1 i hi, (z.2.2 _ ?_ ?_).trans (tube i hi)⟩ <;> unfold Wire at * <;> omega
  have rz : u.basis 1614 = false := (z.2.2 _ (by unfold Wire at *; omega) (by unfold Wire at *; omega)).trans scratch
  have word := reassembleM 1614 (cols j) ref u m X H key.val (colSites j h0 (by omega)) (disjoint j h0 (by omega)) ctrl rz
    (schedule_ok j key) inputs
  dsimp only
  rw [join_shape, run_append, run_take, show measurementCount dp = 0 from (digits_counts _ _ _ _ _ _).2, List.drop_zero]
  refine ⟨word.1.trans z.1, fun i => word.2.1 i.val (by rw [cols_length]; exact i.isLt), ?_⟩
  intro q away
  have safe (k : Nat) (hk : k < 17) : q ≠ Shadow7.a0P (start j) + k := by
    have g := row_eq j ⟨k, hk⟩
    rw [← g.1]
    exact (away _ (List.getElem_mem _)).1
  exact (word.2.2 q away).trans (z.2.2 _ (safe key.val (by omega)) (safe (key.val+1) (by omega)))



/-- dadon's `Leave{s}NearWord.combine`: no tag hot, the word passes the shadows through. -/
theorem nearWord_combine (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (X : Nat) (bound : X < 2^17) (s : State)
    (m : List Bool) (off : ∀ q ∈ tagsP, s.basis q = false)
    (shadow : ∀ i < 17, s.basis (Shadow7.a0P (start j) + i) = X.testBit i)
    (tube : ∀ i < 17, s.basis (Shadow7.bankW (start j) i) = false)
    (scratch : s.basis 1614 = false) :
    let out := run (GateMirror.forward (Shadow7.leaveJoin (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 17, out.basis (row j i).keep = X.testBit i.val ∧ out.basis (row j i).free = false) ∧
      ∀ q, (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) → out.basis q = s.basis q := by
  let ref : BasisState := fun _ => false
  let dp := digits (tagsP.getD · 0) (fun i => Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6) 1613 0 16
  have none : run dp m s = s := by
    apply digits_quiet (digitSites j h0 (by omega))
    intro i _ hi
    exact off _ (tags_mem i hi)
  have sch : schedule ref 17 false 0 (cols j) = true := by
    rw [schedule_hot _ _ _ _ _ (Shadow7.columnsP 225) (hots j)]; decide +kernel
  have members : ∀ c ∈ cols j, ∀ q ∈ c.hot, q ∈ tagsP := by
    intro c hc q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi
    simp only at hq; split at hq
    · simp only [Option.mem_def, Option.some.injEq] at hq; subst hq; exact tags_mem i (by omega)
    · simp at hq
  have inputs : columnsRead (cols j) s.basis X 0 17 0 := by
    intro i hi
    rw [cols_length] at hi
    have g := row_eq j ⟨i, hi⟩
    change s.basis (row j ⟨i, hi⟩).shadow = _ ∧ s.basis (row j ⟨i, hi⟩).tube = _
    rw [g.1, g.2.1]
    simp only [Nat.mod_eq_of_lt bound, Nat.zero_add, Nat.mul_zero, Nat.zero_testBit]
    exact ⟨shadow i hi, tube i hi⟩
  have v := reassembleM 1614 (cols j) ref s m X 0 17 (colSites j h0 (by omega)) (disjoint j h0 (by omega))
    (fun a ha q h => off q (members a ha q h)) scratch sch inputs
  dsimp only
  rw [join_shape, run_append, run_take, show measurementCount dp = 0 from (digits_counts _ _ _ _ _ _).2, List.drop_zero, none]
  refine ⟨v.1, fun i => ?_, v.2.2⟩
  have hv := v.2.1 i.val (by rw [cols_length]; exact i.isLt)
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt bound] using hv

/-! Middle: adjust, barrel, sign bit, join (dadon's `Leave{s}Middle.result`; `middle` = cuts 8..24). -/

def middleOps (s : Nat) : List Gate := Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++ Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.leaveJoin s
theorem fix8_forward (s h : Nat) : GateMirror.forward (Shadow7.fix8P s h) =
    [.CX (Shadow7.e0P s + 3) 1613, .CX 1596 1613, .CX 1597 1613, .CX (Shadow7.e0P s + 6) (Shadow7.e0P s + 3)] := rfl
theorem fix10_forward (s h : Nat) : GateMirror.forward (Shadow7.fix10P s h) =
    [.CX (Shadow7.e0P s + 3) 1613, .CX (Shadow7.e0P s + 6) 1613, .CX 1596 1613, .CX 1597 1613] := rfl
theorem adjust_forward (s : Nat) : GateMirror.forward (Shadow7.leaveAdjust s) =
    Instr.CX (Shadow7.e0P s + 6) (Shadow7.e0P s + 3) :: GateMirror.forward (Shadow7.leaveAdjustCore s) := by
  rw [Shadow7.leaveAdjust, forward_app]
  rfl
theorem run_cx_cons (c t : Wire) (p : Program) (m : List Bool) (s : State) :
    run (Instr.CX c t :: p) m s = run p m ⟨s.phase, writeBit s.basis t (s.basis t ^^ s.basis c)⟩ := rfl

/-- The margin-17 middle: carry-in fold, adjust and barrel, the sign bit, the join. -/
theorem middle_parts (s : Nat) : GateMirror.forward (middleOps s) =
    Instr.CX (Shadow7.e0P s + 6) (Shadow7.e0P s + 3) ::
      (GateMirror.forward (Shadow7.leaveAdjustCore s ++ Shadow7.leaveBarrel s) ++
        ([.CX (Shadow7.e0P s + 3) 1613, .CX 1596 1613, .CX 1597 1613, .CX (Shadow7.e0P s + 6) (Shadow7.e0P s + 3)] ++
          GateMirror.forward (Shadow7.leaveJoin s))) := by
  simp only [middleOps, forward_app, adjust_forward, fix8_forward, List.append_assoc, List.cons_append]

/-- `fix8P`: three CX into the sign wire `t`, then the far flag `f` gets the crossing bit `c` back. -/
theorem run_sign8 (f c p q t : Wire) (m : List Bool) (s : State) (hft : f ≠ t) (hct : c ≠ t) (hpt : p ≠ t) (hqt : q ≠ t)
    (hcf : c ≠ f) :
    (run [.CX f t, .CX p t, .CX q t, .CX c f] m s).phase = s.phase ∧
      (run [.CX f t, .CX p t, .CX q t, .CX c f] m s).basis t = (((s.basis t ^^ s.basis f) ^^ s.basis p) ^^ s.basis q) ∧
      (run [.CX f t, .CX p t, .CX q t, .CX c f] m s).basis f = (s.basis f ^^ s.basis c) ∧
      ∀ w, w ≠ t → w ≠ f → (run [.CX f t, .CX p t, .CX q t, .CX c f] m s).basis w = s.basis w := by
  refine ⟨by simp [run], ?_, ?_, ?_⟩
  · simp [run, writeBit, Function.update_apply, hft, hct, hpt, hqt, hcf, hft.symm, hct.symm, hpt.symm, hqt.symm, hcf.symm]
  · simp [run, writeBit, Function.update_apply, hft, hct, hpt, hqt, hcf, hft.symm, hct.symm, hpt.symm, hqt.symm, hcf.symm]
  · intro w wt wf
    simp [run, writeBit, Function.update_apply, wt, wf]

/-- `fix10P`: four CX into the sign wire `t`. -/
theorem run_sign10 (f c p q t : Wire) (m : List Bool) (s : State) (hft : f ≠ t) (hct : c ≠ t) (hpt : p ≠ t) (hqt : q ≠ t) :
    (run [.CX f t, .CX c t, .CX p t, .CX q t] m s).phase = s.phase ∧
      (run [.CX f t, .CX c t, .CX p t, .CX q t] m s).basis t =
        ((((s.basis t ^^ s.basis f) ^^ s.basis c) ^^ s.basis p) ^^ s.basis q) ∧
      ∀ w, w ≠ t → (run [.CX f t, .CX c t, .CX p t, .CX q t] m s).basis w = s.basis w := by
  refine ⟨by simp [run], ?_, ?_⟩
  · simp [run, writeBit, Function.update_apply, hft, hct, hpt, hqt, hft.symm, hct.symm, hpt.symm, hqt.symm]
  · intro w wt
    simp [run, writeBit, Function.update_apply, wt]

/-- The far middle at margin 17. The selector delivers `e0+6 = d0` (bit 0 of the digit), `1596 = signExpr` and
`1597 = d0 ∧ signExpr`; the carry-in of the adjust is `¬d0` (`e0+3 = far = true`), its sign `signExpr`. -/
theorem middle_result (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (key : Fin 16) (X : Nat) (s : State) (m : List Bool)
    (clean : ∀ q ∈ carries j, s.basis q = false) (selectZero : s.basis 1613 = false)
    (padding : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 → s.basis (Shadow7.bankW (start j) i) = false)
    (one : ∀ q ∈ tagsP, s.basis q = hot key q)
    (shadow : ∀ i < 17, s.basis (Shadow7.a0P (start j) + i) = X.testBit i)
    (farOn : s.basis (Shadow7.e0P (start j) + 3) = true)
    (gate : s.basis 1597 = (s.basis (Shadow7.e0P (start j) + 6) && s.basis 1596))
    (digit : X/2^key.val + 1 = (!s.basis (Shadow7.e0P (start j) + 6)).toNat +
      2*(!(!s.basis (Shadow7.e0P (start j) + 6) && s.basis 1596)).toNat)
    (scratch : s.basis 1614 = false) :
    let H := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (!s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1596)
    let out := run (GateMirror.forward (middleOps (start j))) m s
    out.phase = s.phase ∧
      (∀ i : Fin 17, out.basis (row j i).keep = (2^key.val*H+X%2^key.val).testBit i ∧ out.basis (row j i).free = false) ∧
      (∀ i : Nat, 17 ≤ i → i < Shadow7.wpP (start j) + 15 → out.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i) ∧
      (∀ q, q ≠ 1613 → HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q → (∀ r ∈ cols j, q ≠ r.shadow ∧ q ≠ r.tube) →
        out.basis q = s.basis q) ∧
      out.basis 1613 = (((s.basis (Shadow7.e0P (start j) + 3) ^^ s.basis (Shadow7.e0P (start j) + 6)) ^^ s.basis 1596) ^^ s.basis 1597) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win w1 w2
  have n3 : (Shadow7.e0P (start j) + 3 : Wire) ≠ 1613 := by unfold Wire at *; omega
  have n6 : (Shadow7.e0P (start j) + 6 : Wire) ≠ 1613 := by unfold Wire at *; omega
  have n63 : (Shadow7.e0P (start j) + 6 : Wire) ≠ Shadow7.e0P (start j) + 3 := by unfold Wire at *; omega
  let H := HighBankAdjust.adjusted (regValue (ys j) s.basis) (Shadow7.wpP (start j)) (!s.basis (Shadow7.e0P (start j) + 6)) (s.basis 1596)
  let pre : State := ⟨s.phase, writeBit s.basis (Shadow7.e0P (start j) + 3)
    (s.basis (Shadow7.e0P (start j) + 3) ^^ s.basis (Shadow7.e0P (start j) + 6))⟩
  have preq (q : Wire) (ne : q ≠ Shadow7.e0P (start j) + 3) : pre.basis q = s.basis q := by
    show writeBit s.basis _ _ q = s.basis q
    simp only [writeBit, Function.update_of_ne ne]
  have pre3 : pre.basis (Shadow7.e0P (start j) + 3) = !s.basis (Shadow7.e0P (start j) + 6) := by
    show writeBit s.basis _ _ _ = _
    simp only [writeBit, Function.update_self, farOn, Bool.true_xor]
  have cleanP : ∀ q ∈ carries j, pre.basis q = false := by
    intro q hq
    refine (preq q ?_).trans (clean q hq)
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    have pt := Shadow7.pool_top w1 w2
    have p := Shadow7.pool_cases (i := i) w1 w2; unfold Wire at *; omega
  have selP : pre.basis 1613 = false := (preq _ (Ne.symm n3)).trans selectZero
  have padP : ∀ i : Nat, Shadow7.wpP (start j) ≤ i → i < Shadow7.wpP (start j) + 15 →
      pre.basis (Shadow7.bankW (start j) i) = false := by
    intro i lo hi
    have b := Shadow7.bank_cases w1 w2 hi
    exact (preq _ (by unfold Wire at *; omega)).trans (padding i lo hi)
  have oneP : ∀ q ∈ tagsP, pre.basis q = hot key q := by
    intro q hq
    have t := tags_range' q hq
    exact (preq q (by unfold Wire at *; omega)).trans (one q hq)
  let early := GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))
  let signBit : Program := [.CX (Shadow7.e0P (start j) + 3) 1613, .CX 1596 1613, .CX 1597 1613,
    .CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3)]
  let v := run early m pre
  let tape := m.drop (measurementCount early)
  let u := run signBit tape v
  have a := high_result j h0 (by omega) key pre m cleanP selP padP oneP
  have hval : HighBankAdjust.adjusted (regValue (ys j) pre.basis) (Shadow7.wpP (start j)) (pre.basis (Shadow7.e0P (start j) + 3))
      (pre.basis 1596) = H := by
    have y : regValue (ys j) pre.basis = regValue (ys j) s.basis := (regValue_eq_iff _ _ _).mpr (fun q hq => preq q (by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
      have b := Shadow7.bank_cases w1 w2 (i := i) (by omega); unfold Wire at *; omega))
    rw [y, pre3, preq 1596 (by unfold Wire at *; omega)]
  have bits (i : Nat) (hi : i < Shadow7.wpP (start j) + 15) : v.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i := by
    rw [Nat.mul_comm (2^key.val) H, ← Nat.shiftLeft_eq, ← hval]
    exact a.bits i hi
  have sg := run_sign8 (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 6) 1596 1597 1613 tape v n3 n6 (by decide) (by decide) n63
  have unchanged (q : Wire) (ne : q ≠ 1613) (ne3 : q ≠ Shadow7.e0P (start j) + 3) : u.basis q = v.basis q := sg.2.2.2 q ne ne3
  have old (q : Wire) (ne : q ≠ 1613) (ne3 : q ≠ Shadow7.e0P (start j) + 3)
      (ext : HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q) : u.basis q = s.basis q :=
    (unchanged q ne ne3).trans ((a.frame q ext).trans (preq q ne3))
  have bankOut : ∀ q : Nat, (1556 ≤ q ∧ q ≤ 1597) ∨ (q ≤ 785) ∨ (Shadow7.e0P (start j) + 3 ≤ q ∧ q ≤ Shadow7.e0P (start j) + 9) →
      HighBankBarrel.outside (Shadow7.bankW (start j)) (Shadow7.wpP (start j) + 15) q := by
    intro q hq i hi e
    have b := Shadow7.bank_cases w1 w2 hi
    unfold Wire at *; omega
  have stable : ∀ i, i < Shadow7.wpP (start j) + 15 → (1613:Wire) ≠ Shadow7.bankW (start j) i := fun i hi => (layout j h0 (by omega)).separate i hi
  have ext3 := bankOut (Shadow7.e0P (start j) + 3) (Or.inr (Or.inr (by omega)))
  have ext6 := bankOut (Shadow7.e0P (start j) + 6) (Or.inr (Or.inr (by omega)))
  have v3 : v.basis (Shadow7.e0P (start j) + 3) = !s.basis (Shadow7.e0P (start j) + 6) := (a.frame _ ext3).trans pre3
  have v6 : v.basis (Shadow7.e0P (start j) + 6) = s.basis (Shadow7.e0P (start j) + 6) := (a.frame _ ext6).trans (preq _ n63)
  have v96 : v.basis 1596 = s.basis 1596 :=
    (a.frame _ (bankOut 1596 (Or.inl (by omega)))).trans (preq _ (by unfold Wire at *; omega))
  have v97 : v.basis 1597 = s.basis 1597 :=
    (a.frame _ (bankOut 1597 (Or.inl (by omega)))).trans (preq _ (by unfold Wire at *; omega))
  have select : v.basis 1613 = false := (a.frame _ (layout j h0 (by omega)).separate).trans selP
  have u13 : u.basis 1613 = (((!s.basis (Shadow7.e0P (start j) + 6)) ^^ s.basis 1596) ^^
      (s.basis (Shadow7.e0P (start j) + 6) && s.basis 1596)) := by
    have h := sg.2.1
    rw [select, v3, v96, v97, gate, Bool.false_xor] at h
    exact h
  have u3 : u.basis (Shadow7.e0P (start j) + 3) = true := by
    have h := sg.2.2.1
    rw [v3, v6] at h
    exact h.trans (by cases s.basis (Shadow7.e0P (start j) + 6) <;> rfl)
  have readTags (q : Wire) (hq : q ∈ tagsP) : u.basis q = hot key q := by
    have t := tags_range' q hq
    exact (old q (by unfold Wire at *; omega) (by unfold Wire at *; omega)
      (bankOut q (Or.inl (by unfold Wire at *; omega)))).trans (one q hq)
  have readShadow (i : Nat) (hi : i < 17) : u.basis (Shadow7.a0P (start j) + i) = X.testBit i :=
    (old _ (by unfold Wire at *; omega) (by unfold Wire at *; omega) (bankOut _ (Or.inr (Or.inl (by omega))))).trans (shadow i hi)
  have readTube (i : Nat) (hi : i < 17) : u.basis (Shadow7.bankW (start j) i) = (2^key.val*H).testBit i := by
    have b := Shadow7.bank_cases w1 w2 (i := i) (by omega)
    exact (unchanged _ (stable i (by omega)).symm (by unfold Wire at *; omega)).trans (bits i (by omega))
  have cross : u.basis (Shadow7.e0P (start j) + 6) = s.basis (Shadow7.e0P (start j) + 6) := old _ n6 n63 ext6
  have zero := (old 1614 (by decide) (by unfold Wire at *; omega) (fun i hi e => by
    have b := Shadow7.bank_cases w1 w2 hi; unfold Wire at *; omega)).trans scratch
  have exactDigit : X / 2^key.val = (u.basis (Shadow7.e0P (start j) + 6)).toNat + 2*(u.basis 1613).toNat := by
    rw [cross, u13]
    revert digit
    cases s.basis (Shadow7.e0P (start j) + 6) <;> cases s.basis 1596 <;> simp <;> omega
  have word := combine j h0 (by omega) key X H u tape readTags readShadow readTube exactDigit zero
  dsimp only
  have parts : GateMirror.forward (middleOps (start j)) =
      Instr.CX (Shadow7.e0P (start j) + 6) (Shadow7.e0P (start j) + 3) ::
        (early ++ (signBit ++ GateMirror.forward (Shadow7.leaveJoin (start j)))) := middle_parts (start j)
  rw [parts, run_cx_cons, run_append, run_take, run_append, run_take, show measurementCount signBit = 0 from rfl, List.drop_zero]
  have away13 : ∀ c ∈ cols j, (1613 : Wire) ≠ c.shadow ∧ (1613 : Wire) ≠ c.tube := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
    exact ⟨by dsimp only; unfold Wire at *; omega, by dsimp only; exact stable k (by omega)⟩
  refine ⟨word.1.trans (sg.1.trans a.phase), word.2.1, ?_, ?_, ?_⟩
  · intro i lo hi
    have outsideRows : ∀ c ∈ cols j, Shadow7.bankW (start j) i ≠ c.shadow ∧ Shadow7.bankW (start j) i ≠ c.tube := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hk
      have b := Shadow7.bank_cases w1 w2 hi
      refine ⟨by dsimp only; unfold Wire at *; omega, fun e => ?_⟩
      have := Shadow7.bank_inj w1 w2 hi (by omega) e; omega
    have b := Shadow7.bank_cases w1 w2 hi
    exact (word.2.2 _ outsideRows).trans ((unchanged _ (stable i hi).symm (by unfold Wire at *; omega)).trans (bits i hi))
  · intro q ne ext away
    by_cases e3 : q = Shadow7.e0P (start j) + 3
    · subst e3
      exact (word.2.2 _ away).trans (u3.trans farOn.symm)
    · exact (word.2.2 q away).trans (old q ne e3 ext)
  · refine (word.2.2 1613 away13).trans (u13.trans ?_)
    rw [farOn, gate, Bool.true_xor]

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

def longPairs (j : Fin 24) : List (Wire × Wire) := (List.range 17).map (fun i => (Shadow7.b0P (start j) + i, 1557 + i))
def fullA (j : Fin 24) : List Wire := (List.range 17).map (Shadow7.a0P (start j) + ·)
def fullM (j : Fin 24) : List Wire := (List.range 17).map (Shadow7.b0P (start j) + ·)
def fullC : List Wire := (List.range 16).map (1559 + ·)
def smallA (j : Fin 24) : List Wire := (List.range (Shadow7.lowsP (start j))).map (Shadow7.a0P (start j) + ·)
def smallM (j : Fin 24) : List Wire := (List.range (Shadow7.lowsP (start j))).map (Shadow7.b0P (start j) + ·)
def smallC (j : Fin 24) : List Wire := (List.range (Shadow7.lowsP (start j) - 1)).map (1559 + ·)
/-- dadon's `mask`: `[.X 1557, .CX (a0-1) 1557, .CCX (b0-1) 1557 1558]`. -/
def maskP (j : Fin 24) : Program := [.X 1557, .CX (Shadow7.a0P (start j) - 1) 1557, .CCX (Shadow7.b0P (start j) - 1) 1557 1558]

/-- `Shadow7.fix2P` = long latch ++ mask ++ companion erase (dadon's cuts 93/169/172/242). -/
theorem fix2_parts : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    GateMirror.forward (Shadow7.fix2P (start j) (Shadow7.sbP (start j))) =
      latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j) ++ (maskP j ++
        Companion.eraseM (fullA j) (fullM j) fullC 1556 1558) := by
  decide +kernel

theorem long_layout : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    (1556 :: (Shadow7.b0P (start j) - 1) :: PortalAnd.sites (longPairs j)).Nodup := by
  decide +kernel

theorem full_geometry : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    Companion.Geometry (fullA j) (fullM j) fullC 1556 1558 := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- dadon's `long_run`. -/
theorem long_run (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (m : List Bool)
    (clean : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    run (latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j)) m s =
      ⟨s.phase, writeBit s.basis 1556 (s.basis 1556 ^^ ((digits (Shadow7.b0P (start j) - 1) (longPairs j)).any s.basis))⟩ := by
  simpa only [active, Option.elim_none, Bool.true_and] using
    run_latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j) (long_layout j h0 (by omega)) (by simp) s m clean

/-- dadon's `erase_run`. -/
theorem erase_run (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (m : List Bool)
    (clean : ∀ q ∈ fullC, s.basis q = false)
    (input : (regValue (fullM j) s.basis + (s.basis 1558).toNat) % 2^(fullM j).length =
      copyValue (some 1556) s.basis (regValue (fullA j) s.basis)) :
    let e := Companion.eraseM (fullA j) (fullM j) fullC 1556 1558
    (run e m s).phase = s.phase ∧ (∀ q, q ∉ fullM j → (run e m s).basis q = s.basis q) ∧
      regValue (fullM j) (run e m s).basis = 0 :=
  Companion.clearM (fullA j) (fullM j) fullC 1556 1558 (full_geometry j h0 (by omega)) s m clean input

/-! The low-store restore (generic): `Shadow7.lowRest` = companion restore ++ release mask. -/

def releaseMaskP (j : Fin 24) : Program :=
  [.measureX 1558 [] [.CZ (Shadow7.b0P (start j) - 1) 1557], .CX (Shadow7.a0P (start j) - 1) 1557, .X 1557]

theorem forward_xsG' (xs : List Wire) : GateMirror.forward (xsG xs) = notRegister xs := by
  simp only [xsG, GateMirror.forward, notRegister, List.map_map]; rfl

theorem copy_map (c : Wire) (f g : Nat → Wire) : ∀ xs : List Nat,
    copyRegister (some c) (xs.map f) (xs.map g) = xs.map (fun i => Instr.CCX c (f i) (g i))
  | [] => rfl
  | x::xs => by simp only [List.map_cons, copyRegister, copyGate, copy_map c f g xs]; rfl

theorem lowRest_parts (j : Fin 24) :
    GateMirror.forward (Shadow7.lowRest (start j)) =
      Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558 ++ releaseMaskP j := by
  have hc : GateMirror.forward ((List.range (Shadow7.lowsP (start j))).map
      (fun i => Gate.make 1556 (Shadow7.a0P (start j) + i) (Shadow7.b0P (start j) + i))) =
      copyRegister (some 1556) (smallA j) (smallM j) := by
    rw [smallA, smallM, copy_map]; simp only [GateMirror.forward, List.map_map]; rfl
  simp only [Shadow7.lowRest, forward_app, forward_addG, forward_xsG', hc, Companion.restore, HighBankUnit.sub, mappedSub,
    smallM, smallC, List.append_assoc]
  rfl

theorem small_geometry : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    Companion.Geometry (smallA j) (smallM j) (smallC j) 1556 1558 := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- dadon's `restore_run`. -/
theorem restore_run (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (m : List Bool)
    (clean : ∀ q ∈ smallC j, s.basis q = false) (input : regValue (smallM j) s.basis = 0) :
    let r := Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558
    (run r m s).phase = s.phase ∧ (∀ q, q ∉ smallM j → (run r m s).basis q = s.basis q) ∧
      regValue (smallM j) (run r m s).basis =
        (copyValue (some 1556) s.basis (regValue (smallA j) s.basis) + 2^(smallM j).length - (s.basis 1558).toNat) %
          2^(smallM j).length :=
  Companion.write (smallA j) (smallM j) (smallC j) 1556 1558 (small_geometry j h0 (by omega)) s m clean input

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000

/-- dadon's `Leave{s}InputScan.pairs`: the 18 low columns `(a0-1+i, b0-1+i)`. -/
def scanPairs (j : Fin 24) : List (Wire × Wire) :=
  (List.range 18).map (fun i => (Shadow7.a0P (start j) - 1 + i, Shadow7.b0P (start j) - 1 + i))

theorem scan_emitted : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j))) =
      scan (Shadow7.a0P (start j) + 16) (Shadow7.b0P (start j) + 16) (start j + 30) (Shadow7.e0P (start j) + 5) (scanPairs j) := by
  decide +kernel

theorem scan_layout : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    ScanGeometry (Shadow7.a0P (start j) + 16) (Shadow7.b0P (start j) + 16) (start j + 30) (Shadow7.e0P (start j) + 5) (scanPairs j) := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- The scan reads the stock packet's ports of block `j` (above bit `sb`). -/
theorem scan_ports : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    (scanPairs j).map Prod.fst = ((IntegerPacket.ports (Shadow7.shape j) 15).a.drop (Shadow7.sbP (start j))).map (windowNet j) ∧
    (scanPairs j).map Prod.snd = ((IntegerPacket.ports (Shadow7.shape j) 15).b.drop (Shadow7.sbP (start j))).map (windowNet j) ∧
    Shadow7.a0P (start j) + 16 = windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).aSign ∧
    Shadow7.b0P (start j) + 16 = windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).bSign ∧
    start j + 30 = windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).previous ∧
    Shadow7.sbP (start j) ≤ (IntegerPacket.ports (Shadow7.shape j) 15).a.length ∧
    Shadow7.sbP (start j) ≤ (IntegerPacket.ports (Shadow7.shape j) 15).b.length := by
  decide +kernel

theorem scanPairs_getD (j : Fin 24) (i : Nat) (hi : i < 18) :
    ((scanPairs j).map Prod.fst).getD i 0 = Shadow7.a0P (start j) - 1 + i ∧
    ((scanPairs j).map Prod.snd).getD i 0 = Shadow7.b0P (start j) - 1 + i := by
  simp [scanPairs, List.getD_eq_getElem?_getD, hi]

/-- dadon's `Leave{s}InputScan.result`. -/
theorem inputScan_result (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (tape : List Bool) (u v : Nat)
    (G sg : Bool) (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) s.basis) (fresh : s.basis (Shadow7.e0P (start j) + 5) = false) :
    let t := run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) tape s
    let e := negative sg u
    t.phase = s.phase ∧ t.basis (Shadow7.e0P (start j) + 5) = e ∧
      (∀ i < 18, t.basis (Shadow7.a0P (start j) - 1 + i) = ((u+v)/2^(Shadow7.sbP (start j))).testBit i ∧
        t.basis (Shadow7.b0P (start j) - 1 + i) = ((u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i) ∧
      ∀ q, q ≠ Shadow7.e0P (start j) + 5 → q ∉ RailPair.sites (scanPairs j) → t.basis q = s.basis q := by
  obtain ⟨pl, pr, pa, pb, pg, la, lb⟩ := scan_ports j h0 (by omega)
  rw [scan_emitted j h0 (by omega)]
  generalize ht : run (scan (Shadow7.a0P (start j) + 16) (Shadow7.b0P (start j) + 16) (start j + 30) (Shadow7.e0P (start j) + 5) (scanPairs j)) tape s = t
  have out := scanRouted_shadow7 j (Shadow7.sbP (start j)) _ _ _ _ (scanPairs j) (scan_layout j h0 (by omega)) pl pr pa pb pg s tape u v G sg ready
    fresh la lb
  have frame := scan_run _ _ _ _ _ (scan_layout j h0 (by omega)) s tape fresh
  rw [ht] at out frame
  refine ⟨frame.1, out.1, ?_, frame.2.2.1⟩
  intro i hi
  have g := scanPairs_getD j i hi
  have len : ((scanPairs j).map Prod.fst).length = 18 ∧ ((scanPairs j).map Prod.snd).length = 18 := by simp [scanPairs]
  rw [← g.1, ← g.2, HighBankAdjust.bit_read ((scanPairs j).map Prod.fst) i t.basis (by rw [len.1]; exact hi),
    HighBankAdjust.bit_read ((scanPairs j).map Prod.snd) i t.basis (by rw [len.2]; exact hi), out.2.1, out.2.2]
  exact ⟨rfl, rfl⟩

/-- dadon's `Leave{s}CompanionInput.decode`. -/
theorem companionInput_decode (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (u v sign : Nat)
    (magFit : (u-sign)/2^(Shadow7.sbP (start j)) < 2^18)
    (bits : ∀ i < 18, s.basis (Shadow7.a0P (start j) - 1 + i) = ((u+v)/2^(Shadow7.sbP (start j))).testBit i ∧
      s.basis (Shadow7.b0P (start j) - 1 + i) = ((u-sign)/2^(Shadow7.sbP (start j))).testBit i) :
    ((digits (Shadow7.b0P (start j) - 1) (longPairs j)).any s.basis = decide (2^(Shadow7.sbP (start j)) ≤ u-sign)) ∧
      (s.basis (Shadow7.b0P (start j) - 1) && !s.basis (Shadow7.a0P (start j) - 1)).toNat = upperBorrow (2^(Shadow7.sbP (start j))) u v sign ∧
      regValue (fullA j) s.basis = ((u+v)/2^(Shadow7.sbP (start j) + 1)) % 2^17 ∧
      regValue (fullM j) s.basis = ((u-sign)/2^(Shadow7.sbP (start j) + 1)) % 2^17 := by
  have dlen : (digits (Shadow7.b0P (start j) - 1) (longPairs j)).length = 18 := by simp [digits, longPairs]
  have mag := EnterProof.value_of_bits (digits (Shadow7.b0P (start j) - 1) (longPairs j)) s.basis ((u-sign)/2^(Shadow7.sbP (start j))) (by
    intro i hi
    rw [dlen] at hi
    have geom : (digits (Shadow7.b0P (start j) - 1) (longPairs j)).getD i 0 = Shadow7.b0P (start j) - 1 + i := by
      rcases i with _ | i
      · simp [digits]
      · have : i < 17 := by omega
        simp [digits, longPairs, List.getD_eq_getElem?_getD, this]
        have r := Shadow7.rail_win (start_win75 j h0 (by omega)).1 (start_win75 j h0 (by omega)).2
        unfold Wire at *; omega
    rw [geom]; exact (bits i hi).2)
  rw [dlen, Nat.mod_eq_of_lt magFit] at mag
  have pos : 0 < 2^(Shadow7.sbP (start j)) := Nat.two_pow_pos _
  have half2 : ∀ x : Nat, x / 2^(Shadow7.sbP (start j) + 1) = (x / 2^(Shadow7.sbP (start j))) / 2^1 := by
    intro x; rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [any_positive, mag]
    simp only [Nat.div_pos_iff, pos, true_and]
  · have bs := bits 0 (by decide)
    simp only [Nat.add_zero] at bs
    rw [bs.1, bs.2]; exact borrowBit (2^(Shadow7.sbP (start j))) u v sign pos
  · apply EnterProof.value_of_bits (fullA j)
    intro i hi
    have hl : (fullA j).length = 17 := by simp [fullA]
    rw [hl] at hi
    have geom : (fullA j).getD i 0 = Shadow7.a0P (start j) - 1 + (i+1) := by
      simp [fullA, List.getD_eq_getElem?_getD, hi]
      have r := Shadow7.rail_win (start_win75 j h0 (by omega)).1 (start_win75 j h0 (by omega)).2
      unfold Wire at *; omega
    rw [geom, half2, Nat.testBit_div_two_pow, Nat.add_comm i 1]
    exact (bits (1+i) (show 1 + i < 18 by omega)).1
  · apply EnterProof.value_of_bits (fullM j)
    intro i hi
    have hl : (fullM j).length = 17 := by simp [fullM]
    rw [hl] at hi
    have geom : (fullM j).getD i 0 = Shadow7.b0P (start j) - 1 + (i+1) := by
      simp [fullM, List.getD_eq_getElem?_getD, hi]
      have r := Shadow7.rail_win (start_win75 j h0 (by omega)).1 (start_win75 j h0 (by omega)).2
      unfold Wire at *; omega
    rw [geom, half2, Nat.testBit_div_two_pow, Nat.add_comm i 1]
    exact (bits (1+i) (show 1 + i < 18 by omega)).2


end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step Shadow7.fix0P leaveFix1 Shadow7.fix2P latch Companion.eraseM

/-- dadon's `Leave{s}EraseActual.result`: the long latch, the mask and the companion erase (`Shadow7.fix2P`). -/
theorem eraseActual_result (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (tape : List Bool) (u v sign : Nat)
    (se : sign ≤ 1) (su : sign ≤ u) (small : min u v < 2^(Shadow7.sbP (start j))) (magFit : (u-sign)/2^(Shadow7.sbP (start j)) < 2^18)
    (bits : ∀ i < 18, s.basis (Shadow7.a0P (start j) - 1 + i) = ((u+v)/2^(Shadow7.sbP (start j))).testBit i ∧
      s.basis (Shadow7.b0P (start j) - 1 + i) = ((u-sign)/2^(Shadow7.sbP (start j))).testBit i)
    (clean : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temps : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    let t := run (GateMirror.forward (Shadow7.fix2P (start j) (Shadow7.sbP (start j)))) tape s
    t.phase = s.phase ∧ regValue (fullM j) t.basis = 0 ∧ t.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ u-sign) ∧
      (t.basis 1558).toNat = upperBorrow (2^(Shadow7.sbP (start j))) u v sign ∧
      ∀ q, q ∉ 1556::1557::1558::fullM j → t.basis q = s.basis q := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  have hA : (1556:Nat) ≠ Shadow7.a0P (start j) - 1 ∧ (1557:Nat) ≠ Shadow7.a0P (start j) - 1 ∧ (1558:Nat) ≠ Shadow7.a0P (start j) - 1 ∧
      (1556:Nat) ≠ Shadow7.b0P (start j) - 1 ∧ (1557:Nat) ≠ Shadow7.b0P (start j) - 1 ∧ (1558:Nat) ≠ Shadow7.b0P (start j) - 1 ∧
      Shadow7.a0P (start j) - 1 ≠ Shadow7.b0P (start j) - 1 := by omega
  have d := companionInput_decode j h0 (by omega) s u v sign magFit bits
  dsimp only
  rw [fix2_parts j h0 (by omega), run_append, run_take, run_append, run_take]
  generalize hl : run (latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j)) tape s = l
  generalize hs1 : tape.drop (measurementCount (latch true none 1556 (Shadow7.b0P (start j) - 1) (longPairs j))) = s1
  have flag : l = ⟨s.phase, writeBit s.basis 1556 (decide (2^(Shadow7.sbP (start j)) ≤ u-sign))⟩ := by
    rw [← hl, long_run j h0 (by omega) s tape temps, d.1, clean _ (by simp), Bool.false_xor]
  have base (q : Wire) (h : q ≠ 1556) : l.basis q = s.basis q := by rw [flag]; simp [writeBit, h]
  have hlA : l.basis (Shadow7.a0P (start j) - 1) = s.basis (Shadow7.a0P (start j) - 1) := base _ (fun e => hA.1 (by unfold Wire at *; omega))
  have hlB : l.basis (Shadow7.b0P (start j) - 1) = s.basis (Shadow7.b0P (start j) - 1) := base _ (fun e => hA.2.2.2.1 (by unfold Wire at *; omega))
  have nd : [Shadow7.a0P (start j) - 1, Shadow7.b0P (start j) - 1, (1557:Wire), 1558].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
      not_false_eq_true]; unfold Wire at *; omega
  have m57 : l.basis 1557 = false := (base _ (by decide)).trans (clean _ (by simp))
  have m58 : l.basis 1558 = false := (base _ (by decide)).trans (clean _ (by simp))
  have mo := mask_open (Shadow7.a0P (start j) - 1) (Shadow7.b0P (start j) - 1) 1557 1558 l s1 nd m57 m58
  rw [show (maskP j) = [.X 1557, .CX (Shadow7.a0P (start j) - 1) 1557, .CCX (Shadow7.b0P (start j) - 1) 1557 1558] from rfl, mo]
  generalize hw : (⟨l.phase, writeBit (writeBit l.basis 1557 (!l.basis (Shadow7.a0P (start j) - 1))) 1558
    (l.basis (Shadow7.b0P (start j) - 1) && !l.basis (Shadow7.a0P (start j) - 1))⟩ : State) = w
  have wphase : w.phase = s.phase := by rw [← hw, flag]
  have kept (q : Wire) (h : q ∉ [1556, 1557, 1558]) : w.basis q = s.basis q := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    rw [← hw]; simp only [writeBit, Function.update, h.2.1, h.2.2, dif_neg, not_false_eq_true]; exact base q h.1
  have isLong : w.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ u-sign) := by
    rw [← hw, flag]; simp [writeBit]
  have borrow : (w.basis 1558).toNat = upperBorrow (2^(Shadow7.sbP (start j))) u v sign := by
    rw [← hw]; simp only [writeBit, Function.update_self, hlA, hlB]; exact d.2.1
  have same (rs : List Wire) (ok : ∀ q ∈ rs, q ∉ [1556, 1557, 1558]) : regValue rs w.basis = regValue rs s.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h => kept _ (ok q h))
  have cOut : ∀ q ∈ fullC, q ∉ [1556, 1557, 1558] := by decide
  have cs : ∀ q ∈ fullC, w.basis q = false := by
    intro q h; rw [kept q (cOut q h)]; exact clean _ (by simp [h])
  have aOut : ∀ q ∈ fullA j, q ∉ [1556, 1557, 1558] := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; unfold Wire at *; omega
  have mOut : ∀ q ∈ fullM j, q ∉ [1556, 1557, 1558] := by
    intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; unfold Wire at *; omega
  have mlen : (fullM j).length = 17 := by simp [fullM]
  have condition : (regValue (fullM j) w.basis + (w.basis 1558).toNat) % 2^(fullM j).length =
      copyValue (some 1556) w.basis (regValue (fullA j) w.basis) := by
    rw [same (fullM j) mOut, same (fullA j) aOut, d.2.2.1, d.2.2.2, borrow, mlen]
    have twice : 2*2^(Shadow7.sbP (start j)) = 2^(Shadow7.sbP (start j) + 1) := by rw [Nat.pow_succ]; omega
    have calcValue := upper_clear (2^(Shadow7.sbP (start j))) u v sign (2^17) (Nat.two_pow_pos _) se su small
    rw [twice] at calcValue
    simpa only [copyValue, isLong, decide_eq_true_eq] using calcValue
  have e := erase_run j h0 (by omega) w (s1.drop (measurementCount (maskP j))) cs condition
  have extern (q : Wire) (notM : q ∉ fullM j) :
      (run (Companion.eraseM (fullA j) (fullM j) fullC 1556 1558) (s1.drop (measurementCount (maskP j))) w).basis q =
        w.basis q := e.2.1 q notM
  refine ⟨e.1.trans wphase, e.2.2, (extern _ (fun h => mOut _ h (by simp))).trans isLong, ?_, ?_⟩
  · have h158 := extern 1558 (fun h => (mOut 1558 h) (by simp))
    simp only [maskP] at h158
    rw [h158]
    exact borrow
  · intro q out
    simp only [List.mem_cons, not_or] at out
    exact (extern _ out.2.2.2).trans (kept _ (by simp [out.1, out.2.1, out.2.2.1]))

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000

/-- dadon's `Leave{s}Front.entry` (= `leave.take 242`). -/
def entryOps (s : Nat) : List Gate := Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s)
/-- dadon's `Leave{s}Close.history`: the block's 15 history letters `s+16 .. s+30`. -/
def history (j : Fin 24) : List Wire := (List.range 15).map (start j + 16 + ·)
/-- dadon's `Leave{s}Selector.ports`. -/
def ports (j : Fin 24) : Ports := ⟨start j + 16, Shadow7.a0P (start j), Shadow7.e0P (start j) + 6, Shadow7.e0P (start j) + 7⟩
/-- dadon's `Leave{s}FrontReady.watched`. -/
def watched (j : Fin 24) : List Wire := [Shadow7.e0P (start j) + 6, Shadow7.e0P (start j) + 7] ++ List.range' 1559 39

theorem fix1_forward (s h : Nat) : GateMirror.forward (leaveFix1 s h) = notRegister ((List.range 15).map (s + 16 + ·)) := rfl

/-- Nodup of the history letters, proved outside `entry_core` so `omega` does not see the walk context. -/
theorem history_nodup (j : Fin 24) : ((List.range 15).map (start j + 16 + ·)).Nodup :=
  List.Nodup.map (fun _ _ e => by omega) List.nodup_range

theorem scratchWire_band {q : Nat}
    (h : q ∈ (1556 :: 1557 :: 1558 :: fullC : List Nat)) : 1556 ≤ q ∧ q ≤ 1575 := by
  simp only [List.mem_cons, fullC, List.mem_map, List.mem_range] at h
  rcases h with rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · exact ⟨Nat.le_refl _, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by omega, by omega⟩

theorem longTemp_band (j : Fin 24) {p : Wire × Wire} (h : p ∈ longPairs j) :
    1557 ≤ p.2 ∧ p.2 ≤ 1574 := by
  simp only [longPairs, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨Nat.le_add_right 1557 i, ?_⟩
  exact le_trans (Nat.add_le_add_left (Nat.le_of_lt_succ hi) 1557) (by decide : 1557 + 16 ≤ 1574)

/-! Arithmetic that `entry_core` needs, proved here so `omega` never sees `Shadow7.onRails` or `Shadow7.rail_win`. -/

theorem sb_lo (s : Nat) (hs : s ≤ 405) : 46 ≤ Shadow7.sbP s := by
  simp only [Shadow7.sbP]
  omega

theorem sb_hi (s : Nat) (hs : 75 ≤ s) : Shadow7.sbP s ≤ 212 := by
  simp only [Shadow7.sbP]
  omega

theorem a0_le (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : Shadow7.a0P (start j) ≤ 633 := by
  have w := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  simp only [Shadow7.a0P, Shadow7.sbP]
  omega

theorem b0_ge (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : 833 ≤ Shadow7.b0P (start j) := by
  have w := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  simp only [Shadow7.b0P]
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  omega

theorem b0_le (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : Shadow7.b0P (start j) ≤ 999 := by
  have w := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  simp only [Shadow7.b0P]
  have sb := sb_hi (start j) (by omega)
  omega

theorem aCol_above (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i : Nat) :
    start j + 30 < Shadow7.a0P (start j) - 1 + i := by
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  simp only [Shadow7.a0P]
  omega

theorem bCol_above (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i : Nat) :
    start j + 30 < Shadow7.b0P (start j) - 1 + i := by
  have hb : 833 ≤ Shadow7.b0P (start j) := b0_ge j h0 (by omega)
  have one : 1 ≤ Shadow7.b0P (start j) := le_trans (by decide) hb
  have low : 832 ≤ Shadow7.b0P (start j) - 1 := by simpa using Nat.sub_le_sub_right hb 1
  have base : 832 ≤ Shadow7.b0P (start j) - 1 + i := le_trans low (Nat.le_add_right _ i)
  have top : start j + 30 ≤ 435 := by
    have := (start_win75 j h0 (by omega)).2
    omega
  exact Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : (435 : Nat) < 832) base)

theorem flag_ge (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : 1625 ≤ Shadow7.e0P (start j) + 5 := by
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  simp only [Shadow7.e0P]
  omega

theorem flag_above (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    start j + 30 < Shadow7.e0P (start j) + 5 := by
  have top : start j + 30 ≤ 435 := by
    have := (start_win75 j h0 (by omega)).2
    omega
  exact Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : (435 : Nat) < 1625) (flag_ge j h0 (by omega)))

theorem aCol_le (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i : Nat) (hi : i < 18) :
    Shadow7.a0P (start j) - 1 + i ≤ 650 := by
  have ile : i ≤ 17 := Nat.le_of_lt_succ hi
  have ha : Shadow7.a0P (start j) ≤ 633 := a0_le j h0 (by omega)
  have one : 1 ≤ Shadow7.a0P (start j) := by
    simp only [Shadow7.a0P]
    exact le_trans (by decide : (1 : Nat) ≤ 32) (Nat.le_add_left 32 (start j + Shadow7.sbP (start j)))
  calc Shadow7.a0P (start j) - 1 + i
      ≤ Shadow7.a0P (start j) - 1 + 17 := Nat.add_le_add_left ile _
    _ = Shadow7.a0P (start j) + 16 := by
        rw [show (17 : Nat) = 1 + 16 from rfl, ← Nat.add_assoc, Nat.sub_add_cancel one]
    _ ≤ 633 + 16 := Nat.add_le_add_right ha 16
    _ ≤ 650 := by decide

theorem aCol_out (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i : Nat) (hi : i < 18) :
    Shadow7.a0P (start j) - 1 + i ∉ (1556 :: 1557 :: 1558 :: fullM j : List Nat) := by
  intro h
  have up := aCol_le j h0 (by omega) i hi
  have hb := b0_ge j h0 (by omega)
  simp only [List.mem_cons, fullM, List.mem_map, List.mem_range] at h
  rcases h with h1 | h1 | h1 | ⟨k, hk, h1⟩
  · exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt up (by decide : 650 < 1556)))
  · exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt up (by decide : 650 < 1557)))
  · exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt up (by decide : 650 < 1558)))
  · have ge : 833 ≤ Shadow7.b0P (start j) + k := le_trans hb (Nat.le_add_right _ k)
    exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_le_of_lt up (Nat.lt_of_lt_of_le (by decide : 650 < 833) ge)))

theorem flag_out (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    Shadow7.e0P (start j) + 5 ∉ (1556 :: 1557 :: 1558 :: fullM j : List Nat) := by
  intro h
  have ge := flag_ge j h0 (by omega)
  have hb := b0_le j h0 (by omega)
  simp only [List.mem_cons, fullM, List.mem_map, List.mem_range] at h
  rcases h with h1 | h1 | h1 | ⟨k, hk, h1⟩
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1556 < 1625) ge))
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1557 < 1625) ge))
  · exact absurd h1 (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1558 < 1625) ge))
  · have top : Shadow7.b0P (start j) + k ≤ 1015 :=
      le_trans (Nat.add_le_add hb (Nat.le_of_lt_succ hk)) (by decide : 999 + 16 ≤ 1015)
    exact absurd h1 (Nat.ne_of_lt (Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : 1015 < 1625) ge)))

theorem scan_lt (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) {q : Nat}
    (hq : q ∈ RailPair.sites (scanPairs j)) : q < 1556 := by
  obtain ⟨p, hp, hq'⟩ := List.mem_flatMap.mp hq
  simp only [scanPairs, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
  have ha := a0_le j h0 (by omega)
  have hb := b0_le j h0 (by omega)
  rcases hq' with rfl | rfl <;> omega

theorem scratch_away (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (q : Nat)
    (hq : 1556 ≤ q ∧ q ≤ 1597) :
    (q < start j + 16 ∨ start j + 30 < q) ∧ q ≠ Shadow7.e0P (start j) + 5 ∧
      q ∉ RailPair.sites (scanPairs j) := by
  have w := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have sb := sb_lo (start j) (by simp only [StairPacket.start]; omega)
  refine ⟨Or.inr (by omega), ?_, ?_⟩
  · simp only [Shadow7.e0P]; omega
  · intro hm
    have := scan_lt j h0 (by omega) hm
    omega

theorem watched_lo (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (q : Nat)
    (hq : (q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) ∨ (1559 ≤ q ∧ q < 1559 + 39)) :
    1559 ≤ q := by
  rcases hq with (rfl | rfl) | ⟨lo, _⟩
  · exact le_trans (by decide : (1559 : Nat) ≤ 1625)
      (le_trans (flag_ge j h0 (by omega)) (Nat.add_le_add_left (by decide : (5 : Nat) ≤ 6) (Shadow7.e0P (start j))))
  · exact le_trans (by decide : (1559 : Nat) ≤ 1625)
      (le_trans (flag_ge j h0 (by omega)) (Nat.add_le_add_left (by decide : (5 : Nat) ≤ 7) (Shadow7.e0P (start j))))
  · exact lo

theorem watched_side (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (q : Nat)
    (hq : (q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) ∨ (1559 ≤ q ∧ q < 1559 + 39)) :
    q ∉ (1556 :: 1557 :: 1558 :: fullM j : List Nat) ∧
      (q < start j + 16 ∨ start j + 30 < q) ∧ q ≠ Shadow7.e0P (start j) + 5 ∧
      q ∉ RailPair.sites (scanPairs j) := by
  have lo := watched_lo j h0 (by omega) q hq
  have ge := flag_ge j h0 (by omega)
  have hb := b0_le j h0 (by omega)
  have top : start j + 30 ≤ 435 := by
    have := (start_win75 j h0 (by omega)).2
    omega
  refine ⟨?_, Or.inr (Nat.lt_of_le_of_lt top (Nat.lt_of_lt_of_le (by decide : (435 : Nat) < 1559) lo)), ?_, ?_⟩
  · intro h
    simp only [List.mem_cons, fullM, List.mem_map, List.mem_range] at h
    have neq {n : Nat} (hn : n < 1559) : q ≠ n := Nat.ne_of_gt (Nat.lt_of_lt_of_le hn lo)
    rcases h with h1 | h1 | h1 | ⟨k, hk, h1⟩
    · exact absurd h1 (neq (by decide))
    · exact absurd h1 (neq (by decide))
    · exact absurd h1 (neq (by decide))
    · have bound : Shadow7.b0P (start j) + k ≤ 1015 :=
        le_trans (Nat.add_le_add hb (Nat.le_of_lt_succ hk)) (by decide : 999 + 16 ≤ 1015)
      exact absurd h1 (neq (Nat.lt_of_le_of_lt bound (by decide : 1015 < 1559))).symm
  · rcases hq with (rfl | rfl) | ⟨_, hi⟩
    · exact Nat.ne_of_gt (Nat.lt_succ_self _)
    · exact Nat.ne_of_gt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (le_trans (by decide : 1559 + 39 ≤ 1625) ge))
  · intro hm
    exact absurd (scan_lt j h0 (by omega) hm) (Nat.not_lt_of_ge (le_trans (by decide : (1556 : Nat) ≤ 1559) lo))

theorem run_forward_append (a b : List Gate) (m : List Bool) (s : State) :
    run (GateMirror.forward (a ++ b)) m s =
      run (GateMirror.forward b) (m.drop (measurementCount (GateMirror.forward a)))
        (run (GateMirror.forward a) m s) := by
  rw [forward_app, run_append, run_take]

attribute [local irreducible] run SkywalkNat.step Shadow7.fix0P leaveFix1 Shadow7.fix2P latch Companion.eraseM

theorem flip_dest (s h : Nat) (q : Wire) (hq : q < s + 16 ∨ s + 30 < q) :
    q ∉ (GateMirror.forward (leaveFix1 s h)).map destination := by
  rw [fix1_forward]
  simp only [notRegister, List.map_map, List.mem_map, List.mem_range, not_exists, not_and]
  intro i hi e
  simp only [Function.comp, destination] at e
  unfold Wire at *; omega

/-- The entry run: scan, history flip, erase (the common core of dadon's `Front.result`/`FrontReady.frame`). -/
theorem entry_core (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    let a := SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)
    let e := negative sg a.u
    let out := run (GateMirror.forward (entryOps (start j))) m s
    out.phase = s.phase ∧ regValue (fullM j) out.basis = 0 ∧ out.basis (Shadow7.e0P (start j) + 5) = e ∧
      out.basis 1556 = decide (2^(Shadow7.sbP (start j)) ≤ a.u - e.toNat) ∧
      (out.basis 1558).toNat = upperBorrow (2^(Shadow7.sbP (start j))) a.u a.v e.toNat ∧
      (∀ i < 18, out.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i) ∧
      ∀ q, q ∉ 1556::1557::1558::fullM j → (q < start j + 16 ∨ start j + 30 < q) → q ≠ Shadow7.e0P (start j) + 5 →
        q ∉ RailPair.sites (scanPairs j) → out.basis q = s.basis q := by
  intro a e out
  have scanActual := inputScan_result j h0 (by omega) s m a.u a.v G sg ready fresh
  generalize hu : run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) m s = u at scanActual
  generalize ht : m.drop (measurementCount (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j))))) = t
  generalize hv : run (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j)))) t u = v
  have hist (q : Wire) (hq : q < start j + 16 ∨ start j + 30 < q) : v.basis q = u.basis q := by
    rw [← hv]; exact preserved _ _ _ _ (flip_dest _ _ q hq)
  have vphase : v.phase = u.phase := by
    rw [← hv, fix1_forward, notRegister_correct _ (history_nodup j)]
  have outputBits (i : Nat) (hi : i < 18) :
      v.basis (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i ∧
      v.basis (Shadow7.b0P (start j) - 1 + i) = ((a.u - e.toNat)/2^(Shadow7.sbP (start j))).testBit i := by
    rw [hist _ (Or.inr (aCol_above j h0 (by omega) i)), hist _ (Or.inr (bCol_above j h0 (by omega) i))]
    exact scanActual.2.2.1 i hi
  have same (q : Wire) (h1q : q < start j + 16 ∨ start j + 30 < q) (h2q : q ≠ Shadow7.e0P (start j) + 5)
      (h3q : q ∉ RailPair.sites (scanPairs j)) : v.basis q = s.basis q :=
    (hist _ h1q).trans (scanActual.2.2.2 _ h2q h3q)
  have away (q : Nat) (hq : 1556 ≤ q ∧ q ≤ 1597) := scratch_away j h0 (by omega) q hq
  have clean : ∀ q ∈ 1556::1557::1558::fullC, v.basis q = false := by
    intro q h
    have hr : 1556 ≤ q ∧ q ≤ 1597 := by
      have b := scratchWire_band h
      exact ⟨b.1, Nat.le_trans b.2 (by decide)⟩
    obtain ⟨a1, a2, a3⟩ := away q hr
    rw [same q a1 a2 a3]; exact scratch _ h
  have temps : ∀ p ∈ longPairs j, v.basis p.2 = false := by
    intro p h
    have hr : 1556 ≤ p.2 ∧ p.2 ≤ 1597 := by
      have b := longTemp_band j h
      exact ⟨Nat.le_trans (by decide) b.1, Nat.le_trans b.2 (by decide)⟩
    obtain ⟨a1, a2, a3⟩ := away p.2 hr
    rw [same _ a1 a2 a3]; exact temp _ h
  have cap := LeaveShadowRails.inputFit_shadow7 (Shadow7.sbP (start j)) z small.1 small.2
  have fit : (a.u - e.toNat)/2^(Shadow7.sbP (start j)) < 2^18 :=
    lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_trans (Nat.sub_le a.u e.toNat) (Nat.le_add_right a.u a.v))) cap.2
  have se : e.toNat ≤ 1 := by cases e <;> decide
  have su : e.toNat ≤ a.u := by
    by_cases h : 0 < a.u
    · cases e
      · exact Nat.zero_le _
      · exact Nat.succ_le_of_lt h
    · simp [e, negative, h]
  have done := eraseActual_result j h0 (by omega) v (t.drop (measurementCount (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j))))))
    a.u a.v e.toNat se su cap.1 fit outputBits clean temps
  have splitTape :
      m.drop (measurementCount (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++
          leaveFix1 (start j) (Shadow7.sbP (start j))))) =
        t.drop (measurementCount (GateMirror.forward (leaveFix1 (start j) (Shadow7.sbP (start j))))) := by
    rw [forward_app, measurementCount_append, ← List.drop_drop, ht]
  have hout : out = run (GateMirror.forward ((Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++
        leaveFix1 (start j) (Shadow7.sbP (start j))) ++ Shadow7.fix2P (start j) (Shadow7.sbP (start j)))) m s := rfl
  rw [hout, run_forward_append, run_forward_append, hu, ht, hv, splitTape]
  refine ⟨done.1.trans (vphase.trans scanActual.1), done.2.1, ?_, done.2.2.1, done.2.2.2.1, ?_, ?_⟩
  · exact (done.2.2.2.2 _ (flag_out j h0 (by omega))).trans
      ((hist _ (Or.inr (flag_above j h0 (by omega)))).trans scanActual.2.1)
  · intro i hi
    exact (done.2.2.2.2 _ (aCol_out j h0 (by omega) i hi)).trans (outputBits i hi).1
  · intro q n1 h1q h2q h3q
    exact (done.2.2.2.2 _ n1).trans (same q h1q h2q h3q)



/-- dadon's `Leave{s}FrontReady.frame`: the watched wires survive the entry. -/
theorem frontReady_frame (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (m : List Bool) (z : SkywalkNat.State)
    (G sg : Bool) (small : LeaveJ7.Small7 (Shadow7.sbP (start j)) z)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced (Shadow7.sbP (start j)) 15 z)).v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false)
    (temp : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    ∀ q ∈ watched j, (run (GateMirror.forward (entryOps (start j))) m s).basis q = s.basis q := by
  have core := entry_core j h0 (by omega) s m z G sg small ready fresh scratch temp
  intro q hq
  have hr : (q = Shadow7.e0P (start j) + 6 ∨ q = Shadow7.e0P (start j) + 7) ∨ (1559 ≤ q ∧ q < 1559 + 39) := by
    simpa only [watched, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] using hq
  have side := watched_side j h0 (by omega) q hr
  apply core.2.2.2.2.2.2 q side.1 side.2.1 side.2.2.1 side.2.2.2

/-! EntryAction (dadon's `Leave{s}EntryAction`). -/

/-- dadon's `oddRead`: the history letters, negated. -/
def oddRead (j : Fin 24) (v : BasisState) := (List.range 15).map (fun i => !v ((ports j).g + i))

/-- The scan and the erase never write the history letters (dadon's `historyGeom`). -/
theorem history_untouched : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 → ∀ i < 15,
    start j + 16 + i ∉ (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))).map destination ∧
    start j + 16 + i ∉ (GateMirror.forward (Shadow7.fix2P (start j) (Shadow7.sbP (start j)))).map destination := by
  decide +kernel

/-- dadon's `Leave{s}EntryAction.parity`. -/
theorem entry_parity (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (s : State) (m : List Bool) :
    parityBits (ports j) (run (GateMirror.forward (entryOps (start j))) m s).basis = oddRead j s.basis := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  unfold parityBits oddRead
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [entryOps, forward_app, forward_app, run_append, run_take, run_append, run_take]
  have mem : (ports j).g + i ∈ (List.range 15).map (start j + 16 + ·) := List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  -- fix2 does not touch the history letters
  have after : (ports j).g + i ∉ (GateMirror.forward (Shadow7.fix2P (start j) (Shadow7.sbP (start j)))).map destination :=
    (history_untouched j h0 (by omega) i hi).2
  have before : (ports j).g + i ∉ (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))).map destination :=
    (history_untouched j h0 (by omega) i hi).1
  rw [preserved _ _ _ _ after, fix1_forward, notRegister_correct _ (history_nodup j)]
  dsimp only
  rw [if_pos mem, preserved _ _ _ _ before]

/-- dadon's `Leave{s}EntryAction.upperBits`. -/
theorem upperBits (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (a : SkywalkNat.State) (v : BasisState)
    (bits : ∀ i < 18, v (Shadow7.a0P (start j) - 1 + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j))).testBit i) :
    ∀ i < 17, v (Shadow7.a0P (start j) + i) = ((a.u+a.v)/2^(Shadow7.sbP (start j) + 1)).testBit i := by
  have r := Shadow7.rail_win (start_win75 j h0 (by omega)).1 (start_win75 j h0 (by omega)).2
  intro i hi
  have div : (a.u+a.v)/2^(Shadow7.sbP (start j) + 1) = ((a.u+a.v)/2^(Shadow7.sbP (start j)))/2^1 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [div, Nat.testBit_div_two_pow, show Shadow7.a0P (start j) + i = Shadow7.a0P (start j) - 1 + (i+1) by omega, Nat.add_comm i 1]
  rw [Nat.add_comm 1 i]
  exact bits (i + 1) (Nat.add_lt_add_right hi 1)

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- dadon's `Leave{s}Hit.swaps`: the block's history cells in the `OB5.sig (s+14)` frame. -/
def swaps (j : Fin 24) (i : Nat) : Wire := OB5.sig (start j + 14) (start j + 1044 + i)

theorem swaps_range (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i : Nat) (hi : i < 15) :
    (swaps j i : Nat) ≤ 1300 ∨ (Shadow7.e0P (start j) + 10 ≤ swaps j i ∧ (swaps j i : Nat) ≤ 1812) := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have e := Shadow7.sig_hist (c := 1044 + i) (by omega) w2 (by omega) (by omega)
  unfold swaps; rw [show start j + 1044 + i = start j + (1044 + i) by omega]
  unfold Wire at *; omega

theorem swaps_inj (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i k : Nat) (hi : i < 15) (hk : k < 15)
    (e : swaps j i = swaps j k) : i = k := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have a := Shadow7.sig_hist (c := 1044 + i) (by omega) w2 (by omega) (by omega)
  have b := Shadow7.sig_hist (c := 1044 + k) w1 w2 (by omega) (by omega)
  unfold swaps at e; rw [show start j + 1044 + i = start j + (1044 + i) by omega,
    show start j + 1044 + k = start j + (1044 + k) by omega] at e
  unfold Wire at *; omega

/-- dadon's `Leave{s}Hit.sites`. -/
theorem hit_sites (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : Layout 1560 (swaps j) LeaveSelector.tags 0 15 := by
  obtain ⟨w1, w2⟩ := start_win75 j h0 (by omega)
  have w3 : start j ≤ 405 := by simp only [StairPacket.start]; omega
  have r := Shadow7.rail_win (by omega) w2
  refine ⟨fun i _ hi => ?_, fun i _ hi k lt hk => ?_⟩
  · have a := swaps_range j h0 (by omega) i (by omega)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
      not_false_eq_true, LeaveSelector.tags]
    unfold Wire at *; omega
  · have a := swaps_range j h0 (by omega) k (by omega)
    simp only [LeaveSelector.tags]
    unfold Wire at *; omega

theorem swaps_apart (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (i : Nat) (hi : i < 15) :
    swaps j i ≠ 1559 ∧ swaps j i ≠ 1560 := by
  have r := Shadow7.rail_win (start_win75 j h0 (by omega)).1 (start_win75 j h0 (by omega)).2
  have a := swaps_range j h0 (by omega) i hi
  unfold Wire at *; omega

/-! The selector words. -/

def farOps (j : Fin 24) : List Op := (1559 :: (List.range 5).map (1561 + ·)).map (fun a => .xor a (Shadow7.e0P (start j) + 7))
def zeroOps : List Op := [.xor 1559 1576, .xor 1561 1576]
def suffixOps (j : Fin 24) : List Op :=
  (List.range 12).map (fun i => .save (start j + 29 - i) (if i = 0 then start j + 30 else 1576 + i) (1577 + i))
def selectOps (j : Fin 24) : List Op :=
  [.save 1562 1588 1589, .save 1563 1586 1590, .save 1564 1584 1591, .save 1565 1582 1592, .save 1566 1580 1593,
   .save 1567 1578 1594, .save 1568 (start j + 30) 1595]
def crossOps (j : Fin 24) : List Op :=
  (List.range 16).map (fun i => .mix (tagsP.getD i 0) (Shadow7.a0P (start j) + i) (Shadow7.e0P (start j) + 6))
def signOps : List Op :=
  [.xor 1589 1596, .xor 1590 1596, .xor 1591 1596, .xor 1592 1596, .xor 1593 1596, .xor 1594 1596, .xor 1595 1596,
   .xor 1569 1596, .xor 1570 1596, .xor 1571 1596, .xor 1572 1596, .xor 1573 1596, .xor 1574 1596, .xor 1575 1596,
   .xor 1560 1596]
def productOps (j : Fin 24) : List Op := [.save (Shadow7.e0P (start j) + 6) 1596 1597]
/-- dadon's `Leave{s}Selector.prepare`. -/
def prepare (j : Fin 24) : List Op :=
  farOps j ++ zeroOps ++ suffixOps j ++ selectOps j ++ crossOps j ++ signOps ++ productOps j
/-- dadon's `Leave{s}Selector.retire`. -/
def retire (j : Fin 24) : List Op :=
  (productOps j).reverse ++ signOps ++ (selectOps j).reverse ++ (suffixOps j).reverse ++ zeroOps

end ECDSAAdd.Entrant.StairPacket.LeaveJ7

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen
open Arithmetic RecordedQuantum
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

abbrev SE := LeaveSelector.Expr
abbrev SOp := LeaveSelector.Op

def rE (σ : Nat → Nat) : SE → SE
  | .bit b => .bit b
  | .wire w => .wire (σ w)
  | .both a b => .both (rE σ a) (rE σ b)
  | .xor a b => .xor (rE σ a) (rE σ b)

def rOp (σ : Nat → Nat) : SOp → SOp
  | .xor a t => .xor (σ a) (σ t)
  | .mix a b t => .mix (σ a) (σ b) (σ t)
  | .save a b t => .save (σ a) (σ b) (σ t)

def EIn (P : Nat → Prop) : SE → Prop
  | .bit _ => True
  | .wire w => P w
  | .both a b => EIn P a ∧ EIn P b
  | .xor a b => EIn P a ∧ EIn P b

def OpIn (P : Nat → Prop) : SOp → Prop
  | .xor a t => P a ∧ P t
  | .mix a b t => P a ∧ P b ∧ P t
  | .save a b t => P a ∧ P b ∧ P t

def InjOn (P : Nat → Prop) (σ : Nat → Nat) : Prop := ∀ a b, P a → P b → σ a = σ b → a = b

/-- `g'` is `g` renamed on the domain. -/
def Rel (P : Nat → Prop) (σ : Nat → Nat) (g' g : LeaveSelector.Sym) : Prop := ∀ q, P q → g' (σ q) = rE σ (g q)
/-- every symbol of `g` on the domain mentions only domain wires. -/
def Good (P : Nat → Prop) (g : LeaveSelector.Sym) : Prop := ∀ q, P q → EIn P (g q)

theorem rE_inj {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) :
    ∀ a b : SE, EIn P a → EIn P b → rE σ a = rE σ b → a = b := by
  intro a
  induction a with
  | bit x =>
    intro b _ _ h
    cases b <;> simp_all [rE]
  | wire w =>
    intro b ha hb h
    cases b with
    | wire v =>
      simp only [rE, LeaveSelector.Expr.wire.injEq] at h
      exact congrArg _ (hσ w v ha hb h)
    | bit _ => simp [rE] at h
    | both _ _ => simp [rE] at h
    | xor _ _ => simp [rE] at h
  | both a1 a2 ih1 ih2 =>
    intro b ha hb h
    cases b with
    | both b1 b2 =>
      simp only [rE, LeaveSelector.Expr.both.injEq] at h
      rw [ih1 b1 ha.1 hb.1 h.1, ih2 b2 ha.2 hb.2 h.2]
    | bit _ => simp [rE] at h
    | wire _ => simp [rE] at h
    | xor _ _ => simp [rE] at h
  | xor a1 a2 ih1 ih2 =>
    intro b ha hb h
    cases b with
    | xor b1 b2 =>
      simp only [rE, LeaveSelector.Expr.xor.injEq] at h
      rw [ih1 b1 ha.1 hb.1 h.1, ih2 b2 ha.2 hb.2 h.2]
    | bit _ => simp [rE] at h
    | wire _ => simp [rE] at h
    | both _ _ => simp [rE] at h

theorem rE_conj (σ : Nat → Nat) (a b : SE) :
    rE σ (LeaveSelector.conj a b) = LeaveSelector.conj (rE σ a) (rE σ b) := by
  rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> rfl

theorem EIn_conj {P : Nat → Prop} (a b : SE) (ha : EIn P a) (hb : EIn P b) : EIn P (LeaveSelector.conj a b) := by
  rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

theorem rE_xor {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (a b : SE) (ha : EIn P a) (hb : EIn P b) :
    rE σ (LeaveSelector.xor a b) = LeaveSelector.xor (rE σ a) (rE σ b) := by
  unfold LeaveSelector.xor
  by_cases h : a = b
  · subst h; simp [rE]
  · have h' : rE σ a ≠ rE σ b := fun e => h (rE_inj hσ a b ha hb e)
    rw [if_neg h, if_neg h']
    rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> rfl

theorem EIn_xor {P : Nat → Prop} (a b : SE) (ha : EIn P a) (hb : EIn P b) : EIn P (LeaveSelector.xor a b) := by
  unfold LeaveSelector.xor
  split
  · exact trivial
  · rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

theorem dst_mem {P : Nat → Prop} (o : SOp) (ho : OpIn P o) : P o.dst := by
  cases o with
  | xor a t => exact ho.2
  | mix a b t => exact ho.2.2
  | save a b t => exact ho.2.2

theorem rOp_dst (σ : Nat → Nat) (o : SOp) : (rOp σ o).dst = σ o.dst := by cases o <;> rfl

theorem symbolic_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (o : SOp) (ho : OpIn P o)
    (g' g : LeaveSelector.Sym) (hg : Good P g) (hr : Rel P σ g' g) :
    Rel P σ (LeaveSelector.symbolic (rOp σ o) g') (LeaveSelector.symbolic o g) := by
  intro q hq
  cases o with
  | xor a t =>
    obtain ⟨ha, ht⟩ := ho
    show (if σ q = σ t then LeaveSelector.xor (g' (σ q)) (g' (σ a)) else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.xor (g q) (g a) else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e, hr q hq, hr a ha, rE_xor hσ _ _ (hg q hq) (hg a ha)]
    · rw [if_neg (fun h => e (hσ _ _ hq ht h)), if_neg e, hr q hq]
  | mix a b t =>
    obtain ⟨ha, hb, ht⟩ := ho
    show (if σ q = σ t then LeaveSelector.xor (g' (σ q)) (LeaveSelector.conj (g' (σ a)) (g' (σ b)))
        else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e, hr q hq, hr a ha, hr b hb,
        rE_xor hσ _ _ (hg q hq) (EIn_conj _ _ (hg a ha) (hg b hb)), rE_conj]
    · rw [if_neg (fun h => e (hσ _ _ hq ht h)), if_neg e, hr q hq]
  | save a b t =>
    obtain ⟨ha, hb, ht⟩ := ho
    show (if σ q = σ t then LeaveSelector.xor (g' (σ q)) (LeaveSelector.conj (g' (σ a)) (g' (σ b)))
        else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e, hr q hq, hr a ha, hr b hb,
        rE_xor hσ _ _ (hg q hq) (EIn_conj _ _ (hg a ha) (hg b hb)), rE_conj]
    · rw [if_neg (fun h => e (hσ _ _ hq ht h)), if_neg e, hr q hq]

theorem symbolic_good {P : Nat → Prop} (o : SOp) (ho : OpIn P o) (g : LeaveSelector.Sym) (hg : Good P g) :
    Good P (LeaveSelector.symbolic o g) := by
  intro q hq
  cases o with
  | xor a t =>
    show EIn P (if q = t then LeaveSelector.xor (g q) (g a) else g q)
    split
    · exact EIn_xor _ _ (hg q hq) (hg a ho.1)
    · exact hg q hq
  | mix a b t =>
    show EIn P (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    split
    · exact EIn_xor _ _ (hg q hq) (EIn_conj _ _ (hg a ho.1) (hg b ho.2.1))
    · exact hg q hq
  | save a b t =>
    show EIn P (if q = t then LeaveSelector.xor (g q) (LeaveSelector.conj (g a) (g b)) else g q)
    split
    · exact EIn_xor _ _ (hg q hq) (EIn_conj _ _ (hg a ho.1) (hg b ho.2.1))
    · exact hg q hq

theorem sim_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) :
    ∀ (os : List SOp), (∀ o ∈ os, OpIn P o) → ∀ (g' g : LeaveSelector.Sym), Good P g → Rel P σ g' g →
      Rel P σ (LeaveSelector.sim (os.map (rOp σ)) g') (LeaveSelector.sim os g) ∧ Good P (LeaveSelector.sim os g)
  | [], _, g', g, hg, hr => ⟨hr, hg⟩
  | o :: os, hos, g', g, hg, hr => by
    have h1 : OpIn P o := hos o (by simp)
    exact sim_rel hσ os (fun x hx => hos x (by simp [hx])) _ _ (symbolic_good o h1 g hg)
      (symbolic_rel hσ o h1 g' g hg hr)

/-! Exits: `erase`, `checkExit`, `validExit`, `erased`. -/

theorem erase_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (o : SOp) (ho : OpIn P o)
    (g' g : LeaveSelector.Sym) (hg : Good P g) (hr : Rel P σ g' g) :
    Rel P σ (LeaveSelector.erase (rOp σ o) g') (LeaveSelector.erase o g) := by
  cases o with
  | xor a t => exact symbolic_rel hσ (.xor a t) ho g' g hg hr
  | mix a b t => exact symbolic_rel hσ (.mix a b t) ho g' g hg hr
  | save a b t =>
    intro q hq
    show (if σ q = σ t then LeaveSelector.Expr.bit false else g' (σ q)) =
      rE σ (if q = t then LeaveSelector.Expr.bit false else g q)
    by_cases e : q = t
    · rw [if_pos (congrArg σ e), if_pos e]; rfl
    · rw [if_neg (fun h => e (hσ _ _ hq ho.2.2 h)), if_neg e, hr q hq]

theorem erase_good {P : Nat → Prop} (o : SOp) (ho : OpIn P o) (g : LeaveSelector.Sym) (hg : Good P g) :
    Good P (LeaveSelector.erase o g) := by
  cases o with
  | xor a t => exact symbolic_good (.xor a t) ho g hg
  | mix a b t => exact symbolic_good (.mix a b t) ho g hg
  | save a b t =>
    intro q hq
    show EIn P (if q = t then LeaveSelector.Expr.bit false else g q)
    split
    · exact trivial
    · exact hg q hq

theorem checkExit_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) (o : SOp) (ho : OpIn P o)
    (g' g : LeaveSelector.Sym) (hg : Good P g) (hr : Rel P σ g' g) :
    LeaveSelector.checkExit g' (rOp σ o) = LeaveSelector.checkExit g o := by
  cases o with
  | xor a t => rfl
  | mix a b t => rfl
  | save a b t =>
    obtain ⟨ha, hb, ht⟩ := ho
    show decide (σ t ≠ σ a ∧ σ t ≠ σ b ∧ g' (σ t) = LeaveSelector.conj (g' (σ a)) (g' (σ b))) =
      decide (t ≠ a ∧ t ≠ b ∧ g t = LeaveSelector.conj (g a) (g b))
    rw [hr t ht, hr a ha, hr b hb, ← rE_conj]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (congrArg σ e), fun e => h2 (congrArg σ e),
        rE_inj hσ _ _ (hg t ht) (EIn_conj _ _ (hg a ha) (hg b hb)) h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun e => h1 (hσ _ _ ht ha e), fun e => h2 (hσ _ _ ht hb e), by rw [h3]⟩

theorem exits_rel {P : Nat → Prop} {σ : Nat → Nat} (hσ : InjOn P σ) :
    ∀ (os : List SOp), (∀ o ∈ os, OpIn P o) → ∀ (g' g : LeaveSelector.Sym), Good P g → Rel P σ g' g →
      LeaveSelector.validExit (os.map (rOp σ)) g' = LeaveSelector.validExit os g ∧
      Rel P σ (LeaveSelector.erased (os.map (rOp σ)) g') (LeaveSelector.erased os g) ∧
      Good P (LeaveSelector.erased os g)
  | [], _, g', g, hg, hr => ⟨rfl, hr, hg⟩
  | o :: os, hos, g', g, hg, hr => by
    have h1 : OpIn P o := hos o (by simp)
    obtain ⟨v, r, gd⟩ := exits_rel hσ os (fun x hx => hos x (by simp [hx])) _ _ (erase_good o h1 g hg)
      (erase_rel hσ o h1 g' g hg hr)
    refine ⟨?_, r, gd⟩
    show (LeaveSelector.checkExit g' (rOp σ o) && LeaveSelector.validExit (os.map (rOp σ)) (LeaveSelector.erase (rOp σ o) g')) =
      (LeaveSelector.checkExit g o && LeaveSelector.validExit os (LeaveSelector.erase o g))
    rw [checkExit_rel hσ o h1 g' g hg hr, v]

theorem all_congr_mem {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons]
    rw [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen
open Arithmetic RecordedQuantum Partial GateMirror HighBankFirstHit
open ECDSAAdd.Entrant.StairPacket.LeaveJ
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

/-- block 10's selector wires. -/
def D (q : Nat) : Prop :=
  (1559 ≤ q ∧ q ≤ 1597) ∨ (241 ≤ q ∧ q ≤ 255) ∨ (393 ≤ q ∧ q ≤ 408) ∨ q = 1716 ∨ q = 1717
instance (q : Nat) : Decidable (D q) := by unfold D; infer_instance

/-- block 10 → block j. -/
def ren (j : Fin 24) (q : Nat) : Nat :=
  if 241 ≤ q ∧ q ≤ 255 then q - 225 + start j
  else if 393 ≤ q ∧ q ≤ 408 then q - 393 + Shadow7.a0P (start j)
  else if q = 1716 then Shadow7.e0P (start j) + 6
  else if q = 1717 then Shadow7.e0P (start j) + 7
  else q

theorem geo (j : Fin 24) : Shadow7.a0P (start j) = start j + ((498 - start j - (1 - (91 - start j) - start j / 391)) / 2) + 32 ∧
    Shadow7.e0P (start j) = 1574 + ((498 - start j - (1 - (91 - start j) - start j / 391)) / 2) ∧ start j = 75 + 15 * j.val := ⟨rfl, rfl, rfl⟩

theorem ren_inj (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : InjOn D (ren j) := by
  intro a b ha hb h
  obtain ⟨g1, g2, g3⟩ := geo j
  unfold ren at h
  unfold D at ha hb
  split_ifs at h <;> omega

theorem ren_const (j : Fin 24) (q : Nat) (h : 1559 ≤ q ∧ q ≤ 1597) : ren j q = q := by
  unfold ren; split_ifs <;> omega
theorem ren_g (j : Fin 24) (q : Nat) (h : 241 ≤ q ∧ q ≤ 255) : ren j q = q - 225 + start j := by
  unfold ren; rw [if_pos h]
theorem ren_u (j : Fin 24) (q : Nat) (h : 393 ≤ q ∧ q ≤ 408) : ren j q = q - 393 + Shadow7.a0P (start j) := by
  unfold ren; rw [if_neg (by omega), if_pos h]
theorem ren_cross (j : Fin 24) : ren j 1716 = Shadow7.e0P (start j) + 6 := by unfold ren; simp
theorem ren_near (j : Fin 24) : ren j 1717 = Shadow7.e0P (start j) + 7 := by unfold ren; simp

theorem s10 : start 10 = 225 := rfl
theorem a10 : Shadow7.a0P 225 = 393 := rfl
theorem e10 : Shadow7.e0P 225 = 1710 := rfl

/-! `prepare` and `retire` of block j are block 10's, renamed. -/

theorem farOps_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : (farOps 10).map (rOp (ren j)) = farOps j := by
  unfold farOps; rw [List.map_map]; apply List.map_congr_left; intro a ha
  simp only [List.mem_cons, List.mem_map, List.mem_range] at ha
  simp only [Function.comp_apply, rOp, s10, e10, LeaveSelector.Op.xor.injEq]
  refine ⟨?_, ren_near j⟩
  rcases ha with rfl | ⟨x, hx, rfl⟩ <;> exact ren_const j _ (by omega)

theorem zeroOps_ren (j : Fin 24) : zeroOps.map (rOp (ren j)) = zeroOps := by
  simp only [zeroOps, List.map_cons, List.map_nil, rOp, ren_const j 1559 (by omega), ren_const j 1561 (by omega),
    ren_const j 1576 (by omega)]

/-- constant wires are fixed. -/
def C (q : Nat) : Prop := 1559 ≤ q ∧ q ≤ 1597
instance (q : Nat) : Decidable (C q) := by unfold C; infer_instance
instance (P : Nat → Prop) [DecidablePred P] (o : SOp) : Decidable (OpIn P o) := by
  cases o <;> unfold OpIn <;> infer_instance

theorem map_const (j : Fin 24) (l : List SOp) (h : ∀ o ∈ l, OpIn C o) : l.map (rOp (ren j)) = l := by
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro o ho
  have hc := h o ho
  cases o with
  | xor a t => obtain ⟨ha, ht⟩ := hc; simp only [rOp, id, ren_const j a ha, ren_const j t ht]
  | mix a b t => obtain ⟨ha, hb, ht⟩ := hc; simp only [rOp, id, ren_const j a ha, ren_const j b hb, ren_const j t ht]
  | save a b t => obtain ⟨ha, hb, ht⟩ := hc; simp only [rOp, id, ren_const j a ha, ren_const j b hb, ren_const j t ht]

theorem signOps_ren (j : Fin 24) : signOps.map (rOp (ren j)) = signOps :=
  map_const j _ (by decide)

theorem suffixOps_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    (suffixOps 10).map (rOp (ren j)) = suffixOps j := by
  unfold suffixOps; rw [List.map_map]; apply List.map_congr_left; intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, rOp, s10, LeaveSelector.Op.save.injEq]
  refine ⟨?_, ?_, ren_const j _ (by omega)⟩
  · rw [ren_g j _ (by omega)]; unfold Wire; omega
  · by_cases h : i = 0
    · simp only [h, ↓reduceIte]; rw [ren_g j _ (by omega)]; unfold Wire; omega
    · simp only [h, ↓reduceIte]; exact ren_const j _ (by omega)

theorem selectOps_ren (j : Fin 24) : (selectOps 10).map (rOp (ren j)) = selectOps j := by
  simp only [selectOps, List.map_cons, List.map_nil, rOp, s10, List.cons.injEq, LeaveSelector.Op.save.injEq,
    and_true, ren_const j 1562 (by omega), ren_const j 1563 (by omega), ren_const j 1564 (by omega),
    ren_const j 1565 (by omega), ren_const j 1566 (by omega), ren_const j 1567 (by omega), ren_const j 1568 (by omega),
    ren_const j 1578 (by omega), ren_const j 1580 (by omega), ren_const j 1582 (by omega), ren_const j 1584 (by omega),
    ren_const j 1586 (by omega), ren_const j 1588 (by omega), ren_const j 1589 (by omega), ren_const j 1590 (by omega),
    ren_const j 1591 (by omega), ren_const j 1592 (by omega), ren_const j 1593 (by omega), ren_const j 1594 (by omega),
    ren_const j 1595 (by omega), true_and]
  rw [ren_g j _ (by omega)]; unfold Wire; omega

theorem tags_range : ∀ i < 16, 1559 ≤ tagsP.getD i 0 ∧ tagsP.getD i 0 ≤ 1597 := by decide

theorem crossOps_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    (crossOps 10).map (rOp (ren j)) = crossOps j := by
  unfold crossOps; rw [List.map_map]; apply List.map_congr_left; intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, rOp, s10, a10, e10, LeaveSelector.Op.mix.injEq]
  refine ⟨ren_const j _ (tags_range i hi), ?_, ren_cross j⟩
  rw [ren_u j _ (by omega)]; unfold Wire; omega

theorem productOps_ren (j : Fin 24) : (productOps 10).map (rOp (ren j)) = productOps j := by
  simp only [productOps, List.map_cons, List.map_nil, rOp, s10, e10, ren_cross j, ren_const j 1596 (by omega),
    ren_const j 1597 (by omega)]

theorem prepare_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    (prepare 10).map (rOp (ren j)) = prepare j := by
  simp only [prepare, List.map_append, farOps_ren j h0 (by omega), zeroOps_ren j, suffixOps_ren j h0 (by omega), selectOps_ren j,
    crossOps_ren j h0 (by omega), signOps_ren j, productOps_ren j]

theorem retire_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    (retire 10).map (rOp (ren j)) = retire j := by
  simp only [retire, List.map_append, List.map_reverse, zeroOps_ren j, suffixOps_ren j h0 (by omega), selectOps_ren j,
    signOps_ren j, productOps_ren j]

/-! Facts at block 10, by `decide` on small closed data. -/

theorem ops10_in : ∀ o ∈ prepare 10 ++ retire 10, OpIn D o := by decide
theorem prep10_in : ∀ o ∈ prepare 10, OpIn D o := fun o h => ops10_in o (List.mem_append_left _ h)
theorem retire10_in : ∀ o ∈ retire 10, OpIn D o := fun o h => ops10_in o (List.mem_append_right _ h)
theorem affected10_in : ∀ q ∈ LeaveSelector.affected (ports 10), D q := by decide

/-! Initial and final symbols. -/

theorem start_good (k : LeaveSelector.Mode) : Good D (LeaveSelector.start (ports 10) false k) := by
  intro q hq
  simp only [LeaveSelector.start, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> first | exact trivial | exact hq

theorem start_rel (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.start (ports j) false k) (LeaveSelector.start (ports 10) false k) := by
  obtain ⟨g1, g2, g3⟩ := geo j
  intro q hq
  unfold D at hq
  rcases hq with hc | hg | hu | rfl | rfl
  · rw [ren_const j q hc]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · rw [ren_g j q hg]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | (simp only [rE, ren_g j q hg]; done)
  · rw [ren_u j q hu]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | (simp only [rE, ren_u j q hu]; done)
  · rw [ren_cross j]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · rw [ren_near j]
    simp only [LeaveSelector.start, ports, s10, e10, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl

theorem key_le (k : LeaveSelector.Mode) : LeaveSelector.key k ≤ 15 := by
  unfold LeaveSelector.key; have := k.isLt; omega

theorem crossing_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : LeaveSelector.Mode) :
    rE (ren j) (LeaveSelector.crossing (ports 10) k) = LeaveSelector.crossing (ports j) k := by
  unfold LeaveSelector.crossing
  by_cases h : LeaveSelector.enabled k = true
  · simp only [h, ↓reduceIte, rE, ports, s10, a10]
    have := key_le k
    rw [ren_u j _ (by omega), LeaveSelector.Expr.wire.injEq]; unfold Wire; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem suffix_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) : ∀ (l : List Nat), (∀ x ∈ l, x < 15) →
    rE (ren j) (l.foldr (fun x rest => LeaveSelector.conj (.wire (start 10 + 16 + x)) rest) (.bit true)) =
      l.foldr (fun x rest => LeaveSelector.conj (.wire (start j + 16 + x)) rest) (.bit true)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.foldr_cons]
    rw [rE_conj, suffix_ren j h0 (by omega) xs (fun y hy => h y (by simp [hy]))]
    have hx := h x (by simp)
    congr 1
    show LeaveSelector.Expr.wire (ren j (start 10 + 16 + x)) = _
    rw [s10, ren_g j _ (by omega), LeaveSelector.Expr.wire.injEq]; unfold Wire; omega

theorem suffix_good : ∀ (l : List Nat), (∀ x ∈ l, x < 15) →
    EIn D (l.foldr (fun x rest => LeaveSelector.conj (.wire (start 10 + 16 + x)) rest) (.bit true))
  | [], _ => trivial
  | x :: xs, h => by
    simp only [List.foldr_cons]
    have hx := h x (by simp)
    refine EIn_conj _ _ ?_ (suffix_good xs (fun y hy => h y (by simp [hy])))
    show D (start 10 + 16 + x)
    rw [s10]; unfold D; omega

theorem signExpr_ren (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : LeaveSelector.Mode) :
    rE (ren j) (LeaveSelector.signExpr (ports 10) k) = LeaveSelector.signExpr (ports j) k := by
  unfold LeaveSelector.signExpr LeaveSelector.suffixExpr
  by_cases h : (LeaveSelector.right k && decide (0 < LeaveSelector.key k)) = true
  · simp only [h, ↓reduceIte, ports]
    exact suffix_ren j h0 (by omega) _ (fun x hx => List.mem_range.mp (List.mem_of_mem_drop hx))
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem signExpr_good (k : LeaveSelector.Mode) : EIn D (LeaveSelector.signExpr (ports 10) k) := by
  unfold LeaveSelector.signExpr LeaveSelector.suffixExpr
  split
  · simp only [ports]
    exact suffix_good _ (fun x hx => List.mem_range.mp (List.mem_of_mem_drop hx))
  · exact trivial

theorem cross_eq (j : Fin 24) : ren j (ports 10).crossing = (ports j).crossing := by
  simp only [ports, s10, e10]; exact ren_cross j
theorem near_eq (j : Fin 24) : ren j (ports 10).near = (ports j).near := by
  simp only [ports, s10, e10]; exact ren_near j

theorem cn_iff (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (q : Nat) (hq : D q) :
    (ren j q = (ports j).crossing ∨ ren j q = (ports j).near) ↔ (q = (ports 10).crossing ∨ q = (ports 10).near) := by
  have hσ := ren_inj j h0 (by omega)
  have dc : D (ports 10).crossing := by decide
  have dn : D (ports 10).near := by decide
  rw [← cross_eq j, ← near_eq j]
  constructor
  · rintro (e | e)
    · exact Or.inl (hσ _ _ hq dc e)
    · exact Or.inr (hσ _ _ hq dn e)
  · rintro (e | e)
    · exact Or.inl (congrArg _ e)
    · exact Or.inr (congrArg _ e)

theorem post_good (k : LeaveSelector.Mode) : Good D (LeaveSelector.post (ports 10) (prepare 10) false k) := by
  have hs := (sim_rel (ren_inj 10 (by decide) (by decide)) (prepare 10) prep10_in _ _ (start_good k)
    (start_rel 10 (by decide) (by decide) k)).2
  intro q hq
  simp only [LeaveSelector.post, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  split_ifs
  · exact hq
  · exact EIn_conj _ _ (show D (ports 10).crossing by decide) (signExpr_good k)
  · exact hs q hq

theorem post_rel (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.post (ports j) (prepare j) false k)
      (LeaveSelector.post (ports 10) (prepare 10) false k) := by
  have hσ := ren_inj j h0 (by omega)
  have hs := (sim_rel hσ (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 (by omega) k)).1
  intro q hq
  have i1 := cn_iff j h0 (by omega) q hq
  have i2 : ren j q = 1597 ↔ q = 1597 := by
    constructor
    · intro e; exact hσ _ _ hq (by decide) (e.trans (ren_const j 1597 (by omega)).symm)
    · intro e; rw [e]; exact ren_const j 1597 (by omega)
  rw [← prepare_ren j h0 (by omega)]
  simp only [LeaveSelector.post, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  by_cases c1 : q = (ports 10).crossing ∨ q = (ports 10).near
  · rw [if_pos (i1.mpr c1), if_pos c1]; rfl
  · rw [if_neg (fun h => c1 (i1.mp h)), if_neg c1]
    by_cases c2 : q = 1597
    · rw [if_pos (i2.mpr c2), if_pos c2, rE_conj, signExpr_ren j h0 (by omega) k]
      simp only [rE, cross_eq j]
    · rw [if_neg (fun h => c2 (i2.mp h)), if_neg c2]
      exact hs q hq

theorem restored_good (k : LeaveSelector.Mode) : Good D (LeaveSelector.restored (ports 10) false k) := by
  intro q hq
  simp only [LeaveSelector.restored, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  split_ifs
  · exact hq
  · exact start_good k q hq

theorem restored_rel (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.restored (ports j) false k) (LeaveSelector.restored (ports 10) false k) := by
  intro q hq
  have i1 := cn_iff j h0 (by omega) q hq
  simp only [LeaveSelector.restored, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  by_cases c1 : q = (ports 10).crossing ∨ q = (ports 10).near
  · rw [if_pos (i1.mpr c1), if_pos c1]; rfl
  · rw [if_neg (fun h => c1 (i1.mp h)), if_neg c1]
    exact start_rel j h0 (by omega) k q hq

theorem affected_ren (j : Fin 24) :
    (LeaveSelector.affected (ports 10)).map (ren j) = LeaveSelector.affected (ports j) := by
  simp only [LeaveSelector.affected, List.map_append, List.map_cons, List.map_nil, cross_eq j, near_eq j]
  congr 1

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen
open Arithmetic RecordedQuantum Partial GateMirror HighBankFirstHit LeaveSelector
open ECDSAAdd.Entrant.StairPacket.LeaveJ
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000



/-! The four symbolic certificates at block 10. -/

theorem cert10_control : ∀ k : Mode,
    reads (ports 10) (sim (prepare 10) (LeaveSelector.start (ports 10) false k)) = controls (ports 10) k := by
  decide +kernel
theorem cert10_clean : ∀ k : Mode, targetCert (ports 10) (prepare 10) (retire 10) false k = true := by
  decide +kernel
theorem cert10_tag : ∀ k : Mode, ∀ i : Fin 16,
    sim (prepare 10) (LeaveSelector.start (ports 10) false k) (tagsP.getD i 0) =
      .bit (enabled k && decide (i.val = key k)) := by
  decide +kernel
theorem cert10_foot : (prepare 10 ++ retire 10).all (fun o => decide (o.dst ∈ affected (ports 10))) = true := by
  decide +kernel

/-! Every block. -/

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.controlCert (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : Mode) :
    reads (ports j) (sim (prepare j) (LeaveSelector.start (ports j) false k)) = controls (ports j) k := by
  have hσ := ren_inj j h0 (by omega)
  have hs := (sim_rel hσ (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 (by omega) k)).1
  have c := cert10_control k
  rw [← prepare_ren j h0 (by omega)]
  simp only [reads, controls, List.cons.injEq] at c ⊢
  obtain ⟨c1, c2, c3, c4, -⟩ := c
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rw [← near_eq j, hs _ (by decide), c1]; rfl
  · rw [← cross_eq j, hs _ (by decide), c2, crossing_ren j h0 (by omega) k]
  · have e := hs 1596 (by decide)
    rw [ren_const j 1596 (by omega)] at e
    rw [e, c3, signExpr_ren j h0 (by omega) k]
  · have e := hs 1597 (by decide)
    rw [ren_const j 1597 (by omega)] at e
    rw [e, c4, rE_conj, crossing_ren j h0 (by omega) k, signExpr_ren j h0 (by omega) k]

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.cleanCert (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : Mode) :
    targetCert (ports j) (prepare j) (retire j) false k = true := by
  have hσ := ren_inj j h0 (by omega)
  obtain ⟨v, r, gd⟩ := exits_rel hσ (retire 10) retire10_in _ _ (post_good k) (post_rel j h0 (by omega) k)
  have c := cert10_clean k
  simp only [targetCert] at c ⊢
  rw [← retire_ren j h0 (by omega), v, ← affected_ren j, List.all_map]
  refine Eq.trans ?_ c
  refine congrArg (and _) ?_
  apply all_congr_mem
  intro q hq
  have hqD : D q := affected10_in q hq
  simp only [Function.comp_apply]
  rw [r q hqD, restored_rel j h0 (by omega) k q hqD]
  apply decide_eq_decide.mpr
  exact ⟨rE_inj hσ _ _ (gd q hqD) (restored_good k q hqD), fun e => by rw [e]⟩

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.tagCertificate (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : Mode) (i : Fin 16) :
    sim (prepare j) (LeaveSelector.start (ports j) false k) (tagsP.getD i 0) =
      .bit (enabled k && decide (i.val = key k)) := by
  have hs := (sim_rel (ren_inj j h0 (by omega)) (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 (by omega) k)).1
  have ht := tags_range i i.isLt
  have e := hs (tagsP.getD i 0) (Or.inl ht)
  rw [ren_const j _ ht] at e
  rw [← prepare_ren j h0 (by omega), e, cert10_tag k i]; rfl

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.foot_ok (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) :
    (prepare j ++ retire j).all (fun o => decide (o.dst ∈ affected (ports j))) = true := by
  have hσ := ren_inj j h0 (by omega)
  rw [← prepare_ren j h0 (by omega), ← retire_ren j h0 (by omega), ← List.map_append, List.all_map, ← cert10_foot]
  apply all_congr_mem
  intro o ho
  have hoD : OpIn D o := ops10_in o ho
  simp only [Function.comp_apply, rOp_dst, ← affected_ren j]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    obtain ⟨x, hx, e⟩ := List.mem_map.mp h
    rw [← hσ x o.dst (affected10_in x hx) (dst_mem o hoD) e]; exact hx
  · intro h; exact List.mem_map.mpr ⟨_, h, rfl⟩

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.witnessCert (j : Fin 24) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 22) (k : Mode) :
    witnesses (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) (swaps j) k (restored (ports j) false k) := by
  obtain ⟨g1, g2, g3⟩ := geo j
  refine ⟨?_, ?_, ?_, ?_, fun i => ⟨?_, ?_⟩⟩
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl
  · have hi := i.isLt
    simp only [restored, LeaveSelector.start, ports, LeaveSelector.tags, Bool.not_false, Bool.true_and,
      decide_eq_true_eq, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | simp only [Nat.add_sub_cancel_left]
  · have hr := swaps_range j h0 (by omega) i i.isLt
    simp only [restored, LeaveSelector.start, ports, Bool.not_false, Bool.true_and, decide_eq_true_eq,
      Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | (exfalso; (try unfold Wire at *); omega) | rfl

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ7.prefix_parts : ∀ j : Fin 24, 0 ≤ j.val → j.val ≤ 22 →
    GateMirror.forward (leaveFix3 (start j) (Shadow7.sbP (start j)) ++ leaveFix4 (start j) (Shadow7.sbP (start j)) ++
      leaveFix5 (start j) (Shadow7.sbP (start j))) =
      withHits (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) false (swaps j) ((prepare j).map Op.enter) := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.LeaveJ7.SelRen

end


/- Inlined from ShadowPortal90; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(320, 1558), (321, 1559), (322, 1560), (323, 1561), (324, 1562), (325, 1563), (326, 1564), (327, 1565), (328, 1566), (329, 1567), (330, 1568), (331, 1569), (332, 1570), (333, 1571), (334, 1572), (335, 1573), (336, 1574), (337, 1575), (338, 1576), (339, 1577), (340, 1578), (341, 1579), (342, 1580), (343, 1581), (344, 1582), (345, 1583), (346, 1584), (347, 1585), (348, 1586)]
def threshold := latch true none 1556 319 thresholdPairs
def orientationPairs : List (Wire×Wire) := [(1014, 1556), (1015, 1557), (1016, 1558), (1017, 1559), (1018, 1560), (1019, 1561), (1020, 1562), (1021, 1563), (1022, 1564), (1023, 1565), (1024, 1566), (1025, 1567), (1026, 1568), (1027, 1569), (1028, 1570), (1029, 1571), (1030, 1572), (1031, 1573), (1032, 1574), (1033, 1575), (1034, 1576), (1035, 1577), (1036, 1578), (1037, 1579), (1038, 1580), (1039, 1581), (1040, 1582), (1041, 1583), (1042, 1584), (1043, 1585)]
def orientation := latch false (some 1788) 1789 1013 orientationPairs
end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348]
def railB : List Wire := [1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043]
def carry : List Wire := [1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584]
def bulkA := railA.drop 2
def bulkB := railB.drop 2
def scan : Program := [.CX 348 1790,.CX 1043 1790] ++
  RailPair.exchange 90 (railA.zip railB) ++ signComplement 1790 railB
def flags : Program := threshold ++
  [.CX 1556 1788,.CX 1788 1556] ++ orientation
def erase : Program := [.X 319,.CCX 1014 319 1556] ++
  Companion.erase bulkA bulkB carry 1789 1556 ++
  [.measureX 1556 [] [.CZ 1014 319],.X 319]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1790 (railB.take 2) ++ RailPair.exchange 90 ((railA.take 2).zip (railB.take 2))
theorem emitted : (Shadow7.portalP 75)=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1789 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack2 319 1556 1788 1789 1013 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 319 1014 1556 (PortalBorrow.restore bulkA bulkB carry 1789 1556)
theorem emitted_back : (Shadow7.portalInvP 75)=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags2 319 1556 1788 1789 1013 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 319 1014 1556 (Companion.erase bulkA bulkB carry 1789 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
def activeScratch : List Wire := [1557,1556,1788,1789,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1790 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=(PortalAnd.digits 319 thresholdPairs).any s.basis
    let u:=f && (PortalAnd.digits 1013 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1788 f) 1789 u⟩ := by
  rw [flags_spec]
  apply PortalAnd.flags2_run
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem flags_return (s:State) (m n:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run backFlags n (run flags m s)=s := by
  rw [flags_spec]
  apply PortalAnd.flags2_undo
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
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
    run (Shadow7.portalInvP 75) tape (run (Shadow7.portalP 75) m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1788 ∧ q≠1789 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 75) (OB5.sig 74) 227 348 1043 90 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 348 1043 90 1790 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 348 1043 90 1790 pairs := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 2*2^227 ≤ u+v → min u v < 2^211) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^227) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^227) :
    let far:=decide (2*2^227≤u+v)
    let long:=decide (2*2^227≤u+v ∧ 2^211≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1788 far) 1789 long⟩ := by
  have act:=PortalValues.actual_flags_shadow7 318 319 thresholdPairs orientationPairs 1013 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^227) (2^211) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 2*2^227 ≤ u+v → min u v < 2^211) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^227) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^227)
    (mode:q.basis 1789=decide (2*2^227≤u+v ∧ 2^211≤u)) :
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
  · apply PortalValues.input_eq_shadow7 318 319 1013 1014 1789 bulkA bulkB q.basis (2^227) (2^211) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel


end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 2).zip (railB.take 2)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 90 1790 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 90 1790 1788 1789 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1788 ∧ w≠1789 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1788 ∧ w≠1789 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal75Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 75) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 74) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 74 q∈(W.compactSkywalkTickLayout base 75).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 211 15 z) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 75) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 74) raw
    PackedCut loPairs hiPairs 90 1790 1788 1789 (negative sg z.u)
      (decide (2*2^227≤z.u+z.v)) (decide (2*2^227≤z.u+z.v ∧ 2^211≤z.u))
      origin (run (Shadow7.portalP 75) m origin) := by
  let origin:=pullState (OB5.sig 74) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (2*2^227≤z.u+z.v)
  let long:=decide (2*2^227≤z.u+z.v ∧ 2^211≤z.u)
  have short : 2*2^227 ≤ z.u+z.v → min z.u z.v < 2^211 := by
    intro f
    exact small ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr f)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1790=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 74 1790)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1788 far) 1789 long⟩:=flags_values v t1 _ _ sg short vs left right
  have keep (q:Wire) (qf:q≠1788) (qu:q≠1789):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg short cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 348 1043 90 1790 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 348 ^^ origin.basis 1043)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 90 1790 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 90 1790 1788 1789 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
theorem physical_frame_for (d:Bool) (seed p:Nat) (hp0:0<p) (hx0:0<seed) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:seed<p) (hc:seed.Coprime p) (raw:State) (m:List Bool)
    (h:Rolling1588.Integer.Stage base d seed p 75 raw.basis)
    (route sg:Bool)
    (record:let z:=SkywalkNat.step^[75] (SkywalkNat.init seed p)
      SkywalkIntegerInput (W.compactSkywalkTickLayout base 75) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let z:=SkywalkNat.step^[75] (SkywalkNat.init seed p)
    let origin:=pullState (OB5.sig 74) raw
    PackedCut loPairs hiPairs 90 1790 1788 1789 (negative sg z.u)
      (decide (2*2^227≤z.u+z.v)) (decide (2*2^227≤z.u+z.v ∧ 2^211≤z.u))
      origin (run (Shadow7.portalP 75) m origin) := by
  have _input:=original_input d seed p 75 hp0 hx0 hpo hp hq hx hc (by decide) raw h
  exact physical_frame_local _ (Shadow7.Envelope.inputs seed p 75 (by omega) hp (by decide)).1 raw m route sg record
end ECDSAAdd.Entrant.StairPacket.Portal75Flag7

end


/- Inlined from ShadowPortal405; provenance retained from022799f6. -/
section

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def thresholdPairs : List (Wire×Wire) := [(493,1558),(494,1559),(495,1560),(496,1561),(497,1562),(498,1563),(499,1564),(500,1565),(501,1566),(502,1567),(503,1568),(504,1569),(505,1570),(506,1571),(507,1572),(508,1573),(509,1574),(510,1575),(511,1576),(512,1577),(513,1578),(514,1579),(515,1580),(516,1581),(517,1582),(518,1583),(519,1584),(520,1585),(521,1586),(522,1587),(523,1588),(524,1589),(525,1590),(526,1591),(527,1592),(528,1593)]
def threshold := latch true none 1556 492 thresholdPairs
def orientationPairs : List (Wire×Wire) := [(842,1556),(843,1557),(844,1558),(845,1559),(846,1560),(847,1561),(848,1562),(849,1563),(850,1564),(851,1565),(852,1566),(853,1567),(854,1568),(855,1569),(856,1570),(857,1571),(858,1572),(859,1573),(860,1574),(861,1575),(862,1576),(863,1577),(864,1578),(865,1579),(866,1580),(867,1581),(868,1582),(869,1583),(870,1584),(871,1585),(872,1586),(873,1587),(874,1588),(875,1589),(876,1590),(877,1591),(878,1592)]
def orientation := latch false (some 1616) 1617 841 orientationPairs
end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528]
def railB : List Wire := [841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878]
def carry : List Wire := [1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591]
def bulkA := railA.drop 2
def bulkB := railB.drop 2
def scan : Program := [.CX 528 1618,.CX 878 1618] ++
  RailPair.exchange 435 (railA.zip railB) ++ signComplement 1618 railB
def flags : Program := threshold ++
  [.CX 1556 1616,.CX 1616 1556] ++ orientation
def erase : Program := [.X 492,.CCX 842 492 1556] ++
  Companion.erase bulkA bulkB carry 1617 1556 ++
  [.measureX 1556 [] [.CZ 842 492],.X 492]
def store : Program := RailPair.transfer false (bulkA.zip bulkB) ++
  signComplement 1618 (railB.take 2) ++ RailPair.exchange 435 ((railA.take 2).zip (railB.take 2))
theorem emitted : (Shadow7.portalP 420)=scan++flags++erase++store := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem copy_good : Companion.Geometry bulkA bulkB carry 1617 1556 := by
  constructor <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
def backFlags := PortalAnd.flagsBack2 492 1556 1616 1617 841 thresholdPairs orientationPairs
def backErase := PortalBorrow.wrap 492 842 1556 (PortalBorrow.restore bulkA bulkB carry 1617 1556)
theorem emitted_back : (Shadow7.portalInvP 420)=store.reverse++backErase++backFlags++scan.reverse := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem flags_spec : flags=PortalAnd.flags2 492 1556 1616 1617 841 thresholdPairs orientationPairs := by rfl
theorem erase_spec : erase=PortalBorrow.wrap 492 842 1556 (Companion.erase bulkA bulkB carry 1617 1556) := by rfl
theorem scan_proper : ProperProgram scan := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem store_proper : ProperProgram store := PortalStatic.proper _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
def activeScratch : List Wire := [1557,1556,1616,1617,1556]++thresholdPairs.map Prod.snd++orientationPairs.map Prod.snd++carry
end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
theorem away_scan : ∀q∈activeScratch,q∉wires scan := PortalStatic.separated _ _ 1618 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem flags_do (s:State) (m:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    let f:=(PortalAnd.digits 492 thresholdPairs).any s.basis
    let u:=f && (PortalAnd.digits 841 orientationPairs).any s.basis
    run flags m s=⟨s.phase,writeBit (writeBit s.basis 1616 f) 1617 u⟩ := by
  rw [flags_spec]
  apply PortalAnd.flags2_run
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · exact h _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩))))
  · intro p hp; exact h _ (by simp only [activeScratch,List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))
theorem flags_return (s:State) (m n:List Bool) (h:∀q∈activeScratch,s.basis q=false) :
    run backFlags n (run flags m s)=s := by
  rw [flags_spec]
  apply PortalAnd.flags2_undo
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  · decide
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
    run (Shadow7.portalInvP 420) tape (run (Shadow7.portalP 420) m s)=s := by
  let v:=run scan m s
  have vh:∀q∈activeScratch,v.basis q=false:=fun q hp=>(run_preserves_outside _ _ _ _ (away_scan _ hp)).trans (h _ hp)
  have hc (m0:List Bool) : (run flags m0 v).basis 1556=false ∧ ∀q∈carry,(run flags m0 v).basis q=false := by
    rw [flags_do v m0 vh]
    have dis: ∀q∈carry,q≠1616 ∧ q≠1617 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
    constructor
    · simpa [writeBit] using vh 1556 (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
    · intro q hq; simp [writeBit,(dis _ hq).1,(dis _ hq).2,vh q (by simp [activeScratch,hq])]
  rw [emitted,emitted_back]
  simp only [run_append,run_take]
  rw [run_reverse_proper _ store_proper,erase_return _ _ _ (hc _),flags_return _ _ _ vh,run_reverse_proper _ scan_proper]

end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
def pairs := railA.zip railB
theorem source : Source (W.compactSkywalkTickLayout base 420) (OB5.sig 419) 55 528 878 435 pairs := by constructor <;> decide +kernel
theorem geom : RailPair.ScanGeometry 528 878 435 1618 pairs := by constructor <;> decide +kernel
theorem scan_shape : scan=RailPair.scan 528 878 435 1618 pairs := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

theorem flags_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 2*2^55 ≤ u+v → min u v < 2^39) (scratch:∀k∈activeScratch,q.basis k=false)
    (x:regValue railA q.basis=(u+v)/2^55) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^55) :
    let far:=decide (2*2^55≤u+v)
    let long:=decide (2*2^55≤u+v ∧ 2^39≤u)
    run flags m q=⟨q.phase,writeBit (writeBit q.basis 1616 far) 1617 long⟩ := by
  have act:=PortalValues.actual_flags_shadow7 491 492 thresholdPairs orientationPairs 841 railA railB
    (by decide +kernel) (by decide +kernel) q.basis (2^55) (2^39) u v (negative sg u).toNat
    (by decide) (by decide) small (by cases negative sg u <;> decide) x y
  rw [flags_do q m scratch]
  rw [act.2,act.1]

theorem erase_values (q:State) (m:List Bool) (u v:Nat) (sg:Bool)
    (small : 2*2^55 ≤ u+v → min u v < 2^39) (fresh:q.basis 1556=false ∧ ∀w∈carry,q.basis w=false)
    (x:regValue railA q.basis=(u+v)/2^55) (y:regValue railB q.basis=(u-(negative sg u).toNat)/2^55)
    (mode:q.basis 1617=decide (2*2^55≤u+v ∧ 2^39≤u)) :
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
  · apply PortalValues.input_eq_shadow7 491 492 841 842 1617 bulkA bulkB q.basis (2^55) (2^39) u v (negative sg u).toNat
    · decide
    · decide
    · exact small
    · cases negative sg u <;> decide
    · by_cases pos:0<u <;> cases sg <;> simp_all [negative]; omega
    · exact x
    · exact y
    · exact mode
    · decide +kernel


end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def loPairs := (railA.take 2).zip (railB.take 2)
def hiPairs := bulkA.zip bulkB
theorem pair_split : pairs=loPairs++hiPairs := by decide +kernel
theorem store_shape : store=RailPair.store 435 1618 loPairs hiPairs := by decide +kernel
theorem hi_y : hiPairs.map Prod.snd=bulkB := by decide +kernel
theorem noOverlap : ∀p∈hiPairs,p.1∉hiPairs.map Prod.snd := by decide +kernel
theorem bankLayout : CutLayout loPairs hiPairs 435 1618 1616 1617 := by constructor <;> first | constructor <;> decide +kernel | decide +kernel
theorem pot : ∀w∈railA++railB,w≠1616 ∧ w≠1617 := by decide +kernel
theorem carry_apart : ∀w∈carry,w≠1616 ∧ w≠1617 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

namespace ECDSAAdd.Entrant.StairPacket.Portal420Flag7
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

/-- The real physical portal applied to the genuine rolling secp trajectory leaves
all ordinary exterior bits alone, clears the redundant upper rail, parks the
positive upper word, and produces its actual arithmetic predicates. -/
theorem clean_for (raw:State) (z:SkywalkNat.State) (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 420) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    ∀q∈activeScratch,(pullState (OB5.sig 419) raw).basis q=false:=by
  have pool : ∀q∈activeScratch,OB5.sig 419 q∈(W.compactSkywalkTickLayout base 420).carry := by decide +kernel
  exact fun q hq=>(regValue_zero _ _).mp record.2.2.2.2.2 _ (pool _ hq)
theorem physical_frame_local (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 39 15 z) (raw:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 420) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis) :
    let origin:=pullState (OB5.sig 419) raw
    PackedCut loPairs hiPairs 435 1618 1616 1617 (negative sg z.u)
      (decide (2*2^55≤z.u+z.v)) (decide (2*2^55≤z.u+z.v ∧ 2^39≤z.u))
      origin (run (Shadow7.portalP 420) m origin) := by
  let origin:=pullState (OB5.sig 419) raw
  let v:=run scan m origin
  let t1:=m.drop (measurementCount scan)
  let w:=run flags t1 v
  let t2:=m.drop (measurementCount (scan++flags))
  let x:=run erase t2 w
  let t3:=m.drop (measurementCount (scan++flags++erase))
  let far:=decide (2*2^55≤z.u+z.v)
  let long:=decide (2*2^55≤z.u+z.v ∧ 2^39≤z.u)
  have short : 2*2^55 ≤ z.u+z.v → min z.u z.v < 2^39 := by
    intro f
    exact small ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr f)
  have clean:=clean_for raw z route sg record
  have vs:∀q∈activeScratch,v.basis q=false:=fun q mem=>(run_preserves_outside _ m origin q (away_scan _ mem)).trans (clean q mem)
  have fresh:origin.basis 1618=false:=by
    apply (regValue_zero _ _).mp record.2.2.2.2.2 (OB5.sig 419 1618)
    decide +kernel
  have first:=scan_input _ _ _ _ _ _ _ _ source geom raw m _ _ route sg record fresh
  rw [←scan_shape,show pairs.map Prod.fst=railA by decide +kernel,show pairs.map Prod.snd=railB by decide +kernel] at first
  obtain ⟨neg,_g,left,right⟩:=first
  have wf:w=⟨v.phase,writeBit (writeBit v.basis 1616 far) 1617 long⟩:=flags_values v t1 _ _ sg short vs left right
  have keep (q:Wire) (qf:q≠1616) (qu:q≠1617):w.basis q=v.basis q:=by rw [wf];simp [writeBit,qf,qu]
  have cv:w.basis 1556=false ∧ ∀q∈carry,w.basis q=false := by
    refine ⟨(keep _ (by decide) (by decide)).trans (vs _ (by decide +kernel)),?_⟩
    intro q hq
    exact (keep q (carry_apart _ hq).1 (carry_apart _ hq).2).trans (vs _ (by simp [activeScratch,hq]))
  have vals (r:List Wire) (sub:∀q∈r,q∈railA++railB):regValue r w.basis=regValue r v.basis:=
    regValue_congr _ _ _ (fun q h=>keep _ (pot _ (sub q h)).1 (pot _ (sub q h)).2)
  have xe:=erase_values w t2 _ _ sg short cv
    ((vals _ (fun _ h=>List.mem_append_left _ h)).trans left)
    ((vals _ (fun _ h=>List.mem_append_right _ h)).trans right) (by rw [wf];simp [long,writeBit])
  have scanned:=scan_run 528 878 435 1618 pairs geom origin m fresh
  rw [←scan_shape] at scanned
  have sign:(origin.basis 528 ^^ origin.basis 878)=negative sg z.u:=scanned.2.1.symm.trans neg
  rw [sign,pair_split] at scanned
  have clearHi:∀p∈hiPairs,x.basis p.2=false:=by
    intro p hp
    have hy:p.2∈hiPairs.map Prod.snd:=List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (regValue_zero _ _).mp xe.2.2 p.2 (hi_y ▸ hy)
  have stored:=store_run 435 1618 loPairs hiPairs bankLayout.store x t3 clearHi
  rw [←store_shape] at stored
  rw [emitted]
  simp only [run_append,run_take]
  apply packed loPairs hiPairs 435 1618 1616 1617 _ far long origin v w x (run store t3 x)
    bankLayout scanned.1 neg scanned.2.2.1 scanned.2.2.2 wf
  · rw [hi_y];exact xe
  · exact stored.1
  · exact stored.2.1
  · exact stored.2.2.1
  · exact stored.2.2.2
  · exact noOverlap
end ECDSAAdd.Entrant.StairPacket.Portal420Flag7

end


/- Inlined from ShadowPark405; provenance retained from022799f6. -/
section

section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary4207
open ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
def rawPortsList : List Wire := [426,1659,427,1658,428,1657,429,1656,430,1655,431,1654,432,1653,433,1652,434,1651,435,1650,879,880,881,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923]
def rawPorts (i:Fin 157) : Wire := rawPortsList.getD i 0
def codePortsList : List Wire := [426,1659,427,1658,428,429,1656,430,431,1654,432,1653,433,434,1651,435,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,1657,1655,1652,1650,879,880,881]
def codePorts (i:Fin 157) : Wire := codePortsList.getD i 0
def loadMapList : List Wire := [426,1659,427,1658,428,1657,429,1656,430,1655,431,1654,432,1653,433,1652,434,1651,435,1650,879,880,881,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921]
def loadMap (q:Wire) := loadMapList.getD q 0
def loadMoves : List (Wire×Wire) := (Partial.moveLoadPairs 420).map Prod.swap
def loadRouteList : List (Fin 157) := ArchiveJ.loadRouteList
def loadRoute (i:Fin 157) := loadRouteList.getD i 0
theorem load_program (d:Bool) : (Shadow7.exitLoadP 420) d=placed loadMap (op true d) ++ moves loadMoves := by cases d <;> rfl
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
    let t:=run ((Shadow7.exitLoadP 420) d) m s
    t.phase=s.phase ∧ Frame codePorts (endCols true d) row t ∧ ∀q,(∀i,rawPorts i≠q) → t.basis q=s.basis q := by
  rw [load_program]
  apply packet true d rawPorts codePorts loadMap loadMoves loadRoute load_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) load_route load_sort load_scope row hr s m ready
  intro q h
  have lim:q<155:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,load_map ⟨q,lim⟩⟩
def restoreMapList : List Wire := [426,1659,427,1658,428,429,1656,430,431,1654,432,1653,433,434,1651,435,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568,1569,1570,1571,1572,1573,1574,1575,1576,1577,1578,1579,1580,1581,1582,1583,1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608,1609,1610,1611,1612,1613,1614,1615,1616,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923]
def restoreMap (q:Wire) := restoreMapList.getD q 0
def restoreMoves : List (Wire×Wire) := (Partial.moveRestorePairs 420 879).map Prod.swap
def restoreRouteList : List (Fin 157) := ArchiveJ.restoreRouteList
def restoreRoute (i:Fin 157) := restoreRouteList.getD i 0
theorem restore_program (d:Bool) : (Shadow7.exitRestoreP 420) d=placed restoreMap (op false d) ++ moves restoreMoves := by cases d <;> rfl
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
    let t:=run ((Shadow7.exitRestoreP 420) d) m s
    t.phase=s.phase ∧ Frame rawPorts (endCols false d) row t ∧ ∀q,(∀i,codePorts i≠q) → t.basis q=s.basis q := by
  rw [restore_program]
  apply packet false d codePorts rawPorts restoreMap restoreMoves restoreRoute restore_unique _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)) restore_route restore_sort restore_scope row hr s m ready
  intro q h
  have lim:q<150:=by cases d <;> exact h
  exact ⟨⟨q,by omega⟩,rfl,restore_map ⟨q,lim⟩⟩
theorem code_from_raw : ∀i,∃j,rawPorts j=codePorts i := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem roundtrip (d:Bool) (row:Nat) (hr:row<63145) (s:State) (m n:List Bool)
    (ready:Frame rawPorts raw row s) :
    run ((Shadow7.exitRestoreP 420) d) n (run ((Shadow7.exitLoadP 420) d) m s)=s := by
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
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary4207
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary4207

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction
namespace ArchiveBoundary4207
def sourceIdx : Fin 24 := ⟨22,by decide⟩
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
end ArchiveBoundary4207
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack4207
def program (d:Bool) := renameProgram (OB5.sig 420) (Rolling1588.packAtTick d 410)
def reverse (d:Bool) := renameProgram (OB5.sig 420) (Rolling1588.unpackAtTick d 410)
end NativePack4207
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack4207
def history (q:Fin 10) := OB5.sig 420 (History5.historyMap base 405 q)
theorem histInj : Function.Injective history := by decide +kernel
theorem equals (d:Bool) : program d=Rolling1588.codeEncodeAt d history ∧ reverse d=Rolling1588.codeDecodeAt d history := by cases d <;> decide +kernel
theorem source_law (d:Bool) (s:State) (m:List Bool) (ok:MeasuredCodec5.legalAt history s.basis) :
    (run (program d) m s).phase=s.phase ∧ ∀t,run (reverse d) t (run (program d) m s)=s:=by
  rw [(equals d).1,(equals d).2]
  exact ⟨(Rolling1588.codeEncodeAt_correct d history histInj s m ok).1, fun t=>Rolling1588.codeRoundtripAt d history histInj s m t ok⟩
end NativePack4207
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed RailPair
namespace Portal420Flag7
set_option exponentiation.threshold 1024
theorem release (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 39 15 z) (raw packed:State) (m:List Bool)
    (route sg:Bool)
    (record:SkywalkIntegerInput (W.compactSkywalkTickLayout base 420) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 (PortalValues.negative sg z.u)
      (decide (2*2^55≤z.u+z.v)) (decide (2*2^55≤z.u+z.v ∧ 2^39≤z.u))
      (pullState (OB5.sig 419) raw) packed) :
    run (Shadow7.portalInvP 420) m packed=pullState (OB5.sig 419) raw := by
  rw [cut.unique (physical_frame_local z small raw [] route sg record)]
  exact portal_return _ [] m (clean_for raw z route sg record)

end Portal420Flag7
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed StairArchiveRaw StairArchiveTrace SkywalkRails ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run onRails
namespace NativePack4207
open ArchiveBoundary4207
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
end NativePack4207
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207
open Arithmetic ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
def src : List Wire := [1619,1620,1621]
def dst : List Wire := [879,880,881]
def pairs : List (Wire×Wire) := [(879,1619),(880,1620),(881,1621)]
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
    run (Shadow7.parkP 420) m s=stash s (eraseSites src s) := by
  rw [show (Shadow7.parkP 420)=moves pairs by rfl,moves_run _ (by decide) s m]
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

theorem park_undo (s:State) (m n:List Bool) : run (Shadow7.parkInvP 420) n (run (Shadow7.parkP 420) m s)=s := by
  rw [show (Shadow7.parkP 420)=moves pairs by rfl,show (Shadow7.parkInvP 420)=moves pairs.reverse by rfl,moves_run _ (by decide),moves_run _ (by decide)]
  apply congrArg₂ State.mk rfl
  funext q
  by_cases h:q∈src++dst
  · have inv:∀w∈src++dst,backMap pairs (backMap pairs.reverse w)=w:=by decide
    exact congrArg s.basis (inv _ h)
  · simp only [List.mem_append,src,dst,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    rcases h with ⟨⟨h1,h2,h3⟩,⟨h4,h5,h6⟩⟩
    simp [pairs,backMap,h1,h2,h3,h4,h5,h6]


end ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207
open Arithmetic MappedCompressed Portal420Flag7
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
def misses (i:Instr) := decide (879∉i.wires ∧ 880∉i.wires ∧ 881∉i.wires)
theorem misses_all (P:Program) (h:P.all misses=true) : ∀q∈dst,q∉wires P:=by
  intro q hq
  induction P with
  | nil=>simp [wires]
  | cons i P ih=>
    simp only [List.all_cons,Bool.and_eq_true] at h
    have hi:879∉i.wires ∧ 880∉i.wires ∧ 881∉i.wires:=of_decide_eq_true h.1
    simp only [wires,Finset.mem_union,not_or]
    exact ⟨by rcases List.mem_cons.mp hq with rfl|h'
              · exact hi.1
              · rcases List.mem_cons.mp h' with rfl|h''
                · exact hi.2.1
                · obtain rfl:=List.mem_singleton.mp h'';exact hi.2.2,ih h.2⟩
theorem avoid : ∀q∈dst,q∉wires (Shadow7.portalP 420):=misses_all _ (by decide +kernel)
theorem avoidInv : ∀q∈dst,q∉wires (Shadow7.portalInvP 420):=misses_all _ (by decide +kernel)

theorem parked_release (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 39 15 z) (raw s:State) (m n:List Bool)
    (route sg:Bool)
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 420) (SkywalkRails.encode route sg z.u z.v).a
      (SkywalkRails.encode route sg z.u z.v).b route raw.basis)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 (PortalValues.negative sg z.u)
      (decide (2*2^55≤z.u+z.v)) (decide (2*2^55≤z.u+z.v ∧ 2^39≤z.u))
      (pullState (OB5.sig 419) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) :
    let out:=run (Shadow7.portalInvP 420) n (run (Shadow7.parkP 420) m s)
    out=stash s (pullState (OB5.sig 419) raw) ∧ ∀a b,
      run (Shadow7.parkInvP 420) b (run (Shadow7.portalP 420) a out)=s := by
  have fw (a:List Bool):=cut.unique (physical_frame_local z small raw a route sg input)
  have endEq:run (Shadow7.portalInvP 420) n (run (Shadow7.parkP 420) m s)=stash s (pullState (OB5.sig 419) raw):=by
    rw [park _ _ empty,commutes _ avoidInv,release z small raw _ n route sg input cut]
  refine ⟨endEq,?_⟩
  intro a b
  rw [endEq,commutes _ avoid,←fw,←park s m empty,park_undo]

end ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
theorem released : ∀q∈dst,OB5.sig 419 q∈(W.compactSkywalkSignPoolB base 420).released := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207
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
    (stage:Rolling1588.Integer.Stage base d seed p 420 raw.basis) :
    ∀q∈dst,(pullState (OB5.sig 419) raw).basis q=false:=by
  have bounds:∀q∈dst,420+16<OB5.sig 419 q ∧ OB5.sig 419 q<1044:=by decide +kernel
  intro q hit
  exact dormant 420 d seed p raw (OB5.sig 419 q) stage
    (above_history 420 (by decide) d _ (bounds _ hit).1 (bounds _ hit).2) (released _ hit)

end ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207

end

end


/- Inlined from ShadowExit405; provenance retained from022799f6. -/
section

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def L:=W.compactSkywalkTickLayout base 420
def P:=TickRanges.tick base 420
def Q:=W.ReverseCarry.compactReceiverTick base 420
def physP:=renameProgram (OB5.sig 420) P
def physQ:=renameProgram (OB5.sig 420) Q
theorem supports : wires P⊆L.wires.toFinset ∧ wires Q⊆L.wires.toFinset :=
  ⟨(TickRanges.tick_support base 420 (by decide) base_pool_nodup).trans
    (W.repairedTick_support base 420 (by decide) base_pool_nodup),
    W.ReverseCarry.compactReceiverTick_support base 420 (by decide) base_pool_nodup⟩
theorem physical_free (R:Program) (sub:wires R⊆L.wires.toFinset) (q:Wire)
    (off:OB5.sig 420 q∉L.wires) : q∉wires (renameProgram (OB5.sig 420) R) := by
  rw [JointForward1588.wires_rename_image]
  intro h
  obtain ⟨w,mem,rfl⟩:=Finset.mem_image.mp h
  rw [OB5.sig_invol 420 (by decide)] at off
  exact off (List.mem_toFinset.mp (sub mem))
theorem spared : ∀q∈ParkEndpoint4207.dst,OB5.sig 420 q∉L.wires := by decide +kernel
theorem stashP : ∀q∈ParkEndpoint4207.dst,q∉wires physP := fun q hit=>physical_free P supports.1 q (spared q hit)
theorem stashQ : ∀q∈ParkEndpoint4207.dst,q∉wires physQ := fun q hit=>physical_free Q supports.2 q (spared q hit)
end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
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

end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
open Arithmetic Secp256k1 MappedCompressed
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def canonical:= W.compactSkywalkTick base 420
def Reads (a b:State) := ∀q∈L.wires.toFinset,a.basis q=b.basis q
theorem apply_old (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 420 original.basis) (a b:List Bool) :
    run P a actual=run canonical b actual:=by
  obtain ⟨w,sw,agree⟩:=Rolling1588.Integer.old_stage_local base d base_pool_nodup x p 420 (by decide) original stage
  have old:=TickRanges.tick_eq5 x hx0 hx 420 (by decide) w a sw
  have same:=Stack5.local_replace P (W.repairedTick base 420) L.wires.toFinset supports.1
    (W.repairedTick_support base 420 (by decide) base_pool_nodup) original w a a agree old
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have reference:=Rolling1588.Integer.repaired_eq base d base_pool_nodup x p 420 hp0 hx0 hpo hp gap hx cop (by decide) original a b stage
  exact Stack5.local_replace P canonical L.wires.toFinset supports.1
    (W.compactSkywalkTick_support base 420 (by decide) base_pool_nodup) actual original a b read (same.trans reference)

theorem compact_undo (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (actual original:State)
    (read:Reads actual original) (stage:Rolling1588.Integer.Stage base d x p 420 original.basis) (a b:List Bool) :
    run Q b (run canonical a actual)=actual:=by
  obtain ⟨ref,stock,agree⟩:=local_reference 420 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  exact undo_on_domain base base_pool_nodup x p 420 (by decide) hp0 hx0 hpo hp gap hx cop actual ref a b stock
    (fun q h=>(read _ (List.mem_toFinset.mpr h)).trans (agree _ (List.mem_toFinset.mpr h)))


end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] run
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem physical (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State)
    (read:Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 420 original.basis)
    (hist:raw.basis (base (1028+420))=false) (swapSlot:raw.basis (base (2053-420))=false)
    (m:List Bool) :
    let start:=ParkEndpoint4207.stash tags (pullState (OB5.sig 419) raw)
    let out:=run physP m start
    out=ParkEndpoint4207.stash tags (pullState (OB5.sig 420) (run canonical [] raw)) ∧
      ∀t,run physQ t out=start := by
  have pre:pullState (OB5.sig 419) raw=pullState (OB5.sig 420) raw:=
    OB5.pull_step 420 (by decide) raw hist (fun _=>swapSlot)
  have result:run physP m (ParkEndpoint4207.stash tags (pullState (OB5.sig 419) raw))=
      ParkEndpoint4207.stash tags (pullState (OB5.sig 420) (run canonical [] raw)):=by
    rw [ParkEndpoint4207.commutes _ stashP,pre,physP,OB5.run_rename _ (by decide),apply_old d x hx0 hx raw original read stage m []]
  refine ⟨result,?_⟩
  intro t
  rw [result,ParkEndpoint4207.commutes _ stashQ,physQ,OB5.run_rename _ (by decide),compact_undo d x hx0 hx raw original read stage,←pre]

end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveBoundary4207
theorem load_cover (d:Bool) : wires ((Shadow7.exitLoadP 420) d) ⊆ rawPortsList.toFinset := by
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
end ArchiveBoundary4207
end ECDSAAdd.Entrant.StairPacket

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
open Arithmetic MappedCompressed IntegerPacket
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
attribute [local irreducible] run
def readOnly (q:Wire) := OB5.sig 420 q∉L.wires ∨ q=435
instance (q:Wire) : Decidable (readOnly q) := by unfold readOnly;infer_instance
theorem observes (q:Wire) (h:readOnly q) (s:State) (m:List Bool) (prev:(run physP m s).basis 435=s.basis 435) : (run physP m s).basis q=s.basis q := by
  rcases h with h|rfl
  · exact run_preserves_outside _ _ _ _ (physical_free P supports.1 _ h)
  · exact prev
theorem oldPrefix : ∀i,readOnly (NativePack4207.history i) := by ((try unfold ECDSAAdd.Entrant.StairPacket.EndTick4207.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem oldBank : ∀i:Fin 23,readOnly (ArchiveBoundary4207.rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩) := by ((try unfold ECDSAAdd.Entrant.StairPacket.EndTick4207.readOnly); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
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
    (stage:Rolling1588.Integer.Stage base d x p 420 original.basis) :
    ∃ref:State,W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 420 ref.basis ∧
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 421 (run canonical [] ref).basis ∧
      Reads raw ref ∧ Reads (run canonical [] raw) (run canonical [] ref) := by
  obtain ⟨ref,hs,agree⟩:=local_reference 420 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have r:Reads raw ref:=fun q h=>(read q h).trans (agree q h)
  exact ⟨ref,hs,(W.compactSkywalkStageStep base base_pool_nodup x p 420 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).2,r,
    canonical_reads 420 (by decide) ref raw r []⟩

theorem pastG (i j:Nat) (hi:i≤512) (hj:j < i) (r:SkywalkRails.State) (b:BasisState)
    (hs:W.CompactSkywalkStage base r i b) :
    b (base j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 :=
  (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.1 j hj).1

theorem full_carry (i:Nat) (hi:i≤512) (r:SkywalkRails.State) (b:BasisState) (hs:W.CompactSkywalkStage base r i b) :
    ∀q∈wireBlock base 1540 257,b q=false :=
  (regValue_zero _ _).mp (((W.compactSkywalkStage_fields_iff base r i hi base_pool_nodup b).mp hs).2.2.2.2.2.1)

end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3000000
set_option maxRecDepth 15000
attribute [local irreducible] run
theorem carry_member (i:Nat) (q:Wire) (mem:q∈(W.compactSkywalkTickLayout base i).carry) :
    q∈(W.compactSkywalkTickLayout base i).wires.toFinset := List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires,mem])
theorem previous_member (i:Nat) : (W.compactSkywalkTickLayout base i).previous∈(W.compactSkywalkTickLayout base i).wires.toFinset :=
  List.mem_toFinset.mpr (by simp [SkywalkIntegerLayout.wires])
theorem scratch_lanes : ∀k:Fin 134,k.val+420<512 → 1556+k.val∈L.carry ∧ 1556+k.val∈wireBlock base 1540 257 := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
/-- window405: the scratch hosts `790+k` (the ports beyond the stock carry) are no wires of the end tick. -/
theorem host_lanes : ∀k:Fin 134,512≤k.val+420 → (790+k.val:Wire)∉L.wires.toFinset := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem after_cells (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 420 original.basis)
    (hosts:∀k:Fin 134,512≤k.val+420 → raw.basis (790+k.val)=false) :
    (run canonical [] raw).basis 435=raw.basis 435 ∧
    ∀k:Fin 134,(run canonical [] raw).basis (Shadow7.scratchX 420 k.val)=false := by
  obtain ⟨ref,old,next,pre,post⟩:=after_reference d x hx0 hx raw original read stage
  have prev:435∈L.wires.toFinset:=previous_member 420
  have a:=pastG 420 419 (by decide) (by decide) _ _ old
  have b:=pastG 421 419 (by decide) (by decide) _ _ next
  exact ⟨(post _ prev).trans (b.trans (a.symm.trans (pre _ prev).symm)),
    fun k=>by
      have _kl:=k.isLt
      by_cases hk:k.val+420<512
      · rw [show Shadow7.scratchX 420 k.val = 1556+k.val by
          unfold Shadow7.scratchX
          rw [if_neg (by decide : ¬ 420 ≤ 369), if_pos (by omega)]]
        exact (post _ (carry_member 420 _ (scratch_lanes k hk).1)).trans (full_carry 421 (by decide) _ _ next _ (scratch_lanes k hk).2)
      · rw [show Shadow7.scratchX 420 k.val = 790+k.val by
          unfold Shadow7.scratchX
          rw [if_neg (by decide : ¬ 420 ≤ 369), if_neg (by omega)]
          change 878+4+(1556+k.val+420-2068) = 790+k.val
          omega,
          run_preserves_outside canonical [] raw _ (fun used=>host_lanes k (by omega)
            ((W.compactSkywalkTick_support base 420 (by decide) base_pool_nodup) used))]
        exact hosts k (by omega)⟩

end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.EndTick4207
open Arithmetic MappedCompressed Secp256k1 ArchiveBoundary4207 ParkEndpoint4207
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
theorem no_phase (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 420 original.basis) : (run canonical [] raw).phase=raw.phase := by
  obtain ⟨ref,hs,ag⟩:=local_reference 420 (by decide) d x original stage
  have ⟨hp0,hpo,hp,cop⟩:=StackOB5.prime_facts x hx0 hx
  have gap:p+2^32≤2^256:=by norm_num [p]
  have step:=(W.compactSkywalkStageStep base base_pool_nodup x p 420 hp0 hx0 hpo hp gap hx cop (by decide) ref [] hs).1
  have inc:=(run_local_increment canonical raw ref [] (fun q h=>by
    have mem:=(W.compactSkywalkTick_support base 420 (by decide) base_pool_nodup) h
    exact (read q mem).trans (ag q mem))).1
  change (run canonical [] ref).phase=ref.phase at step
  rw [step,Bool.xor_self] at inc
  cases h:(run canonical [] raw).phase <;> cases k:raw.phase <;> simp_all

theorem scratch_table : ∀i:Fin 157,23≤ i.val →
    rawPorts i∉dst ∧ OB5.sig 420 (rawPorts i)=Shadow7.scratchX 420 (i.val-23) ∧ ∀v:Fin 10,rawPorts i≠NativePack4207.history v := by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem coordinate (s raw:State) : (stash s (pullState (OB5.sig 420) raw)).basis 435=raw.basis 435 ∧
    (stash s (pullState (OB5.sig 419) raw)).basis 435=raw.basis 435 := ⟨rfl,rfl⟩

theorem stash_slots (raw after tags:State) (phase:after.phase=raw.phase) (same:after.basis 435=raw.basis 435)
    (zero:∀k:Fin 134,after.basis (Shadow7.scratchX 420 k.val)=false) :
    let start:=stash tags (pullState (OB5.sig 419) raw)
    let out:=stash tags (pullState (OB5.sig 420) after)
    out.phase=start.phase ∧ out.basis 435=start.basis 435 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  refine ⟨phase,(coordinate _ _).1.trans (same.trans (coordinate _ _).2.symm),?_⟩
  intro i hi
  have ⟨off,eq,_⟩:=scratch_table i hi
  simp only [stash,if_neg off]
  exact (congrArg after.basis eq).trans (zero ⟨i.val-23,by have h:=i.isLt;omega⟩)

theorem exposed (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 420 original.basis)
    (hist:raw.basis (base (1028+420))=false) (swapSlot:raw.basis (base (2053-420))=false)
    (hosts:∀k:Fin 134,512≤k.val+420 → raw.basis (790+k.val)=false) (m:List Bool) :
    let start:=stash tags (pullState (OB5.sig 419) raw)
    let out:=run physP m start
    out.phase=start.phase ∧ out.basis 435=start.basis 435 ∧
      ∀i:Fin 157,23≤ i.val → out.basis (rawPorts i)=false := by
  have out:=(physical d x hx0 hx raw original tags read stage hist swapSlot m).1
  have bits:=after_cells d x hx0 hx raw original read stage hosts
  dsimp only
  rw [out]
  exact stash_slots raw (run canonical [] raw) tags (no_phase d x hx0 hx raw original read stage) bits.1 bits.2

end ECDSAAdd.Entrant.StairPacket.EndTick4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207
open Arithmetic MappedCompressed IntegerPacket RailPair Portal420Flag7 ArchiveBoundary4207
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def ordinary (q:Wire) : Prop := q∉src ∧ q∉dst ∧ q≠1618 ∧ q≠1616 ∧ q≠1617 ∧ q∉sites hiPairs
instance (q:Wire) : Decidable (ordinary q):=by unfold ordinary;infer_instance
theorem past_sites : ∀r:Fin 15,ordinary (windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).a0) ∧
    ordinary (windowNet sourceIdx (ports (Shadow7.shape sourceIdx) r).history) := by ((try unfold ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207.ordinary); open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
theorem earlier (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 n f u
    (pullState (OB5.sig 419) raw) (eraseSites src s)) (q:Wire) (clean:ordinary q) :
    (stash s (pullState (OB5.sig 419) raw)).basis q=s.basis q := by
  obtain ⟨hs,hd,hn,hf,hu,hh⟩:=clean
  have eq:=cut.unchanged _ hn hf hu hh
  simpa [stash,eraseSites,hs,hd] using eq.symm

theorem past_cells (raw s:State) (n f u:Bool) (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 n f u
    (pullState (OB5.sig 419) raw) (eraseSites src s)) :
    Shadow7.physicalCells sourceIdx (stash s (pullState (OB5.sig 419) raw))=Shadow7.physicalCells sourceIdx s := by
  rw [Shadow7.physicalCells_eq, Shadow7.physicalCells_eq]
  apply cells_congr _ _ _ _ _ _ (by decide)
  intro r
  exact Prod.ext (earlier _ _ _ _ _ cut _ (past_sites r).1) (earlier _ _ _ _ _ cut _ (past_sites r).2)
theorem tag_address (s other:State) :
    (stash s other).basis (rawPorts 20)=s.basis 1619 ∧
    (stash s other).basis (rawPorts 21)=s.basis 1620 ∧
    (stash s other).basis (rawPorts 22)=s.basis 1621:=⟨rfl,rfl,rfl⟩
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack4207
open Arithmetic IntegerPacket MappedCompressed SkywalkRails StairArchiveRaw StairArchiveTrace ArchiveBoundary4207 ArchivePortAction
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
    (odd:past.v%2=1) (small : Shadow7.SmallIfFar 46 15 past) (prior:PastFacts sourceIdx rawPorts 46 past g sign cross start)
    (keptFive:∀i,tick.basis (history i)=start.basis (history i))
    (bank:∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=start.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩))
    (scratch:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) :
    MeasuredCodec5.legalAt history tick.basis ∧ ∃row<63145,ArchivePortAction.Frame rawPorts raw row (run (program d) m tick) := by
  let cells:=Shadow7.physicalCells sourceIdx start
  let f:=decide (Shadow.far 46 15 past)
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
    (outside d _ (EndTick4207.scratch_table i hi).2.2 m tick).trans (scratch i hi)
  obtain ⟨row,limit,matchRow⟩:=interrupted_row_shadow7 46 past small odd g sign cross cells
    (((Shadow7.physicalCells_eq _ _).trans prior.records).trans (true_records_shadow7 _ _ small odd _ _).symm)
  exact ⟨legal_prefix _ _ legal keptFive,row,limit,starting_frame rawPorts out row data matchRow hw fresh⟩

end ECDSAAdd.Entrant.StairPacket.NativePack4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack4207
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary4207
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
def endSlice (d:Bool) := EndTick4207.physP ++ (program d ++ (Shadow7.exitLoadP 420) d)
def endUndo (d:Bool) := (Shadow7.exitRestoreP 420) d ++ (reverse d ++ EndTick4207.physQ)
structure Transition (inverse:Program) (s tick:State) : Prop where
  phase : tick.phase=s.phase
  keptFive : ∀i,tick.basis (history i)=s.basis (history i)
  keptBank : ∀i:Fin 23,tick.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)=s.basis (rawPorts ⟨i,Nat.lt_trans i.isLt (by decide : 23<157)⟩)
  scratch : ∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false
  undo : ∀n,run inverse n tick=s

abbrev TickStep:=Transition EndTick4207.physQ

theorem tick_intro (s tick:State) (ph:tick.phase=s.phase)
    (obs:∀q,EndTick4207.readOnly q → tick.basis q=s.basis q)
    (zero:∀i:Fin 157,23≤ i.val → tick.basis (rawPorts i)=false) (undo:∀m,run EndTick4207.physQ m tick=s) :
    TickStep s tick :=
  ⟨ph,fun i=>obs _ (EndTick4207.oldPrefix i),fun i=>obs _ (EndTick4207.oldBank i),zero,undo⟩

theorem observe_tick (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original tags:State) (read:EndTick4207.Reads raw original)
    (stage:Rolling1588.Integer.Stage base d x p 420 original.basis)
    (hist:raw.basis (base (1028+420))=false) (swapSlot:raw.basis (base (2053-420))=false)
    (hosts:∀k:Fin 134,512≤k.val+420 → raw.basis (790+k.val)=false) (m:List Bool) :
    let start:=ParkEndpoint4207.stash tags (pullState (OB5.sig 419) raw)
    TickStep start (run EndTick4207.physP m start) := by
  let s:=ParkEndpoint4207.stash tags (pullState (OB5.sig 419) raw)
  have h:=EndTick4207.exposed d x hx0 hx raw original tags read stage hist swapSlot hosts m
  have u:=(EndTick4207.physical d x hx0 hx raw original tags read stage hist swapSlot m).2
  exact tick_intro s (run EndTick4207.physP m s) h.1 (fun q hq=>EndTick4207.observes q hq s m h.2.1) h.2.2 u

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

end ECDSAAdd.Entrant.StairPacket.NativePack4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack4207
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary4207 ParkEndpoint4207 Portal420Flag7 StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def lastWindow (d:Bool) := (Shadow7.parkP 420) ++ ((Shadow7.portalInvP 420) ++ endSlice d)
def lastUnwind (d:Bool) := endUndo d ++ ((Shadow7.portalP 420) ++ (Shadow7.parkInvP 420))

theorem after_park (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 n f u (pullState (OB5.sig 419) raw) (eraseSites src s))
    (past:SkywalkNat.State) (G S cross:Bool)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode G S past.u past.v))
    (mode:s.basis 1619=decide (Shadow.far 46 15 past))
    (orientation:s.basis 1620=(decide (Shadow.far 46 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1621=(decide (Shadow.far 46 15 past) && cross)) :
    PastFacts sourceIdx rawPorts 46 past G S cross (stash s (pullState (OB5.sig 419) raw)) := by
  have cells:=past_cells raw s n f u cut
  have tag:=tag_address s (pullState (OB5.sig 419) raw)
  refine ⟨(Shadow7.physicalCells_eq _ _).symm.trans (cells.trans records),tag.1.trans mode,?_,tag.2.2.trans flipped⟩
  rw [←Shadow7.physicalCells_eq, cells];exact tag.2.1.trans orientation

end ECDSAAdd.Entrant.StairPacket.NativePack4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack4207
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary4207 ParkEndpoint4207 Portal420Flag7 StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
theorem empty_from_cut (raw s:State) (n f u:Bool)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 n f u (pullState (OB5.sig 419) raw) (eraseSites src s))
    (source:∀q∈dst,(pullState (OB5.sig 419) raw).basis q=false) : ∀q∈dst,s.basis q=false:=by
  have regular:∀q∈dst,q∉src ∧ q≠1618 ∧ q≠1616 ∧ q≠1617 ∧ q∉RailPair.sites hiPairs:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  intro q member
  obtain ⟨out,hn,hf,hu,hh⟩:=regular _ member
  have eq:=cut.unchanged q hn hf hu hh
  simpa [eraseSites,out] using eq.trans (source _ member)
end ECDSAAdd.Entrant.StairPacket.NativePack4207

end

section
namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
theorem terminal4207 (d:Bool) (x:Nat) (s:State) (dom:Domain 420 x p s) :
    ∃ref:State,Rolling1588.Integer.Stage base d x p 420 ref.basis ∧ EndTick4207.Reads s ref ∧
    s.basis (base (1028+420))=false ∧ s.basis (base (2053-420))=false ∧
    (∀q∈ParkEndpoint4207.dst,(pullState (OB5.sig 419) s).basis q=false) ∧
    ∀k:Fin 134,512≤k.val+420 → s.basis (790+k.val)=false := by
  obtain ⟨ref,stage,link⟩:=leaves_reference 420 x p (by decide) d s dom
  have bounds:∀q∈ParkEndpoint4207.dst,420+16<OB5.sig 419 q ∧ OB5.sig 419 q<1044:=by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)
  refine ⟨ref,stage,reads_now (by decide) link,future_history (Nat.le_refl _) (by decide) dom,?_,?_,?_⟩
  · exact (link.2 _ (outside_above (by decide))).trans ((Rolling1588.Integer.stage_zero d x 420 (by decide) _ stage).2 (by decide))
  · intro q hit
    exact (link.2 _ (outside_between (bounds _ hit).1 (bounds _ hit).2)).trans (ParkEndpoint4207.clear_dest d x p ref stage q hit)
  · intro k hk
    have _kl := k.isLt
    have released : ∀ i : Fin 134, 512 ≤ i.val+420 →
        790+i.val ∈ (W.compactSkywalkSignPoolB base 420).released := by decide +kernel
    exact (link.2 _ (outside_between (by omega) (by omega))).trans
      (ParkEndpoint4207.dormant 420 d x p ref _ stage
        (ParkEndpoint4207.above_history 420 (by decide) d _ (by omega) (by omega)) (released k hk))
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section
namespace ECDSAAdd.Entrant.StairPacket.NativePack4207
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary4207
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open ArchiveBoundary4207 ParkEndpoint4207 Portal420Flag7 Secp256k1 SkywalkRails StairArchiveTrace
theorem matched_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small : Shadow7.SmallIfFar 46 15 past)
    (prior:PastFacts sourceIdx rawPorts 46 past G S cross s) :
    let out:=run (p ++ (program d ++ (Shadow7.exitLoadP 420) d)) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run ((Shadow7.exitRestoreP 420) d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=row_truth sourceIdx rawPorts chronological row past G S s pre prior.records
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have enc:=source_law d tick e legal
  have act:=load_run d row limit pre f frame
  exact sequence_law p (program d) ((Shadow7.exitLoadP 420) d) ((Shadow7.exitRestoreP 420) d)
    (reverse d) q s m (fun out=>∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run ((Shadow7.exitLoadP 420) d) f pre) rfl act.1
    ⟨row,limit,truth,act.2.1⟩ (fun n=>roundtrip d row limit pre f n frame)

theorem matched_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick4207.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small : Shadow7.SmallIfFar 46 15 past)
    (prior:PastFacts sourceIdx rawPorts 46 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past G S row ∧ Frame codePorts (code d) row out) ∧
      ∀n,run (endUndo d) n out=s :=
  matched_generic EndTick4207.physP EndTick4207.physQ d s m step past G S cross odd small prior
theorem matched_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick4207.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 420 original.basis)
    (hist:raw.basis (base (1028+420))=false) (swapSlot:raw.basis (base (2053-420))=false)
    (hosts:∀k:Fin 134,512≤k.val+420 → raw.basis (790+k.val)=false)
    (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 39 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick4207.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 (PortalValues.negative S z.u)
      (decide (2*2^55≤z.u+z.v)) (decide (2*2^55≤z.u+z.v ∧ 2^39≤z.u)) (pullState (OB5.sig 419) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm : Shadow7.SmallIfFar 46 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1619=decide (Shadow.far 46 15 past))
    (angle:s.basis 1620=(decide (Shadow.far 46 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1621=(decide (Shadow.far 46 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount (Shadow7.parkP 420))
  let one:=run (Shadow7.portalInvP 420) n (run (Shadow7.parkP 420) m s)
  let tape:=n.drop (measurementCount (Shadow7.portalInvP 420))
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot hosts tape
  have eqOne:one=stash s (pullState (OB5.sig 419) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 46 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick4207.physP tape one):=by rw [eqOne];exact tick
  have body:=matched_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem matched_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 420 x p raw) (z:SkywalkNat.State) (small : Shadow7.SmallIfFar 39 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick4207.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 (PortalValues.negative S z.u)
      (decide (2*2^55≤z.u+z.v)) (decide (2*2^55≤z.u+z.v ∧ 2^39≤z.u)) (pullState (OB5.sig 419) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm : Shadow7.SmallIfFar 46 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1619=decide (Shadow.far 46 15 past))
    (angle:s.basis 1620=(decide (Shadow.far 46 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1621=(decide (Shadow.far 46 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (∃row<63145,RowTruth past pg ps row ∧ ArchivePortAction.Frame codePorts (code d) row out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty,hosts⟩:=WideReference.terminal4207 d x raw domain
  exact matched_last d x hx0 hx raw ref s m read stage history swapSlot hosts z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack4207

end

end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowParams7
open ECDSAAdd.Entrant.StairPacket.WindowFold

/-- The shadow window's blocks after the first: 1..22. Block 22 starts at tick 405; the exit is index 23 at tick 420. -/
def rest7 : List (Fin 24) := (List.finRange 24).filter (fun j => 1 ≤ j.val && j.val ≤ 22)

theorem rest7_eq : rest7 = [⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩,⟨10,by decide⟩,⟨11,by decide⟩,⟨12,by decide⟩,⟨13,by decide⟩,⟨14,by decide⟩,⟨15,by decide⟩,⟨16,by decide⟩,⟨17,by decide⟩,⟨18,by decide⟩,⟨19,by decide⟩,⟨20,by decide⟩,⟨21,by decide⟩,⟨22,by decide⟩] := by decide

theorem consec7 : Consec WindowParams.first rest7 := by
  rw [rest7_eq]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,trivial⟩

theorem last7 : (lastBlock WindowParams.first rest7).val = 22 := by rw [rest7_eq]; rfl

theorem lastBlock_405 : lastBlock WindowParams.first rest7 = ⟨22,by decide⟩ := by rw [rest7_eq]; rfl

theorem mem_rest22 {k : Fin 24} (h : k ∈ rest7) : 1 ≤ k.val ∧ k.val ≤ 22 := by
  simp only [rest7,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at h
  omega

end ECDSAAdd.Entrant.StairPacket.WindowParams7
end
