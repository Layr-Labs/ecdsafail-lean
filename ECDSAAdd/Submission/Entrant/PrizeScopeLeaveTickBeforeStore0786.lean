import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickEraseActual16ba
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFlagScratch8371
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickFullArithmetic39b7
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickLoaded78b0
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225MaskThrough
open Arithmetic Partial LeaveCompanion LeaveCompanion225 LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

def openPart:Program := (leave225.drop 169).take 3
def interior:Program := (leave225.drop 172).take 2146
def closePart:Program := (leave225.drop 2318).take 3
theorem openShape : openPart=[.X 1557,.CX 400 1557,.CCX 930 1557 1558] := by decide +kernel
theorem closeShape : closePart=[.measureX 1558 [] [.CZ 930 1557],.CX 400 1557,.X 1557] := by decide +kernel
theorem layout : ∀q∈[400,930,1557,1558],q∉interior.map destination := by decide +kernel

theorem released (s:State) (m₀ m₁ m₂:List Bool) (x:s.basis 1557=false) (y:s.basis 1558=false) :
    let u:=run openPart m₀ s
    let v:=run interior m₁ u
    run closePart m₂ v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let u:=run openPart m₀ s
  let v:=run interior m₁ u
  have fresh:u=⟨s.phase,writeBit (writeBit s.basis 1557 (!s.basis 400)) 1558 (s.basis 930 && !s.basis 400)⟩ := by
    change run openPart m₀ s=_
    rw [openShape]
    exact mask_open 400 930 1557 1558 s m₀ (by decide) x y
  have kept (q:Wire) (h:q∈[400,930,1557,1558]) : v.basis q=u.basis q :=
    preserved interior u m₁ q (layout q h)
  dsimp only
  rw [closeShape]
  apply mask_close _ _ _ _ _ _ (by decide)
  · change v.basis 1557= !v.basis 400
    rw [kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
  · change v.basis 1558=(v.basis 930 && v.basis 1557)
    rw [kept _ (by decide),kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
end ECDSAAdd.Entrant.StairPacket.Leave225MaskThrough


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Readout
open Arithmetic Partial LeaveCompanion225 Leave225OutputPorts LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev throughRestore := ((leave225.drop 2188).take 133)

theorem retained (s : State) (m : List Bool) (i : Fin 112) :
    (run throughRestore m s).basis (live i)=s.basis (live i) := by
  have layout : ∀j:Fin 112,live j∉throughRestore.map destination := by decide +kernel
  exact preserved _ _ _ _ (layout i)

theorem nextFlag (s : State) (m m' : List Bool) (Z : Nat) (bound : Z<2^112)
    (bits : ∀i<112,s.basis (live i)=Z.testBit i)
    (fresh : (run throughRestore m s).basis 1558=false)
    (clean : ∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (3 ≤ Z/2^7))⟩ := by
  let v:=run throughRestore m s
  have valid (i : Nat) (h : i<112) : v.basis (live i)=Z.testBit i :=
    (retained s m ⟨i,h⟩).trans (bits i h)
  have read := (outputRegisters v Z valid).2
  have fits : Z/2^7<2^105 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
  rw [Nat.mod_eq_of_lt fits] at read
  dsimp only
  rw [←read]
  exact pending_three v m' fresh clean

end ECDSAAdd.Entrant.StairPacket.Leave225Readout


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240MaskThrough
open Arithmetic Partial LeaveCompanion LeaveCompanion240 LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

def openPart:Program := (leave240.drop 169).take 3
def interior:Program := (leave240.drop 172).take 2287
def closePart:Program := (leave240.drop 2459).take 3
theorem openShape : openPart=[.X 1557,.CX 407 1557,.CCX 922 1557 1558] := by decide +kernel
theorem closeShape : closePart=[.measureX 1558 [] [.CZ 922 1557],.CX 407 1557,.X 1557] := by decide +kernel
theorem layout : ∀q∈[407,922,1557,1558],q∉interior.map destination := by decide +kernel

theorem released (s:State) (m₀ m₁ m₂:List Bool) (x:s.basis 1557=false) (y:s.basis 1558=false) :
    let u:=run openPart m₀ s
    let v:=run interior m₁ u
    run closePart m₂ v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let u:=run openPart m₀ s
  let v:=run interior m₁ u
  have fresh:u=⟨s.phase,writeBit (writeBit s.basis 1557 (!s.basis 407)) 1558 (s.basis 922 && !s.basis 407)⟩ := by
    change run openPart m₀ s=_
    rw [openShape]
    exact mask_open 407 922 1557 1558 s m₀ (by decide) x y
  have kept (q:Wire) (h:q∈[407,922,1557,1558]) : v.basis q=u.basis q :=
    preserved interior u m₁ q (layout q h)
  dsimp only
  rw [closeShape]
  apply mask_close _ _ _ _ _ _ (by decide)
  · change v.basis 1557= !v.basis 407
    rw [kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
  · change v.basis 1558=(v.basis 922 && v.basis 1557)
    rw [kept _ (by decide),kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
end ECDSAAdd.Entrant.StairPacket.Leave240MaskThrough


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Readout
open Arithmetic Partial LeaveCompanion240 Leave240OutputPorts LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev throughRestore := ((leave240.drop 2323).take 139)

theorem retained (s : State) (m : List Bool) (i : Fin 120) :
    (run throughRestore m s).basis (live i)=s.basis (live i) := by
  have layout : ∀j:Fin 120,live j∉throughRestore.map destination := by decide +kernel
  exact preserved _ _ _ _ (layout i)

theorem nextFlag (s : State) (m m' : List Bool) (Z : Nat) (bound : Z<2^120)
    (bits : ∀i<120,s.basis (live i)=Z.testBit i)
    (fresh : (run throughRestore m s).basis 1558=false)
    (clean : ∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (3 ≤ Z/2^8))⟩ := by
  let v:=run throughRestore m s
  have valid (i : Nat) (h : i<120) : v.basis (live i)=Z.testBit i :=
    (retained s m ⟨i,h⟩).trans (bits i h)
  have read := (outputRegisters v Z valid).2
  have fits : Z/2^8<2^112 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
  rw [Nat.mod_eq_of_lt fits] at read
  dsimp only
  rw [←read]
  exact pending_three v m' fresh clean

end ECDSAAdd.Entrant.StairPacket.Leave240Readout


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255MaskThrough
open Arithmetic Partial LeaveCompanion LeaveCompanion255 LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

def openPart:Program := (leave255.drop 169).take 3
def interior:Program := (leave255.drop 172).take 2401
def closePart:Program := (leave255.drop 2573).take 3
theorem openShape : openPart=[.X 1557,.CX 415 1557,.CCX 915 1557 1558] := by decide +kernel
theorem closeShape : closePart=[.measureX 1558 [] [.CZ 915 1557],.CX 415 1557,.X 1557] := by decide +kernel
theorem layout : ∀q∈[415,915,1557,1558],q∉interior.map destination := by decide +kernel

theorem released (s:State) (m₀ m₁ m₂:List Bool) (x:s.basis 1557=false) (y:s.basis 1558=false) :
    let u:=run openPart m₀ s
    let v:=run interior m₁ u
    run closePart m₂ v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let u:=run openPart m₀ s
  let v:=run interior m₁ u
  have fresh:u=⟨s.phase,writeBit (writeBit s.basis 1557 (!s.basis 415)) 1558 (s.basis 915 && !s.basis 415)⟩ := by
    change run openPart m₀ s=_
    rw [openShape]
    exact mask_open 415 915 1557 1558 s m₀ (by decide) x y
  have kept (q:Wire) (h:q∈[415,915,1557,1558]) : v.basis q=u.basis q :=
    preserved interior u m₁ q (layout q h)
  dsimp only
  rw [closeShape]
  apply mask_close _ _ _ _ _ _ (by decide)
  · change v.basis 1557= !v.basis 415
    rw [kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
  · change v.basis 1558=(v.basis 915 && v.basis 1557)
    rw [kept _ (by decide),kept _ (by decide),kept _ (by decide),fresh]
    simp [writeBit]
end ECDSAAdd.Entrant.StairPacket.Leave255MaskThrough


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Readout
open Arithmetic Partial LeaveCompanion255 Leave255OutputPorts LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev throughRestore := ((leave255.drop 2443).take 133)

theorem retained (s : State) (m : List Bool) (i : Fin 127) :
    (run throughRestore m s).basis (live i)=s.basis (live i) := by
  have layout : ∀j:Fin 127,live j∉throughRestore.map destination := by decide +kernel
  exact preserved _ _ _ _ (layout i)

theorem nextFlag (s : State) (m m' : List Bool) (Z : Nat) (bound : Z<2^127)
    (bits : ∀i<127,s.basis (live i)=Z.testBit i)
    (fresh : (run throughRestore m s).basis 1558=false)
    (clean : ∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (3 ≤ Z/2^7))⟩ := by
  let v:=run throughRestore m s
  have valid (i : Nat) (h : i<127) : v.basis (live i)=Z.testBit i :=
    (retained s m ⟨i,h⟩).trans (bits i h)
  have read := (outputRegisters v Z valid).2
  have fits : Z/2^7<2^120 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
  rw [Nat.mod_eq_of_lt fits] at read
  dsimp only
  rw [←read]
  exact pending_three v m' fresh clean

end ECDSAAdd.Entrant.StairPacket.Leave255Readout


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NextFlagTruth
open Arithmetic SkywalkNat LeaveCompanion LeaveCompanion225 Leave225OutputPorts
open Leave225Readout
attribute [local irreducible] SkywalkNat.step

def endpoint (z:SkywalkNat.State) := step^[15] z

theorem value (z:SkywalkNat.State) :
    Leave225TrueMiddle.F z/2^7=Shadow.high 136 15 (endpoint z) := by
  change ((endpoint z).u+(endpoint z).v)/2^145/2^7=_ 
  rw [Nat.div_div_eq_div_mul]
  rfl

theorem physical (z:SkywalkNat.State) (s:ECDSAAdd.State) (m m':List Bool)
    (bound:Leave225TrueMiddle.F z<2^112)
    (bits:∀i<112,s.basis (live i)=(Leave225TrueMiddle.F z).testBit i)
    (fresh:(run throughRestore m s).basis 1558=false)
    (clean:∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (Shadow.far 136 15 (endpoint z)))⟩ := by
  dsimp only
  rw [nextFlag s m m' _ bound bits fresh clean,value]
  rfl

theorem boundNear (a:SkywalkNat.State) (sign:Nat) (near:¬Shadow.far 136 15 a) :
    a.u-sign<(2*2^144)*2^smallM.length := by
  apply near_bound a.u a.v sign (Shadow.limb 136 15) _ (by decide) (by decide)
  simpa only [decide_eq_false_iff_not] using near

theorem orientation (a:SkywalkNat.State) (sign:Nat) (bit:sign≤1)
    (small:min a.u a.v<2^136) (far:Shadow.far 136 15 a) :
    (2^144≤a.u-sign) ↔ (2^136≤a.u) := by
  have lower:= (Nat.le_div_iff_mul_le (by decide : 0<Shadow.limb 136 15)).mp far
  change 3*2^152≤a.u+a.v at lower
  omega

end ECDSAAdd.Entrant.StairPacket.Leave225NextFlagTruth


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NextFlagTruth
open Arithmetic SkywalkNat LeaveCompanion LeaveCompanion240 Leave240OutputPorts
open Leave240Readout
attribute [local irreducible] SkywalkNat.step

def endpoint (z:SkywalkNat.State) := step^[15] z

theorem value (z:SkywalkNat.State) :
    Leave240TrueMiddle.F z/2^8=Shadow.high 129 15 (endpoint z) := by
  change ((endpoint z).u+(endpoint z).v)/2^137/2^8=_ 
  rw [Nat.div_div_eq_div_mul]
  rfl

theorem physical (z:SkywalkNat.State) (s:ECDSAAdd.State) (m m':List Bool)
    (bound:Leave240TrueMiddle.F z<2^120)
    (bits:∀i<120,s.basis (live i)=(Leave240TrueMiddle.F z).testBit i)
    (fresh:(run throughRestore m s).basis 1558=false)
    (clean:∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (Shadow.far 129 15 (endpoint z)))⟩ := by
  dsimp only
  rw [nextFlag s m m' _ bound bits fresh clean,value]
  rfl

theorem boundNear (a:SkywalkNat.State) (sign:Nat) (near:¬Shadow.far 129 15 a) :
    a.u-sign<(2*2^136)*2^smallM.length := by
  apply near_bound a.u a.v sign (Shadow.limb 129 15) _ (by decide) (by decide)
  simpa only [decide_eq_false_iff_not] using near

theorem orientation (a:SkywalkNat.State) (sign:Nat) (bit:sign≤1)
    (small:min a.u a.v<2^129) (far:Shadow.far 129 15 a) :
    (2^136≤a.u-sign) ↔ (2^129≤a.u) := by
  have lower:= (Nat.le_div_iff_mul_le (by decide : 0<Shadow.limb 129 15)).mp far
  change 3*2^145≤a.u+a.v at lower
  omega

end ECDSAAdd.Entrant.StairPacket.Leave240NextFlagTruth


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NextFlagTruth
open Arithmetic SkywalkNat LeaveCompanion LeaveCompanion255 Leave255OutputPorts
open Leave255Readout
attribute [local irreducible] SkywalkNat.step

def endpoint (z:SkywalkNat.State) := step^[15] z

theorem value (z:SkywalkNat.State) :
    Leave255TrueMiddle.F z/2^7=Shadow.high 121 15 (endpoint z) := by
  change ((endpoint z).u+(endpoint z).v)/2^130/2^7=_ 
  rw [Nat.div_div_eq_div_mul]
  rfl

theorem physical (z:SkywalkNat.State) (s:ECDSAAdd.State) (m m':List Bool)
    (bound:Leave255TrueMiddle.F z<2^127)
    (bits:∀i<127,s.basis (live i)=(Leave255TrueMiddle.F z).testBit i)
    (fresh:(run throughRestore m s).basis 1558=false)
    (clean:∀p∈pendingPairs,(run throughRestore m s).basis p.2=false) :
    let v:=run throughRestore m s
    run pending m' v=⟨v.phase,writeBit v.basis 1557 (v.basis 1557 ^^ decide (Shadow.far 121 15 (endpoint z)))⟩ := by
  dsimp only
  rw [nextFlag s m m' _ bound bits fresh clean,value]
  rfl

theorem boundNear (a:SkywalkNat.State) (sign:Nat) (near:¬Shadow.far 121 15 a) :
    a.u-sign<(2*2^129)*2^smallM.length := by
  apply near_bound a.u a.v sign (Shadow.limb 121 15) _ (by decide) (by decide)
  simpa only [decide_eq_false_iff_not] using near

theorem orientation (a:SkywalkNat.State) (sign:Nat) (bit:sign≤1)
    (small:min a.u a.v<2^121) (far:Shadow.far 121 15 a) :
    (2^129≤a.u-sign) ↔ (2^121≤a.u) := by
  have lower:= (Nat.le_div_iff_mul_le (by decide : 0<Shadow.limb 121 15)).mp far
  change 3*2^137≤a.u+a.v at lower
  omega

end ECDSAAdd.Entrant.StairPacket.Leave255NextFlagTruth


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225TailFlags
open Arithmetic Partial LeaveCompanion LeaveCompanion225 Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program:Program := (leave225.drop 2321).take 467
theorem shape : program=pending++(nextU++clearFlag) := by decide +kernel
attribute [local irreducible] run
theorem result (a:SkywalkNat.State) (s:State) (m:List Bool) (sign:Nat)
    (bit:sign≤1) (small:min a.u a.v<2^136) (x:s.basis 1557=false) (y:s.basis 1558=false)
    (scan:regValue scanned s.basis=Shadow.high 136 15 a)
    (clean:∀p∈pendingPairs,s.basis p.2=false) (scratch:∀p∈clearFlagPairs,s.basis p.2=false)
    (long:s.basis 1556=decide (2^144≤a.u-sign))
    (low:s.basis 930=decide (2^144≤(a.u-sign)%(2*2^144)))
    (upper:regValue smallM s.basis=((a.u-sign)/(2*2^144))%2^smallM.length) :
    let f:=decide (Shadow.far 136 15 a)
    let u:=f && decide (2^136≤a.u)
    run program m s=⟨s.phase,writeBit (writeBit (writeBit s.basis 1557 f) 1558 u) 1556 false⟩ := by
  let f:=decide (Shadow.far 136 15 a)
  let u:=f && decide (2^136≤a.u)
  let b₁:=writeBit s.basis 1557 f
  let b₂:=writeBit b₁ 1558 u
  have stage:run pending m s=⟨s.phase,b₁⟩ := by
    rw [pending_three s m y clean,x,Bool.false_xor]
    change (State.mk s.phase (writeBit s.basis 1557 (decide (3≤regValue scanned s.basis))))=_
    rw [scan]; rfl
  have side:(s.basis 1556 && f)=u := by
    by_cases far:Shadow.far 136 15 a
    · simp only [f,u,far,decide_true,Bool.and_true,Bool.true_and,long]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using Leave225NextFlagTruth.orientation a sign bit small far)
    · simp [f,u,far]
  have keep (q:Wire) (h:q≠1557 ∧ q≠1558) : b₂ q=s.basis q := by simp [b₂,b₁,writeBit,h.1,h.2]
  have turn (mm:List Bool):run nextU mm ⟨s.phase,b₁⟩=⟨s.phase,b₂⟩ := by
    rw [nextU_run _ _ (by simpa [b₁,writeBit] using y)]
    simp [b₂,b₁,writeBit,side]
  have last (mm:List Bool):run clearFlag mm ⟨s.phase,b₂⟩=⟨s.phase,writeBit b₂ 1556 false⟩ := by
    apply clearFlag_value _ _ (2^144) (a.u-sign) (by decide)
    · intro p hp
      exact (keep p.2 ((by decide +kernel : ∀p∈clearFlagPairs,p.2≠1557 ∧ p.2≠1558) p hp)).trans (scratch p hp)
    · intro h
      apply Leave225NextFlagTruth.boundNear a sign
      simpa [b₂,b₁,writeBit,f] using h
    · exact (keep _ (by decide)).trans long
    · change b₂ 1558=(b₂ 1556 && b₂ 1557)
      simp [b₂,b₁,writeBit,side]
    · exact (keep _ (by decide)).trans low
    · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>keep q ((by decide +kernel : ∀q∈smallM,q≠1557 ∧ q≠1558) q h))).trans upper
  dsimp only
  rw [shape,run_append,run_take,stage,run_append,run_take,turn,last]

end ECDSAAdd.Entrant.StairPacket.Leave225TailFlags


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240TailFlags
open Arithmetic Partial LeaveCompanion LeaveCompanion240 Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program:Program := (leave240.drop 2462).take 499
theorem shape : program=pending++(nextU++clearFlag) := by decide +kernel
attribute [local irreducible] run
theorem result (a:SkywalkNat.State) (s:State) (m:List Bool) (sign:Nat)
    (bit:sign≤1) (small:min a.u a.v<2^129) (x:s.basis 1557=false) (y:s.basis 1558=false)
    (scan:regValue scanned s.basis=Shadow.high 129 15 a)
    (clean:∀p∈pendingPairs,s.basis p.2=false) (scratch:∀p∈clearFlagPairs,s.basis p.2=false)
    (long:s.basis 1556=decide (2^136≤a.u-sign))
    (low:s.basis 922=decide (2^136≤(a.u-sign)%(2*2^136)))
    (upper:regValue smallM s.basis=((a.u-sign)/(2*2^136))%2^smallM.length) :
    let f:=decide (Shadow.far 129 15 a)
    let u:=f && decide (2^129≤a.u)
    run program m s=⟨s.phase,writeBit (writeBit (writeBit s.basis 1557 f) 1558 u) 1556 false⟩ := by
  let f:=decide (Shadow.far 129 15 a)
  let u:=f && decide (2^129≤a.u)
  let b₁:=writeBit s.basis 1557 f
  let b₂:=writeBit b₁ 1558 u
  have stage:run pending m s=⟨s.phase,b₁⟩ := by
    rw [pending_three s m y clean,x,Bool.false_xor]
    change (State.mk s.phase (writeBit s.basis 1557 (decide (3≤regValue scanned s.basis))))=_
    rw [scan]; rfl
  have side:(s.basis 1556 && f)=u := by
    by_cases far:Shadow.far 129 15 a
    · simp only [f,u,far,decide_true,Bool.and_true,Bool.true_and,long]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using Leave240NextFlagTruth.orientation a sign bit small far)
    · simp [f,u,far]
  have keep (q:Wire) (h:q≠1557 ∧ q≠1558) : b₂ q=s.basis q := by simp [b₂,b₁,writeBit,h.1,h.2]
  have turn (mm:List Bool):run nextU mm ⟨s.phase,b₁⟩=⟨s.phase,b₂⟩ := by
    rw [nextU_run _ _ (by simpa [b₁,writeBit] using y)]
    simp [b₂,b₁,writeBit,side]
  have last (mm:List Bool):run clearFlag mm ⟨s.phase,b₂⟩=⟨s.phase,writeBit b₂ 1556 false⟩ := by
    apply clearFlag_value _ _ (2^136) (a.u-sign) (by decide)
    · intro p hp
      exact (keep p.2 ((by decide +kernel : ∀p∈clearFlagPairs,p.2≠1557 ∧ p.2≠1558) p hp)).trans (scratch p hp)
    · intro h
      apply Leave240NextFlagTruth.boundNear a sign
      simpa [b₂,b₁,writeBit,f] using h
    · exact (keep _ (by decide)).trans long
    · change b₂ 1558=(b₂ 1556 && b₂ 1557)
      simp [b₂,b₁,writeBit,side]
    · exact (keep _ (by decide)).trans low
    · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>keep q ((by decide +kernel : ∀q∈smallM,q≠1557 ∧ q≠1558) q h))).trans upper
  dsimp only
  rw [shape,run_append,run_take,stage,run_append,run_take,turn,last]

end ECDSAAdd.Entrant.StairPacket.Leave240TailFlags


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255TailFlags
open Arithmetic Partial LeaveCompanion LeaveCompanion255 Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

def program:Program := (leave255.drop 2576).take 527
theorem shape : program=pending++(nextU++clearFlag) := by decide +kernel
attribute [local irreducible] run
theorem result (a:SkywalkNat.State) (s:State) (m:List Bool) (sign:Nat)
    (bit:sign≤1) (small:min a.u a.v<2^121) (x:s.basis 1557=false) (y:s.basis 1558=false)
    (scan:regValue scanned s.basis=Shadow.high 121 15 a)
    (clean:∀p∈pendingPairs,s.basis p.2=false) (scratch:∀p∈clearFlagPairs,s.basis p.2=false)
    (long:s.basis 1556=decide (2^129≤a.u-sign))
    (low:s.basis 915=decide (2^129≤(a.u-sign)%(2*2^129)))
    (upper:regValue smallM s.basis=((a.u-sign)/(2*2^129))%2^smallM.length) :
    let f:=decide (Shadow.far 121 15 a)
    let u:=f && decide (2^121≤a.u)
    run program m s=⟨s.phase,writeBit (writeBit (writeBit s.basis 1557 f) 1558 u) 1556 false⟩ := by
  let f:=decide (Shadow.far 121 15 a)
  let u:=f && decide (2^121≤a.u)
  let b₁:=writeBit s.basis 1557 f
  let b₂:=writeBit b₁ 1558 u
  have stage:run pending m s=⟨s.phase,b₁⟩ := by
    rw [pending_three s m y clean,x,Bool.false_xor]
    change (State.mk s.phase (writeBit s.basis 1557 (decide (3≤regValue scanned s.basis))))=_
    rw [scan]; rfl
  have side:(s.basis 1556 && f)=u := by
    by_cases far:Shadow.far 121 15 a
    · simp only [f,u,far,decide_true,Bool.and_true,Bool.true_and,long]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using Leave255NextFlagTruth.orientation a sign bit small far)
    · simp [f,u,far]
  have keep (q:Wire) (h:q≠1557 ∧ q≠1558) : b₂ q=s.basis q := by simp [b₂,b₁,writeBit,h.1,h.2]
  have turn (mm:List Bool):run nextU mm ⟨s.phase,b₁⟩=⟨s.phase,b₂⟩ := by
    rw [nextU_run _ _ (by simpa [b₁,writeBit] using y)]
    simp [b₂,b₁,writeBit,side]
  have last (mm:List Bool):run clearFlag mm ⟨s.phase,b₂⟩=⟨s.phase,writeBit b₂ 1556 false⟩ := by
    apply clearFlag_value _ _ (2^129) (a.u-sign) (by decide)
    · intro p hp
      exact (keep p.2 ((by decide +kernel : ∀p∈clearFlagPairs,p.2≠1557 ∧ p.2≠1558) p hp)).trans (scratch p hp)
    · intro h
      apply Leave255NextFlagTruth.boundNear a sign
      simpa [b₂,b₁,writeBit,f] using h
    · exact (keep _ (by decide)).trans long
    · change b₂ 1558=(b₂ 1556 && b₂ 1557)
      simp [b₂,b₁,writeBit,side]
    · exact (keep _ (by decide)).trans low
    · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>keep q ((by decide +kernel : ∀q∈smallM,q≠1557 ∧ q≠1558) q h))).trans upper
  dsimp only
  rw [shape,run_append,run_take,stage,run_append,run_take,turn,last]

end ECDSAAdd.Entrant.StairPacket.Leave255TailFlags


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225InputScan Leave225Front
open LeaveReadoutFrame Leave225MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def beforeOpen := leave225.take 169
theorem beforeShape : beforeOpen=scanPart++(flipHistory++long) := by decide +kernel
theorem split : Leave225FullArithmetic.program=beforeOpen++(openPart++interior) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let v:=run Leave225FullArithmetic.program m s
    v.basis 930=decide (2^144≤mag%(2*2^144)) ∧
    ∀mm,run closePart mm v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let h:=SkywalkNat.step^[15] (Shadow.reduced 144 15 z)
  let sc:=run scanPart m s
  let a:=run flipHistory (m.drop (measurementCount scanPart)) sc
  have input:=Leave225InputScan.result s m h.u h.v G sg ready fresh
  have hist (q:Wire) (ok:q∉flipHistory.map destination):a.basis q=sc.basis q:=preserved _ _ _ q ok
  have safe (q:Wire) (ok:q∉flipHistory.map destination ∧ q≠1723 ∧ q∉RailPair.sites pairs):a.basis q=s.basis q:=
    (hist _ ok.1).trans (input.2.2.2 _ ok.2.1 ok.2.2)
  have temps:∀p∈longPairs,a.basis p.2=false := by
    intro p hq
    exact (safe _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1723 ∧ p.2∉RailPair.sites pairs) p hq)).trans (temp p hq)
  let e:=run beforeOpen m s
  have eq:e=⟨a.phase,writeBit a.basis 1556 (a.basis 1556 ^^ ((PortalAnd.digits 930 longPairs).any a.basis))⟩ := by
    change run beforeOpen m s=_
    rw [beforeShape,run_append,run_take,run_append,run_take,long_run _ _ temps]
  have keep (q:Wire) (neq:q≠1556):e.basis q=a.basis q := by rw [eq];simp [writeBit,neq]
  have x:e.basis 1557=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  have y:e.basis 1558=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  let n:=m.drop (measurementCount beforeOpen)
  let w:=run openPart n e
  let w':=n.drop (measurementCount openPart)
  have bit:(run interior w' w).basis 930=e.basis 930 :=
    (preserved _ _ _ _ (layout _ (by decide))).trans (preserved openPart e n _ (by decide +kernel))
  have raw:e.basis 930=((h.u-(negative sg h.u).toNat)/2^144).testBit 0 :=
    (keep _ (by decide)).trans ((hist _ (by decide)).trans (input.2.2.1 0 (by decide)).2)
  have tr:=LeaveRestoreTruth.truth 144 z small sg
  dsimp only
  rw [split,run_append,run_take,run_append,run_take]
  constructor
  · rw [bit,raw,thresholdBit _ _ (by decide),tr.2.2.2,tr.2.2.1]
  · exact fun mm=>released e n w' mm x y
end ECDSAAdd.Entrant.StairPacket.Leave225MaskCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240InputScan Leave240Front
open LeaveReadoutFrame Leave240MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def beforeOpen := leave240.take 169
theorem beforeShape : beforeOpen=scanPart++(flipHistory++long) := by decide +kernel
theorem split : Leave240FullArithmetic.program=beforeOpen++(openPart++interior) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let v:=run Leave240FullArithmetic.program m s
    v.basis 922=decide (2^136≤mag%(2*2^136)) ∧
    ∀mm,run closePart mm v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let h:=SkywalkNat.step^[15] (Shadow.reduced 136 15 z)
  let sc:=run scanPart m s
  let a:=run flipHistory (m.drop (measurementCount scanPart)) sc
  have input:=Leave240InputScan.result s m h.u h.v G sg ready fresh
  have hist (q:Wire) (ok:q∉flipHistory.map destination):a.basis q=sc.basis q:=preserved _ _ _ q ok
  have safe (q:Wire) (ok:q∉flipHistory.map destination ∧ q≠1715 ∧ q∉RailPair.sites pairs):a.basis q=s.basis q:=
    (hist _ ok.1).trans (input.2.2.2 _ ok.2.1 ok.2.2)
  have temps:∀p∈longPairs,a.basis p.2=false := by
    intro p hq
    exact (safe _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1715 ∧ p.2∉RailPair.sites pairs) p hq)).trans (temp p hq)
  let e:=run beforeOpen m s
  have eq:e=⟨a.phase,writeBit a.basis 1556 (a.basis 1556 ^^ ((PortalAnd.digits 922 longPairs).any a.basis))⟩ := by
    change run beforeOpen m s=_
    rw [beforeShape,run_append,run_take,run_append,run_take,long_run _ _ temps]
  have keep (q:Wire) (neq:q≠1556):e.basis q=a.basis q := by rw [eq];simp [writeBit,neq]
  have x:e.basis 1557=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  have y:e.basis 1558=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  let n:=m.drop (measurementCount beforeOpen)
  let w:=run openPart n e
  let w':=n.drop (measurementCount openPart)
  have bit:(run interior w' w).basis 922=e.basis 922 :=
    (preserved _ _ _ _ (layout _ (by decide))).trans (preserved openPart e n _ (by decide +kernel))
  have raw:e.basis 922=((h.u-(negative sg h.u).toNat)/2^136).testBit 0 :=
    (keep _ (by decide)).trans ((hist _ (by decide)).trans (input.2.2.1 0 (by decide)).2)
  have tr:=LeaveRestoreTruth.truth 136 z small sg
  dsimp only
  rw [split,run_append,run_take,run_append,run_take]
  constructor
  · rw [bit,raw,thresholdBit _ _ (by decide),tr.2.2.2,tr.2.2.1]
  · exact fun mm=>released e n w' mm x y
end ECDSAAdd.Entrant.StairPacket.Leave240MaskCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255InputScan Leave255Front
open LeaveReadoutFrame Leave255MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def beforeOpen := leave255.take 169
theorem beforeShape : beforeOpen=scanPart++(flipHistory++long) := by decide +kernel
theorem split : Leave255FullArithmetic.program=beforeOpen++(openPart++interior) := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let v:=run Leave255FullArithmetic.program m s
    v.basis 915=decide (2^129≤mag%(2*2^129)) ∧
    ∀mm,run closePart mm v=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := by
  let h:=SkywalkNat.step^[15] (Shadow.reduced 129 15 z)
  let sc:=run scanPart m s
  let a:=run flipHistory (m.drop (measurementCount scanPart)) sc
  have input:=Leave255InputScan.result s m h.u h.v G sg ready fresh
  have hist (q:Wire) (ok:q∉flipHistory.map destination):a.basis q=sc.basis q:=preserved _ _ _ q ok
  have safe (q:Wire) (ok:q∉flipHistory.map destination ∧ q≠1708 ∧ q∉RailPair.sites pairs):a.basis q=s.basis q:=
    (hist _ ok.1).trans (input.2.2.2 _ ok.2.1 ok.2.2)
  have temps:∀p∈longPairs,a.basis p.2=false := by
    intro p hq
    exact (safe _ ((by decide +kernel : ∀p∈longPairs,p.2∉flipHistory.map destination ∧ p.2≠1708 ∧ p.2∉RailPair.sites pairs) p hq)).trans (temp p hq)
  let e:=run beforeOpen m s
  have eq:e=⟨a.phase,writeBit a.basis 1556 (a.basis 1556 ^^ ((PortalAnd.digits 915 longPairs).any a.basis))⟩ := by
    change run beforeOpen m s=_
    rw [beforeShape,run_append,run_take,run_append,run_take,long_run _ _ temps]
  have keep (q:Wire) (neq:q≠1556):e.basis q=a.basis q := by rw [eq];simp [writeBit,neq]
  have x:e.basis 1557=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  have y:e.basis 1558=false := (keep _ (by decide)).trans ((safe _ (by decide)).trans (scratch _ (by decide)))
  let n:=m.drop (measurementCount beforeOpen)
  let w:=run openPart n e
  let w':=n.drop (measurementCount openPart)
  have bit:(run interior w' w).basis 915=e.basis 915 :=
    (preserved _ _ _ _ (layout _ (by decide))).trans (preserved openPart e n _ (by decide +kernel))
  have raw:e.basis 915=((h.u-(negative sg h.u).toNat)/2^129).testBit 0 :=
    (keep _ (by decide)).trans ((hist _ (by decide)).trans (input.2.2.1 0 (by decide)).2)
  have tr:=LeaveRestoreTruth.truth 129 z small sg
  dsimp only
  rw [split,run_append,run_take,run_append,run_take]
  constructor
  · rw [bit,raw,thresholdBit _ _ (by decide),tr.2.2.2,tr.2.2.1]
  · exact fun mm=>released e n w' mm x y
end ECDSAAdd.Entrant.StairPacket.Leave255MaskCut


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program := leave225.take 2788
theorem shape : program=Leave225FullArithmetic.program++(Leave225MaskThrough.closePart++Leave225TailFlags.program) := by decide +kernel
def finalBits (v:BasisState) (f u:Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^144)
    (ready:onRails 10 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 144 15 z)).v) s.basis)
    (fresh:s.basis 1723=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈Leave225FrontReady.watched,s.basis q=false)
    (par:Leave225EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=key (actualMode 144 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^136)
    (bound:Leave225TrueMiddle.F z<2^112) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let far:=decide (Shadow.far 136 15 a)
    let v:=run Leave225FullArithmetic.program m s
    let out:=run program m s
    out.phase=s.phase ∧ out.basis 1556=false ∧ out.basis 1557=far ∧ out.basis 1558=(far && decide (2^136≤a.u)) ∧
      regValue smallM out.basis=(mag/2^145)%2^10 ∧
      (∀i<112,out.basis (live i)=(Leave225TrueMiddle.F z).testBit i) ∧
      ∀q,q≠1556 → q≠1557 → q≠1558 → out.basis q=v.basis q := by
  let a:=SkywalkNat.step^[15] z
  let e:=(negative sg a.u).toNat
  let v:=run Leave225FullArithmetic.program m s
  let n:=m.drop (measurementCount Leave225FullArithmetic.program)
  let u:=run Leave225MaskThrough.closePart n v
  let n':=n.drop (measurementCount Leave225MaskThrough.closePart)
  have ar:=Leave225FullArithmetic.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have clears:=Leave225FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have mask:=Leave225MaskCut.result s m z G sg small ready fresh scratch temp
  have closed:u=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  have kept (q:Wire) (h:q≠1557 ∧ q≠1558) : u.basis q=v.basis q := by rw [closed];simp [writeBit,h.1,h.2]
  have lo:∀i:Fin 112,live i≠1557 ∧ live i≠1558 ∧ live i≠1556 := by decide +kernel
  have ms:∀q∈smallM,q≠1557 ∧ q≠1558 ∧ q≠1556 := by decide +kernel
  have bits:∀i<112,u.basis (live i)=(Leave225TrueMiddle.F z).testBit i := fun i h=>
    (kept _ ⟨(lo ⟨i,h⟩).1,(lo ⟨i,h⟩).2.1⟩).trans (ar.2.2.2 i h)
  have upper:regValue smallM u.basis=regValue smallM v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ ⟨(ms _ h).1,(ms _ h).2.1⟩)
  have scan:regValue scanned u.basis=Shadow.high 136 15 a := by
    rw [(outputRegisters u _ bits).2]
    have fit:Leave225TrueMiddle.F z/2^7<2^105 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
    rw [Nat.mod_eq_of_lt fit]
    exact Leave225NextFlagTruth.value z
  have cleanAt (q:Wire) (h:q∈Leave225FlagScratch.targets) : u.basis q=false := by
    have geom:∀q∈Leave225FlagScratch.targets,q≠1557 ∧ q≠1558 := by decide +kernel
    exact (kept _ (geom _ h)).trans (clears _ h)
  have tail:=Leave225TailFlags.result a u n' e (by dsimp [e];cases negative sg a.u <;> decide) nextSmall
    (by rw [closed];simp [writeBit]) (by rw [closed];simp [writeBit]) scan
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩))
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_right _ h,rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ (by decide)).trans mask.1)
    (by rw [upper,ar.2.1];rfl)
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take,tail]
  let f:=decide (Shadow.far 136 15 a)
  let side:=f && decide (2^136≤a.u)
  have frame (q:Wire) (hx:q≠1556) (hy:q≠1557) (hz:q≠1558):finalBits u.basis f side q=v.basis q := by
    simpa [finalBits,writeBit,hx,hy,hz] using kept q ⟨hy,hz⟩
  refine ⟨(show u.phase=v.phase by rw [closed]).trans ar.1,?_,?_,?_,?_,?_,frame⟩
  · simp [writeBit]
  · change finalBits u.basis f side 1557=f
    simp [finalBits,writeBit]
  · change finalBits u.basis f side 1558=side
    simp [finalBits,writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>frame q (ms _ h).2.2 (ms _ h).1 (ms _ h).2.1)).trans ar.2.1
  · intro i h
    exact (frame _ (lo ⟨i,h⟩).2.2 (lo ⟨i,h⟩).1 (lo ⟨i,h⟩).2.1).trans (ar.2.2.2 i h)
end ECDSAAdd.Entrant.StairPacket.Leave225BeforeStore


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program := leave240.take 2961
theorem shape : program=Leave240FullArithmetic.program++(Leave240MaskThrough.closePart++Leave240TailFlags.program) := by decide +kernel
def finalBits (v:BasisState) (f u:Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^136)
    (ready:onRails 11 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 136 15 z)).v) s.basis)
    (fresh:s.basis 1715=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈Leave240FrontReady.watched,s.basis q=false)
    (par:Leave240EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=key (actualMode 136 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^129)
    (bound:Leave240TrueMiddle.F z<2^120) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let far:=decide (Shadow.far 129 15 a)
    let v:=run Leave240FullArithmetic.program m s
    let out:=run program m s
    out.phase=s.phase ∧ out.basis 1556=false ∧ out.basis 1557=far ∧ out.basis 1558=(far && decide (2^129≤a.u)) ∧
      regValue smallM out.basis=(mag/2^137)%2^11 ∧
      (∀i<120,out.basis (live i)=(Leave240TrueMiddle.F z).testBit i) ∧
      ∀q,q≠1556 → q≠1557 → q≠1558 → out.basis q=v.basis q := by
  let a:=SkywalkNat.step^[15] z
  let e:=(negative sg a.u).toNat
  let v:=run Leave240FullArithmetic.program m s
  let n:=m.drop (measurementCount Leave240FullArithmetic.program)
  let u:=run Leave240MaskThrough.closePart n v
  let n':=n.drop (measurementCount Leave240MaskThrough.closePart)
  have ar:=Leave240FullArithmetic.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have clears:=Leave240FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have mask:=Leave240MaskCut.result s m z G sg small ready fresh scratch temp
  have closed:u=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  have kept (q:Wire) (h:q≠1557 ∧ q≠1558) : u.basis q=v.basis q := by rw [closed];simp [writeBit,h.1,h.2]
  have lo:∀i:Fin 120,live i≠1557 ∧ live i≠1558 ∧ live i≠1556 := by decide +kernel
  have ms:∀q∈smallM,q≠1557 ∧ q≠1558 ∧ q≠1556 := by decide +kernel
  have bits:∀i<120,u.basis (live i)=(Leave240TrueMiddle.F z).testBit i := fun i h=>
    (kept _ ⟨(lo ⟨i,h⟩).1,(lo ⟨i,h⟩).2.1⟩).trans (ar.2.2.2 i h)
  have upper:regValue smallM u.basis=regValue smallM v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ ⟨(ms _ h).1,(ms _ h).2.1⟩)
  have scan:regValue scanned u.basis=Shadow.high 129 15 a := by
    rw [(outputRegisters u _ bits).2]
    have fit:Leave240TrueMiddle.F z/2^8<2^112 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
    rw [Nat.mod_eq_of_lt fit]
    exact Leave240NextFlagTruth.value z
  have cleanAt (q:Wire) (h:q∈Leave240FlagScratch.targets) : u.basis q=false := by
    have geom:∀q∈Leave240FlagScratch.targets,q≠1557 ∧ q≠1558 := by decide +kernel
    exact (kept _ (geom _ h)).trans (clears _ h)
  have tail:=Leave240TailFlags.result a u n' e (by dsimp [e];cases negative sg a.u <;> decide) nextSmall
    (by rw [closed];simp [writeBit]) (by rw [closed];simp [writeBit]) scan
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩))
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_right _ h,rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ (by decide)).trans mask.1)
    (by rw [upper,ar.2.1];rfl)
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take,tail]
  let f:=decide (Shadow.far 129 15 a)
  let side:=f && decide (2^129≤a.u)
  have frame (q:Wire) (hx:q≠1556) (hy:q≠1557) (hz:q≠1558):finalBits u.basis f side q=v.basis q := by
    simpa [finalBits,writeBit,hx,hy,hz] using kept q ⟨hy,hz⟩
  refine ⟨(show u.phase=v.phase by rw [closed]).trans ar.1,?_,?_,?_,?_,?_,frame⟩
  · simp [writeBit]
  · change finalBits u.basis f side 1557=f
    simp [finalBits,writeBit]
  · change finalBits u.basis f side 1558=side
    simp [finalBits,writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>frame q (ms _ h).2.2 (ms _ h).1 (ms _ h).2.1)).trans ar.2.1
  · intro i h
    exact (frame _ (lo ⟨i,h⟩).2.2 (lo ⟨i,h⟩).1 (lo ⟨i,h⟩).2.1).trans (ar.2.2.2 i h)
end ECDSAAdd.Entrant.StairPacket.Leave240BeforeStore


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def program := leave255.take 3103
theorem shape : program=Leave255FullArithmetic.program++(Leave255MaskThrough.closePart++Leave255TailFlags.program) := by decide +kernel
def finalBits (v:BasisState) (f u:Bool) := writeBit (writeBit (writeBit v 1557 f) 1558 u) 1556 false
attribute [local irreducible] run SkywalkNat.step

theorem result (s : State) (m : List Bool) (z : SkywalkNat.State) (G sg : Bool)
    (small:min z.u z.v<2^129)
    (ready:onRails 12 15 (SkywalkRails.encode G sg (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).u
        (SkywalkNat.step^[15] (Shadow.reduced 129 15 z)).v) s.basis)
    (fresh:s.basis 1708=false)
    (scratch:∀q∈1556::1557::1558::fullC,s.basis q=false)
    (temp:∀p∈longPairs,s.basis p.2=false)
    (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈Leave255FrontReady.watched,s.basis q=false)
    (par:Leave255EntryAction.oddRead s.basis=oddBits (letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=key (actualMode 129 z)))
    (nextSmall:min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v<2^121)
    (bound:Leave255TrueMiddle.F z<2^127) :
    let a:=SkywalkNat.step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let far:=decide (Shadow.far 121 15 a)
    let v:=run Leave255FullArithmetic.program m s
    let out:=run program m s
    out.phase=s.phase ∧ out.basis 1556=false ∧ out.basis 1557=far ∧ out.basis 1558=(far && decide (2^121≤a.u)) ∧
      regValue smallM out.basis=(mag/2^130)%2^10 ∧
      (∀i<127,out.basis (live i)=(Leave255TrueMiddle.F z).testBit i) ∧
      ∀q,q≠1556 → q≠1557 → q≠1558 → out.basis q=v.basis q := by
  let a:=SkywalkNat.step^[15] z
  let e:=(negative sg a.u).toNat
  let v:=run Leave255FullArithmetic.program m s
  let n:=m.drop (measurementCount Leave255FullArithmetic.program)
  let u:=run Leave255MaskThrough.closePart n v
  let n':=n.drop (measurementCount Leave255MaskThrough.closePart)
  have ar:=Leave255FullArithmetic.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have clears:=Leave255FlagScratch.result s m z G sg small ready fresh scratch temp odd room clean padding bank zero par mode events
  have mask:=Leave255MaskCut.result s m z G sg small ready fresh scratch temp
  have closed:u=⟨v.phase,writeBit (writeBit v.basis 1557 false) 1558 false⟩ := mask.2 n
  have kept (q:Wire) (h:q≠1557 ∧ q≠1558) : u.basis q=v.basis q := by rw [closed];simp [writeBit,h.1,h.2]
  have lo:∀i:Fin 127,live i≠1557 ∧ live i≠1558 ∧ live i≠1556 := by decide +kernel
  have ms:∀q∈smallM,q≠1557 ∧ q≠1558 ∧ q≠1556 := by decide +kernel
  have bits:∀i<127,u.basis (live i)=(Leave255TrueMiddle.F z).testBit i := fun i h=>
    (kept _ ⟨(lo ⟨i,h⟩).1,(lo ⟨i,h⟩).2.1⟩).trans (ar.2.2.2 i h)
  have upper:regValue smallM u.basis=regValue smallM v.basis :=
    (regValue_eq_iff _ _ _).mpr (fun q h=>kept _ ⟨(ms _ h).1,(ms _ h).2.1⟩)
  have scan:regValue scanned u.basis=Shadow.high 121 15 a := by
    rw [(outputRegisters u _ bits).2]
    have fit:Leave255TrueMiddle.F z/2^7<2^120 := (Nat.div_lt_iff_lt_mul (by decide)).mpr bound
    rw [Nat.mod_eq_of_lt fit]
    exact Leave255NextFlagTruth.value z
  have cleanAt (q:Wire) (h:q∈Leave255FlagScratch.targets) : u.basis q=false := by
    have geom:∀q∈Leave255FlagScratch.targets,q≠1557 ∧ q≠1558 := by decide +kernel
    exact (kept _ (geom _ h)).trans (clears _ h)
  have tail:=Leave255TailFlags.result a u n' e (by dsimp [e];cases negative sg a.u <;> decide) nextSmall
    (by rw [closed];simp [writeBit]) (by rw [closed];simp [writeBit]) scan
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_left _ h,rfl⟩))
    (fun p h=>cleanAt _ (List.mem_map.mpr ⟨p,List.mem_append_right _ h,rfl⟩))
    ((kept _ (by decide)).trans ar.2.2.1) ((kept _ (by decide)).trans mask.1)
    (by rw [upper,ar.2.1];rfl)
  dsimp only
  rw [shape,run_append,run_take,run_append,run_take,tail]
  let f:=decide (Shadow.far 121 15 a)
  let side:=f && decide (2^121≤a.u)
  have frame (q:Wire) (hx:q≠1556) (hy:q≠1557) (hz:q≠1558):finalBits u.basis f side q=v.basis q := by
    simpa [finalBits,writeBit,hx,hy,hz] using kept q ⟨hy,hz⟩
  refine ⟨(show u.phase=v.phase by rw [closed]).trans ar.1,?_,?_,?_,?_,?_,frame⟩
  · simp [writeBit]
  · change finalBits u.basis f side 1557=f
    simp [finalBits,writeBit]
  · change finalBits u.basis f side 1558=side
    simp [finalBits,writeBit]
  · exact ((regValue_eq_iff _ _ _).mpr (fun q h=>frame q (ms _ h).2.2 (ms _ h).1 (ms _ h).2.1)).trans ar.2.1
  · intro i h
    exact (frame _ (lo ⟨i,h⟩).2.2 (lo ⟨i,h⟩).1 (lo ⟨i,h⟩).2.1).trans (ar.2.2.2 i h)
end ECDSAAdd.Entrant.StairPacket.Leave255BeforeStore


end
