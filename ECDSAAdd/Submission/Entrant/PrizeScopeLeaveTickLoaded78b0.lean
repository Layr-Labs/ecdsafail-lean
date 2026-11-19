import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRetireActual981d
import ECDSAAdd.Submission.Entrant.PrizeTail227303371
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveBankEnvelope
open SkywalkNat

/-- After the first tick the true sum fits within one and a half input rails.
    This gives the signed high-bank increment room for the possible increment. -/
theorem after_first (x y B : Nat) (hx : x≤B) (hy : y≤B) (k : Nat) :
    let z := step^[k+1] (init x y)
    z.u+z.v ≤ B+B/2 := by
  dsimp only
  rw [Function.iterate_succ_apply]
  apply (iter_sum_nonincrease _ _).trans
  unfold step init
  split_ifs <;> dsimp only at * <;> omega

theorem bounds (z : SkywalkNat.State) (h : z.u+z.v≤2^256+2^255) :
    Shadow.high 144 15 z+1 < 2^97 ∧ Shadow.high 136 15 z+1 < 2^105 ∧
    Shadow.high 129 15 z+1 < 2^112 := by
  simp only [Shadow.high,Shadow.limb]
  norm_num1 at h ⊢
  omega

theorem outputs (z : SkywalkNat.State) (h : z.u+z.v<2^257) (k : Nat) :
    let a := step^[k] z
    (a.u+a.v)/2^145<2^112 ∧ (a.u+a.v)/2^137<2^120 ∧ (a.u+a.v)/2^130<2^127 := by
  dsimp only
  have noninc := iter_sum_nonincrease k z
  norm_num1 at h ⊢
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveBankEnvelope


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225TrueMiddle
open Arithmetic SkywalkNat IntegerHigh Shadow HighBankSum HighBankBarrel
open Leave225Join Leave225Word Leave225High Leave225Barrel Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev r (z : SkywalkNat.State) := reduced 144 15 z
def key (z : SkywalkNat.State) : Fin 16 :=
  ⟨if 2^144≤z.u then 0 else wait 15 z.u,by have h:=wait_le 15 z.u;split <;> omega⟩
def X (z : SkywalkNat.State) := total (step^[15] (r z))/2^145
def F (z : SkywalkNat.State) := total (step^[15] z)/2^145
def d (z : SkywalkNat.State) := X z/2^(key z).val
def neg (z : SkywalkNat.State) := cross (d z) && (!(decide (2^144≤z.u)) && negative (oddBits (letters 15 (r z))))

/-- The actual word-update segment, from its physical input registers to every
    output bit of the true fifteen-tick sum and all retired column sites. -/
theorem actual (z : SkywalkNat.State) (s : ECDSAAdd.State) (m : List Bool)
    (small : min z.u z.v<2^144) (odd : z.v%2=1) (room : high 144 15 z+1<2^97)
    (clean : ∀q∈carries,s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (tag : ∀q∈tags,s.basis q=if far 144 15 z then hot (key z) q else false)
    (shadow : ∀i<18,s.basis (401+i)=(X z).testBit i)
    (bank : regValue ys s.basis=if far 144 15 z then high 144 15 z else 0)
    (cin : s.basis 1724=if far 144 15 z then cross (d z) else false)
    (sign : far 144 15 z → s.basis 1597=neg z) (scratch : s.basis 1614=false) :
    let u:=run Leave225Middle.middle m s
    u.phase=s.phase ∧ (∀i<112,u.basis (live i)=(F z).testBit i) ∧
      (∀i:Fin 18,u.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 112 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → u.basis q=s.basis q := by
  dsimp only
  by_cases f : far 144 15 z
  · simp only [if_pos f] at tag bank cin
    have law := LeaveShadowRails.far_result 144 97 z small f odd room
    change d z=(cross (d z)).toNat+2*(!neg z).toNat ∧ F z=2^(key z).val*HighBankAdjust.adjusted (high 144 15 z) 97 (cross (d z)) (neg z)+X z%2^(key z).val at law
    rw [←cin,←sign f,←bank] at law
    have out := Leave225Middle.result (key z) (X z) s m clean selectZero padding tag shadow law.1 scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [law.2]
    exact activeBits _ _ _ _ (fun i=>(out.2.1 i).1) out.2.2.1
  · simp only [if_neg f] at tag bank cin
    have law := LeaveShadowRails.near_result 144 z f
    have eq : X z=F z := by unfold X F r;rw [law.1]
    have bound : X z<2^18 := eq ▸ law.2
    have out := Leave225NearMiddle.result (X z) bound s m clean selectZero padding tag shadow bank cin scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [←eq]
    exact inactiveBits _ bound _ (fun i=>(out.2.1 i).1) out.2.2.1

end ECDSAAdd.Entrant.StairPacket.Leave225TrueMiddle


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240TrueMiddle
open Arithmetic SkywalkNat IntegerHigh Shadow HighBankSum HighBankBarrel
open Leave240Join Leave240Word Leave240High Leave240Barrel Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev r (z : SkywalkNat.State) := reduced 136 15 z
def key (z : SkywalkNat.State) : Fin 16 :=
  ⟨if 2^136≤z.u then 0 else wait 15 z.u,by have h:=wait_le 15 z.u;split <;> omega⟩
def X (z : SkywalkNat.State) := total (step^[15] (r z))/2^137
def F (z : SkywalkNat.State) := total (step^[15] z)/2^137
def d (z : SkywalkNat.State) := X z/2^(key z).val
def neg (z : SkywalkNat.State) := cross (d z) && (!(decide (2^136≤z.u)) && negative (oddBits (letters 15 (r z))))

/-- The actual word-update segment, from its physical input registers to every
    output bit of the true fifteen-tick sum and all retired column sites. -/
theorem actual (z : SkywalkNat.State) (s : ECDSAAdd.State) (m : List Bool)
    (small : min z.u z.v<2^136) (odd : z.v%2=1) (room : high 136 15 z+1<2^105)
    (clean : ∀q∈carries,s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (tag : ∀q∈tags,s.basis q=if far 136 15 z then hot (key z) q else false)
    (shadow : ∀i<18,s.basis (408+i)=(X z).testBit i)
    (bank : regValue ys s.basis=if far 136 15 z then high 136 15 z else 0)
    (cin : s.basis 1716=if far 136 15 z then cross (d z) else false)
    (sign : far 136 15 z → s.basis 1597=neg z) (scratch : s.basis 1614=false) :
    let u:=run Leave240Middle.middle m s
    u.phase=s.phase ∧ (∀i<120,u.basis (live i)=(F z).testBit i) ∧
      (∀i:Fin 18,u.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 120 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → u.basis q=s.basis q := by
  dsimp only
  by_cases f : far 136 15 z
  · simp only [if_pos f] at tag bank cin
    have law := LeaveShadowRails.far_result 136 105 z small f odd room
    change d z=(cross (d z)).toNat+2*(!neg z).toNat ∧ F z=2^(key z).val*HighBankAdjust.adjusted (high 136 15 z) 105 (cross (d z)) (neg z)+X z%2^(key z).val at law
    rw [←cin,←sign f,←bank] at law
    have out := Leave240Middle.result (key z) (X z) s m clean selectZero padding tag shadow law.1 scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [law.2]
    exact activeBits _ _ _ _ (fun i=>(out.2.1 i).1) out.2.2.1
  · simp only [if_neg f] at tag bank cin
    have law := LeaveShadowRails.near_result 136 z f
    have eq : X z=F z := by unfold X F r;rw [law.1]
    have bound : X z<2^18 := eq ▸ law.2
    have out := Leave240NearMiddle.result (X z) bound s m clean selectZero padding tag shadow bank cin scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [←eq]
    exact inactiveBits _ bound _ (fun i=>(out.2.1 i).1) out.2.2.1

end ECDSAAdd.Entrant.StairPacket.Leave240TrueMiddle


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255TrueMiddle
open Arithmetic SkywalkNat IntegerHigh Shadow HighBankSum HighBankBarrel
open Leave255Join Leave255Word Leave255High Leave255Barrel Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

abbrev r (z : SkywalkNat.State) := reduced 129 15 z
def key (z : SkywalkNat.State) : Fin 16 :=
  ⟨if 2^129≤z.u then 0 else wait 15 z.u,by have h:=wait_le 15 z.u;split <;> omega⟩
def X (z : SkywalkNat.State) := total (step^[15] (r z))/2^130
def F (z : SkywalkNat.State) := total (step^[15] z)/2^130
def d (z : SkywalkNat.State) := X z/2^(key z).val
def neg (z : SkywalkNat.State) := cross (d z) && (!(decide (2^129≤z.u)) && negative (oddBits (letters 15 (r z))))

/-- The actual word-update segment, from its physical input registers to every
    output bit of the true fifteen-tick sum and all retired column sites. -/
theorem actual (z : SkywalkNat.State) (s : ECDSAAdd.State) (m : List Bool)
    (small : min z.u z.v<2^129) (odd : z.v%2=1) (room : high 129 15 z+1<2^112)
    (clean : ∀q∈carries,s.basis q=false) (selectZero : s.basis 1613=false)
    (padding : ∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (tag : ∀q∈tags,s.basis q=if far 129 15 z then hot (key z) q else false)
    (shadow : ∀i<18,s.basis (416+i)=(X z).testBit i)
    (bank : regValue ys s.basis=if far 129 15 z then high 129 15 z else 0)
    (cin : s.basis 1709=if far 129 15 z then cross (d z) else false)
    (sign : far 129 15 z → s.basis 1597=neg z) (scratch : s.basis 1614=false) :
    let u:=run Leave255Middle.middle m s
    u.phase=s.phase ∧ (∀i<127,u.basis (live i)=(F z).testBit i) ∧
      (∀i:Fin 18,u.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 127 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → u.basis q=s.basis q := by
  dsimp only
  by_cases f : far 129 15 z
  · simp only [if_pos f] at tag bank cin
    have law := LeaveShadowRails.far_result 129 112 z small f odd room
    change d z=(cross (d z)).toNat+2*(!neg z).toNat ∧ F z=2^(key z).val*HighBankAdjust.adjusted (high 129 15 z) 112 (cross (d z)) (neg z)+X z%2^(key z).val at law
    rw [←cin,←sign f,←bank] at law
    have out := Leave255Middle.result (key z) (X z) s m clean selectZero padding tag shadow law.1 scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [law.2]
    exact activeBits _ _ _ _ (fun i=>(out.2.1 i).1) out.2.2.1
  · simp only [if_neg f] at tag bank cin
    have law := LeaveShadowRails.near_result 129 z f
    have eq : X z=F z := by unfold X F r;rw [law.1]
    have bound : X z<2^18 := eq ▸ law.2
    have out := Leave255NearMiddle.result (X z) bound s m clean selectZero padding tag shadow bank cin scratch
    refine ⟨out.1,?_,fun i=>(out.2.1 i).2,out.2.2.2⟩
    rw [←eq]
    exact inactiveBits _ bound _ (fun i=>(out.2.1 i).1) out.2.2.1

end ECDSAAdd.Entrant.StairPacket.Leave255TrueMiddle


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Loaded
open Arithmetic LeaveSelector Leave225Selector Leave225RetireActual SkywalkNat IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem physicalTags : ∀k:Mode,∀q∈Leave225Join.tags,
    prior k q=.bit (enabled k && decide (q=Leave225Join.tags.getD (LeaveSelector.key k) 0)) := by decide +kernel

theorem tags (z:SkywalkNat.State) (v:BasisState) (q:Wire) (hq:q∈Leave225Join.tags) :
    (prior (actualMode 144 z) q).read v=
      if Shadow.far 144 15 z then Leave225Word.hot (Leave225TrueMiddle.key z) q else false := by
  rw [physicalTags _ _ hq]
  by_cases f:Shadow.far 144 15 z
  · rw [if_pos f]
    obtain ⟨idx,_,on⟩:=modeKey 144 z f
    simp only [Expr.read,on,Bool.true_and,idx]
    rfl
  · simp [f,Expr.read,actualMode,farMode,ofFlags,enabled]

private theorem extract (p:Ports) (k:Mode) (s:Sym) (h:reads p s=controls p k) :
    s p.crossing=crossing p k ∧ s 1597=conj (crossing p k) (signExpr p k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at h
  exact ⟨h.2.1,h.2.2.2⟩

theorem controlsAt (k:Mode) :
    prior k 1724=crossing ports k ∧ prior k 1597=conj (crossing ports k) (signExpr ports k) :=
  extract ports k (prior k) (controlCert k)

theorem signed (z:SkywalkNat.State) (ref:BasisState)
    (small:min z.u z.v<2^144) (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (bits:∀i<16,ref (ports.u+i)=(Leave225TrueMiddle.X z).testBit i)
    (par:parityBits ports ref=oddBits (letters 15 (Shadow.reduced 144 15 z))) :
    let k:=actualMode 144 z
    let s:=fun q=>(prior k q).read ref
    s 1724=(if Shadow.far 144 15 z then HighBankSum.cross (Leave225TrueMiddle.d z) else false) ∧
    s 1597=(s 1724 && (signExpr ports k).read ref) ∧ (Shadow.far 144 15 z → s 1597=Leave225TrueMiddle.neg z) := by
  have h:=trueControls 144 97 z small odd room ports ref bits par
  obtain ⟨cx,gate⟩:=controlsAt (actualMode 144 z)
  dsimp only
  rw [cx,gate,read_conj]
  refine ⟨h.1,rfl,?_⟩
  intro f
  rw [h.1,h.2 f,if_pos f]
  rfl

end ECDSAAdd.Entrant.StairPacket.Leave225Loaded


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Loaded
open Arithmetic LeaveSelector Leave240Selector Leave240RetireActual SkywalkNat IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem physicalTags : ∀k:Mode,∀q∈Leave240Join.tags,
    prior k q=.bit (enabled k && decide (q=Leave240Join.tags.getD (LeaveSelector.key k) 0)) := by decide +kernel

theorem tags (z:SkywalkNat.State) (v:BasisState) (q:Wire) (hq:q∈Leave240Join.tags) :
    (prior (actualMode 136 z) q).read v=
      if Shadow.far 136 15 z then Leave240Word.hot (Leave240TrueMiddle.key z) q else false := by
  rw [physicalTags _ _ hq]
  by_cases f:Shadow.far 136 15 z
  · rw [if_pos f]
    obtain ⟨idx,_,on⟩:=modeKey 136 z f
    simp only [Expr.read,on,Bool.true_and,idx]
    rfl
  · simp [f,Expr.read,actualMode,farMode,ofFlags,enabled]

private theorem extract (p:Ports) (k:Mode) (s:Sym) (h:reads p s=controls p k) :
    s p.crossing=crossing p k ∧ s 1597=conj (crossing p k) (signExpr p k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at h
  exact ⟨h.2.1,h.2.2.2⟩

theorem controlsAt (k:Mode) :
    prior k 1716=crossing ports k ∧ prior k 1597=conj (crossing ports k) (signExpr ports k) :=
  extract ports k (prior k) (controlCert k)

theorem signed (z:SkywalkNat.State) (ref:BasisState)
    (small:min z.u z.v<2^136) (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (bits:∀i<16,ref (ports.u+i)=(Leave240TrueMiddle.X z).testBit i)
    (par:parityBits ports ref=oddBits (letters 15 (Shadow.reduced 136 15 z))) :
    let k:=actualMode 136 z
    let s:=fun q=>(prior k q).read ref
    s 1716=(if Shadow.far 136 15 z then HighBankSum.cross (Leave240TrueMiddle.d z) else false) ∧
    s 1597=(s 1716 && (signExpr ports k).read ref) ∧ (Shadow.far 136 15 z → s 1597=Leave240TrueMiddle.neg z) := by
  have h:=trueControls 136 105 z small odd room ports ref bits par
  obtain ⟨cx,gate⟩:=controlsAt (actualMode 136 z)
  dsimp only
  rw [cx,gate,read_conj]
  refine ⟨h.1,rfl,?_⟩
  intro f
  rw [h.1,h.2 f,if_pos f]
  rfl

end ECDSAAdd.Entrant.StairPacket.Leave240Loaded


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Loaded
open Arithmetic LeaveSelector Leave255Selector Leave255RetireActual SkywalkNat IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem physicalTags : ∀k:Mode,∀q∈Leave255Join.tags,
    prior k q=.bit (enabled k && decide (q=Leave255Join.tags.getD (LeaveSelector.key k) 0)) := by decide +kernel

theorem tags (z:SkywalkNat.State) (v:BasisState) (q:Wire) (hq:q∈Leave255Join.tags) :
    (prior (actualMode 129 z) q).read v=
      if Shadow.far 129 15 z then Leave255Word.hot (Leave255TrueMiddle.key z) q else false := by
  rw [physicalTags _ _ hq]
  by_cases f:Shadow.far 129 15 z
  · rw [if_pos f]
    obtain ⟨idx,_,on⟩:=modeKey 129 z f
    simp only [Expr.read,on,Bool.true_and,idx]
    rfl
  · simp [f,Expr.read,actualMode,farMode,ofFlags,enabled]

private theorem extract (p:Ports) (k:Mode) (s:Sym) (h:reads p s=controls p k) :
    s p.crossing=crossing p k ∧ s 1597=conj (crossing p k) (signExpr p k) := by
  simp only [reads,LeaveSelector.controls,List.cons.injEq,and_true,eq_self] at h
  exact ⟨h.2.1,h.2.2.2⟩

theorem controlsAt (k:Mode) :
    prior k 1709=crossing ports k ∧ prior k 1597=conj (crossing ports k) (signExpr ports k) :=
  extract ports k (prior k) (controlCert k)

theorem signed (z:SkywalkNat.State) (ref:BasisState)
    (small:min z.u z.v<2^129) (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (bits:∀i<16,ref (ports.u+i)=(Leave255TrueMiddle.X z).testBit i)
    (par:parityBits ports ref=oddBits (letters 15 (Shadow.reduced 129 15 z))) :
    let k:=actualMode 129 z
    let s:=fun q=>(prior k q).read ref
    s 1709=(if Shadow.far 129 15 z then HighBankSum.cross (Leave255TrueMiddle.d z) else false) ∧
    s 1597=(s 1709 && (signExpr ports k).read ref) ∧ (Shadow.far 129 15 z → s 1597=Leave255TrueMiddle.neg z) := by
  have h:=trueControls 129 112 z small odd room ports ref bits par
  obtain ⟨cx,gate⟩:=controlsAt (actualMode 129 z)
  dsimp only
  rw [cx,gate,read_conj]
  refine ⟨h.1,rfl,?_⟩
  intro f
  rw [h.1,h.2 f,if_pos f]
  rfl

end ECDSAAdd.Entrant.StairPacket.Leave255Loaded


end
