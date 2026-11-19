import ECDSAAdd.Submission.Entrant.PrizeLeave225Join2ee362a
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickEraseActual16ba
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickLoaded78b0
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickPrepared375e
import ECDSAAdd.Submission.Entrant.PrizeScopeLeaveTickRetireActual981d
import ECDSAAdd.Submission.Entrant.PrizeTail227303371

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat Shadow HighBankSum

theorem min_step (z : SkywalkNat.State) : min (step z).u (step z).v≤min z.u z.v := by
  unfold step
  split_ifs <;> (try dsimp only) <;> omega

theorem min_iter (k : Nat) (z : SkywalkNat.State) : min (step^[k] z).u (step^[k] z).v≤min z.u z.v := by
  induction k with
  | zero => exact le_refl _
  | succ k ih => rw [Function.iterate_succ_apply'];exact (min_step _).trans ih

theorem inputFit (b : Nat) (z : SkywalkNat.State) (small : min z.u z.v<2^b) :
    let a:=step^[15] (reduced b 15 z)
    min a.u a.v<2^b ∧ (a.u+a.v)/2^b<2^19 := by
  let r:=reduced b 15 z
  have rsmall : min r.u r.v<2^b := by
    unfold r reduced
    split_ifs <;> (try dsimp only) <;> omega
  have upper : r.u+r.v<3*limb b 15 := by
    by_cases f : far b 15 z
    · exact (represented b 15 z small f).2.2
    · have low : (z.u+z.v)/limb b 15<3 := Nat.lt_of_not_ge f
      simpa only [r,reduced,if_neg f] using (Nat.div_lt_iff_lt_mul (by unfold limb;positivity)).mp low
  dsimp only
  refine ⟨lt_of_le_of_lt (min_iter 15 r) rsmall,?_⟩
  have noninc:=iter_sum_nonincrease 15 r
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr
  change (step^[15] r).u+(step^[15] r).v<_
  rw [scale,pow_succ] at upper
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails


end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum

theorem beforeFresh (p : Ports) (k : Mode) (v : BasisState)
    (scratch : ∀q:Nat, 1561≤q → q≤1597 → v q=false)
    (cross : v p.crossing=false) (nearbyClean : v p.near=false)
    (q : Wire) (a : q≠1559) (b : q≠1560) :
    v q=(before p false k q).read v := by
  by_cases low : 1561≤q ∧ q≤1575
  · simpa [before,b,low,Expr.read] using scratch q low.1 (Nat.le_trans low.2 (by decide))
  by_cases high : 1576≤q ∧ q≤1597
  · simpa [before,start,a,b,low,high,Expr.read] using scratch q (Nat.le_trans (by decide : 1561≤1576) high.1) high.2
  by_cases c : q=p.crossing
  · subst q
    simpa [before,start,a,b,low,high,Expr.read] using cross
  by_cases n : q=p.near
  · subst q
    simpa [before,start,a,b,low,high,c,Expr.read] using nearbyClean
  simp [before,start,a,b,low,high,c,n,Expr.read]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector


end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow HighBankSum

theorem sumFloor (z : SkywalkNat.State) : (z.u+z.v)/2≤total (step z) := by
  unfold total step
  split_ifs <;> (try dsimp only) <;> omega

theorem sumLower (k A : Nat) (z : SkywalkNat.State) (bound : 2^k*A≤total z) :
    A≤total (step^[k] z) := by
  induction k generalizing z with
  | zero => simpa using bound
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    have floor:=sumFloor z
    rw [pow_succ] at bound
    change 2^k*2*A≤z.u+z.v at bound
    rw [show 2^k*2*A=2*(2^k*A) by ring] at bound
    omega

theorem terminalRel (k : Nat) (z r : SkywalkNat.State) (h : Rel k z r) :
    Rel 0 (step^[k] z) (step^[k] r) := by
  induction k generalizing z r with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply]
    exact ih _ _ (advance h).2

theorem sameThreshold (half e : Nat) (z r : SkywalkNat.State) (rel : Rel 0 z r)
    (en:e≤1) (sum:2*half+1≤r.u+r.v) :
    (half≤z.u-e ↔ half≤r.u-e) ∧ (0<z.u ↔ 0<r.u) := by
  cases rel with
  | left B s D guard =>
    dsimp only
    change s+1≤B at guard
    change 2*half+1≤B+s at sum
    simp only [pow_zero,one_mul]
    omega
  | right => exact ⟨Iff.rfl,Iff.rfl⟩

theorem afterThreshold (b : Nat) (z : SkywalkNat.State) (small:min z.u z.v<2^b) (e:Nat) (en:e≤1) :
    let full:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    (2^b≤full.u-e ↔ 2^b≤r.u-e) ∧ (0<full.u ↔ 0<r.u) := by
  by_cases f: far b 15 z
  · have rep:=represented b 15 z small f
    have cap:=rep.2.1
    rw [scale,pow_succ 2 b] at cap
    have low:=sumLower 15 (2*(2^b*2)) (reduced b 15 z) (by unfold total;omega)
    apply sameThreshold _ _ _ _ (terminalRel _ _ _ rep.1) en
    unfold total at low
    have h:=Nat.two_pow_pos b
    omega
  · simp [reduced,f]


theorem limbGaps (b : Nat) (z : SkywalkNat.State) (small:min z.u z.v<2^b) :
    let full:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    ∃a c:Nat,full.u=r.u+2^(b+1)*a ∧ full.v=r.v+2^(b+1)*c := by
  by_cases f : far b 15 z
  · let r:=reduced b 15 z
    let H:=high b 15 z-2
    let V:=2^(b+1)
    let D:=V*H
    have side:=rail b z small f
    dsimp only
    by_cases long : 2^b≤z.u
    · obtain ⟨rv,fullU,valid⟩:=side.1 long
      have shape : z=⟨r.u+2^15*D,r.v⟩:=SkywalkNat.State.ext fullU rv.symm
      have result:=long_u 15 r.u r.v D valid
      rw [←shape] at result
      rw [result]
      exact ⟨H,0,rfl,by rw [Nat.mul_zero,Nat.add_zero]⟩
    · obtain ⟨ru,fullV,valid⟩:=side.2 (Nat.lt_of_not_ge long)
      have shape : z=⟨r.u,r.v+2^15*D⟩:=SkywalkNat.State.ext ru.symm fullV
      have result:=long_v 15 r.v r.u D valid
      rw [←shape] at result
      dsimp only at result
      let J:=2^(wait 15 r.u)*H
      have shift : 2^(wait 15 r.u)*D=V*J := by dsimp [D,J];ring
      rw [shift] at result
      split at result
      · rw [result];exact ⟨0,J,by rw [Nat.mul_zero,Nat.add_zero],rfl⟩
      · rw [result];exact ⟨J,0,rfl,by rw [Nat.mul_zero,Nat.add_zero]⟩
  · refine ⟨0,0,?_,?_⟩ <;> simp [reduced,f]

theorem retainedLow (b : Nat) (z : SkywalkNat.State) (small:min z.u z.v<2^b) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=PortalValues.negative sg r.u
    let V:=2^(b+1)
    PortalValues.negative sg F.u=e ∧ (F.u+F.v)%V=(r.u+r.v)%V ∧ (F.u-e.toNat)%V=(r.u-e.toNat)%V := by
  let F:=step^[15] z
  let r:=step^[15] (reduced b 15 z)
  let e:=PortalValues.negative sg r.u
  let V:=2^(b+1)
  obtain ⟨a,c,ahu,chv⟩:=limbGaps b z small
  have same:0<F.u ↔ 0<r.u:=(afterThreshold b z small 0 (by decide)).2
  have se:e.toNat≤r.u := by
    by_cases p:0<r.u
    · have le:e.toNat≤1:=by cases e <;> decide
      omega
    · simp [e,PortalValues.negative,p]
  change PortalValues.negative sg F.u=e ∧ (F.u+F.v)%V=(r.u+r.v)%V ∧ (F.u-e.toNat)%V=(r.u-e.toNat)%V
  refine ⟨by simp only [e,PortalValues.negative,same],?_,?_⟩
  · have sum:F.u+F.v=r.u+r.v+V*(a+c) := by
      change F.u=r.u+V*a at ahu
      change F.v=r.v+V*c at chv
      rw [ahu,chv];ring
    rw [sum,Nat.add_mul_mod_self_left]
  · change F.u=r.u+V*a at ahu
    rw [ahu,show r.u+V*a-e.toNat=(r.u-e.toNat)+V*a by omega,Nat.add_mul_mod_self_left]

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225SignClose
open Arithmetic Partial Leave225Middle Leave225High Leave225Barrel HighBankBarrel LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def closeSign : Program := [.CX 1597 1613,.X 1613]
def extended := middle++closeSign

private theorem startBits (s:State) (m:List Bool) (h:s.basis 1613=false) :
    (run signBit m s).basis 1597=s.basis 1597 ∧ (run signBit m s).basis 1613= !s.basis 1597 := by
  simp [run,writeBit,Function.update,h]

private theorem finish (u:State) (m:List Bool) (h:u.basis 1613= !u.basis 1597) :
    run closeSign m u=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply congrArg (State.mk u.phase)
  funext q
  by_cases eq:q=1613 <;> simp [Function.update,writeBit,h,eq]

theorem result (s:State) (m:List Bool) (initial:(run first m s).basis 1613=false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  let a:=run first m s
  let f:=m.drop (measurementCount first)
  let v:=run signBit f a
  have eq:run middle m s=run lastPart f v := by
    rw [Leave225Middle.split,run_append,run_take,run_append,run_take]
    rfl
  have after (q:Wire) (h:q∉lastPart.map destination) :
      (run middle m s).basis q=v.basis q := by rw [eq];exact preserved lastPart v f q h
  have start:=startBits a f initial
  have flag:=(after 1597 (by decide +kernel)).trans start.1
  have work:=(after 1613 (by decide +kernel)).trans start.2
  dsimp only
  rw [extended,run_append,run_take]
  apply finish
  rw [flag,work]

theorem closed (z:SkywalkNat.State) (s:State) (m:List Bool)
    (clean:∀q∈carries,s.basis q=false) (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (tags:∀q∈Leave225Join.tags,s.basis q=if Shadow.far 144 15 z then Leave225Word.hot (Leave225TrueMiddle.key z) q else false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply result
  have zero:=clean 1613 (by decide)
  by_cases far:Shadow.far 144 15 z
  · simp only [if_pos far] at tags
    have h:=Leave225High.result (Leave225TrueMiddle.key z) s m clean zero padding tags
    exact (h.frame _ Leave225Shift.layout3.separate).trans zero
  · simp only [if_neg far] at tags
    have h:=Leave225NearHigh.result s m clean zero padding tags
    exact (h.frame _ Leave225Shift.layout3.separate).trans zero

end ECDSAAdd.Entrant.StairPacket.Leave225SignClose


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240SignClose
open Arithmetic Partial Leave240Middle Leave240High Leave240Barrel HighBankBarrel LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def closeSign : Program := [.CX 1597 1613,.X 1613]
def extended := middle++closeSign

private theorem startBits (s:State) (m:List Bool) (h:s.basis 1613=false) :
    (run signBit m s).basis 1597=s.basis 1597 ∧ (run signBit m s).basis 1613= !s.basis 1597 := by
  simp [run,writeBit,Function.update,h]

private theorem finish (u:State) (m:List Bool) (h:u.basis 1613= !u.basis 1597) :
    run closeSign m u=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply congrArg (State.mk u.phase)
  funext q
  by_cases eq:q=1613 <;> simp [Function.update,writeBit,h,eq]

theorem result (s:State) (m:List Bool) (initial:(run first m s).basis 1613=false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  let a:=run first m s
  let f:=m.drop (measurementCount first)
  let v:=run signBit f a
  have eq:run middle m s=run lastPart f v := by
    rw [Leave240Middle.split,run_append,run_take,run_append,run_take]
    rfl
  have after (q:Wire) (h:q∉lastPart.map destination) :
      (run middle m s).basis q=v.basis q := by rw [eq];exact preserved lastPart v f q h
  have start:=startBits a f initial
  have flag:=(after 1597 (by decide +kernel)).trans start.1
  have work:=(after 1613 (by decide +kernel)).trans start.2
  dsimp only
  rw [extended,run_append,run_take]
  apply finish
  rw [flag,work]

theorem closed (z:SkywalkNat.State) (s:State) (m:List Bool)
    (clean:∀q∈carries,s.basis q=false) (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (tags:∀q∈Leave240Join.tags,s.basis q=if Shadow.far 136 15 z then Leave240Word.hot (Leave240TrueMiddle.key z) q else false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply result
  have zero:=clean 1613 (by decide)
  by_cases far:Shadow.far 136 15 z
  · simp only [if_pos far] at tags
    have h:=Leave240High.result (Leave240TrueMiddle.key z) s m clean zero padding tags
    exact (h.frame _ Leave240Shift.layout3.separate).trans zero
  · simp only [if_neg far] at tags
    have h:=Leave240NearHigh.result s m clean zero padding tags
    exact (h.frame _ Leave240Shift.layout3.separate).trans zero

end ECDSAAdd.Entrant.StairPacket.Leave240SignClose


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255SignClose
open Arithmetic Partial Leave255Middle Leave255High Leave255Barrel HighBankBarrel LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

def closeSign : Program := [.CX 1597 1613,.X 1613]
def extended := middle++closeSign

private theorem startBits (s:State) (m:List Bool) (h:s.basis 1613=false) :
    (run signBit m s).basis 1597=s.basis 1597 ∧ (run signBit m s).basis 1613= !s.basis 1597 := by
  simp [run,writeBit,Function.update,h]

private theorem finish (u:State) (m:List Bool) (h:u.basis 1613= !u.basis 1597) :
    run closeSign m u=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply congrArg (State.mk u.phase)
  funext q
  by_cases eq:q=1613 <;> simp [Function.update,writeBit,h,eq]

theorem result (s:State) (m:List Bool) (initial:(run first m s).basis 1613=false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  let a:=run first m s
  let f:=m.drop (measurementCount first)
  let v:=run signBit f a
  have eq:run middle m s=run lastPart f v := by
    rw [Leave255Middle.split,run_append,run_take,run_append,run_take]
    rfl
  have after (q:Wire) (h:q∉lastPart.map destination) :
      (run middle m s).basis q=v.basis q := by rw [eq];exact preserved lastPart v f q h
  have start:=startBits a f initial
  have flag:=(after 1597 (by decide +kernel)).trans start.1
  have work:=(after 1613 (by decide +kernel)).trans start.2
  dsimp only
  rw [extended,run_append,run_take]
  apply finish
  rw [flag,work]

theorem closed (z:SkywalkNat.State) (s:State) (m:List Bool)
    (clean:∀q∈carries,s.basis q=false) (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (tags:∀q∈Leave255Join.tags,s.basis q=if Shadow.far 129 15 z then Leave255Word.hot (Leave255TrueMiddle.key z) q else false) :
    let u:=run middle m s
    run extended m s=⟨u.phase,writeBit u.basis 1613 false⟩ := by
  apply result
  have zero:=clean 1613 (by decide)
  by_cases far:Shadow.far 129 15 z
  · simp only [if_pos far] at tags
    have h:=Leave255High.result (Leave255TrueMiddle.key z) s m clean zero padding tags
    exact (h.frame _ Leave255Shift.layout3.separate).trans zero
  · simp only [if_neg far] at tags
    have h:=Leave255NearHigh.result s m clean zero padding tags
    exact (h.frame _ Leave255Shift.layout3.separate).trans zero

end ECDSAAdd.Entrant.StairPacket.Leave255SignClose


end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth
open SkywalkNat Shadow LeaveCompanion PortalValues
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem truth (b : Nat) (z : SkywalkNat.State) (small:min z.u z.v<2^b) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=(negative sg r.u).toNat
    (decide (2^b≤r.u-e)=decide (2^b≤F.u-e)) ∧
      upperBorrow (2^b) r.u r.v e=upperBorrow (2^b) F.u F.v e ∧
      (F.u-e)%(2*2^b)=(r.u-e)%(2*2^b) ∧
      negative sg F.u=negative sg r.u := by
  let F:=step^[15] z
  let r:=step^[15] (reduced b 15 z)
  let e:=(negative sg r.u).toNat
  have smallE:e≤1:=by cases h : negative sg r.u <;> simp [e,h]
  have low:=LeaveShadowRails.retainedLow b z small sg
  have hi:=(LeaveShadowRails.afterThreshold b z small e smallE).1
  have two : 2*2^b=2^(b+1) := (Nat.mul_comm _ _).trans (pow_succ 2 b).symm
  dsimp only at low hi ⊢
  refine ⟨by apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq];exact hi.symm,?_,?_,low.1⟩
  · unfold upperBorrow
    rw [two,low.2.1,low.2.2]
  · rw [two];exact low.2.2

theorem restored (b k : Nat) (z : SkywalkNat.State) (small:min z.u z.v<2^b) (sg:Bool) :
    let F:=step^[15] z
    let r:=step^[15] (reduced b 15 z)
    let e:=(negative sg r.u).toNat
    ((if 2^b≤r.u-e then ((F.u+F.v)/2^(b+1))%2^k else 0)+2^k-upperBorrow (2^b) r.u r.v e)%2^k =
      ((F.u-e)/2^(b+1))%2^k := by
  let F:=step^[15] z
  let r:=step^[15] (reduced b 15 z)
  let e:=(negative sg r.u).toNat
  have le:e≤1 := by cases h:negative sg r.u <;> simp [e,h]
  have eq:=truth b z small sg
  have pos:0<F.u ↔ 0<r.u := (LeaveShadowRails.afterThreshold b z small e le).2
  have eu:e≤F.u := by
    by_cases h:0<F.u
    · omega
    · have no:¬0<r.u:=fun hr=>h (pos.mpr hr)
      simp [e,negative,no]
  have sm:min F.u F.v<2^b := lt_of_le_of_lt (LeaveShadowRails.min_iter 15 z) small
  have out:=upper_restore (2^b) F.u F.v e (2^k) (Nat.two_pow_pos _) le eu sm (Nat.two_pow_pos _)
  have h:2^b≤r.u-e ↔ 2^b≤F.u-e := (LeaveShadowRails.afterThreshold b z small e le).1.symm
  have two : 2*2^b=2^(b+1) := (Nat.mul_comm _ _).trans (pow_succ 2 b).symm
  change ((if 2^b≤r.u-e then ((F.u+F.v)/2^(b+1))%2^k else 0)+2^k-upperBorrow (2^b) r.u r.v e)%2^k=_
  have bor : upperBorrow (2^b) r.u r.v e=upperBorrow (2^b) F.u F.v e := eq.2.1
  simp only [h,bor]
  simpa only [two] using out

end ECDSAAdd.Entrant.StairPacket.LeaveRestoreTruth


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Core
open Arithmetic Partial Leave225SignClose Leave225Selector LeaveSelector Leave225Barrel Leave225High Leave225Word Leave225Join
open HighBankBarrel Leave225RetireActual Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def work:=((leave225.drop 334).take 1926)
theorem shape : work=extended++fullPostfix false := by decide +kernel
def watched := (List.range' 1559 39)++paritySites++[1724,1721,1722]++(List.range 15).map Leave225Hit.swaps

theorem untouched : ∀q∈watched,q≠1613 ∧ (∀i:Fin 112,q≠wire i.val) ∧
    ∀a∈columns,q≠a.shadow ∧ q≠a.tube := by decide +kernel

attribute [local irreducible] run

private theorem finish (z:SkywalkNat.State) (s a t:State)
    (fix:t=⟨a.phase,writeBit a.basis 1613 false⟩) (clean:s.basis 1613=false)
    (ar:a.phase=s.phase ∧ (∀i<112,a.basis (live i)=(Leave225TrueMiddle.F z).testBit i) ∧
      (∀i:Fin 18,a.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 112 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → a.basis q=s.basis q) :
    t.phase=s.phase ∧ (∀i<112,(cleared t.basis) (live i)=(Leave225TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,(cleared t.basis) (row j).free=false) ∧ (∀j:Fin 39,(cleared t.basis) (1559+j.val)=false) ∧
      (∀q,outside wire 112 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → (cleared t.basis) q=cleared s.basis q) := by
  have base (q:Wire) (diff:q≠1613) : t.basis q=a.basis q := by rw [fix];simp [writeBit,diff]
  have pass (q:Nat) (diff:q≠1613 ∧ ¬(1559≤q ∧ q≤1597)) : cleared t.basis q=a.basis q := by
    rw [cleared,if_neg diff.2];exact base _ diff.1
  refine ⟨(congrArg State.phase fix).trans ar.1,?_,?_,?_,?_⟩
  · intro i h
    have geom : ∀j:Fin 112,live j≠1613 ∧ ¬(1559≤live j ∧ live j≤1597) := by decide +kernel
    exact (pass _ (geom ⟨i,h⟩)).trans (ar.2.1 i h)
  · intro j
    have geom : ∀j:Fin 18,(row j).free≠1613 ∧ ¬(1559≤(row j).free ∧ (row j).free≤1597) := by decide +kernel
    exact (pass _ (geom j)).trans (ar.2.2.1 j)
  · intro j;have h:=j.isLt
    change (if 1559≤1559+j.val ∧ 1559+j.val≤1597 then _ else _)=_
    rw [if_pos (by omega)]
  · intro q out cols
    by_cases eq:q=1613
    · subst q
      change t.basis 1613=s.basis 1613
      rw [fix,clean]
      simp [writeBit]
    · unfold cleared
      split
      · rfl
      · exact (base _ eq).trans (ar.2.2.2 _ eq out cols)


theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool) (k:Mode) (ref:BasisState)
    (small:min z.u z.v<2^144) (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (tag:∀q∈Leave225Join.tags,s.basis q=if Shadow.far 144 15 z then Leave225Word.hot (Leave225TrueMiddle.key z) q else false)
    (shadow:∀i<18,s.basis (401+i)=(Leave225TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (cin:s.basis 1724=if Shadow.far 144 15 z then HighBankSum.cross (Leave225TrueMiddle.d z) else false)
    (sign:Shadow.far 144 15 z → s.basis 1597=Leave225TrueMiddle.neg z)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read ref)
    (parity:∀q∈paritySites,ref q=s.basis q)
    (product:s.basis 1597=(s.basis 1724 && (signExpr ports k).read ref))
    (leftFlag:left k=(s.basis 1721 && s.basis 1722)) (rightFlag:right k=(s.basis 1721 && !s.basis 1722))
    (events:right k=true → ∀i<15,i≤LeaveSelector.key k → s.basis (Leave225Hit.swaps i)=decide (i=LeaveSelector.key k)) :
    let out:=run work tape s
    out.phase=s.phase ∧ (∀i<112,out.basis (live i)=(Leave225TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
      (∀q,outside wire 112 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → out.basis q=cleared s.basis q) := by
  let a:=run Leave225Middle.middle tape s
  let t:=run extended tape s
  have ar:=Leave225TrueMiddle.actual z s tape small odd room clean (clean _ (by decide)) padding tag shadow bank cin sign (clean _ (by decide))
  have fix:=closed z s tape clean padding tag
  change t=⟨a.phase,writeBit a.basis 1613 false⟩ at fix
  have saved (q:Wire) (mem:q∈watched) : t.basis q=s.basis q := by
    obtain ⟨diff,out,cols⟩:=untouched _ mem
    rw [fix];simp only [writeBit,Function.update_of_ne diff]
    exact ar.2.2.2 q diff (fun i hi=>out ⟨i,hi⟩) cols
  have ctl : ∀j:Fin 39,1559+j.val∈watched := by decide +kernel
  have pa : ∀q∈paritySites,q∈watched := by decide +kernel
  have sw : ∀i:Fin 15,Leave225Hit.swaps i∈watched := by decide +kernel
  have retire:=Leave225RetireActual.result k ref t (tape.drop (measurementCount extended))
    (fun j=>(saved _ (ctl ⟨j.val,by have h:=j.isLt;omega⟩)).trans (bits j))
    (fun q h=>(parity q h).trans (saved _ (pa q h)).symm)
    (by rw [saved 1597 (by decide),saved 1724 (by decide)];exact product)
    (by rw [saved 1721 (by decide),saved 1722 (by decide)];exact leftFlag)
    (by rw [saved 1721 (by decide),saved 1722 (by decide)];exact rightFlag)
    (fun on i hi h=>(saved _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take,retire]
  exact finish z s a t fix (clean _ (by decide)) ar

end ECDSAAdd.Entrant.StairPacket.Leave225Core


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Restored
open Arithmetic SkywalkNat Shadow PortalValues LeaveCompanion LeaveCompanion225
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m:List Bool)
    (small:min z.u z.v<2^144) (clean:∀q∈smallC,s.basis q=false) (cleared:regValue smallM s.basis=0)
    (input:let r:=step^[15] (reduced 144 15 z)
           let F:=step^[15] z
           let e:=(negative sg r.u).toNat
           s.basis 1556=decide (2^144≤r.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^144) r.u r.v e ∧
             regValue smallA s.basis=((F.u+F.v)/2^145)%2^10) :
    let F:=step^[15] z
    let e:=(negative sg F.u).toNat
    let out:=run restore m s
    out.phase=s.phase ∧ (∀q,q∉smallM → out.basis q=s.basis q) ∧
      regValue smallM out.basis=((F.u-e)/2^145)%2^10 := by
  have hardware:=restore_run s m clean cleared
  refine ⟨hardware.1,hardware.2.1,hardware.2.2.trans ?_⟩
  dsimp only at input ⊢
  have math:=LeaveRestoreTruth.restored 144 10 z small sg
  have sign:=(LeaveRestoreTruth.truth 144 z small sg).2.2.2
  rw [show smallM.length=10 from rfl,copyValue,input.1,input.2.1,input.2.2,sign]
  simpa only [decide_eq_true_eq] using math

end ECDSAAdd.Entrant.StairPacket.Leave225Restored


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Core
open Arithmetic Partial Leave240SignClose Leave240Selector LeaveSelector Leave240Barrel Leave240High Leave240Word Leave240Join
open HighBankBarrel Leave240RetireActual Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def work:=((leave240.drop 334).take 2061)
theorem shape : work=extended++fullPostfix false := by decide +kernel
def watched := (List.range' 1559 39)++paritySites++[1716,1713,1714]++(List.range 15).map Leave240Hit.swaps

theorem untouched : ∀q∈watched,q≠1613 ∧ (∀i:Fin 120,q≠wire i.val) ∧
    ∀a∈columns,q≠a.shadow ∧ q≠a.tube := by decide +kernel

attribute [local irreducible] run

private theorem finish (z:SkywalkNat.State) (s a t:State)
    (fix:t=⟨a.phase,writeBit a.basis 1613 false⟩) (clean:s.basis 1613=false)
    (ar:a.phase=s.phase ∧ (∀i<120,a.basis (live i)=(Leave240TrueMiddle.F z).testBit i) ∧
      (∀i:Fin 18,a.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 120 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → a.basis q=s.basis q) :
    t.phase=s.phase ∧ (∀i<120,(cleared t.basis) (live i)=(Leave240TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,(cleared t.basis) (row j).free=false) ∧ (∀j:Fin 39,(cleared t.basis) (1559+j.val)=false) ∧
      (∀q,outside wire 120 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → (cleared t.basis) q=cleared s.basis q) := by
  have base (q:Wire) (diff:q≠1613) : t.basis q=a.basis q := by rw [fix];simp [writeBit,diff]
  have pass (q:Nat) (diff:q≠1613 ∧ ¬(1559≤q ∧ q≤1597)) : cleared t.basis q=a.basis q := by
    rw [cleared,if_neg diff.2];exact base _ diff.1
  refine ⟨(congrArg State.phase fix).trans ar.1,?_,?_,?_,?_⟩
  · intro i h
    have geom : ∀j:Fin 120,live j≠1613 ∧ ¬(1559≤live j ∧ live j≤1597) := by decide +kernel
    exact (pass _ (geom ⟨i,h⟩)).trans (ar.2.1 i h)
  · intro j
    have geom : ∀j:Fin 18,(row j).free≠1613 ∧ ¬(1559≤(row j).free ∧ (row j).free≤1597) := by decide +kernel
    exact (pass _ (geom j)).trans (ar.2.2.1 j)
  · intro j;have h:=j.isLt
    change (if 1559≤1559+j.val ∧ 1559+j.val≤1597 then _ else _)=_
    rw [if_pos (by omega)]
  · intro q out cols
    by_cases eq:q=1613
    · subst q
      change t.basis 1613=s.basis 1613
      rw [fix,clean]
      simp [writeBit]
    · unfold cleared
      split
      · rfl
      · exact (base _ eq).trans (ar.2.2.2 _ eq out cols)


theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool) (k:Mode) (ref:BasisState)
    (small:min z.u z.v<2^136) (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (tag:∀q∈Leave240Join.tags,s.basis q=if Shadow.far 136 15 z then Leave240Word.hot (Leave240TrueMiddle.key z) q else false)
    (shadow:∀i<18,s.basis (408+i)=(Leave240TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (cin:s.basis 1716=if Shadow.far 136 15 z then HighBankSum.cross (Leave240TrueMiddle.d z) else false)
    (sign:Shadow.far 136 15 z → s.basis 1597=Leave240TrueMiddle.neg z)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read ref)
    (parity:∀q∈paritySites,ref q=s.basis q)
    (product:s.basis 1597=(s.basis 1716 && (signExpr ports k).read ref))
    (leftFlag:left k=(s.basis 1713 && s.basis 1714)) (rightFlag:right k=(s.basis 1713 && !s.basis 1714))
    (events:right k=true → ∀i<15,i≤LeaveSelector.key k → s.basis (Leave240Hit.swaps i)=decide (i=LeaveSelector.key k)) :
    let out:=run work tape s
    out.phase=s.phase ∧ (∀i<120,out.basis (live i)=(Leave240TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
      (∀q,outside wire 120 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → out.basis q=cleared s.basis q) := by
  let a:=run Leave240Middle.middle tape s
  let t:=run extended tape s
  have ar:=Leave240TrueMiddle.actual z s tape small odd room clean (clean _ (by decide)) padding tag shadow bank cin sign (clean _ (by decide))
  have fix:=closed z s tape clean padding tag
  change t=⟨a.phase,writeBit a.basis 1613 false⟩ at fix
  have saved (q:Wire) (mem:q∈watched) : t.basis q=s.basis q := by
    obtain ⟨diff,out,cols⟩:=untouched _ mem
    rw [fix];simp only [writeBit,Function.update_of_ne diff]
    exact ar.2.2.2 q diff (fun i hi=>out ⟨i,hi⟩) cols
  have ctl : ∀j:Fin 39,1559+j.val∈watched := by decide +kernel
  have pa : ∀q∈paritySites,q∈watched := by decide +kernel
  have sw : ∀i:Fin 15,Leave240Hit.swaps i∈watched := by decide +kernel
  have retire:=Leave240RetireActual.result k ref t (tape.drop (measurementCount extended))
    (fun j=>(saved _ (ctl ⟨j.val,by have h:=j.isLt;omega⟩)).trans (bits j))
    (fun q h=>(parity q h).trans (saved _ (pa q h)).symm)
    (by rw [saved 1597 (by decide),saved 1716 (by decide)];exact product)
    (by rw [saved 1713 (by decide),saved 1714 (by decide)];exact leftFlag)
    (by rw [saved 1713 (by decide),saved 1714 (by decide)];exact rightFlag)
    (fun on i hi h=>(saved _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take,retire]
  exact finish z s a t fix (clean _ (by decide)) ar

end ECDSAAdd.Entrant.StairPacket.Leave240Core


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Restored
open Arithmetic SkywalkNat Shadow PortalValues LeaveCompanion LeaveCompanion240
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m:List Bool)
    (small:min z.u z.v<2^136) (clean:∀q∈smallC,s.basis q=false) (cleared:regValue smallM s.basis=0)
    (input:let r:=step^[15] (reduced 136 15 z)
           let F:=step^[15] z
           let e:=(negative sg r.u).toNat
           s.basis 1556=decide (2^136≤r.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^136) r.u r.v e ∧
             regValue smallA s.basis=((F.u+F.v)/2^137)%2^11) :
    let F:=step^[15] z
    let e:=(negative sg F.u).toNat
    let out:=run restore m s
    out.phase=s.phase ∧ (∀q,q∉smallM → out.basis q=s.basis q) ∧
      regValue smallM out.basis=((F.u-e)/2^137)%2^11 := by
  have hardware:=restore_run s m clean cleared
  refine ⟨hardware.1,hardware.2.1,hardware.2.2.trans ?_⟩
  dsimp only at input ⊢
  have math:=LeaveRestoreTruth.restored 136 11 z small sg
  have sign:=(LeaveRestoreTruth.truth 136 z small sg).2.2.2
  rw [show smallM.length=11 from rfl,copyValue,input.1,input.2.1,input.2.2,sign]
  simpa only [decide_eq_true_eq] using math

end ECDSAAdd.Entrant.StairPacket.Leave240Restored


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Core
open Arithmetic Partial Leave255SignClose Leave255Selector LeaveSelector Leave255Barrel Leave255High Leave255Word Leave255Join
open HighBankBarrel Leave255RetireActual Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

def work:=((leave255.drop 334).take 2181)
theorem shape : work=extended++fullPostfix false := by decide +kernel
def watched := (List.range' 1559 39)++paritySites++[1709,1706,1707]++(List.range 15).map Leave255Hit.swaps

theorem untouched : ∀q∈watched,q≠1613 ∧ (∀i:Fin 127,q≠wire i.val) ∧
    ∀a∈columns,q≠a.shadow ∧ q≠a.tube := by decide +kernel

attribute [local irreducible] run

private theorem finish (z:SkywalkNat.State) (s a t:State)
    (fix:t=⟨a.phase,writeBit a.basis 1613 false⟩) (clean:s.basis 1613=false)
    (ar:a.phase=s.phase ∧ (∀i<127,a.basis (live i)=(Leave255TrueMiddle.F z).testBit i) ∧
      (∀i:Fin 18,a.basis (row i).free=false) ∧
      ∀q,q≠1613 → outside wire 127 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → a.basis q=s.basis q) :
    t.phase=s.phase ∧ (∀i<127,(cleared t.basis) (live i)=(Leave255TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,(cleared t.basis) (row j).free=false) ∧ (∀j:Fin 39,(cleared t.basis) (1559+j.val)=false) ∧
      (∀q,outside wire 127 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → (cleared t.basis) q=cleared s.basis q) := by
  have base (q:Wire) (diff:q≠1613) : t.basis q=a.basis q := by rw [fix];simp [writeBit,diff]
  have pass (q:Nat) (diff:q≠1613 ∧ ¬(1559≤q ∧ q≤1597)) : cleared t.basis q=a.basis q := by
    rw [cleared,if_neg diff.2];exact base _ diff.1
  refine ⟨(congrArg State.phase fix).trans ar.1,?_,?_,?_,?_⟩
  · intro i h
    have geom : ∀j:Fin 127,live j≠1613 ∧ ¬(1559≤live j ∧ live j≤1597) := by decide +kernel
    exact (pass _ (geom ⟨i,h⟩)).trans (ar.2.1 i h)
  · intro j
    have geom : ∀j:Fin 18,(row j).free≠1613 ∧ ¬(1559≤(row j).free ∧ (row j).free≤1597) := by decide +kernel
    exact (pass _ (geom j)).trans (ar.2.2.1 j)
  · intro j;have h:=j.isLt
    change (if 1559≤1559+j.val ∧ 1559+j.val≤1597 then _ else _)=_
    rw [if_pos (by omega)]
  · intro q out cols
    by_cases eq:q=1613
    · subst q
      change t.basis 1613=s.basis 1613
      rw [fix,clean]
      simp [writeBit]
    · unfold cleared
      split
      · rfl
      · exact (base _ eq).trans (ar.2.2.2 _ eq out cols)


theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool) (k:Mode) (ref:BasisState)
    (small:min z.u z.v<2^129) (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (tag:∀q∈Leave255Join.tags,s.basis q=if Shadow.far 129 15 z then Leave255Word.hot (Leave255TrueMiddle.key z) q else false)
    (shadow:∀i<18,s.basis (416+i)=(Leave255TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (cin:s.basis 1709=if Shadow.far 129 15 z then HighBankSum.cross (Leave255TrueMiddle.d z) else false)
    (sign:Shadow.far 129 15 z → s.basis 1597=Leave255TrueMiddle.neg z)
    (bits:∀j:Fin 38,s.basis (1559+j.val)=(prior k (1559+j.val)).read ref)
    (parity:∀q∈paritySites,ref q=s.basis q)
    (product:s.basis 1597=(s.basis 1709 && (signExpr ports k).read ref))
    (leftFlag:left k=(s.basis 1706 && s.basis 1707)) (rightFlag:right k=(s.basis 1706 && !s.basis 1707))
    (events:right k=true → ∀i<15,i≤LeaveSelector.key k → s.basis (Leave255Hit.swaps i)=decide (i=LeaveSelector.key k)) :
    let out:=run work tape s
    out.phase=s.phase ∧ (∀i<127,out.basis (live i)=(Leave255TrueMiddle.F z).testBit i) ∧
      (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
      (∀q,outside wire 127 q → (∀a∈columns,q≠a.shadow ∧ q≠a.tube) → out.basis q=cleared s.basis q) := by
  let a:=run Leave255Middle.middle tape s
  let t:=run extended tape s
  have ar:=Leave255TrueMiddle.actual z s tape small odd room clean (clean _ (by decide)) padding tag shadow bank cin sign (clean _ (by decide))
  have fix:=closed z s tape clean padding tag
  change t=⟨a.phase,writeBit a.basis 1613 false⟩ at fix
  have saved (q:Wire) (mem:q∈watched) : t.basis q=s.basis q := by
    obtain ⟨diff,out,cols⟩:=untouched _ mem
    rw [fix];simp only [writeBit,Function.update_of_ne diff]
    exact ar.2.2.2 q diff (fun i hi=>out ⟨i,hi⟩) cols
  have ctl : ∀j:Fin 39,1559+j.val∈watched := by decide +kernel
  have pa : ∀q∈paritySites,q∈watched := by decide +kernel
  have sw : ∀i:Fin 15,Leave255Hit.swaps i∈watched := by decide +kernel
  have retire:=Leave255RetireActual.result k ref t (tape.drop (measurementCount extended))
    (fun j=>(saved _ (ctl ⟨j.val,by have h:=j.isLt;omega⟩)).trans (bits j))
    (fun q h=>(parity q h).trans (saved _ (pa q h)).symm)
    (by rw [saved 1597 (by decide),saved 1709 (by decide)];exact product)
    (by rw [saved 1706 (by decide),saved 1707 (by decide)];exact leftFlag)
    (by rw [saved 1706 (by decide),saved 1707 (by decide)];exact rightFlag)
    (fun on i hi h=>(saved _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take,retire]
  exact finish z s a t fix (clean _ (by decide)) ar

end ECDSAAdd.Entrant.StairPacket.Leave255Core


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Restored
open Arithmetic SkywalkNat Shadow PortalValues LeaveCompanion LeaveCompanion255
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m:List Bool)
    (small:min z.u z.v<2^129) (clean:∀q∈smallC,s.basis q=false) (cleared:regValue smallM s.basis=0)
    (input:let r:=step^[15] (reduced 129 15 z)
           let F:=step^[15] z
           let e:=(negative sg r.u).toNat
           s.basis 1556=decide (2^129≤r.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^129) r.u r.v e ∧
             regValue smallA s.basis=((F.u+F.v)/2^130)%2^10) :
    let F:=step^[15] z
    let e:=(negative sg F.u).toNat
    let out:=run restore m s
    out.phase=s.phase ∧ (∀q,q∉smallM → out.basis q=s.basis q) ∧
      regValue smallM out.basis=((F.u-e)/2^130)%2^10 := by
  have hardware:=restore_run s m clean cleared
  refine ⟨hardware.1,hardware.2.1,hardware.2.2.trans ?_⟩
  dsimp only at input ⊢
  have math:=LeaveRestoreTruth.restored 129 10 z small sg
  have sign:=(LeaveRestoreTruth.truth 129 z small sg).2.2.2
  rw [show smallM.length=10 from rfl,copyValue,input.1,input.2.1,input.2.2,sign]
  simpa only [decide_eq_true_eq] using math

end ECDSAAdd.Entrant.StairPacket.Leave255Restored


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Routed
open Arithmetic Partial IntegerHigh LeaveSelector Leave225Selector Leave225RetireActual Leave225Barrel Leave225High Leave225Word Leave225Join
open LeaveReadoutFrame Leave225OutputPorts HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def body:Program := (leave225.drop 242).take 2018
theorem shape : body=fullPrefix false++Leave225Core.work := by decide +kernel
def untouched (q:Wire) := q∉(fullPrefix false).map destination
instance (q:Wire):Decidable (untouched q) := inferInstanceAs (Decidable (q∉_))
attribute [local irreducible] run

theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool)
    (small:min z.u z.v<2^144) (odd:z.v%2=1) (room:Shadow.high 144 15 z+1<2^97)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,97 ≤ i → i<112 → s.basis (wire i)=false)
    (shadow:∀i<18,s.basis (401+i)=(Leave225TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 144 15 z then Shadow.high 144 15 z else 0)
    (zero:∀q∈[ports.crossing,ports.near]++List.range' 1559 39,s.basis q=false)
    (par:parityBits ports s.basis=oddBits (IntegerHigh.letters 15 (Shadow.reduced 144 15 z)))
    (mode:actualMode 144 z=farMode (s.basis 1721) (s.basis 1722) z.u)
    (events:right (actualMode 144 z)=true → ∀i<15,i≤LeaveSelector.key (actualMode 144 z) → s.basis (Leave225Hit.swaps i)=decide (i=LeaveSelector.key (actualMode 144 z))) :
    let out:=run body tape s
    let t:=run (fullPrefix false) tape s
    out.phase=s.phase ∧ (∀i<112,out.basis (live i)=(Leave225TrueMiddle.F z).testBit i) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀q,outside wire 112 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → out.basis q=cleared t.basis q) := by
  let k:=actualMode 144 z
  let t:=run (fullPrefix false) tape s
  have base : ∀q:Nat,1561≤q → q≤1597 → s.basis q=false := by
    intro q lo hi
    apply zero
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  have prepared:t=⟨s.phase,fun q=>(prior k q).read s.basis⟩ := preparedState false s tape s.basis z.u k mode
    (zero _ (by decide)) (zero _ (by decide))
    (beforeFresh _ _ _ base (zero _ (by decide)) (zero _ (by decide))) events
  have sym (q:Wire):t.basis q=(prior k q).read s.basis := congrArg (fun st:State=>st.basis q) prepared
  have keep (q:Wire) (ok:untouched q) : t.basis q=s.basis q := preserved _ s tape q ok
  have cs : ∀q∈carries,untouched q := by decide +kernel
  have pad : ∀i:Fin 112,97 ≤ i.val → untouched (wire i) := by decide +kernel
  have sh : ∀i:Fin 18,untouched (401+i.val) := by decide +kernel
  have ysOK : ∀q∈ys,untouched q := by decide +kernel
  have pa : ∀q∈paritySites,untouched q := by decide +kernel
  have sw : ∀i:Fin 15,untouched (Leave225Hit.swaps i) := by decide +kernel
  have math:=Leave225Loaded.signed z s.basis small odd room (fun i hi=>shadow i (Nat.lt_trans hi (by decide : 16<18))) par
  have flags:=mode_flags (s.basis 1721) (s.basis 1722) (⟨IntegerHigh.wait 15 z.u, by have h:=IntegerHigh.wait_le 15 z.u;omega⟩:Fin 16)
  have leftOK:left k=(t.basis 1721 && t.basis 1722) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.1
  have rightOK:right k=(t.basis 1721 && !t.basis 1722) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.2.1
  have done:=Leave225Core.result z t (tape.drop (measurementCount (fullPrefix false))) k s.basis small odd room
    (fun q h=>(keep _ (cs q h)).trans (clean q h)) (fun i lo hi=>(keep _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (fun q h=>(sym q).trans (Leave225Loaded.tags z s.basis q h)) (fun i h=>(keep _ (sh ⟨i,h⟩)).trans (shadow i h))
    (((regValue_eq_iff _ _ _).mpr (fun q h=>keep _ (ysOK q h))).trans bank)
    ((sym _).trans math.1) (fun far=>(sym _).trans (math.2.2 far)) (fun j=>sym _)
    (fun q h=>(keep _ (pa q h)).symm) (by rw [sym 1597,sym 1724]; exact math.2.1) leftOK rightOK
    (fun on i hi h=>(keep _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans (by rw [prepared]),done.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave225Routed


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Routed
open Arithmetic Partial IntegerHigh LeaveSelector Leave240Selector Leave240RetireActual Leave240Barrel Leave240High Leave240Word Leave240Join
open LeaveReadoutFrame Leave240OutputPorts HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def body:Program := (leave240.drop 242).take 2153
theorem shape : body=fullPrefix false++Leave240Core.work := by decide +kernel
def untouched (q:Wire) := q∉(fullPrefix false).map destination
instance (q:Wire):Decidable (untouched q) := inferInstanceAs (Decidable (q∉_))
attribute [local irreducible] run

theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool)
    (small:min z.u z.v<2^136) (odd:z.v%2=1) (room:Shadow.high 136 15 z+1<2^105)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,105 ≤ i → i<120 → s.basis (wire i)=false)
    (shadow:∀i<18,s.basis (408+i)=(Leave240TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 136 15 z then Shadow.high 136 15 z else 0)
    (zero:∀q∈[ports.crossing,ports.near]++List.range' 1559 39,s.basis q=false)
    (par:parityBits ports s.basis=oddBits (IntegerHigh.letters 15 (Shadow.reduced 136 15 z)))
    (mode:actualMode 136 z=farMode (s.basis 1713) (s.basis 1714) z.u)
    (events:right (actualMode 136 z)=true → ∀i<15,i≤LeaveSelector.key (actualMode 136 z) → s.basis (Leave240Hit.swaps i)=decide (i=LeaveSelector.key (actualMode 136 z))) :
    let out:=run body tape s
    let t:=run (fullPrefix false) tape s
    out.phase=s.phase ∧ (∀i<120,out.basis (live i)=(Leave240TrueMiddle.F z).testBit i) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀q,outside wire 120 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → out.basis q=cleared t.basis q) := by
  let k:=actualMode 136 z
  let t:=run (fullPrefix false) tape s
  have base : ∀q:Nat,1561≤q → q≤1597 → s.basis q=false := by
    intro q lo hi
    apply zero
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  have prepared:t=⟨s.phase,fun q=>(prior k q).read s.basis⟩ := preparedState false s tape s.basis z.u k mode
    (zero _ (by decide)) (zero _ (by decide))
    (beforeFresh _ _ _ base (zero _ (by decide)) (zero _ (by decide))) events
  have sym (q:Wire):t.basis q=(prior k q).read s.basis := congrArg (fun st:State=>st.basis q) prepared
  have keep (q:Wire) (ok:untouched q) : t.basis q=s.basis q := preserved _ s tape q ok
  have cs : ∀q∈carries,untouched q := by decide +kernel
  have pad : ∀i:Fin 120,105 ≤ i.val → untouched (wire i) := by decide +kernel
  have sh : ∀i:Fin 18,untouched (408+i.val) := by decide +kernel
  have ysOK : ∀q∈ys,untouched q := by decide +kernel
  have pa : ∀q∈paritySites,untouched q := by decide +kernel
  have sw : ∀i:Fin 15,untouched (Leave240Hit.swaps i) := by decide +kernel
  have math:=Leave240Loaded.signed z s.basis small odd room (fun i hi=>shadow i (Nat.lt_trans hi (by decide : 16<18))) par
  have flags:=mode_flags (s.basis 1713) (s.basis 1714) (⟨IntegerHigh.wait 15 z.u, by have h:=IntegerHigh.wait_le 15 z.u;omega⟩:Fin 16)
  have leftOK:left k=(t.basis 1713 && t.basis 1714) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.1
  have rightOK:right k=(t.basis 1713 && !t.basis 1714) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.2.1
  have done:=Leave240Core.result z t (tape.drop (measurementCount (fullPrefix false))) k s.basis small odd room
    (fun q h=>(keep _ (cs q h)).trans (clean q h)) (fun i lo hi=>(keep _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (fun q h=>(sym q).trans (Leave240Loaded.tags z s.basis q h)) (fun i h=>(keep _ (sh ⟨i,h⟩)).trans (shadow i h))
    (((regValue_eq_iff _ _ _).mpr (fun q h=>keep _ (ysOK q h))).trans bank)
    ((sym _).trans math.1) (fun far=>(sym _).trans (math.2.2 far)) (fun j=>sym _)
    (fun q h=>(keep _ (pa q h)).symm) (by rw [sym 1597,sym 1716]; exact math.2.1) leftOK rightOK
    (fun on i hi h=>(keep _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans (by rw [prepared]),done.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave240Routed


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Routed
open Arithmetic Partial IntegerHigh LeaveSelector Leave255Selector Leave255RetireActual Leave255Barrel Leave255High Leave255Word Leave255Join
open LeaveReadoutFrame Leave255OutputPorts HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

def body:Program := (leave255.drop 242).take 2273
theorem shape : body=fullPrefix false++Leave255Core.work := by decide +kernel
def untouched (q:Wire) := q∉(fullPrefix false).map destination
instance (q:Wire):Decidable (untouched q) := inferInstanceAs (Decidable (q∉_))
attribute [local irreducible] run

theorem result (z:SkywalkNat.State) (s:State) (tape:List Bool)
    (small:min z.u z.v<2^129) (odd:z.v%2=1) (room:Shadow.high 129 15 z+1<2^112)
    (clean:∀q∈carries,s.basis q=false)
    (padding:∀i:Nat,112 ≤ i → i<127 → s.basis (wire i)=false)
    (shadow:∀i<18,s.basis (416+i)=(Leave255TrueMiddle.X z).testBit i)
    (bank:regValue ys s.basis=if Shadow.far 129 15 z then Shadow.high 129 15 z else 0)
    (zero:∀q∈[ports.crossing,ports.near]++List.range' 1559 39,s.basis q=false)
    (par:parityBits ports s.basis=oddBits (IntegerHigh.letters 15 (Shadow.reduced 129 15 z)))
    (mode:actualMode 129 z=farMode (s.basis 1706) (s.basis 1707) z.u)
    (events:right (actualMode 129 z)=true → ∀i<15,i≤LeaveSelector.key (actualMode 129 z) → s.basis (Leave255Hit.swaps i)=decide (i=LeaveSelector.key (actualMode 129 z))) :
    let out:=run body tape s
    let t:=run (fullPrefix false) tape s
    out.phase=s.phase ∧ (∀i<127,out.basis (live i)=(Leave255TrueMiddle.F z).testBit i) ∧
    (∀j:Fin 18,out.basis (row j).free=false) ∧ (∀j:Fin 39,out.basis (1559+j.val)=false) ∧
    (∀q,outside wire 127 q → (∀r∈columns,q≠r.shadow ∧ q≠r.tube) → out.basis q=cleared t.basis q) := by
  let k:=actualMode 129 z
  let t:=run (fullPrefix false) tape s
  have base : ∀q:Nat,1561≤q → q≤1597 → s.basis q=false := by
    intro q lo hi
    apply zero
    apply List.mem_append_right
    rw [List.mem_range']; exact ⟨q-1559,by omega,by omega⟩
  have prepared:t=⟨s.phase,fun q=>(prior k q).read s.basis⟩ := preparedState false s tape s.basis z.u k mode
    (zero _ (by decide)) (zero _ (by decide))
    (beforeFresh _ _ _ base (zero _ (by decide)) (zero _ (by decide))) events
  have sym (q:Wire):t.basis q=(prior k q).read s.basis := congrArg (fun st:State=>st.basis q) prepared
  have keep (q:Wire) (ok:untouched q) : t.basis q=s.basis q := preserved _ s tape q ok
  have cs : ∀q∈carries,untouched q := by decide +kernel
  have pad : ∀i:Fin 127,112 ≤ i.val → untouched (wire i) := by decide +kernel
  have sh : ∀i:Fin 18,untouched (416+i.val) := by decide +kernel
  have ysOK : ∀q∈ys,untouched q := by decide +kernel
  have pa : ∀q∈paritySites,untouched q := by decide +kernel
  have sw : ∀i:Fin 15,untouched (Leave255Hit.swaps i) := by decide +kernel
  have math:=Leave255Loaded.signed z s.basis small odd room (fun i hi=>shadow i (Nat.lt_trans hi (by decide : 16<18))) par
  have flags:=mode_flags (s.basis 1706) (s.basis 1707) (⟨IntegerHigh.wait 15 z.u, by have h:=IntegerHigh.wait_le 15 z.u;omega⟩:Fin 16)
  have leftOK:left k=(t.basis 1706 && t.basis 1707) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.1
  have rightOK:right k=(t.basis 1706 && !t.basis 1707) := by rw [keep _ (by decide),keep _ (by decide),show k=_ from mode]; exact flags.2.1
  have done:=Leave255Core.result z t (tape.drop (measurementCount (fullPrefix false))) k s.basis small odd room
    (fun q h=>(keep _ (cs q h)).trans (clean q h)) (fun i lo hi=>(keep _ (pad ⟨i,hi⟩ lo)).trans (padding i lo hi))
    (fun q h=>(sym q).trans (Leave255Loaded.tags z s.basis q h)) (fun i h=>(keep _ (sh ⟨i,h⟩)).trans (shadow i h))
    (((regValue_eq_iff _ _ _).mpr (fun q h=>keep _ (ysOK q h))).trans bank)
    ((sym _).trans math.1) (fun far=>(sym _).trans (math.2.2 far)) (fun j=>sym _)
    (fun q h=>(keep _ (pa q h)).symm) (by rw [sym 1597,sym 1709]; exact math.2.1) leftOK rightOK
    (fun on i hi h=>(keep _ (sw ⟨i,hi⟩)).trans (events on i hi h))
  dsimp only
  rw [shape,run_append,run_take]
  exact ⟨done.1.trans (by rw [prepared]),done.2⟩

end ECDSAAdd.Entrant.StairPacket.Leave255Routed


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RoutedRestore
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225OutputPorts LeaveReadoutFrame
open Leave225Routed SkywalkNat
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retained : ∀q∈1556::1558::smallM,q∉Leave225Routed.body.map destination := by decide +kernel
theorem carryIndex : ∀q∈smallC,∃i:Fin 39,q=1559+i.val := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m m':List Bool)
    (small:min z.u z.v<2^144) (mag0:regValue fullM s.basis=0)
    (flags:let a:=step^[15] (Shadow.reduced 144 15 z)
           let e:=(negative sg a.u).toNat
           s.basis 1556=decide (2^144≤a.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^144) a.u a.v e)
    (liveBits:∀i<112,(run Leave225Routed.body m s).basis (live i)=(Leave225TrueMiddle.F z).testBit i)
    (retired:∀i:Fin 39,(run Leave225Routed.body m s).basis (1559+i.val)=false) :
    let a:=step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let u:=run Leave225Routed.body m s
    let v:=run restore m' u
    v.phase=u.phase ∧ (∀q,q∉smallM → v.basis q=u.basis q) ∧
      regValue smallM v.basis=(mag/2^145)%2^10 ∧
      v.basis 1556=decide (2^144≤mag) ∧ (∀i<112,v.basis (live i)=(Leave225TrueMiddle.F z).testBit i) := by
  let u:=run Leave225Routed.body m s
  have keep (q:Wire) (h:q∈1556::1558::smallM) : u.basis q=s.basis q := preserved _ _ _ q (retained q h)
  have clear:∀q∈smallC,u.basis q=false := by
    intro q h
    obtain ⟨i,rfl⟩:=carryIndex q h
    exact retired i
  have mag:regValue smallM u.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q h
    exact (keep q (by simp [h])).trans ((regValue_zero _ _).mp mag0 q ((by decide +kernel : ∀q∈smallM,q∈fullM) q h))
  have reg:=(outputRegisters u (Leave225TrueMiddle.F z) liveBits).1
  have old:= (keep 1556 (by decide)).trans flags.1
  have new:=Leave225Restored.result z sg u m' small clear mag
    ⟨old,(congrArg Bool.toNat (keep 1558 (by decide))).trans flags.2,reg⟩
  have ch:=LeaveRestoreTruth.truth 144 z small sg
  refine ⟨new.1,new.2.1,new.2.2,?_,?_⟩
  · rw [new.2.1 _ (by decide),old,ch.1,ch.2.2.2]
  · intro i hi
    have outside:∀j:Fin 112,live j∉smallM := by decide +kernel
    exact (new.2.1 _ (outside ⟨i,hi⟩)).trans (liveBits i hi)

end ECDSAAdd.Entrant.StairPacket.Leave225RoutedRestore


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RoutedRestore
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240OutputPorts LeaveReadoutFrame
open Leave240Routed SkywalkNat
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retained : ∀q∈1556::1558::smallM,q∉Leave240Routed.body.map destination := by decide +kernel
theorem carryIndex : ∀q∈smallC,∃i:Fin 39,q=1559+i.val := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m m':List Bool)
    (small:min z.u z.v<2^136) (mag0:regValue fullM s.basis=0)
    (flags:let a:=step^[15] (Shadow.reduced 136 15 z)
           let e:=(negative sg a.u).toNat
           s.basis 1556=decide (2^136≤a.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^136) a.u a.v e)
    (liveBits:∀i<120,(run Leave240Routed.body m s).basis (live i)=(Leave240TrueMiddle.F z).testBit i)
    (retired:∀i:Fin 39,(run Leave240Routed.body m s).basis (1559+i.val)=false) :
    let a:=step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let u:=run Leave240Routed.body m s
    let v:=run restore m' u
    v.phase=u.phase ∧ (∀q,q∉smallM → v.basis q=u.basis q) ∧
      regValue smallM v.basis=(mag/2^137)%2^11 ∧
      v.basis 1556=decide (2^136≤mag) ∧ (∀i<120,v.basis (live i)=(Leave240TrueMiddle.F z).testBit i) := by
  let u:=run Leave240Routed.body m s
  have keep (q:Wire) (h:q∈1556::1558::smallM) : u.basis q=s.basis q := preserved _ _ _ q (retained q h)
  have clear:∀q∈smallC,u.basis q=false := by
    intro q h
    obtain ⟨i,rfl⟩:=carryIndex q h
    exact retired i
  have mag:regValue smallM u.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q h
    exact (keep q (by simp [h])).trans ((regValue_zero _ _).mp mag0 q ((by decide +kernel : ∀q∈smallM,q∈fullM) q h))
  have reg:=(outputRegisters u (Leave240TrueMiddle.F z) liveBits).1
  have old:= (keep 1556 (by decide)).trans flags.1
  have new:=Leave240Restored.result z sg u m' small clear mag
    ⟨old,(congrArg Bool.toNat (keep 1558 (by decide))).trans flags.2,reg⟩
  have ch:=LeaveRestoreTruth.truth 136 z small sg
  refine ⟨new.1,new.2.1,new.2.2,?_,?_⟩
  · rw [new.2.1 _ (by decide),old,ch.1,ch.2.2.2]
  · intro i hi
    have outside:∀j:Fin 120,live j∉smallM := by decide +kernel
    exact (new.2.1 _ (outside ⟨i,hi⟩)).trans (liveBits i hi)

end ECDSAAdd.Entrant.StairPacket.Leave240RoutedRestore


end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RoutedRestore
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255OutputPorts LeaveReadoutFrame
open Leave255Routed SkywalkNat
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

theorem retained : ∀q∈1556::1558::smallM,q∉Leave255Routed.body.map destination := by decide +kernel
theorem carryIndex : ∀q∈smallC,∃i:Fin 39,q=1559+i.val := by decide +kernel
attribute [local irreducible] run SkywalkNat.step

theorem result (z:SkywalkNat.State) (sg:Bool) (s:ECDSAAdd.State) (m m':List Bool)
    (small:min z.u z.v<2^129) (mag0:regValue fullM s.basis=0)
    (flags:let a:=step^[15] (Shadow.reduced 129 15 z)
           let e:=(negative sg a.u).toNat
           s.basis 1556=decide (2^129≤a.u-e) ∧ (s.basis 1558).toNat=upperBorrow (2^129) a.u a.v e)
    (liveBits:∀i<127,(run Leave255Routed.body m s).basis (live i)=(Leave255TrueMiddle.F z).testBit i)
    (retired:∀i:Fin 39,(run Leave255Routed.body m s).basis (1559+i.val)=false) :
    let a:=step^[15] z
    let mag:=a.u-(negative sg a.u).toNat
    let u:=run Leave255Routed.body m s
    let v:=run restore m' u
    v.phase=u.phase ∧ (∀q,q∉smallM → v.basis q=u.basis q) ∧
      regValue smallM v.basis=(mag/2^130)%2^10 ∧
      v.basis 1556=decide (2^129≤mag) ∧ (∀i<127,v.basis (live i)=(Leave255TrueMiddle.F z).testBit i) := by
  let u:=run Leave255Routed.body m s
  have keep (q:Wire) (h:q∈1556::1558::smallM) : u.basis q=s.basis q := preserved _ _ _ q (retained q h)
  have clear:∀q∈smallC,u.basis q=false := by
    intro q h
    obtain ⟨i,rfl⟩:=carryIndex q h
    exact retired i
  have mag:regValue smallM u.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q h
    exact (keep q (by simp [h])).trans ((regValue_zero _ _).mp mag0 q ((by decide +kernel : ∀q∈smallM,q∈fullM) q h))
  have reg:=(outputRegisters u (Leave255TrueMiddle.F z) liveBits).1
  have old:= (keep 1556 (by decide)).trans flags.1
  have new:=Leave255Restored.result z sg u m' small clear mag
    ⟨old,(congrArg Bool.toNat (keep 1558 (by decide))).trans flags.2,reg⟩
  have ch:=LeaveRestoreTruth.truth 129 z small sg
  refine ⟨new.1,new.2.1,new.2.2,?_,?_⟩
  · rw [new.2.1 _ (by decide),old,ch.1,ch.2.2.2]
  · intro i hi
    have outside:∀j:Fin 127,live j∉smallM := by decide +kernel
    exact (new.2.1 _ (outside ⟨i,hi⟩)).trans (liveBits i hi)

end ECDSAAdd.Entrant.StairPacket.Leave255RoutedRestore


end
