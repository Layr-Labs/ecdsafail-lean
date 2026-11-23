import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Arithmetic.SkywalkIntegerTick
import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Submission.Entrant.MainPart07Core
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Arithmetic.SignedRecordProgram
import ECDSAAdd.Framework.Cost
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Math.SkywalkTrace

-- ==== part Window ====
-- Window = PrizeLeave225Join2ee362a ++ PrizeTail46901f669 ++ PrizeTail227303371 ++ PrizeTail10d9efffc.a
-- ==== begin PrizeLeave225Join2ee362a ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Join
open HighBankJoin Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225Join

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Join
open HighBankJoin Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240Join

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterLimb

def guardWord (m h w : Nat) (far long : Bool) :=
  let a:=h%8
  let na:=if far then 2 else a
  (((((m%8+w)%8) ^^^ (if long then a else 0) ^^^ (if long then na else 0))+8-w)%8)

/-- A far numerator loses an exact multiple of U. Its low limb is intact and
its next digit is two. A far denominator receives the identical decrement
exactly when the long coordinate is u. -/
theorem limbs (U X M w : Nat) (positive:0<U) (bw:w≤1) (long:Bool)
    (far:3≤X/U) (same:long=true → X/U=M/U+w) :
    let d:=(X/U-2)*U
    (X-d)%U=X%U ∧ (X-d)/U=2 ∧
    (M-(if long then d else 0))%U=M%U ∧
    ((M-(if long then d else 0))/U)%8=guardWord (M/U) (X/U) w true long := by
  let H:=X/U
  let D:=(H-2)*U
  have hx:=Nat.mod_add_div X U
  have xm:=Nat.mod_lt X positive
  have splitX:U*H=D+U*2 := by
    change U*H=(H-2)*U+U*2
    rw [Nat.mul_comm (H-2) U,←Nat.mul_add,show H-2+2=H by change 3≤H at far;omega]
  have rx:X-D=X%U+U*2:=by change X%U+U*H=X at hx;omega
  dsimp only
  change (X-D)%U=X%U ∧ (X-D)/U=2 ∧ _
  rw [rx,Nat.add_mul_mod_self_left,Nat.mod_mod,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt xm,Nat.zero_add]
  refine ⟨rfl,rfl,?_⟩
  cases long with
  | false =>
    simp [guardWord,Nat.add_mod]
    omega
  | true =>
    have eq:H=M/U+w:=same rfl
    have ym:=Nat.mod_lt M positive
    have hy:=Nat.mod_add_div M U
    have q:M/U=(H-2)+(2-w):=by change 3≤H at far; omega
    have splitM:U*(M/U)=D+U*(2-w) := by rw [q,Nat.mul_add,Nat.mul_comm U (H-2)]
    have ry:M-D=M%U+U*(2-w):=by omega
    change (M-D)%U=M%U ∧ ((M-D)/U)%8=_
    rw [ry,Nat.add_mul_mod_self_left,Nat.mod_mod,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt ym,Nat.zero_add]
    refine ⟨rfl,?_⟩
    have eqMod:((M/U)%8+w)%8=H%8:=by rw [eq,Nat.mod_add_mod]
    change (2-w)%8=(((M/U%8+w)%8 ^^^ H%8 ^^^ 2)+8-w)%8
    rw [eqMod,Nat.xor_self,Nat.zero_xor]
    omega

theorem unchanged (M H w : Nat) (bw:w≤1) (long:Bool) :
    guardWord M H w false long=M%8 := by
  cases long <;> simp [guardWord] <;> omega

/-- margin 17 (T1): the far digit of the reduced numerator is one (gap (H-1)U), not two. -/
def guardWord17 (m h w : Nat) (far long : Bool) :=
  let a:=h%8
  let na:=if far then 1 else a
  (((((m%8+w)%8) ^^^ (if long then a else 0) ^^^ (if long then na else 0))+8-w)%8)

theorem limbs17 (U X M w : Nat) (positive:0<U) (bw:w≤1) (long:Bool)
    (far:2≤X/U) (same:long=true → X/U=M/U+w) :
    let d:=(X/U-1)*U
    (X-d)%U=X%U ∧ (X-d)/U=1 ∧
    (M-(if long then d else 0))%U=M%U ∧
    ((M-(if long then d else 0))/U)%8=guardWord17 (M/U) (X/U) w true long := by
  let H:=X/U
  let D:=(H-1)*U
  have hx:=Nat.mod_add_div X U
  have xm:=Nat.mod_lt X positive
  have splitX:U*H=D+U*1 := by
    change U*H=(H-1)*U+U*1
    rw [Nat.mul_comm (H-1) U,←Nat.mul_add,show H-1+1=H by change 2≤H at far;omega]
  have rx:X-D=X%U+U*1:=by change X%U+U*H=X at hx;omega
  dsimp only
  change (X-D)%U=X%U ∧ (X-D)/U=1 ∧ _
  rw [rx,Nat.add_mul_mod_self_left,Nat.mod_mod,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt xm,Nat.zero_add]
  refine ⟨rfl,rfl,?_⟩
  cases long with
  | false =>
    simp [guardWord17,Nat.add_mod]
    omega
  | true =>
    have eq:H=M/U+w:=same rfl
    have ym:=Nat.mod_lt M positive
    have hy:=Nat.mod_add_div M U
    have q:M/U=(H-1)+(1-w):=by change 2≤H at far; omega
    have splitM:U*(M/U)=D+U*(1-w) := by rw [q,Nat.mul_add,Nat.mul_comm U (H-1)]
    have ry:M-D=M%U+U*(1-w):=by omega
    change (M-D)%U=M%U ∧ ((M-D)/U)%8=_
    rw [ry,Nat.add_mul_mod_self_left,Nat.mod_mod,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt ym,Nat.zero_add]
    refine ⟨rfl,?_⟩
    have eqMod:((M/U)%8+w)%8=H%8:=by rw [eq,Nat.mod_add_mod]
    change (1-w)%8=(((M/U%8+w)%8 ^^^ H%8 ^^^ 1)+8-w)%8
    rw [eqMod,Nat.xor_self,Nat.zero_xor]
    omega

theorem unchanged17 (M H w : Nat) (bw:w≤1) (long:Bool) :
    guardWord17 M H w false long=M%8 := by
  cases long <;> simp [guardWord17] <;> omega



end ECDSAAdd.Entrant.StairPacket.EnterLimb

end


section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Shift
open Partial HighBankLookup
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225Shift

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Shift
open Partial HighBankLookup
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240Shift

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

def wordPos (L:SkywalkIntegerLayout) (g:Bool) := if g then L.b else L.a
def wordSigned (L:SkywalkIntegerLayout) (g:Bool) := if g then L.a else L.b
def negative (sg:Bool) (u:Nat) := sg && decide (0<u)

theorem mathematical (L:SkywalkIntegerLayout) (g sg:Bool) (u v:Nat) (s:BasisState)
    (h:SkywalkIntegerInput L (SkywalkRails.encode g sg u v).a (SkywalkRails.encode g sg u v).b g s) :
    let e:=negative sg u
    s L.previous=g ∧ (s L.aSign ^^ s L.bSign)=e ∧
    regValue (wordPos L g) s=u+v ∧
    regValue (wordSigned L g) (fun q=>s q ^^ e)=u-e.toNat := by
  obtain ⟨a,b,g0,_⟩:=h
  have orient (lo:List Wire) (sign:Wire) (signed:signedRegValue (lo++[sign]) s=SkywalkRails.signed sg u) :
      s sign=negative sg u ∧ regValue (lo++[sign]) (fun q=>s q ^^ negative sg u)=u-(negative sg u).toNat := by
    have h:=full lo sign s _ signed
    have n:SkywalkRails.neg (SkywalkRails.signed sg u)=negative sg u := by
      cases sg <;> simp [SkywalkRails.neg,SkywalkRails.signed,negative]
    have r:s sign=negative sg u:=h.1.trans n
    rw [r] at h
    have mag:(SkywalkRails.signed sg u).natAbs=u:=by cases sg <;> simp [SkywalkRails.signed]
    exact ⟨r,by simpa only [mag] using h.2⟩
  cases g with
  | false =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=(u:Int)+v at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=SkywalkRails.signed sg u at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using a)
    obtain ⟨s0,sv⟩:=orient _ _ b
    exact ⟨g0,by rw [p0,s0,Bool.false_xor],pv,sv⟩
  | true =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=SkywalkRails.signed sg u at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=(u:Int)+v at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using b)
    obtain ⟨s0,sv⟩:=orient _ _ a
    exact ⟨g0,by rw [s0,p0,Bool.xor_false],pv,sv⟩


end ECDSAAdd.Entrant.StairPacket.PortalValues

end












section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem listMap (p:List α) (f g:α→Wire) (s u:BasisState) (same:∀x∈p,s (f x)=u (g x)) :
    regValue (p.map f) s=regValue (p.map g) u := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    change (if s (f x) then 1 else 0)+2*regValue (p.map f) s=(if u (g x) then 1 else 0)+2*regValue (p.map g) u
    rw [same _ (by simp),ih (fun q h=>same q (List.mem_cons_of_mem _ h))]

theorem scan_values (a b g n:Wire) (ps:List (Wire×Wire)) (loc:RailPair.ScanGeometry a b g n ps)
    (s:State) (m:List Bool) (fresh:s.basis n=false) :
    let t:=run (RailPair.scan a b g n ps) m s
    let e:=s.basis a ^^ s.basis b
    let l:=ps.map Prod.fst; let r:=ps.map Prod.snd
    regValue l t.basis=(if s.basis g then regValue r s.basis else regValue l s.basis) ∧
    regValue r t.basis=(if s.basis g then regValue l (fun q=>s.basis q ^^ e) else regValue r (fun q=>s.basis q ^^ e)) := by
  dsimp only
  have act:=RailPair.scan_run _ _ _ _ _ loc s m fresh
  cases eq:s.basis g <;> simp only [eq,ite_true,Bool.false_eq_true,ite_false] at *
  · exact ⟨listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).1),
      listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).2)⟩
  · exact ⟨listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).1),
      listMap ps _ _ _ _ (fun x h=>by simpa [eq] using (act.2.2.2 x h).2)⟩

theorem unroute (f:Wire→Wire) (rs:List Wire) (s:BasisState) :
    regValue (rs.map f) s=regValue rs (fun q=>s (f q)) := by
  simpa using listMap rs f id s (fun q=>s (f q)) (fun _ _=>rfl)

end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open SkywalkNat

/-- Every shortened decoded state still fits a signed word of log2(U)+3 bits;
the physical sign used by the guard and archive survives numerator reduction. -/
theorem reduced_values (b k : Nat) (z:SkywalkNat.State) (sg:Bool) (small:min z.u z.v<2^b) :
    let T:=reduced b k z
    let f:=far b k z
    let h:=limb b k
    let d:=if f then gap b k z else 0
    let lu:=decide (f ∧ 2^b≤z.u)
    T.u=z.u-(if lu then d else 0) ∧ (T.u+T.v=z.u+z.v-d) ∧ T.u+T.v<2*h ∧
    PortalValues.negative sg T.u=PortalValues.negative sg z.u ∧
    (T.u-(PortalValues.negative sg T.u).toNat)=
      (z.u-(PortalValues.negative sg z.u).toNat)-(if lu then d else 0) := by
  have hu:0<limb b k:=by simp [limb]
  have half:2^b≤limb b k:=by
    unfold limb;apply Nat.pow_le_pow_right (by decide); omega
  by_cases hf:far b k z
  · obtain ⟨_,lo,hi⟩:=represented b k z small hf
    dsimp only
    rw [reduced,if_pos hf] at lo hi ⊢
    simp only [hf,true_and,ite_true] at *
    by_cases lu:2^b≤z.u
    · simp only [lu,ite_true,decide_true] at lo hi ⊢
      change limb b k≤z.u-gap b k z+z.v at lo
      have hv:z.v<2^b:=by omega
      have nonzero:0<z.u-gap b k z:=by omega
      have nz:0<z.u:=by omega
      simp only [nonzero,nz,PortalValues.negative,decide_true,Bool.and_true]
      exact ⟨trivial,by omega,hi,trivial,by cases sg <;> simp; omega⟩
    · simp only [lu,ite_false,decide_false] at lo hi ⊢
      change limb b k≤z.u+(z.v-gap b k z) at lo
      have nz:0<z.v-gap b k z:=by omega
      exact ⟨rfl,by omega,hi,trivial,rfl⟩
  · have dst:reduced b k z=z:=by simp [reduced,hf]
    have low:(z.u+z.v)/limb b k<2:=Nat.lt_of_not_ge hf
    have lt:z.u+z.v<2*limb b k:=(Nat.div_lt_iff_lt_mul hu).mp low
    simp [dst,hf,lt]

end ECDSAAdd.Entrant.StairPacket.Shadow

end


section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Control
open Partial HighBankControl Leave225Shift
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225Control

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Control
open Partial HighBankControl Leave240Shift
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240Control

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Partial LeaveSelector HighBankFirstHit Leave255Hit
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem third (a b c:Wire) (rest:List Wire) (s:BasisState) :
    s c=true ↔ 4≤regValue (a::b::c::rest) s%8 := by
  change s c=true ↔ 4≤((if s a then 1 else 0)+2*((if s b then 1 else 0)+
      2*((if s c then 1 else 0)+2*regValue rest s)))%8
  cases s a <;> cases s b <;> cases s c <;> simp <;> omega

theorem wideThird (a b c:Wire) (rest:List Wire) (s:BasisState) (U W:Nat)
    (hp:0<U) (eq:regValue (a::b::c::rest) s=W/U) :
    s c=true ↔ 4*U≤W%(8*U) := by
  rw [third a b c rest s,eq,Nat.mul_comm 8 U,Nat.mod_mul]
  have rem:=Nat.mod_lt W hp
  constructor
  · intro h
    have big:=Nat.mul_le_mul_left U h
    omega
  · intro h
    by_contra not
    have ub:(W/U%8)+1≤4:=by omega
    have p:=Nat.mul_le_mul_left U ub
    rw [Nat.mul_add,Nat.mul_one] at p
    omega

theorem upper (a b c:Wire) (rest:List Wire) (s:BasisState) (U W:Nat)
    (eq:regValue (a::b::c::rest) s=W/U) :
    regValue rest s=W/(8*U) := by
  have z:=shiftedValue (a::b::c::rest) 3 (by simp) s
  rw [eq,Nat.div_div_eq_div_mul,Nat.mul_comm U] at z
  exact z

end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Barrel
open Partial Leave225Control Leave225Shift HighBankBarrel HighBankControl

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave225Barrel

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Barrel
open Partial Leave240Control Leave240Shift HighBankBarrel HighBankControl

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave240Barrel

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
open Arithmetic PortalAnd
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion225

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
open Arithmetic PortalAnd
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion240

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion255
open Arithmetic PortalAnd
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion255

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion
open Arithmetic

theorem mask_open (a b x t:Wire) (s:State) (m:List Bool) (nd:[a,b,x,t].Nodup)
    (hx:s.basis x=false) (ht:s.basis t=false) :
    run [.X x,.CX a x,.CCX b x t] m s =
      ⟨s.phase, writeBit (writeBit s.basis x (!s.basis a)) t (s.basis b && !s.basis a)⟩ := by
  obtain ⟨_,ax,_,bx,bt,xt⟩:a≠b ∧ a≠x ∧ a≠t ∧ b≠x ∧ b≠t ∧ x≠t := by simpa [and_assoc] using nd
  apply congrArg (State.mk s.phase)
  funext q
  by_cases qt:q=t <;> by_cases qx:q=x <;> simp_all [writeBit,Function.update]

theorem mask_close (a b x t:Wire) (s:State) (m:List Bool) (nd:[a,b,x,t].Nodup)
    (hx:s.basis x=(!s.basis a)) (ht:s.basis t=(s.basis b && s.basis x)) :
    run [.measureX t [] [.CZ b x],.CX a x,.X x] m s =
      ⟨s.phase, writeBit (writeBit s.basis x false) t false⟩ := by
  obtain ⟨_,ax,at0,_,bt,xt⟩:a≠b ∧ a≠x ∧ a≠t ∧ b≠x ∧ b≠t ∧ x≠t := by simpa [and_assoc] using nd
  change run [.CX a x,.X x] (m.drop 1) (run [.measureX t [] [.CZ b x]] m s)=_
  rw [PortalAnd.measure_and _ _ _ _ _ bt xt ht]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases qt:q=t <;> by_cases qx:q=x <;> simp_all [writeBit,Function.update]

theorem any_positive (qs : List Wire) (s : BasisState) :
    qs.any s = decide (0 < regValue qs s) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.any_cons, ih, regValue]
    cases h : s q <;> simp [h]

theorem high_three (a b : Wire) (qs : List (Wire × Wire)) (s : BasisState) :
    PortalAnd.high a b qs s = decide (3 ≤ regValue (a::b::qs.map Prod.fst) s) := by
  simp only [PortalAnd.high,any_positive,regValue]
  apply Bool.eq_iff_iff.mpr
  cases ha : s a <;> cases hb : s b <;> simp [ha,hb] <;> omega

end ECDSAAdd.Entrant.StairPacket.LeaveCompanion

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic MappedCompressed

structure Source (L:SkywalkIntegerLayout) (f:Wire→Wire) (k a b g:Nat) (pairs:List (Wire×Wire)) : Prop where
  left : (pairs.map Prod.fst).map f=L.a.drop k
  right : (pairs.map Prod.snd).map f=L.b.drop k
  aTop : f a=L.aSign
  bTop : f b=L.bSign
  previous : f g=L.previous
  aLength : k≤L.a.length
  bLength : k≤L.b.length

theorem scan_input (L:SkywalkIntegerLayout) (f:Wire→Wire) (k a b g n:Nat) (pairs:List (Wire×Wire))
    (src:Source L f k a b g pairs) (valid:RailPair.ScanGeometry a b g n pairs)
    (raw:State) (m:List Bool) (u v:Nat) (route sg:Bool)
    (input:SkywalkIntegerInput L (SkywalkRails.encode route sg u v).a (SkywalkRails.encode route sg u v).b route raw.basis)
    (clean:(pullState f raw).basis n=false) :
    let t:=run (RailPair.scan a b g n pairs) m (pullState f raw)
    let e:=negative sg u
    t.basis n=e ∧ t.basis g=route ∧ regValue (pairs.map Prod.fst) t.basis=(u+v)/2^k ∧
    regValue (pairs.map Prod.snd) t.basis=(u-e.toNat)/2^k := by
  let st:=pullState f raw
  have math:=mathematical L route sg u v raw.basis input
  have gg:st.basis g=route:=(congrArg raw.basis src.previous).trans math.1
  have ss:(st.basis a ^^ st.basis b)=negative sg u:=by
    change (raw.basis (f a) ^^ raw.basis (f b))=_
    rw [src.aTop,src.bTop];exact math.2.1
  have out:=RailPair.scan_run _ _ _ _ _ valid st m clean
  have values:=scan_values _ _ _ _ _ valid st m clean
  have nv:=List.nodup_cons.mp valid.unique
  have outside:g∉RailPair.sites pairs:=(List.nodup_cons.mp nv.2).1
  have gn:g≠n:=fun eq=>nv.1 (List.mem_cons.mpr (Or.inl eq.symm))
  have lift (rs:List Wire) (b:BasisState):regValue rs (fun q=>b (f q))=regValue (rs.map f) b:=(unroute f rs b).symm
  have L0:regValue (pairs.map Prod.fst) st.basis=regValue L.a raw.basis/2^k:=by
    rw [show st.basis=fun q=>raw.basis (f q) by rfl,lift,src.left,shiftedValue _ _ src.aLength]
  have R0:regValue (pairs.map Prod.snd) st.basis=regValue L.b raw.basis/2^k:=by
    rw [show st.basis=fun q=>raw.basis (f q) by rfl,lift,src.right,shiftedValue _ _ src.bLength]
  let e:=negative sg u
  have L1:regValue (pairs.map Prod.fst) (fun q=>st.basis q ^^ e)=regValue L.a (fun q=>raw.basis q ^^ e)/2^k:=by
    rw [show (fun q=>st.basis q ^^ e)=(fun q=>(fun t=>raw.basis t ^^ e) (f q)) by rfl,lift (pairs.map Prod.fst) (fun t=>raw.basis t ^^ e),src.left,shiftedValue _ _ src.aLength]
  have R1:regValue (pairs.map Prod.snd) (fun q=>st.basis q ^^ e)=regValue L.b (fun q=>raw.basis q ^^ e)/2^k:=by
    rw [show (fun q=>st.basis q ^^ e)=(fun q=>(fun t=>raw.basis t ^^ e) (f q)) by rfl,lift (pairs.map Prod.snd) (fun t=>raw.basis t ^^ e),src.right,shiftedValue _ _ src.bLength]
  refine ⟨out.2.1.trans ss,(out.2.2.1 g gn outside).trans gg,?_⟩
  obtain ⟨pos,mag⟩:=math.2.2
  dsimp only at values
  rw [gg,ss] at values
  cases route <;> simp only [wordPos,wordSigned,ite_true,Bool.false_eq_true,ite_false] at pos mag values
  · exact ⟨values.1.trans (L0.trans (congrArg (· /2^k) pos)),values.2.trans (R1.trans (congrArg (· /2^k) mag))⟩
  · exact ⟨values.1.trans (R0.trans (congrArg (· /2^k) pos)),values.2.trans (L1.trans (congrArg (· /2^k) mag))⟩

theorem real_input (d:Bool) (x p i:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256)
    (hq:p+2^32≤2^256) (hx:x<p) (hc:x.Coprime p) (hi:i<512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis) :
    let z:=SkywalkNat.step^[i] (SkywalkNat.init x p)
    ∃ g sg:Bool, SkywalkIntegerInput (W.compactSkywalkTickLayout base i)
      (SkywalkRails.encode g sg z.u z.v).a (SkywalkRails.encode g sg z.u z.v).b g s.basis := by
  obtain ⟨g,sg,eq⟩:=SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  have source:=original_input d x p i hp0 hx0 hpo hp hq hx hc hi s stage
  change SkywalkIntegerInput _ (SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)).a
    (SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)).b
    (SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)).g _ at source
  change SkywalkTrace.next^[i] (SkywalkRails.encode false false x p)=_ at eq
  rw [eq] at source
  refine ⟨g,sg,?_⟩
  cases g <;> exact source



end ECDSAAdd.Entrant.StairPacket.PortalValues

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225High
open Partial Arithmetic HighBankAdjust HighBankBarrel Leave225Barrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225High

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Word
open Partial Leave225Join Leave225Barrel HighBankJoin HighBankReassemble

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave225Word

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240High
open Partial Arithmetic HighBankAdjust HighBankBarrel Leave240Barrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240High

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Word
open Partial Leave240Join Leave240Barrel HighBankJoin HighBankReassemble

set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave240Word

end

section

open ECDSAAdd.Arithmetic
set_option maxRecDepth 32000
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion255
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion255

end



section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open LeaveSelector
end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end


section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion
open Arithmetic

/-- Compression keeps the top test of the unsigned magnitude unless the
    retained part wraps. That case is marked by the next far indicator. -/
theorem retain_flag (half bound mag : Nat) (far : Bool) (width : half ≤ bound)
    (near : far = false → mag < bound) :
    ((decide (half ≤ mag) && far) || decide (half ≤ mag % bound)) =
      decide (half ≤ mag) := by
  cases far with
  | false => simp [Nat.mod_eq_of_lt (near rfl)]
  | true =>
    by_cases h : half ≤ mag
    · simp [h]
    · have l : mag < bound := by omega
      simp [h,Nat.mod_eq_of_lt l]

/-- Converting a post-merge magnitude to a physical lower limb and sign bit
    gives the exact threshold test even when the whole magnitude has wrapped. -/
theorem lower_nonzero (half limb mag : Nat) (hp : 0 < half)  :
    (decide (half ≤ mag % (2*half)) || decide (0 < (mag / (2*half)) % limb)) =
      decide (half ≤ mag % ((2*half)*limb)) := by
  let r := mag % ((2*half)*limb)
  have bottom : r % (2*half)=mag%(2*half) :=
    Nat.mod_mod_of_dvd mag (dvd_mul_right (2*half) limb)
  have top : r / (2*half)=(mag/(2*half))%limb := Nat.mod_mul_right_div_self _ _ _
  rw [←bottom,←top]
  change (_ || _) = decide (half ≤ r)
  by_cases h : r < 2*half
  · simp [Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]
  · have pos : 0 < r/(2*half) := Nat.div_pos (by omega) (by omega)
    simp [pos,show half ≤ r by omega]

def upperBorrow (half u v sign : Nat) : Nat :=
  if half ≤ (u-sign)%(2*half) ∧ (u+v)%(2*half)<half then 1 else 0

/-- Before the merge, adding the physical borrow to M cancels the
    enabled copy of A in the pre-merge register, modulo its actual width. -/
theorem upper_clear (half u v sign radix : Nat) (hp : 0<half)
    (se : sign≤1) (su : sign≤u) (small : min u v<half) :
    (((u-sign)/(2*half))%radix+upperBorrow half u v sign)%radix =
    (if half ≤ u-sign then ((u+v)/(2*half))%radix else 0) := by
  have hc := companion_upper half u v sign hp se su small
  dsimp only at hc
  by_cases h : half ≤ u-sign
  · simp only [if_pos h] at hc ⊢
    rw [hc, Nat.mod_add_mod]
    rfl
  · simp only [if_neg h] at hc ⊢
    have lt : u-sign<2*half := by omega
    simp [hc,upperBorrow,Nat.mod_eq_of_lt lt,h]

/-- After copying the corrected positive rail, subtraction of the same single
    borrow reconstructs precisely the retained magnitude, including wrap. -/
theorem upper_restore (half u v sign radix : Nat) (hp : 0<half)
    (se : sign≤1) (su : sign≤u) (small : min u v<half) (rp : 0<radix) :
    ((if half≤u-sign then ((u+v)/(2*half))%radix else 0)+radix-
        upperBorrow half u v sign)%radix = ((u-sign)/(2*half))%radix := by
  rw [←upper_clear half u v sign radix hp se su small]
  let y := ((u-sign)/(2*half))%radix
  let b := upperBorrow half u v sign
  have by1 : b≤1 := by dsimp [b,upperBorrow]; split <;> omega
  have yl : y<radix := Nat.mod_lt _ rp
  change ((y+b)%radix+radix-b)%radix=y
  rw [show (y+b)%radix+radix-b=(y+b)%radix+(radix-b) by omega,
    Nat.mod_add_mod,show y+b+(radix-b)=y+radix by omega,Nat.add_mod_right,
    Nat.mod_eq_of_lt yl]

theorem near_bound (u v sign divisor bound : Nat) (dp : 0<divisor) (wide : 3*divisor≤bound)
    (near : decide (3≤(u+v)/divisor)=false) : u-sign<bound := by
  have lo : (u+v)/divisor<3 := by simpa using near
  have lim := (Nat.div_lt_iff_lt_mul dp).mp lo
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveCompanion

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

private theorem select (i:Nat) (scratch:List Wire) (pool:∀q∈scratch,OB5.sig (i-1) q∈(W.compactSkywalkTickLayout base i).carry)
    (d:Bool) (x p:Nat) (hp0:0<p) (hx0:0<x) (hpo:p%2=1) (hp:p<2^256) (hq:p+2^32≤2^256)
    (hx:x<p) (hc:x.Coprime p) (hi:i<512) (s:State)
    (h:Rolling1588.Integer.Stage base d x p i s.basis) : ∀q∈scratch,(pullState (OB5.sig (i-1)) s).basis q=false:=by
  have input:=original_input d x p i hp0 hx0 hpo hp hq hx hc hi s h
  exact fun q hq=>(regValue_zero _ _).mp input.2.2.2.2.2 _ (pool q hq)

end ECDSAAdd.Entrant.StairPacket

end


section

open ECDSAAdd.Arithmetic
set_option maxRecDepth 32000
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion225
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion240
namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion255
end ECDSAAdd.Entrant.StairPacket.LeaveCompanion255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 8192
def input : Cols := [0x9999999a9999999a9999999aa6666666ffffaaaa0000aaaaaab56d55ab6a5529ad56a, 0x2d2d2d2e2d2d2d2ee1e1e1e2b8787878ffffcccc0000cccccf39b986320c66400998c, 0x2fd02fe02fd02fefe01fe02bf807f80fffff0f00000f0f0f3dffe18cdf08001f6630, 0x2fffe0002fffefffe0002bfff8000ffffff000000ff00fffff8000000000000000, 0xccccccccccccccccccccccccccccccccaaaaffffaaaa0000fc1e37e0f1bf078d387c0, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccffffcccc0000001fc7ff01c007f03f800, 0xff00ff00ff00ff00ff00ff00ff00ff00f0f0fffff0f00000ffe007fffe3ff801c0000, 0xffff0000ffff0000ffff0000ffff0000ff00ffffff000000000007ffffc0000000000, 0xffffffff00000000ffffffff00000000ffff0000ffff0000fffff800003ffffe00000, 0xffffffffffffffff0000000000000000ffffffff00000000ffffffffffc0000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000, 0xffffffffffffffffffffffffffffffff0000000000000000000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
def output : Cols := [0x9999999a9999999a9999999aa6666666ffffaaaa0000aaaaaab56d55ab6a5529ad56a, 0xddddddde000000001111111200000000ffff000000000000cf39b986320c66400998c, 0x22222221ffffffffeeeeeeedffffffffffffffff0000fffff3dffe18cdf08001f6630, 0xffffffff000000000000000000000000ffff000000000000fffff8000000000000000, 0xccccccccccccccccccccccccccccccccaaaaffffaaaa0000fc1e37e0f1bf078d387c0, 0xddddddde00000000488888880000ffff00000000001fc7ff01c007f03f800, 0xffffffff22222221ffffffffb7777777ffffffffffff0000ffe007fffe3ff801c0000, 0xffffffff00000000000000000000ffff00000000000007ffffc0000000000, 0xffffffff00000000ffffffff00000000ffff0000ffff0000fffff800003ffffe00000, 0x0, 0xffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000, 0xffffffffffffffffffffffffffffffff0000000000000000000000000000000000000, 0xf0f0f0f02d2d2d2ef0f0f0f0b8787878cccccccccccccccc000000000000000000000, 0xff00ff0002fd02feff00ff00bf807f80f0f0f0f0f0f0f0f0000000000000000000000, 0xffff00000002fffeffff0000bfff8000ff00ff00ff00ff00000000000000000000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]
def mask : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def forward : Program := [ .CX 1 5, .CCX 8 5 1, .CX 1 5, .CX 2 6, .CCX 8 6 2, .CX 2 6, .CX 3 7, .CCX 8 7 3, .CX 3 7, .CX 9 5, .CX 9 6, .CX 9 7, .CCX 11 1 21, .CX 1 18, .CCX 10 18 1, .CX 1 18, .CX 2 19, .CCX 10 19 2, .CX 2 19, .CX 10 2, .CX 3 20, .CX 20 3, .CCX 5 21 22, .measureX 7 [] [.CZ 6 10, .CZ 6 19, .CZ 11 20], .CX 22 6, .CX 21 5, .measureX 22 [] [.Z 21, .CZ 5 21], .CCX 11 19 6, .CX 11 6, .CX 21 6, .measureX 21 [] [.CZ 5 18, .CZ 6 18], .CX 9 5, .CX 9 6, .CX 9 7, .CX 1 5, .CCX 8 5 1, .CX 1 5, .CX 2 6, .CCX 8 6 2, .CX 2 6, .CX 3 7, .CCX 8 7 3, .CX 3 7, .CX 3 9, .CX 7 9, .CX 18 12, .CX 12 18, .CX 18 12, .CX 19 13, .CX 13 19, .CX 19 13, .CX 20 14, .CX 14 20, .CX 20 14, .CX 0 4, .CX 0 4, .CX 15 16, .CX 15 16, .CX 17 15, .CX 17 15]
theorem forward_checked : eval mask forward input=(true,output) := by decide +kernel
def backward : Program := [ .CX 20 14, .CX 14 20, .CX 20 14, .CX 19 13, .CX 13 19, .CX 19 13, .CX 18 12, .CX 12 18, .CX 18 12, .CX 7 9, .CX 3 9, .measureX 3 [] [.CZ 8 9], .measureX 7 [] [.Z 9, .CZ 8 9], .CX 2 6, .CCX 8 6 2, .CX 2 6, .CX 1 5, .CCX 8 5 1, .CX 1 5, .CX 9 6, .CX 9 5, .CCX 5 18 6, .CX 10 18, .CCX 5 18 22, .CX 10 18, .CX 10 19, .CCX 22 19 7, .CX 10 19, .CCX 11 20 7, .CCX 11 19 6, .CX 11 6, .CCX 11 18 5, .measureX 22 [] [.CZ 5 10, .CZ 5 18], .CX 20 3, .CX 3 20, .CX 10 2, .CX 2 19, .CCX 10 19 2, .CX 2 19, .CX 1 18, .CCX 10 18 1, .CX 1 18, .CX 9 7, .CX 9 6, .CX 9 5, .CX 3 7, .CCX 8 7 3, .CX 3 7, .CX 2 6, .CCX 8 6 2, .CX 2 6, .CX 1 5, .CCX 8 5 1, .CX 1 5, .CX 0 4, .CX 0 4, .CX 15 16, .CX 15 16, .CX 17 15, .CX 17 15, .CX 21 17, .CX 21 17]
theorem backward_checked : eval mask backward output=(true,input) := by decide +kernel
def result (r : Nat) : Nat :=
  let ra:=r%16; let rb:=r/16%16; let g:=r.testBit 8; let neg:=r.testBit 9
  let f:=r.testBit 10; let u:=r.testBit 11
  let a:=if g then rb else ra; let m:=(if g then ra else rb) ^^^ (if neg then 15 else 0)
  let w:=if u && m.testBit 0 && !a.testBit 0 then 1 else 0
  let h:=a/2; let sh:=if f then 2 else h
  let sm:=((((m/2+w)%8) ^^^ (if u then h else 0) ^^^ (if u then sh else 0))+8-w)%8
  let x:=2*sh+a%2; let y:=(2*sm+m%2) ^^^ (if neg then 15 else 0)
  let l:=if g then y else x; let b:=if g then x else y
  l+16*b+256*g.toNat+512*(neg ^^ l.testBit 3 ^^ b.testBit 3).toNat+
    1024*f.toNat+2048*u.toNat+4096*f.toNat*h
def width : Nat := 23

/-- Rows of the enter table that the 7-bit walk reaches (`Shadow7.SmallIfFar`): decode a row into its digits. -/
def rowA (r : Nat) : Nat := if r.testBit 8 then r/16%16 else r%16

def rowM (r : Nat) : Nat := (if r.testBit 8 then r%16 else r/16%16) ^^^ (if r.testBit 9 then 15 else 0)

/-- Not far: `m ≤ a ≤ 5`; far and short: `m = 0`; far and long: `m ∈ {a, a-1 mod 16}` (kaankolcu's decf4047 276-row
restriction). -/
def reachRow (r : Nat) : Bool :=
  (!r.testBit 10 && !r.testBit 11 && decide (rowM r ≤ rowA r) && decide (rowA r ≤ 5)) ||
  (r.testBit 10 && !r.testBit 11 && decide (rowM r = 0)) ||
  (r.testBit 10 && r.testBit 11 && (decide (rowM r = rowA r) || decide (rowM r = (rowA r + 15) % 16)))

def rows276 : List Nat := [0, 1, 2, 3, 4, 5, 17, 18, 19, 20, 21, 34, 35, 36, 37, 51, 52, 53, 68, 69, 85, 256, 272, 273, 288, 289, 290, 304, 305, 306, 307, 320, 321, 322, 323, 324, 336, 337, 338, 339, 340, 341, 677, 692, 693, 707, 708, 709, 722, 723, 724, 725, 737, 738, 739, 740, 741, 752, 753, 754, 755, 756, 757, 783, 798, 799, 813, 814, 815, 828, 829, 830, 831, 843, 844, 845, 846, 847, 858, 859, 860, 861, 862, 863, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1280, 1296, 1312, 1328, 1344, 1360, 1376, 1392, 1408, 1424, 1440, 1456, 1472, 1488, 1504, 1520, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1807, 1823, 1839, 1855, 1871, 1887, 1903, 1919, 1935, 1951, 1967, 1983, 1999, 2015, 2031, 2047, 3072, 3073, 3089, 3090, 3106, 3107, 3123, 3124, 3140, 3141, 3157, 3158, 3174, 3175, 3191, 3192, 3208, 3209, 3225, 3226, 3242, 3243, 3259, 3260, 3276, 3277, 3293, 3294, 3310, 3311, 3312, 3327, 3328, 3343, 3344, 3345, 3361, 3362, 3378, 3379, 3395, 3396, 3412, 3413, 3429, 3430, 3446, 3447, 3463, 3464, 3480, 3481, 3497, 3498, 3514, 3515, 3531, 3532, 3548, 3549, 3565, 3566, 3582, 3583, 3584, 3599, 3614, 3615, 3629, 3630, 3644, 3645, 3659, 3660, 3674, 3675, 3689, 3690, 3704, 3705, 3719, 3720, 3734, 3735, 3749, 3750, 3764, 3765, 3779, 3780, 3794, 3795, 3809, 3810, 3824, 3825, 3840, 3855, 3870, 3871, 3885, 3886, 3900, 3901, 3915, 3916, 3930, 3931, 3945, 3946, 3960, 3961, 3975, 3976, 3990, 3991, 4005, 4006, 4020, 4021, 4035, 4036, 4050, 4051, 4065, 4066, 4080, 4081]

theorem rows276_spec : rows276 = (List.range 4096).filter reachRow := by decide +kernel

theorem rows276_length : rows276.length = 276 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave255Hit Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 1500000

end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 8192
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic enter piece of block `j` (par-c2, job C2 of PARAMETRIC.md). Tick `s = start j`, `h = sbP s`.
Every per-block number of dadon's `Enter{s}` / `EnterProof.ports{s}` is a function of `j` here; the
programs are par-b's `enterP j = forward (enterOps (start j))`. `EnterJ.ports 12 = EnterProof.ports255`. -/

/-- Orientation gate `s+15` and the three flags `n f u` (`e0+5, e0+3, e0+4`). -/
def gate (j : Fin 24) : Wire := start j+15
def flagN (j : Fin 24) : Wire := sbP (start j)+1579
def flagF (j : Fin 24) : Wire := sbP (start j)+1577
def flagU (j : Fin 24) : Wire := sbP (start j)+1578
/-- The parked bank: three low pairs, then `Wp-3` upper pairs up to the B rail's top `785+R`. -/
def lowerPairs (j : Fin 24) : List (Wire×Wire) :=
  [(start j+sbP (start j)+32, sbP (start j)+802), (start j+sbP (start j)+33, sbP (start j)+803),
   (start j+sbP (start j)+34, sbP (start j)+804)]
def upperPairs (j : Fin 24) : List (Wire×Wire) :=
  (List.range (wpP (start j)-3)).map (fun i => (start j+sbP (start j)+35+i, sbP (start j)+805+i))
def pending (j : Fin 24) : List Wire := [sbP (start j)+1580, sbP (start j)+1581, sbP (start j)+1582]
def safe (j : Fin 24) (q : Wire) : Prop :=
  (q<start j+16 ∨ start j+sbP (start j)+31≤q) ∧ (q<786 ∨ sbP (start j)+801≤q)
instance (j : Fin 24) (q : Wire) : Decidable (safe j q) := by unfold safe; infer_instance
def pull (j : Fin 24) : Wire → Wire := OB5.sig (start j-1)
end ECDSAAdd.Entrant.StairPacket.EnterJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic CodecBitSliceVerify

def Formula (r : Nat) : Prop :=
  ∀ q:Fin width,(get input q).testBit r=(rows276.getD r 0).testBit q ∧ (get output q).testBit r=(result (rows276.getD r 0)).testBit q
instance (r:Nat) : Decidable (Formula r) := inferInstanceAs (Decidable (∀_:Fin width,_))

def Interval (lo n : Nat) : Prop := ∀ j : Fin n, Formula (lo+j)
instance (lo n:Nat) : Decidable (Interval lo n) := inferInstanceAs (Decidable (∀_:Fin n,_))

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum LeaveSelector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def hiPairs := bulkA.zip bulkB
end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave225Hit
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave240Hit
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave255Hit
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end


section

namespace ECDSAAdd.Entrant.StairPacket.Portal225Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal225Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal270Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal270Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
theorem allRows : Interval 0 276 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
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

private theorem lookup (inv : Bool) (r : Fin 276) (q:Fin width) :
    (get (source inv) q).testBit r=(initial inv (rows276.getD r 0)).testBit q ∧
    (get (destination inv) q).testBit r=(finalValue inv (rows276.getD r 0)).testBit q := by
  have h:=allRows r q
  simp only [Nat.zero_add] at h
  cases inv
  · exact h
  · exact ⟨h.2,h.1⟩

theorem apply_guard (f:Wire→Wire) (inv:Bool) (r:Fin 276)
    (inj:∀a b : Fin width, f a=f b → a=b) (m:List Bool) (s:State)
    (entry:∀q∈wires (step inv),s.basis (f q)=(initial inv (rows276.getD r 0)).testBit q) :
    (run (renameProgram f (step inv)) m s).phase=s.phase ∧
    (∀q∈wires (step inv),(run (renameProgram f (step inv)) m s).basis (f q)=(finalValue inv (rows276.getD r 0)).testBit q) ∧
    ∀q∉wires (renameProgram f (step inv)),(run (renameProgram f (step inv)) m s).basis q=s.basis q := by
  have targetOK:∀g∈step inv,target g < (source inv).length := by cases inv <;> decide +kernel
  have active:mask.testBit r=true := by
    change (2^276-1:Nat).testBit r=true
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

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave225Hit
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave240Hit
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum LeaveSelector HighBankFirstHit Leave255Hit
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

/-- A nibble of the signed rail is encoded by the one's complement of its
magnitude whenever the full signed rail is negative. -/
def signedNibble (n:Bool) (m:Nat) := m ^^^ (if n then 15 else 0)

def encodedPair (g neg:Bool) (a m:Nat) := if g then signedNibble neg m+16*a else a+16*signedNibble neg m

def rowOf (a m:Nat) (g neg f u:Bool) :=
  encodedPair g neg a m + 256*g.toNat+512*neg.toNat+1024*f.toNat+2048*u.toNat

def borrow (a m:Nat) (u:Bool) := (u && m.testBit 0 && !a.testBit 0).toNat
def updateA (a:Nat) (f:Bool) := 2*(if f then 2 else a/2)+a%2
def updateM (a m:Nat) (f u:Bool) := 2*EnterLimb.guardWord (m/2) (a/2) (borrow a m u) f u+m%2
def updateA17 (a:Nat) (f:Bool) := 2*(if f then 1 else a/2)+a%2
def updateM17 (a m:Nat) (f u:Bool) := 2*EnterLimb.guardWord17 (m/2) (a/2) (borrow a m u) f u+m%2

def expected (a m:Nat) (g neg f u:Bool) :=
  let x:=updateA a f;let y:=updateM a m f u
  let sg:=neg ^^ x.testBit 3 ^^ (signedNibble neg y).testBit 3
  encodedPair g neg x y+256*g.toNat+512*sg.toNat+1024*f.toNat+2048*u.toNat+(if f then 4096*(a/2) else 0)

def RowSpec (x:Nat) : Prop :=
  ∀ y:Fin 16,∀g n f u:Bool,rowOf x y g n f u<4096 ∧ result (rowOf x y g n f u)=expected x y g n f u
instance (x:Nat):Decidable (RowSpec x):=inferInstanceAs (Decidable (∀_:Fin 16,∀ _ _ _ _:Bool,_))

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
end ECDSAAdd.Entrant.StairPacket.EnterProof

end




section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row0 : RowSpec 0 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row1 : RowSpec 1 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row10 : RowSpec 10 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row11 : RowSpec 11 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row12 : RowSpec 12 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row13 : RowSpec 13 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row14 : RowSpec 14 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row15 : RowSpec 15 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row2 : RowSpec 2 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row3 : RowSpec 3 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row4 : RowSpec 4 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row5 : RowSpec 5 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row6 : RowSpec 6 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row7 : RowSpec 7 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row8 : RowSpec 8 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem row9 : RowSpec 9 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

def nibble (W V:Nat):Nat:=(W/V)%16

theorem digit (W V:Nat):nibble W V/2=W/(2*V)%8 := by
  rw [Nat.mul_comm 2 V,←Nat.div_div_eq_div_mul]
  unfold nibble
  omega

theorem bit (W V:Nat) (pos:0<V): (nibble W V).testBit 0=true ↔ V≤W%(2*V) := by
  rw [←Nat.mod_two_eq_one_iff_testBit_zero,Nat.mul_comm 2 V,Nat.mod_mul]
  have rem:=Nat.mod_lt W pos
  change (W/V%16)%2=1 ↔ _
  by_cases b:W/V%2=1
  · rw [b,Nat.mul_one];omega
  · have z:W/V%2=0:=by omega
    rw [z,Nat.mul_zero];omega

theorem frac (W V:Nat) (pos:0<V):nibble W V%2=(W%(2*V))/V := by
  rw [Nat.mul_comm 2 V,Nat.mod_mul,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt (Nat.mod_lt _ pos)]
  unfold nibble;omega

theorem digit_join (W V:Nat):nibble W V=2*(W/(2*V)%8)+nibble W V%2 := by
  rw [←digit];omega

theorem borrowed (W M V:Nat) (pos:0<V) :
    borrow (nibble W V) (nibble M V) true=(if V≤M%(2*V) ∧ W%(2*V)<V then 1 else 0) := by
  have m:=bit M V pos
  have w:=bit W V pos
  cases hb:(nibble M V).testBit 0 <;> cases ha:(nibble W V).testBit 0 <;> simp_all [borrow]

theorem short_digits (W M V e:Nat) (pos:0<V) (ew:e≤1)
    (rel:W/(2*V)=M/(2*V)+e) (actual:e=borrow (nibble W V) (nibble M V) true)
    (df:3≤W/(2*V)) :
    let d:=(W/(2*V)-2)*(2*V)
    updateA (nibble W V) true=nibble (W-d) V ∧
    updateM (nibble W V) (nibble M V) true true=nibble (M-d) V := by
  have hh:=EnterLimb.limbs (2*V) W M e (by omega) ew true df (fun _=>rel)
  dsimp only at hh ⊢
  obtain ⟨wmod,wh,mm,mh⟩:=hh
  simp only [ite_true] at mm mh
  have p1: nibble (W-(W/(2*V)-2)*(2*V)) V%2=nibble W V%2:=by rw [frac _ _ pos,wmod,←frac _ _ pos]
  have p2: nibble (M-(W/(2*V)-2)*(2*V)) V%2=nibble M V%2:=by rw [frac _ _ pos,mm,←frac _ _ pos]
  constructor
  · rw [digit_join (W-_) V,wh,p1]
    rfl
  · rw [digit_join (M-_) V,p2,mh]
    unfold updateM
    rw [digit,digit,←actual]
    simp [EnterLimb.guardWord]

theorem short_other (W M V:Nat) (pos:0<V) (df:3≤W/(2*V)) :
    let d:=(W/(2*V)-2)*(2*V)
    updateA (nibble W V) true=nibble (W-d) V ∧
    updateM (nibble W V) (nibble M V) true false=nibble M V := by
  have hh:=EnterLimb.limbs (2*V) W M 0 (by omega) (by decide) false df (by simp)
  obtain ⟨wm,wh,_⟩:=hh
  dsimp only at wm wh ⊢
  constructor
  · rw [digit_join (W-_) V,wh,frac (W-_) _ pos,wm,←frac];rfl
    exact pos
  · unfold updateM
    simp only [borrow,Bool.false_and,Bool.toNat_false,EnterLimb.guardWord,Bool.false_eq_true,ite_false,
      Nat.add_zero,Nat.sub_zero,Nat.xor_zero,Nat.add_mod_right,Nat.mod_mod]
    have z:nibble M V<16:=Nat.mod_lt _ (by decide)
    omega

theorem near_digits (W M V:Nat) :
    updateA (nibble W V) false=nibble W V ∧
    updateM (nibble W V) (nibble M V) false false=nibble M V := by
  constructor
  · simp [updateA];omega
  · unfold updateM
    rw [EnterLimb.unchanged _ _ _ (by simp [borrow])]
    have z:nibble M V<16:=Nat.mod_lt _ (by decide)
    omega

theorem short_digits17 (W M V e:Nat) (pos:0<V) (ew:e≤1)
    (rel:W/(2*V)=M/(2*V)+e) (actual:e=borrow (nibble W V) (nibble M V) true)
    (df:2≤W/(2*V)) :
    let d:=(W/(2*V)-1)*(2*V)
    updateA17 (nibble W V) true=nibble (W-d) V ∧
    updateM17 (nibble W V) (nibble M V) true true=nibble (M-d) V := by
  have hh:=EnterLimb.limbs17 (2*V) W M e (by omega) ew true df (fun _=>rel)
  dsimp only at hh ⊢
  obtain ⟨wmod,wh,mm,mh⟩:=hh
  simp only [ite_true] at mm mh
  have p1: nibble (W-(W/(2*V)-1)*(2*V)) V%2=nibble W V%2:=by rw [frac _ _ pos,wmod,←frac _ _ pos]
  have p2: nibble (M-(W/(2*V)-1)*(2*V)) V%2=nibble M V%2:=by rw [frac _ _ pos,mm,←frac _ _ pos]
  constructor
  · rw [digit_join (W-_) V,wh,p1]
    rfl
  · rw [digit_join (M-_) V,p2,mh]
    unfold updateM17
    rw [digit,digit,←actual]
    simp [EnterLimb.guardWord17]

theorem short_other17 (W M V:Nat) (pos:0<V) (df:2≤W/(2*V)) :
    let d:=(W/(2*V)-1)*(2*V)
    updateA17 (nibble W V) true=nibble (W-d) V ∧
    updateM17 (nibble W V) (nibble M V) true false=nibble M V := by
  have hh:=EnterLimb.limbs17 (2*V) W M 0 (by omega) (by decide) false df (by simp)
  obtain ⟨wm,wh,_⟩:=hh
  dsimp only at wm wh ⊢
  constructor
  · rw [digit_join (W-_) V,wh,frac (W-_) _ pos,wm,←frac];rfl
    exact pos
  · unfold updateM17
    simp only [borrow,Bool.false_and,Bool.toNat_false,EnterLimb.guardWord17,Bool.false_eq_true,ite_false,
      Nat.add_zero,Nat.sub_zero,Nat.xor_zero,Nat.add_mod_right,Nat.mod_mod]
    have z:nibble M V<16:=Nat.mod_lt _ (by decide)
    omega

theorem near_digits17 (W M V:Nat) :
    updateA17 (nibble W V) false=nibble W V ∧
    updateM17 (nibble W V) (nibble M V) false false=nibble M V := by
  constructor
  · simp [updateA17];omega
  · unfold updateM17
    rw [EnterLimb.unchanged17 _ _ _ (by simp [borrow])]
    have z:nibble M V<16:=Nat.mod_lt _ (by decide)
    omega


end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
theorem shape (a m:Fin 16) (g n f u:Bool) : rowOf a m g n f u<4096 ∧ result (rowOf a m g n f u)=expected a m g n f u := by
  apply (show RowSpec a from ?_) m g n f u
  fin_cases a
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

def cutUnit (b k:Nat):Nat:=2^(b+k)

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof

def initialRow (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) :=
  let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
  rowOf (nibble (z.u+z.v) V) (nibble (z.u-e.toNat) V) g e
    (decide (Shadow.far b k z)) (decide (Shadow.far b k z ∧ 2^b≤z.u))

def shadowRow (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) :=
  let T:=Shadow.reduced b k z; let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
  encodedPair g e (nibble (T.u+T.v) V) (nibble (T.u-e.toNat) V)+256*g.toNat+
    1024*(decide (Shadow.far b k z)).toNat+2048*(decide (Shadow.far b k z ∧ 2^b≤z.u)).toNat+
    (if Shadow.far b k z then 4096*(Shadow.high b k z%8) else 0)

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open EnterProof

theorem actual_residue (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small:min z.u z.v<2^b) :
    let T:=reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
    (T.u+T.v)%V=(z.u+z.v)%V ∧ (T.u-e.toNat)%V=(z.u-e.toNat)%V := by
  let V:=cutUnit b k
  let T:=reduced b k z
  let e:=PortalValues.negative sg z.u
  obtain ⟨tu,tx,hi,sign,tm⟩:=reduced_values b k z sg small
  rw [sign] at tm
  have scale:limb b k=2*V:=by simp [limb,cutUnit,V,pow_succ,Nat.mul_comm]
  have periodic (N d:Nat) (eq:N≥d) (mul:V∣d):(N-d)%V=N%V:=by
    obtain ⟨j,rfl⟩:=mul
    conv_rhs => rw [show N=N-V*j+V*j by omega,Nat.add_mul_mod_self_left]
  have dep:V∣gap b k z := by
    unfold gap;rw [scale]
    exact ⟨(high b k z-1)*2,by ring⟩
  change (T.u+T.v)%V=(z.u+z.v)%V ∧ (T.u-e.toNat)%V=(z.u-e.toNat)%V
  have pos:0<V:=by simp [V,cutUnit]
  by_cases hf:far b k z
  · obtain ⟨_,bound,_⟩:=represented _ _ _ small hf
    change limb b k≤T.u+T.v at bound
    simp only [hf,ite_true,true_and] at tx tm tu
    have light:2^b≤limb b k:=by unfold limb;apply Nat.pow_le_pow_right (by decide);omega
    change T.u+T.v=z.u+z.v-gap b k z at tx
    have enough:gap b k z≤z.u+z.v:=by omega
    rw [tx,periodic _ _ enough dep]
    refine ⟨rfl,?_⟩
    by_cases hl:2^b≤z.u
    · simp only [hl,decide_true,ite_true] at tm tu
      have tv:T.v=z.v:=by simp [T,reduced,hf,hl]
      have sm:z.v<2^b:=by omega
      have boundU:0<T.u:=by omega
      have nne:z.u≥gap b k z+1:=by change T.u=z.u-gap b k z at tu;omega
      have eBound:e.toNat≤1:=by cases e <;> decide
      change T.u-e.toNat=z.u-e.toNat-gap b k z at tm
      rw [tm]
      exact periodic _ _ (by change gap b k z≤z.u-e.toNat;omega) dep
    · simp only [hl,decide_false] at tm
      change T.u-e.toNat=z.u-e.toNat at tm
      rw [tm]
  · simp [T,reduced,hf]


/-- margin 17 (T1): the gap (H-1)U is a multiple of the whole limb, so the residues agree modulo `limb`
(the cut of a register that keeps only rows from b+k+1 on). -/
theorem actual_residue_limb (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small:min z.u z.v<2^b) :
    let T:=reduced b k z;let e:=PortalValues.negative sg z.u
    (T.u+T.v)%limb b k=(z.u+z.v)%limb b k ∧ (T.u-e.toNat)%limb b k=(z.u-e.toNat)%limb b k := by
  let T:=reduced b k z
  let e:=PortalValues.negative sg z.u
  obtain ⟨tu,tx,hi,sign,tm⟩:=reduced_values b k z sg small
  rw [sign] at tm
  have periodic (N d:Nat) (eq:N≥d) (mul:limb b k∣d):(N-d)%limb b k=N%limb b k:=by
    obtain ⟨j,rfl⟩:=mul
    conv_rhs => rw [show N=N-limb b k*j+limb b k*j by omega,Nat.add_mul_mod_self_left]
  have dep:limb b k∣gap b k z := Nat.dvd_mul_left (limb b k) (high b k z-1)
  change (T.u+T.v)%limb b k=(z.u+z.v)%limb b k ∧ (T.u-e.toNat)%limb b k=(z.u-e.toNat)%limb b k
  by_cases hf:far b k z
  · obtain ⟨_,bound,_⟩:=represented _ _ _ small hf
    change limb b k≤T.u+T.v at bound
    simp only [hf,ite_true,true_and] at tx tm tu
    have light:2^b≤limb b k:=by unfold limb;apply Nat.pow_le_pow_right (by decide);omega
    change T.u+T.v=z.u+z.v-gap b k z at tx
    have enough:gap b k z≤z.u+z.v:=by omega
    rw [tx,periodic _ _ enough dep]
    refine ⟨rfl,?_⟩
    by_cases hl:2^b≤z.u
    · simp only [hl,decide_true,ite_true] at tm tu
      have tv:T.v=z.v:=by simp [T,reduced,hf,hl]
      have sm:z.v<2^b:=by omega
      have boundU:0<T.u:=by omega
      have nne:z.u≥gap b k z+1:=by change T.u=z.u-gap b k z at tu;omega
      have eBound:e.toNat≤1:=by cases e <;> decide
      change T.u-e.toNat=z.u-e.toNat-gap b k z at tm
      rw [tm]
      exact periodic _ _ (by change gap b k z≤z.u-e.toNat;omega) dep
    · simp only [hl,decide_false] at tm
      change T.u-e.toNat=z.u-e.toNat at tm
      rw [tm]
  · simp [T,reduced,hf]
end ECDSAAdd.Entrant.StairPacket.Shadow

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 10000

def rowBefore (inv:Bool) (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :=
  if inv then shadowRow b k z g s else initialRow b k z g s

def rowAfter (inv:Bool) (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :=
  if inv then initialRow b k z g s else shadowRow b k z g s

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic

theorem bitAt (r:List Wire) (s:BasisState) (i:Nat) (h:i<r.length):
    s (r.getD i 0)=(regValue r s).testBit i := by
  have v:=regValue_bit r i 0 s h
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases b:s (r.getD i 0) <;> simp only [b,Bool.toNat_false,Bool.toNat_true] at v ⊢ <;> simp [←v]

theorem takeValue (r:List Wire) (n:Nat) (bound:n≤r.length) (s:BasisState) :
    regValue (r.take n) s=regValue r s%2^n := by
  have h:=regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left bound] at h
  rw [h,Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by simpa only [List.length_take,Nat.min_eq_left bound] using regValue_lt (r.take n) s)).symm

theorem slice_value (r:List Wire) (k:Nat) (hi:k+4≤r.length) (s:BasisState) :
    regValue ((r.drop k).take 4) s=nibble (regValue r s) (2^k) := by
  rw [takeValue _ _ (by simp;omega),PortalValues.shiftedValue _ _ (by omega)]
  rfl

private theorem nibble_inverse : ∀x:Fin 16,(15-x.val) ^^^ 15=x.val := by decide +kernel

theorem sign_digits (r:List Wire) (size:r.length=4) (s:BasisState) (neg:Bool) :
    regValue r s=signedNibble neg (regValue r (fun q=>s q ^^ neg)) := by
  cases neg
  · simp [signedNibble]
  · simp only [Bool.xor_true,regValue_complement,size,signedNibble,ite_true]
    exact (nibble_inverse ⟨regValue r s,by simpa [size] using regValue_lt r s⟩).symm

structure Ports (A B:List Wire) (g n f u:Wire) (rs:List Wire) where
  a : A.length=4
  b : B.length=4
  clear : List Wire
  list : rs=A++B++[g,n,f,u]++clear

theorem read_ports {A B g n f u rs} (ports:Ports A B g n f u rs) (z:SkywalkNat.State) (k b:Nat) (G S:Bool) (s:BasisState)
    (G0:s g=G) (N:s n=PortalValues.negative S z.u)
    (F:s f=decide (Shadow.far b k z)) (U:s u=decide (Shadow.far b k z ∧ 2^b≤z.u))
    (zero:∀q∈ports.clear,s q=false)
    (x:regValue (if G then B else A) s=nibble (z.u+z.v) (cutUnit b k))
    (y:regValue (if G then A else B) (fun q=>s q ^^ PortalValues.negative S z.u)=
      nibble (z.u-(PortalValues.negative S z.u).toNat) (cutUnit b k)) :
    regValue rs s=initialRow b k z G S := by
  have h0:regValue ports.clear s=0:=(regValue_zero _ _).mpr zero
  have controlValue:regValue [g,n,f,u] s=(s g).toNat+2*((s n).toNat+2*((s f).toNat+2*(s u).toNat)):=by
    simp [regValue,Bool.toNat]
    cases s g <;> cases s n <;> cases s f <;> cases s u <;> rfl
  rw [ports.list,regValue_append,regValue_append,regValue_append,h0,Nat.mul_zero,Nat.add_zero,
    List.length_append,ports.a,ports.b,controlValue,G0,N,F,U]
  cases G <;> simp only [Bool.false_eq_true,ite_false,ite_true] at x y
  · have y0:=sign_digits B ports.b s (PortalValues.negative S z.u)
    rw [y] at y0
    rw [x,y0];simp only [initialRow,rowOf,encodedPair,Bool.false_eq_true,ite_false,Bool.toNat_false];omega
  · have y0:=sign_digits A ports.a s (PortalValues.negative S z.u)
    rw [y] at y0
    rw [x,y0];simp only [initialRow,rowOf,encodedPair,ite_true,Bool.toNat_true];omega

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic
set_option maxRecDepth 16000

theorem value_of_bits (r:List Wire) (s:BasisState) (W:Nat)
    (h:∀i<r.length,s (r.getD i 0)=W.testBit i):regValue r s=W%2^r.length := by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases low:i<r.length
  · rw [←bitAt r s i low,h i low,Nat.testBit_mod_two_pow]
    simp [low]
  · rw [Nat.testBit_mod_two_pow,Nat.testBit_lt_two_pow (lt_of_lt_of_le (regValue_lt r s)
      (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp [low]

theorem forward_all : wires forward=Finset.range width:=by decide +kernel

def leftWord (g e:Bool) (A M:Nat) := if g then signedNibble e M else A
def rightWord (g e:Bool) (A M:Nat) := if g then A else signedNibble e M

private theorem signedSmall (e:Bool) (M:Fin 16) : signedNibble e M<16 := by
  have t:∀b:Bool,∀m:Fin 16,signedNibble b m<16:=by decide +kernel
  exact t e M

theorem projected (b k:Nat) (z:SkywalkNat.State) (G S:Bool) :
    let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
    let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V;let W:=shadowRow b k z G S
    W%16=leftWord G e A M ∧ (W/16)%16=rightWord G e A M ∧ W/32768=0 := by
  dsimp only
  let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
  let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V
  have ar:A<16:=Nat.mod_lt _ (by decide)
  have mr:M<16:=Nat.mod_lt _ (by decide)
  have sn:signedNibble e M<16:=signedSmall e ⟨M,mr⟩
  have gr:G.toNat≤1:=by cases G <;> decide
  let f:=decide (Shadow.far b k z)
  let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  have fb:f.toNat≤1:=by cases f <;> decide
  have ub:u.toNat≤1:=by cases u <;> decide
  let h:=(if Shadow.far b k z then Shadow.high b k z%8 else 0)
  have hh:h<8:=by dsimp [h];split <;> omega
  let X:=encodedPair G e A M+256*G.toNat+1024*f.toNat+2048*u.toNat+4096*h
  have val:shadowRow b k z G S=X:=by
    unfold shadowRow X h
    by_cases off:Shadow.far b k z <;> simp [off,T,V,e,A,M,f,u]
  rw [val]
  change X%16=leftWord G e A M ∧ X/16%16=rightWord G e A M ∧ X/32768=0
  dsimp only [X,encodedPair,leftWord,rightWord]
  cases G <;> simp only [ite_true,Bool.false_eq_true,ite_false,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem output_values (ports:List Wire) (s:BasisState) (b k:Nat) (z:SkywalkNat.State) (G S:Bool)
    (plen:ports.length=width)
    (data:∀q∈wires forward,s (ports.getD q 0)=(shadowRow b k z G S).testBit q) :
    let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
    let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V
    regValue (ports.take 4) s=leftWord G e A M ∧
    regValue ((ports.drop 4).take 4) s=rightWord G e A M ∧ regValue (ports.drop 15) s=0 := by
  let W:=shadowRow b k z G S
  have p:=projected b k z G S
  have N:ports.length=23:=plen
  have whole:=value_of_bits ports s W (fun q h=>data q (forward_all ▸ Finset.mem_range.mpr (plen ▸ h)))
  rw [N,Nat.mod_eq_of_lt (show W<2^23 by have h:W/32768=0:=p.2.2;omega)] at whole
  rw [takeValue _ _ (by omega),whole,takeValue _ _ (by simp [N]),
    PortalValues.shiftedValue _ 4 (by omega),whole,PortalValues.shiftedValue _ 15 (by omega),whole]
  exact p

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic RailPair

theorem PackedCut.unchanged {lo hi g n f u neg far long orig result}
    (P:PackedCut lo hi g n f u neg far long orig result) (q:Wire) (qn:q≠n) (qf:q≠f) (qu:q≠u)
    (qh:q∉sites hi) : result.basis q=orig.basis q:=by
  by_cases l:q∈sites lo
  · obtain ⟨p,hp,e⟩:=List.mem_flatMap.mp l
    rcases List.mem_cons.mp e with rfl|tail
    · exact (P.low p hp).1
    · obtain rfl:=List.mem_singleton.mp tail
      exact (P.low p hp).2
  · exact P.frame q qn qf qu l qh

namespace EnterProof
structure Aperture (lo hi:List (Wire×Wire)) (g n f u:Wire) (ports:List Wire) (L:SkywalkIntegerLayout)
    (net:Wire→Wire) (cut:Nat) where
  a : List Wire
  b : List Wire
  spec : Ports a b g n f u ports
  g0 : net g=L.previous
  xa : a.map net=(L.a.drop cut).take 4
  xb : b.map net=(L.b.drop cut).take 4
  na : cut+4≤L.a.length
  nb : cut+4≤L.b.length
  protected0 : ∀q∈g::(a++b++spec.clear),q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi
  temps : ∀q∈spec.clear,net q∈L.carry

theorem read_packed {lo hi g n f u rs L net b k} (A:Aperture lo hi g n f u rs L net (b+k))
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
      (shape:ns.map net=(full.drop (b+k)).take 4) (sz:b+k+4≤full.length) (flip:Bool) :
      regValue ns (fun q=>result.basis q ^^ flip)=nibble (regValue full (fun q=>raw.basis q ^^ flip)) (cutUnit b k) := by
    calc
      _=regValue ns (fun q=>raw.basis (net q) ^^ flip):=regValue_congr _ _ _ (fun q h=>congrArg (· ^^ flip) (eq q (ok q h)))
      _=regValue (ns.map net) (fun q=>raw.basis q ^^ flip):=(PortalValues.unroute net ns (fun q=>raw.basis q ^^ flip)).symm
      _=_:=by rw [shape,slice_value _ _ sz];rfl
  have left (s:Bool):=view A.a L.a (by intro q h;simp [h]) A.xa A.na s
  have right (s:Bool):=view A.b L.b (by intro q h;simp [h]) A.xb A.nb s
  apply read_ports A.spec z k b G S result.basis gOk P.sign P.mode P.orientation clean
  · cases G
    · exact (by simpa using left false : regValue A.a result.basis=_).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.1)
    · exact (by simpa using right false : regValue A.b result.basis=_).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.1)
  · cases G
    · exact (right neg).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.2)
    · exact (left neg).trans (congrArg (fun x=>nibble x (cutUnit b k)) math.2.2.2)

end EnterProof
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic

theorem join (lo hi:List Wire) (cut W:Nat) (s:BasisState) (size:lo.length=cut)
    (low:regValue lo s=W%2^cut) (high:regValue hi s=nibble W (2^cut)) (bound:W/(2^cut)<16) :
    regValue (lo++hi) s=W := by
  rw [regValue_append,size,low,high,nibble,Nat.mod_eq_of_lt bound,Nat.mod_add_div]

theorem norm_nibble (r:List Wire) (size:r.length=4) (s:BasisState) (e:Bool) (Y:Nat)
    (v:regValue r s=signedNibble e Y) : regValue r (fun q=>s q ^^ e)=Y := by
  have eq: signedNibble e (regValue r (fun q=>s q ^^ e))=signedNibble e Y:=(sign_digits _ size s e).symm.trans v
  exact Nat.xor_left_inj.mp eq

theorem ordinary (rs:List Wire) (bit:Nat) (length:rs.length=bit+1) (s:BasisState) (N:Nat)
    (low:N<2^bit) (value:regValue rs s=N) : signedRegValue rs s=N:=by
  simp [signedRegValue,signedDecode,length,value,low]

theorem signed (rs:List Wire) (bit:Nat) (length:rs.length=bit+1) (s:BasisState) (u:Nat) (sg:Bool)
    (small:u<2^bit)
    (value:regValue rs (fun q=>s q ^^ PortalValues.negative sg u)=u-(PortalValues.negative sg u).toNat) :
    signedRegValue rs s=SkywalkRails.signed sg u:=by
  have lim:=regValue_lt rs s
  rw [length,pow_succ] at lim
  by_cases neg:PortalValues.negative sg u
  · have su:sg=true ∧ 0<u:=by simpa [PortalValues.negative] using neg
    rw [neg] at value
    simp only [Bool.xor_true,regValue_complement,length,pow_succ,Bool.toNat_true] at value
    unfold signedRegValue signedDecode
    simp only [length,Nat.add_sub_cancel,show ¬regValue rs s<2^bit by omega,ite_false,pow_succ,
      SkywalkRails.signed,su.1,ite_true]
    omega
  · have no:PortalValues.negative sg u=false:=by simpa using neg
    simp only [no,Bool.xor_false,Bool.toNat_false,Nat.sub_zero] at value
    rw [ordinary rs bit length _ u small value]
    cases sg
    · rfl
    · have zu:u=0:=by simp [PortalValues.negative] at no;omega
      simp [zu,SkywalkRails.signed]

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic
set_option maxRecDepth 12000

theorem tags (b k:Nat) (z:SkywalkNat.State) (g s:Bool) :
    let W:=shadowRow b k z g s
    W.testBit 8=g ∧ W.testBit 9=false ∧ W.testBit 10=decide (Shadow.far b k z) ∧
    W.testBit 11=decide (Shadow.far b k z ∧ 2^b≤z.u) ∧ W/4096=
      (if Shadow.far b k z then Shadow.high b k z%8 else 0) := by
  let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative s z.u
  let A:=nibble (T.u+T.v) V;let M:=nibble (T.u-e.toNat) V
  have ar:A<16:=Nat.mod_lt _ (by decide)
  have mr:M<16:=Nat.mod_lt _ (by decide)
  have small:∀x:Fin 16,∀n:Bool,signedNibble n x<16:=by decide +kernel
  have sn:signedNibble e M<16:=small ⟨_,mr⟩ e
  let f:=decide (Shadow.far b k z);let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  let h:=(if Shadow.far b k z then Shadow.high b k z%8 else 0)
  let W:=encodedPair g e A M+256*g.toNat+1024*f.toNat+2048*u.toNat+4096*h
  have w:shadowRow b k z g s=W:=by
    unfold shadowRow W h
    by_cases absent:Shadow.far b k z <;> simp [absent,T,V,e,A,M,f,u]
  have base:encodedPair g e A M<256:=by cases g <;> dsimp [encodedPair] <;> omega
  dsimp only
  rw [w]
  change W.testBit 8=g ∧ W.testBit 9=false ∧ W.testBit 10=f ∧ W.testBit 11=u ∧ W/4096=h
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  change decide (W/256%2=1)=g ∧ decide (W/512%2=1)=false ∧ decide (W/1024%2=1)=f ∧
    decide (W/2048%2=1)=u ∧ W/4096=h
  dsimp only [W]
  cases g <;> cases f <;> cases u <;> simp only [Bool.toNat_true,Bool.toNat_false,decide_eq_true_eq,decide_eq_false_iff_not] <;> omega

theorem actual_tags (ports:List Wire) (s:BasisState) (b k:Nat) (z:SkywalkNat.State) (G S:Bool)
    (h:∀q∈wires forward,s (ports.getD q 0)=(shadowRow b k z G S).testBit q) :
    s (ports.getD 8 0)=G ∧ s (ports.getD 9 0)=false ∧ s (ports.getD 10 0)=decide (Shadow.far b k z) ∧
    s (ports.getD 11 0)=decide (Shadow.far b k z ∧ 2^b≤z.u) := by
  rw [h 8 (by decide +kernel),h 9 (by decide +kernel),h 10 (by decide +kernel),h 11 (by decide +kernel)]
  have ⟨a,b,c,d,_⟩:=tags b k z G S
  exact ⟨a,b,c,d⟩

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic RailPair
set_option maxRecDepth 12000

structure WordPlacement {lo hi g n f u rs L net b k}
    (A:Aperture lo hi g n f u rs L net (b+k)) (P:Program) where
  lowA : List Wire
  lowB : List Wire
  al : lowA.length=b+k
  bl : lowB.length=b+k
  xa : lowA.map net=L.a.take (b+k)
  xb : lowB.map net=L.b.take (b+k)
  aTop : rs.take 4=A.a
  bTop : (rs.drop 4).take 4=A.b
  protected0 : ∀q∈lowA++lowB,q∉wires P ∧ q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi
  portsCount : rs.length=width

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed RailPair IntegerPacket
set_option maxRecDepth 16000

end ECDSAAdd.Entrant.StairPacket.EnterProof

end
end
-- ==== w4: par-c1 batch 2 (a1dfeeb, Leave225Join appendix) ====

/-! par-c1: generic leave families, batch 2: the companion pieces (dadon's `LeaveCompanion{s}`). The pieces that live
inside par-b's fixed segment `leaveFix2` (long latch, mask, companion erase) are identified with dadon's gadgets by
one small decide over the window blocks (fixed segment only); the low-store restore is generic. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror PortalAnd
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

def longPairs (j : Fin 24) : List (Wire × Wire) := (List.range 18).map (fun i => (b0P (start j) + i, 1557 + i))
def fullA (j : Fin 24) : List Wire := (List.range 18).map (a0P (start j) + ·)
def fullM (j : Fin 24) : List Wire := (List.range 18).map (b0P (start j) + ·)
def fullC : List Wire := (List.range 17).map (1559 + ·)
def smallA (j : Fin 24) : List Wire := (List.range (lowsP (start j))).map (a0P (start j) + ·)
def smallM (j : Fin 24) : List Wire := (List.range (lowsP (start j))).map (b0P (start j) + ·)
def smallC (j : Fin 24) : List Wire := (List.range (lowsP (start j) - 1)).map (1559 + ·)
/-- dadon's `mask`: `[.X 1557, .CX (a0-1) 1557, .CCX (b0-1) 1557 1558]`. -/
def maskP (j : Fin 24) : Program := [.X 1557, .CX (a0P (start j) - 1) 1557, .CCX (b0P (start j) - 1) 1557 1558]

/-- `leaveFix2` = long latch ++ mask ++ companion erase (dadon's cuts 93/169/172/242). -/
theorem fix2_parts : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    GateMirror.forward (leaveFix2 (start j) (sbP (start j))) =
      latch true none 1556 (b0P (start j) - 1) (longPairs j) ++ (maskP j ++
        Companion.erase (fullA j) (fullM j) fullC 1556 1558) := by
  decide +kernel

theorem long_layout : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    (1556 :: (b0P (start j) - 1) :: PortalAnd.sites (longPairs j)).Nodup := by
  decide +kernel

theorem full_geometry : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    Companion.Geometry (fullA j) (fullM j) fullC 1556 1558 := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- dadon's `long_run`. -/
theorem long_run (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State) (m : List Bool)
    (clean : ∀ p ∈ longPairs j, s.basis p.2 = false) :
    run (latch true none 1556 (b0P (start j) - 1) (longPairs j)) m s =
      ⟨s.phase, writeBit s.basis 1556 (s.basis 1556 ^^ ((digits (b0P (start j) - 1) (longPairs j)).any s.basis))⟩ := by
  simpa only [active, Option.elim_none, Bool.true_and] using
    run_latch true none 1556 (b0P (start j) - 1) (longPairs j) (long_layout j h0 h1) (by simp) s m clean

/-- dadon's `erase_run`. -/
theorem erase_run (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State) (m : List Bool)
    (clean : ∀ q ∈ fullC, s.basis q = false)
    (input : (regValue (fullM j) s.basis + (s.basis 1558).toNat) % 2^(fullM j).length =
      copyValue (some 1556) s.basis (regValue (fullA j) s.basis)) :
    let e := Companion.erase (fullA j) (fullM j) fullC 1556 1558
    (run e m s).phase = s.phase ∧ (∀ q, q ∉ fullM j → (run e m s).basis q = s.basis q) ∧
      regValue (fullM j) (run e m s).basis = 0 :=
  Companion.clear (fullA j) (fullM j) fullC 1556 1558 (full_geometry j h0 h1) s m clean input

/-! The low-store restore (generic): `lowRest` = companion restore ++ release mask. -/

def releaseMaskP (j : Fin 24) : Program :=
  [.measureX 1558 [] [.CZ (b0P (start j) - 1) 1557], .CX (a0P (start j) - 1) 1557, .X 1557]

theorem forward_xsG' (xs : List Wire) : GateMirror.forward (xsG xs) = notRegister xs := by
  simp only [xsG, GateMirror.forward, notRegister, List.map_map]; rfl

theorem copy_map (c : Wire) (f g : Nat → Wire) : ∀ xs : List Nat,
    copyRegister (some c) (xs.map f) (xs.map g) = xs.map (fun i => Instr.CCX c (f i) (g i))
  | [] => rfl
  | x::xs => by simp only [List.map_cons, copyRegister, copyGate, copy_map c f g xs]; rfl

theorem lowRest_parts (j : Fin 24) :
    GateMirror.forward (lowRest (start j)) =
      Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558 ++ releaseMaskP j := by
  have hc : GateMirror.forward ((List.range (lowsP (start j))).map
      (fun i => Gate.ccx 1556 (a0P (start j) + i) (b0P (start j) + i))) =
      copyRegister (some 1556) (smallA j) (smallM j) := by
    rw [smallA, smallM, copy_map]; simp only [GateMirror.forward, List.map_map]; rfl
  simp only [lowRest, forward_app, forward_addG, forward_xsG', hc, Companion.restore, HighBankUnit.sub, mappedSub,
    smallM, smallC, List.append_assoc]
  rfl

theorem small_geometry : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    Companion.Geometry (smallA j) (smallM j) (smallC j) 1556 1558 := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- dadon's `restore_run`. -/
theorem restore_run (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State) (m : List Bool)
    (clean : ∀ q ∈ smallC j, s.basis q = false) (input : regValue (smallM j) s.basis = 0) :
    let r := Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558
    (run r m s).phase = s.phase ∧ (∀ q, q ∉ smallM j → (run r m s).basis q = s.basis q) ∧
      regValue (smallM j) (run r m s).basis =
        (copyValue (some 1556) s.basis (regValue (smallA j) s.basis) + 2^(smallM j).length - (s.basis 1558).toNat) %
          2^(smallM j).length :=
  Companion.write (smallA j) (smallM j) (smallC j) 1556 1558 (small_geometry j h0 h1) s m clean input

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ==== end PrizeLeave225Join2ee362a ====

-- ==== begin PrizeTail46901f669 ====
section

section

-- proof-only helper block
section
namespace ECDSAAdd.Entrant.WSlimMain
open ECDSAAdd
/-! Generic single-pass lemmas. Proof-only helpers: they let a
`decide +kernel` run ONE Bool pass over a concrete program instead of building the program-wide
`Finset` of `wires` (quadratic `Finset.union`, deep non-tail recursion). -/

/-- Wires of a correction list, as a list. -/
def corrList : List Correction → List Wire
  | [] => []
  | .Z t :: cs => t :: corrList cs
  | .CZ a b :: cs => a :: b :: corrList cs

/-- Wires of an instruction, as a list (same members as `Instr.wires`). -/
def instrList : Instr → List Wire
  | .X t => [t]
  | .CX c t => [c, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c₀ c₁ => t :: (corrList c₀ ++ corrList c₁)

theorem mem_correctionWires_iff (q : Wire) (cs : List Correction) :
    q ∈ correctionWires cs ↔ q ∈ corrList cs := by
  induction cs with
  | nil => simp [correctionWires, corrList]
  | cons c cs ih => cases c <;> simp [correctionWires, corrList, ih]

theorem mem_instr_wires_iff (q : Wire) (i : Instr) : q ∈ i.wires ↔ q ∈ instrList i := by
  cases i <;> simp [Instr.wires, instrList, mem_correctionWires_iff]

/-- `∀ q ∈ wires P, p q` from one Bool pass over `P`. -/
theorem forall_mem_wires_of_all {P : Program} {p : Wire → Bool}
    (h : P.all (fun i => (instrList i).all p) = true) : ∀ q ∈ wires P, p q = true := by
  intro q hq
  induction P with
  | nil => simp [wires] at hq
  | cons i P ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [wires, Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact List.all_eq_true.mp h.1 q ((mem_instr_wires_iff q i).mp hq)
    · exact ih h.2 hq

/-- `wires P ⊆ Finset.range n` from one Bool pass over `P` (no list membership). -/
theorem wires_subset_range_of_all {P : Program} {n : Nat}
    (h : P.all (fun i => (instrList i).all (fun q => decide (q < n))) = true) : wires P ⊆ Finset.range n := by
  intro q hq
  simpa using forall_mem_wires_of_all h q hq

end ECDSAAdd.Entrant.WSlimMain
end

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ
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
theorem frame (j : Fin 24) : start j=75+15*j.val ∧ j.val<24 ∧ 2*sbP (start j)+start j≤513 ∧
    512≤2*sbP (start j)+start j ∧ 3<wpP (start j) ∧ wpP (start j)+sbP (start j)≤242 := by
  have hj:=j.isLt
  refine ⟨rfl,hj,?_,?_,?_,?_⟩ <;> simp only [start,wpP,railP,sbP] <;> (try split_ifs) <;> omega

end ECDSAAdd.Entrant.StairPacket.EnterJ
end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BarrelBits
open Partial Leave225Barrel Leave225Control Leave225Shift HighBankBarrel HighBankControl
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave225BarrelBits

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Middle
open Arithmetic Partial Leave225Barrel Leave225High Leave225Word Leave225Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave225Middle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NearWord
open Partial Leave225Join Leave225Barrel Leave225Word HighBankJoin HighBankReassemble
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225NearWord

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BarrelBits
open Partial Leave240Barrel Leave240Control Leave240Shift HighBankBarrel HighBankControl
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave240BarrelBits

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Middle
open Arithmetic Partial Leave240Barrel Leave240High Leave240Word Leave240Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave240Middle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NearWord
open Partial Leave240Join Leave240Barrel Leave240Word HighBankJoin HighBankReassemble
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240NearWord

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BarrelBits
open Partial Leave255Barrel Leave255Control Leave255Shift HighBankBarrel HighBankControl
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.Leave255BarrelBits

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Middle
open Arithmetic Partial Leave255Barrel Leave255High Leave255Word Leave255Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave255Middle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NearWord
open Partial Leave255Join Leave255Barrel Leave255Word HighBankJoin HighBankReassemble
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255NearWord

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket
attribute [local irreducible] run onRails
set_option maxHeartbeats 2000000

/-- An archive edit follows the first native tick. Its local preservation of
the active rails and first record suffices for the complete fifteen-step trace. -/
theorem split_run (j:Fin 24) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (s:State) (m n:List Bool)
    (ready:onRails j 0 z s.basis) (v:State)
    (active:onRails j 1 (SkywalkTrace.next z) v.basis)
    (first:cell (shape j) 0 (mappedBasis j v.basis)=
      cell (shape j) 0 (mappedBasis j (run (routed j 0 1) m s).basis)) :
    let out:=run (routed j 1 14) n v
    onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
    readCells (shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z := by
  have post:=route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have back:=route_records j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) v n active
  have front:=(route_records j 0 1 (by decide) z odd s m ready).1
  have firstValue:=congrArg List.head? front
  simp only [readCells,SkywalkTrace.trace,List.head?_cons,Option.some.injEq] at firstValue
  exact ⟨post.2,congr (congrArg List.cons ((back.2 0 (by decide)).trans (first.trans firstValue))) back.1⟩


end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed

/-- Every future raw S position is clean; prior history may already be byte-encoded. -/
theorem stock_history (d:Bool) (x p i:Nat) (s:State) (stage:Rolling1588.Integer.Stage base d x p i s.basis)
    (j:Nat) (after:i≤j) (limit:j<512) : s.basis (base (1028+j))=false:=by
  obtain ⟨raw,hraw,hs⟩:=stage
  have f:=(W.compactSkywalkStage_fields_iff base _ i (by omega) base_pool_nodup raw.basis).mp hraw
  have mem:base (1028+j)∈(W.compactSkywalkTickLayout base j).wires:=by
    change (W.compactSkywalkTickLayout base j).history∈_
    simp [SkywalkIntegerLayout.wires]
  rw [hs]
  have dis:=Rolling1588.Integer.prefix_disjoint_layout base d base_pool_nodup i j after limit
  exact (run_preserves_outside _ [] raw _ (fun h=>Finset.disjoint_left.mp dis h (List.mem_toFinset.mpr mem))).trans
    (f.2.2.2.2.1 j after limit).2

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def idx : Fin 24 := ⟨10,by decide⟩
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
def idx : Fin 24 := ⟨11,by decide⟩
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section
namespace ECDSAAdd.Entrant.StairPacket.EnterJ
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

end ECDSAAdd.Entrant.StairPacket.EnterJ
end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NearHigh
open Arithmetic Partial Leave225Barrel Leave225High HighBankControl HighBankAdjust HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225NearHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NearHigh
open Arithmetic Partial Leave240Barrel Leave240High HighBankControl HighBankAdjust HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240NearHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NearHigh
open Arithmetic Partial Leave255Barrel Leave255High HighBankControl HighBankAdjust HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255NearHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw

theorem shadow_odd (b:Nat) (z:SkywalkNat.State) (small:min z.u z.v<2^b) (odd:z.v%2=1) :
    (Shadow.reduced b 15 z).v%2=1 := by
  by_cases f:Shadow.far b 15 z
  · have h:IntegerHigh.Rel 15 z (Shadow.reduced b 15 z):=(Shadow.represented _ _ _ small f).1
    suffices ∀x y:SkywalkNat.State,IntegerHigh.Rel 15 x y → x.v%2=1 → y.v%2=1 from this _ _ h odd
    intro x y rel
    cases rel with
    | left => exact id
    | right B s D _ =>
      change (B+32768*D)%2=1 → B%2=1
      omega
  · simpa [Shadow.reduced,f] using odd

theorem true_records (b:Nat) (z:SkywalkNat.State) (small:min z.u z.v<2^b) (odd:z.v%2=1) (G S:Bool) :
    let T:=Shadow.reduced b 15 z
    SkywalkTrace.trace 15 (encode G S T.u T.v)=SkywalkTrace.trace 15 (encode G S z.u z.v) := by
  by_cases f:Shadow.far b 15 z
  · have h:=(Shadow.represented _ _ _ small f).1
    have o:=shadow_odd b z small odd
    exact (IntegerHigh.trace_eq h G S G S (by omega) odd (by omega) o).symm
  · simp [Shadow.reduced,f]

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction

theorem read_cells (p:Shape) (start count index:Nat) (b:BasisState) (h:index<count) :
    read (readCells p start count b) index=cell p (start+index) b := by
  induction count generalizing start index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp [StairArchiveRaw.read,readCells]
    | succ index =>
      change read (readCells p (start+1) count b) index=_
      simpa only [Nat.add_assoc,Nat.add_comm 1 index] using ih (start+1) index (by omega)

def nativeRawPort (j:Fin 24) (q:Nat) :=
  let p:=ports (shape j) (5+q/2)
  windowNet j (if q%2=0 then p.a0 else p.history)

theorem native_raw_read (j:Fin 24) (s:State) (q:Nat) (h:q<20) :
    let cells:=readCells (shape j) 0 15 (mappedBasis j s.basis)
    s.basis (nativeRawPort j q)=letterBit (read (cells.drop 5) (q/2)) q := by
  have head : ∀xs:List (Bool×Bool), read (xs.drop 5) (q/2)=read xs (5+q/2):=by
    intro xs
    simp only [StairArchiveRaw.read,List.getElem?_drop]
  dsimp only
  rw [head,read_cells _ 0 15 _ _ (by omega),Nat.zero_add]
  unfold nativeRawPort letterBit cell mappedBasis
  split <;> rfl

namespace ArchiveBoundary240
def sourceIdx : Fin 24 := ⟨10,by decide⟩
theorem chronological : ∀i:Fin 20, rawPorts ⟨i,by omega⟩=nativeRawPort sourceIdx i := by decide +kernel
end ArchiveBoundary240

namespace ArchiveBoundary255
end ArchiveBoundary255

namespace ArchiveJ
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
end ArchiveJ

namespace ArchiveBoundary270
end ArchiveBoundary270


end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section
namespace ECDSAAdd.Entrant.StairPacket.EnterJ
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

end ECDSAAdd.Entrant.StairPacket.EnterJ
end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NearMiddle
open Arithmetic Partial Leave225Barrel Leave225High Leave225Word Leave225Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave225NearMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NearMiddle
open Arithmetic Partial Leave240Barrel Leave240High Leave240Word Leave240Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave240NearMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NearMiddle
open Arithmetic Partial Leave255Barrel Leave255High Leave255Word Leave255Join HighBankBarrel HighBankAdjust

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave255NearMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section
namespace ECDSAAdd.Entrant.StairPacket.EnterJ
open Arithmetic MappedCompressed Partial EnterProof RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

end ECDSAAdd.Entrant.StairPacket.EnterJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225OutputPorts
open Arithmetic Leave225Word Leave225Barrel LeaveCompanion225
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave225OutputPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240OutputPorts
open Arithmetic Leave240Word Leave240Barrel LeaveCompanion240
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave240OutputPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255OutputPorts
open Arithmetic Leave255Word Leave255Barrel LeaveCompanion255
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave255OutputPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket
def watch (j:Fin 24) :=
  let p:=shape j
  let L:=ports p 1
  (L.a++L.b++[L.previous]++L.carry++((List.range' 1 14).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

set_option linter.unusedSimpArgs false in
theorem watch_congr (j:Fin 24) (s t:State) (agree:∀q∈watch j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:onRails j 1 z s.basis) :
    onRails j 1 z t.basis ∧ cell (shape j) 0 (mappedBasis j t.basis)=cell (shape j) 0 (mappedBasis j s.basis) := by
  let p:=shape j
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

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace NativePack225
end NativePack225
namespace NativePack240
end NativePack240
namespace NativePack255
end NativePack255

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic native pack of block `j` (par-c2): the stock pack at tick `s-10` (`s = start j`) in the `OB5.sig s`
frame, then the window archive of block `j-1` (`archiveLoadP (prev j)`). dadon's `NativePack{s}` is
`NativeJ` at `j = (s-75)/15`. Valid for `2 ≤ j` (the pack is due: `s-10 ≥ 95`, `s-10 ≡ 0 mod 5`). -/

end ECDSAAdd.Entrant.StairPacket.NativeJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! Generic first-form native pack (par-c2): the window's first block `j` (`s = start j`) packs the five
pre-window letters at tick `s` (group `s-5`) in the `OB5.sig s` frame; no archive. dadon's `NativePack225`
(first block of 225..270) is `NativeFirstJ 10`. -/

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

theorem archive_blank (d:Bool) (i:Fin 157) (h:16≤ i.val) : get (code d) i=0 := by
  by_cases low:i.val<23
  · have table:∀j:Fin 23,16≤ j.val → get (code d) j=0 := by cases d <;> decide +kernel
    exact table ⟨i,low⟩ h
  · exact (blank true d i (by omega)).2

namespace ArchiveBoundary240
def nextIdx : Fin 24 := ⟨11,by decide⟩
theorem past_only : ∀i:Fin 23,rawPorts ⟨i,by omega⟩∉watch nextIdx := by decide +kernel
end ArchiveBoundary240

namespace ArchiveBoundary255
end ArchiveBoundary255

namespace ArchiveJ
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
end ArchiveJ


end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.EnterProof

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails

def body (j:Fin 24) (admin:Program) := routed j 0 1 ++ (admin ++ routed j 1 14)
def unbody (j:Fin 24) (reverse:Program) := unrouted j 1 14 ++ (reverse ++ unrouted j 0 1)

structure AdminResult (j:Fin 24) (reverse:Program) (src out:State) : Prop where
  phase : out.phase=src.phase
  unchanged : ∀q∈watch j,out.basis q=src.basis q
  undo : ∀m,run reverse m out=src

theorem body_run (j:Fin 24) (admin reverse:Program) (s:State) (m:List Bool)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:onRails j 0 z s.basis)
    (mid:let src:=run (routed j 0 1) m s
      AdminResult j reverse src (run admin (m.drop (measurementCount (routed j 0 1))) src)) :
    let out:=run (body j admin) m s
    out.phase=s.phase ∧ onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unbody j reverse) n out=s := by
  let src:=run (routed j 0 1) m s
  let t:=m.drop (measurementCount (routed j 0 1))
  let pre:=run admin t src
  let n:=t.drop (measurementCount admin)
  have head:=route_frame j 0 1 (by decide) z odd s m active
  have valid:onRails j 1 (SkywalkTrace.next z) src.basis:=head.2
  have pass:=watch_congr j src pre mid.unchanged _ valid
  have span:=split_run j z odd s m n active pre pass.1 pass.2
  have last:=route_frame j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n pass.1
  dsimp only [body,unbody]
  simp only [run_append,run_take]
  refine ⟨last.1.trans (mid.phase.trans head.1),span.1,span.2,?_⟩
  intro r
  have endBack:=route_undo j 1 14 (by decide) (SkywalkTrace.next z) (nextOdd z odd) pre n r pass.1
  change run (unrouted j 0 1) _ (run reverse _ (run (unrouted j 1 14) r (run (routed j 1 14) n pre)))=s
  rw [endBack,mid.undo]
  exact route_undo j 0 1 (by decide) z odd s m _ active

namespace NativePack225
end NativePack225

namespace NativePack240
end NativePack240

namespace NativePack255
end NativePack255

namespace NativePack270
def program (d:Bool) := renameProgram (OB5.sig 270) (Rolling1588.packAtTick d 260)
end NativePack270
namespace NativePack270
end NativePack270


end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run unrouted onRails
namespace NativePack225
end NativePack225

namespace NativePack240
open ArchiveBoundary240
end NativePack240

namespace NativePack255
open ArchiveBoundary255
end NativePack255

namespace NativeJ
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
end NativeJ


end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run unrouted onRails
namespace NativePack225
end NativePack225
namespace NativePack240
end NativePack240
namespace NativePack255
end NativePack255

namespace NativeJ
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
end NativeJ

end ECDSAAdd.Entrant.StairPacket

end


section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
end ECDSAAdd.Entrant.StairPacket.NativeFirstJ

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkIntegerLayout.wires

def firstUnchanged (j:Fin 24) (q:Wire) : Prop :=
  let r:=windowNet j q
  r=(ports (shape j) 0).previous ∨ r∉(ports (shape j) 0).wires
instance (j:Fin 24) (q:Wire) : Decidable (firstUnchanged j q) := by unfold firstUnchanged;infer_instance

theorem first_preserves (j:Fin 24) (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (s:State) (m:List Bool)
    (ready:onRails j 0 z s.basis) (q:Wire) (free:firstUnchanged j q) :
    (run (routed j 0 1) m s).basis q=s.basis q := by
  let p:=shape j
  let L:=ports p 0
  let virt:=pullState (windowNet j) s
  let v:=windowNet j q
  have inv:windowNet j v=q:=by
    apply OB5.sig_invol
    have b:=j.isLt
    simp [start];omega
  have step:=pull_routed j 0 1 (by decide) m s
  simp only [seq,List.append_nil] at step
  have at_q:=congrArg (fun x:State=>x.basis v) step
  change (run (routed j 0 1) m s).basis (windowNet j v)=(run (skywalkIntegerTick L) m virt).basis v at at_q
  rw [inv] at at_q
  refine at_q.trans (Eq.trans ?_ (show virt.basis v=s.basis q from congrArg s.basis inv))
  rcases free with e|e
  · change v=L.previous at e
    rw [e]
    obtain ⟨ha,hb,hg,hc,hnew⟩:=ready
    obtain ⟨he,hh⟩:=hnew 0 (by decide) (by change 0<15;decide)
    obtain ⟨_,_,_,_,_,prev,_⟩:=executed p ⟨0,by change 0<15;decide⟩ _ _ _ odd virt m ⟨ha,hb,hg,he,hh,hc⟩
    exact prev.trans hg.symm
  · apply run_preserves_outside
    exact fun used=>e (List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok p ⟨0,by change 0<15;decide⟩)).1 used))


end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

theorem preserve_readonly (P:Program) (q:Wire) (unused:∀i∈P,CodecBitSliceVerify.target i≠q)
    (s:State) (m:List Bool) : (run P m s).basis q=s.basis q := by
  induction P generalizing s m with
  | nil=>rfl
  | cons i rest ih=>
    change (run ([i]++rest) m s).basis q=s.basis q
    rw [run_append,ih (fun j h=>unused _ (List.mem_cons_of_mem _ h))]
    have neq:=unused i (by simp)
    cases i <;> simp only [CodecBitSliceVerify.target] at neq <;> simp [run,measureAndCorrect,writeBit,Ne.symm neq]

theorem legal_congr {a b:Fin 10→Wire} {s t:BasisState}
    (same:∀i,s (a i)=t (b i)) (ok:MeasuredCodec5.legalAt b t) : MeasuredCodec5.legalAt a s := by
  apply (MeasuredCodec5.legalAt_iff _ _).mpr
  intro i
  simp only [same]
  exact (MeasuredCodec5.legalAt_iff _ _).mp ok i

namespace NativePack225
end NativePack225
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run onRails unrouted

end ECDSAAdd.Entrant.StairPacket.NativePack225

end
end
-- ==== end PrizeTail46901f669 ====

-- ==== begin PrizeTail227303371 ====
section

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed RailPair

theorem PackedCut.unique {lo hi g n f u neg far long origin a b}
    (x:PackedCut lo hi g n f u neg far long origin a) (y:PackedCut lo hi g n f u neg far long origin b) : a=b:=by
  have phase:=x.phase.trans y.phase.symm
  have basis:a.basis=b.basis:=by
    funext q
    by_cases hn:q=n
    · subst q;exact x.sign.trans y.sign.symm
    by_cases hf:q=f
    · subst q;exact x.mode.trans y.mode.symm
    by_cases hu:q=u
    · subst q;exact x.orientation.trans y.orientation.symm
    by_cases hh:q∈sites hi
    · obtain ⟨p,hp,hit⟩:=List.mem_flatMap.mp hh
      rcases List.mem_cons.mp hit with rfl|tail
      · exact (x.upper _ hp).1.trans (y.upper _ hp).1.symm
      · obtain rfl:=List.mem_singleton.mp tail
        exact (x.upper _ hp).2.trans (y.upper _ hp).2.symm
    · exact (x.unchanged _ hn hf hu hh).trans (y.unchanged _ hn hf hu hh).symm
  cases a;cases b;congr
namespace Portal270Flag
set_option exponentiation.threshold 1024
end Portal270Flag
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.HighBankSum
open HighBankAdjust

/-- Convert the signed high-bank update into the correction to the saved quotient. -/
theorem corrected (H w d : Nat) (c neg : Bool) (far : 2 ≤ H)
    (room : H-2+d < 2^w) (legal : neg=true → c=true)
    (digit : d=c.toNat+2*(!neg).toNat) : adjusted H w c neg=H-2+d := by
  cases c <;> cases neg <;> simp_all [adjusted,Bool.toNat]
  all_goals first
    | omega
    | exact Nat.mod_eq_of_lt (by omega)
    | rw [Nat.mod_eq_of_lt (by omega)] <;> omega
    | rw [show H+2^w-1 = H-1+2^w by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)] ; omega

/-- The restored word begins at bit E of the actual integer sum. -/
theorem value (F S H w E t : Nat) (c neg : Bool)
    (gap : F=S+2^t*(2^E*(H-2))) (far : 2 ≤ H)
    (room : H-2+S/2^E/2^t < 2^w) (legal : neg=true → c=true)
    (digit : S/2^E/2^t=c.toNat+2*(!neg).toNat) :
    F/2^E = 2^t*adjusted H w c neg + S/2^E%2^t := by
  have h := corrected H w _ c neg far room legal digit
  rw [h,gap,show 2^t*(2^E*(H-2))=2^E*(2^t*(H-2)) by ring,
      Nat.add_mul_div_left _ _ (by positivity),Nat.mul_add]
  have decomposition := Nat.mod_add_div (S/2^E) (2^t)
  omega

end ECDSAAdd.Entrant.StairPacket.HighBankSum

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveRelocation

def one (a b : Wire) : Program := [.CX a b,.CX b a,.CX a b]
def flip (a b q : Wire) := if q=a then b else if q=b then a else q
def program (xs : List (Wire×Wire)) := xs.flatMap (fun p=>one p.1 p.2)
def source (xs : List (Wire×Wire)) (q : Wire) := xs.foldr (fun p i=>flip p.1 p.2 i) q

theorem oneRun (a b : Wire) (diff : a≠b) (s : State) (m : List Bool) :
    run (one a b) m s=⟨s.phase,fun q=>s.basis (flip a b q)⟩ := by
  apply congrArg (State.mk s.phase)
  funext q
  by_cases x : q=a <;> by_cases y : q=b <;> simp_all [flip,writeBit,Function.update,Bool.xor_comm,Bool.xor_left_comm]

theorem actual (xs : List (Wire×Wire)) (diff : ∀p∈xs,p.1≠p.2) (s : State) (m : List Bool) :
    run (program xs) m s=⟨s.phase,fun q=>s.basis (source xs q)⟩ := by
  induction xs generalizing s m with
  | nil => rfl
  | cons p rest ih =>
    change run (one p.1 p.2 ++ program rest) m s=_
    rw [run_append,run_take]
    rw [oneRun _ _ (diff p (by simp)),ih (fun t ht=>diff t (List.mem_cons_of_mem _ ht))]
    rfl


theorem outside (xs : List (Wire×Wire)) (q : Wire) (away : ∀p∈xs,q≠p.1 ∧ q≠p.2) : source xs q=q := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    change flip p.1 p.2 (source ps q)=q
    rw [ih (fun r h=>away r (List.mem_cons_of_mem _ h))]
    simp [flip,(away p (by simp)).1,(away p (by simp)).2]

theorem append (xs ys : List (Wire×Wire)) (q : Wire) : source (xs++ys) q=source xs (source ys q) := by
  simp [source,List.foldr_append]

end ECDSAAdd.Entrant.StairPacket.LeaveRelocation

end

-- proof-only (single-pass lemmas)
section
namespace ECDSAAdd.Entrant.WSlimMain

end ECDSAAdd.Entrant.WSlimMain
end


section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed

def eraseSites (sites:List Wire) (s:State) : State :=
  ⟨s.phase,fun q=>if q∈sites then false else s.basis q⟩

theorem erase_run (sites:List Wire) (P:Program) (avoid:∀q∈sites,q∉wires P) (m:List Bool) (s:State) :
    run P m (eraseSites sites s)=eraseSites sites (run P m s) := by
  have locality:=run_measured_locality P (wires P) (Finset.Subset.refl _) (eraseSites sites s) s m rfl
    (fun q mem=>by simp [eraseSites,show q∉sites from fun hit=>avoid _ hit mem])
  apply congrArg₂ State.mk locality.1
  funext q
  by_cases used:q∈wires P
  · have outside:q∉sites:=fun hit=>avoid _ hit used
    simpa [eraseSites,outside] using locality.2 q used
  · rw [run_preserves_outside _ m (eraseSites sites s) _ used]
    simp only [eraseSites,run_preserves_outside _ m s _ used]

def zeroSites (j:Fin 24) :=
  let p:=shape j
  let L:=ports p 0
  (L.a++L.b++[L.previous]++L.carry++((List.range' 0 15).flatMap fun r=>[(ports p r).ext,(ports p r).history])++
    [(ports p 0).a0,(ports p 0).history]).map (windowNet j)

set_option linter.unusedSimpArgs false in
theorem zero_congr (j:Fin 24) (s t:State) (agree:∀q∈zeroSites j,t.basis q=s.basis q)
    (z:SkywalkRails.State) (active:onRails j 0 z s.basis) :
    onRails j 0 z t.basis ∧ cell (shape j) 0 (mappedBasis j t.basis)=cell (shape j) 0 (mappedBasis j s.basis) := by
  let p:=shape j
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
namespace Enter240
end Enter240
namespace Enter255
end Enter255

namespace EnterJ
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

end EnterJ

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.HighBankSum
open IntegerHigh SkywalkNat

def total (z : SkywalkNat.State) := z.u+z.v
def cross (d : Nat) := decide (d≠2)

theorem decode (d : Nat) (n : Bool) (h : d=if d=2 then 2 else if n then 1 else 3) :
    d=(cross d).toNat + 2*(!(cross d && n)).toNat := by
  by_cases e : d=2
  · simp [e,cross]
  · rw [if_neg e] at h
    cases n <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> subst d <;> decide

theorem right (k B s H w E : Nat) (hk : 0<k) (ready : guard k s ≤ B)
    (odd : B%2=1) (small : s<2^E) (low : 2*(2^k*2^E)≤B+s) (high : B+s<3*(2^k*2^E))
    (far : 2≤H) :
    let z : SkywalkNat.State := ⟨s,B⟩
    let S := total (step^[k] z)
    let F := total (step^[k] ⟨s,B+2^k*(2^E*(H-2))⟩)
    let t := wait k s
    let d := S/2^E/2^t
    let neg := cross d && negative (oddBits (letters k z))
    H-2+d<2^w →
      d=(cross d).toNat+2*(!neg).toNat ∧ F/2^E=2^t*HighBankAdjust.adjusted H w (cross d) neg+S/2^E%2^t := by
  dsimp only
  intro room
  have q := corrected_digit k B s (2^E) hk ready odd small low high
  dsimp only at q
  rw [Nat.mul_comm (2^_) (2^E),←Nat.div_div_eq_div_mul] at q
  have digit := decode _ _ q
  exact ⟨digit,value _ _ _ _ _ _ _ _ (right_sum k B s _ ready) far room (fun hn => (Bool.and_eq_true_iff.mp hn).1) digit⟩

theorem left (k B s H w E : Nat) (ready : guard k s ≤ B)
    (odd : s%2=1) (small : s<2^E) (low : 2*(2^k*2^E)≤B+s) (high : B+s<3*(2^k*2^E))
    (far : 2≤H) :
    let S := total (step^[k] ⟨B,s⟩)
    let F := total (step^[k] ⟨B+2^k*(2^E*(H-2)),s⟩)
    let d := S/2^E
    H-2+d<2^w →
      d=(cross d).toNat+2 ∧ F/2^E=HighBankAdjust.adjusted H w (cross d) false := by
  dsimp only
  intro room
  have h := left_digit k B s (2^E) ready odd small low high
  dsimp only at h
  have digit : total (step^[k] ⟨B,s⟩)/2^E=(cross (total (step^[k] ⟨B,s⟩)/2^E)).toNat+2 := by
    rcases h with h|h <;> simp [total,h,cross]
  have gap : total (step^[k] ⟨B+2^k*(2^E*(H-2)),s⟩) =
      total (step^[k] ⟨B,s⟩)+2^E*(H-2) := by
    rw [long_u k B s _ ready]
    dsimp [total]
    omega
  have actual := value _ _ H w E 0 _ false (by simpa only [pow_zero,one_mul] using gap)
    far (by simpa only [pow_zero,Nat.div_one] using room) (by simp)
    (by simpa only [pow_zero,Nat.div_one,Bool.not_false,Bool.toNat_true,Nat.mul_one] using digit)
  exact ⟨digit,by simpa only [pow_zero,one_mul,Nat.mod_one,Nat.add_zero] using actual⟩


/-! Margin 17: the reduced far sum lies in [U,2U), the far digit in {0,1,2}; `d+1` obeys the old law. -/

def cross17 (d : Nat) := decide (d≠1)

theorem decode17 (d : Nat) (n : Bool) (h : d=if d=1 then 1 else if n then 0 else 2) :
    d+1=(cross17 d).toNat + 2*(!(cross17 d && n)).toNat := by
  by_cases e : d=1
  · simp [e,cross17]
  · rw [if_neg e] at h
    cases n <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> subst d <;> decide

theorem value17 (F S H w E t : Nat) (c neg : Bool)
    (gap : F=S+2^t*(2^E*(H-1))) (far : 2 ≤ H)
    (room : H-1+S/2^E/2^t < 2^w) (legal : neg=true → c=true)
    (digit : S/2^E/2^t+1=c.toNat+2*(!neg).toNat) :
    F/2^E = 2^t*HighBankAdjust.adjusted H w c neg + S/2^E%2^t := by
  have h := corrected H w _ c neg far (by omega) legal digit
  have h' : HighBankAdjust.adjusted H w c neg = H-1+S/2^E/2^t := by omega
  rw [h',gap,show 2^t*(2^E*(H-1))=2^E*(2^t*(H-1)) by ring,
      Nat.add_mul_div_left _ _ (by positivity),Nat.mul_add]
  have decomposition := Nat.mod_add_div (S/2^E) (2^t)
  omega

theorem right17 (k B s H w E : Nat) (hk : 0<k) (ready : guard k s ≤ B)
    (odd : B%2=1) (small : s<2^E) (low : 2^k*2^E≤B+s) (high : B+s<2*(2^k*2^E))
    (far : 2≤H) :
    let z : SkywalkNat.State := ⟨s,B⟩
    let S := total (step^[k] z)
    let F := total (step^[k] ⟨s,B+2^k*(2^E*(H-1))⟩)
    let t := wait k s
    let d := S/2^E/2^t
    let neg := cross17 d && negative (oddBits (letters k z))
    H-1+d<2^w →
      d+1=(cross17 d).toNat+2*(!neg).toNat ∧ F/2^E=2^t*HighBankAdjust.adjusted H w (cross17 d) neg+S/2^E%2^t := by
  dsimp only
  intro room
  have q := corrected_digit17 k B s (2^E) hk ready odd small low high
  dsimp only at q
  rw [Nat.mul_comm (2^_) (2^E),←Nat.div_div_eq_div_mul] at q
  have digit := decode17 _ _ q
  exact ⟨digit,value17 _ _ _ _ _ _ _ _ (right_sum k B s _ ready) far room (fun hn => (Bool.and_eq_true_iff.mp hn).1) digit⟩

theorem left17 (k B s H w E : Nat) (ready : guard k s ≤ B)
    (odd : s%2=1) (small : s<2^E) (low : 2^k*2^E≤B+s) (high : B+s<2*(2^k*2^E))
    (far : 2≤H) :
    let S := total (step^[k] ⟨B,s⟩)
    let F := total (step^[k] ⟨B+2^k*(2^E*(H-1)),s⟩)
    let d := S/2^E
    H-1+d<2^w →
      d+1=(cross17 d).toNat+2 ∧ F/2^E=HighBankAdjust.adjusted H w (cross17 d) false := by
  dsimp only
  intro room
  have h := left_digit17 k B s (2^E) ready odd small low high
  dsimp only at h
  have digit : total (step^[k] ⟨B,s⟩)/2^E+1=(cross17 (total (step^[k] ⟨B,s⟩)/2^E)).toNat+2 := by
    rcases h with h|h <;> simp [total,h,cross17]
  have gap : total (step^[k] ⟨B+2^k*(2^E*(H-1)),s⟩) =
      total (step^[k] ⟨B,s⟩)+2^E*(H-1) := by
    rw [long_u k B s _ ready]
    dsimp [total]
    omega
  have actual := value17 _ _ H w E 0 _ false (by simpa only [pow_zero,one_mul] using gap)
    far (by simpa only [pow_zero,Nat.div_one] using room) (by simp)
    (by simpa only [pow_zero,Nat.div_one,Bool.not_false,Bool.toNat_true,Nat.mul_one] using digit)
  exact ⟨digit,by simpa only [pow_zero,one_mul,Nat.mod_one,Nat.add_zero] using actual⟩

/-- With carry-in 0 the adjust ignores its sign wire. -/
theorem adjusted_idle (x w : Nat) (n : Bool) (h : x<2^w) : HighBankAdjust.adjusted x w false n=x := by
  cases n <;> simp [HighBankAdjust.adjusted,Nat.mod_eq_of_lt h]

/-- The physical crossing wire `e0+6` at margin 17: bit 0 of the far digit d ∈ {0,1,2} (this is the bit the archive stores). -/
def crossBit (d : Nat) : Bool := !cross17 d

/-- The sign wire may be read without the crossing gate: it only matters when the carry-in is set. -/
theorem adjusted_gate (x w : Nat) (c n : Bool) (h : x<2^w) : HighBankAdjust.adjusted x w c (c && n)=HighBankAdjust.adjusted x w c n := by
  cases c
  · rw [Bool.false_and,adjusted_idle x w false h,adjusted_idle x w n h]
  · rw [Bool.true_and]

end ECDSAAdd.Entrant.StairPacket.HighBankSum

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Relocated
open Partial LeaveRelocation Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave225Relocated

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Relocated
open Partial LeaveRelocation Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave240Relocated

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Relocated
open Partial LeaveRelocation Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave255Relocated

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed StairArchiveRaw StairArchiveTrace SkywalkRails ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run onRails

theorem member_cell (p:Shape) (n i r:Nat) (b:BasisState) (hr:r<n) :
    cell p (i+r) b∈readCells p i n b := by
  induction n generalizing i r with
  | zero=>omega
  | succ n ih=>
    cases r with
    | zero=>simp [readCells]
    | succ r=>
      apply List.mem_cons_of_mem
      simpa only [Nat.add_assoc,Nat.add_comm 1 r] using ih (i+1) r (by omega)

theorem not_both {a b:Bool} (h:(a,b)≠(true,true)) : (a&&b)=false:=by
  cases a <;> cases b <;> simp_all
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255
namespace NativePack270
open ArchiveBoundary270
end NativePack270

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
def src : List Wire := [1701,1702,1703]
def dst : List Wire := [1029,1030,1031]
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveShadowRails
open SkywalkNat IntegerHigh Shadow

theorem scale (b : Nat) : limb b 15=2^15*2^(b+1) := by
  rw [limb,show b+15+1=15+(b+1) by omega,pow_add]

/-- margin 17 (T1): the exact guard bound. The reduced long word only keeps U - short, and
guard 15 s + s = 2^15 (2s+1) ≤ U holds exactly for s < 2^b. -/
theorem guard_tight (b s : Nat) (hs : s<2^b) : guard 15 s+s≤limb b 15 := by
  have a : 2*s+1≤2*2^b := by omega
  have mul := Nat.mul_le_mul_left (2^15) a
  have f := guard_formula 15 s
  have e : limb b 15=2^15*(2*2^b) := by
    rw [scale,pow_succ 2 b,Nat.mul_comm (2^b) 2]
  rw [f,e]
  exact mul

theorem rail (b : Nat) (z : SkywalkNat.State) (small : min z.u z.v<2^b) (far : Shadow.far b 15 z) :
    let r := reduced b 15 z
    let D := 2^(b+1)*(high b 15 z-1)
    (2^b≤z.u → r.v=z.v ∧ z.u=r.u+2^15*D ∧ guard 15 r.v≤r.u) ∧
    (z.u<2^b → r.u=z.u ∧ z.v=r.v+2^15*D ∧ guard 15 r.u≤r.v) := by
  dsimp only
  have hr := (represented b 15 z small far).2.1
  have amount : gap b 15 z=2^15*(2^(b+1)*(high b 15 z-1)) := by rw [gap,scale];ring
  have base : 2^b≤limb b 15 := Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · intro h
    have sh : z.v<2^b := by omega
    rw [reduced,if_pos far,if_pos h] at hr ⊢
    dsimp only at hr ⊢
    exact ⟨rfl,by omega,(by have t:=guard_tight b z.v sh; omega)⟩
  · intro h
    rw [reduced,if_pos far,if_neg (Nat.not_le.mpr h)] at hr ⊢
    dsimp only at hr ⊢
    exact ⟨rfl,by omega,(by have t:=guard_tight b z.u h; omega)⟩


open HighBankSum

/-- With the short integer input and actual saved high quotient, the physical
    crossing decoder and shifted high correction give the true endpoint. -/
theorem far_result (b w : Nat) (z : SkywalkNat.State) (small : min z.u z.v<2^b)
    (far : Shadow.far b 15 z) (odd : z.v%2=1) (enough : high b 15 z+1<2^w) :
    let r:=reduced b 15 z
    let S:=total (step^[15] r)
    let F:=total (step^[15] z)
    let t:=if 2^b≤z.u then 0 else wait 15 z.u
    let d:=S/2^(b+1)/2^t
    let neg:=cross17 d && (!(decide (2^b≤z.u)) && negative (oddBits (letters 15 r)))
    d+1=(cross17 d).toNat+2*(!neg).toNat ∧
      F/2^(b+1)=2^t*HighBankAdjust.adjusted (high b 15 z) w (cross17 d) neg+S/2^(b+1)%2^t := by
  let r:=reduced b 15 z
  let H:=high b 15 z
  let V:=2^(b+1)
  let D:=V*(H-1)
  have sides:=rail b z small far
  have bounds := (represented b 15 z small far).2
  rw [scale] at bounds
  have hH : 2≤H := far
  have pos : 2^b<V := by dsimp [V];rw [pow_succ];have := Nat.two_pow_pos b;omega
  dsimp only
  by_cases h : 2^b≤z.u
  · obtain ⟨eqV,eqU,guarded⟩:=sides.1 h
    have shape : z=⟨r.u+2^15*D,r.v⟩:=SkywalkNat.State.ext eqU eqV.symm
    have short : r.v<V := by dsimp [r];omega
    have rodd : r.v%2=1 := eqV ▸ odd
    have dcap := left_digit17 15 r.u r.v V guarded rodd short bounds.1 bounds.2
    change total (step^[15] r)/V=1 ∨ total (step^[15] r)/V=2 at dcap
    have room : H-1+total (step^[15] r)/V<2^w := by change H+1<2^w at enough;omega
    have outcome:=HighBankSum.left17 15 r.u r.v H w (b+1) guarded rodd short bounds.1 bounds.2 hH room
    rw [←shape] at outcome
    simpa only [if_pos h,decide_eq_true h,Bool.not_true,Bool.false_and,Bool.and_false,Bool.not_false,Bool.toNat_true,Nat.mul_one,pow_zero,Nat.div_one,one_mul,Nat.mod_one,Nat.add_zero] using outcome
  · obtain ⟨eqU,eqV,guarded⟩:=sides.2 (Nat.lt_of_not_ge h)
    have shape : z=⟨r.u,r.v+2^15*D⟩:=SkywalkNat.State.ext eqU.symm eqV
    have short : r.u<V := by dsimp [r];omega
    have rodd : r.v%2=1 := by change z.v=r.v+32768*D at eqV;omega
    have dcap := (right_digit17 15 r.v r.u V guarded rodd short (by simpa only [Nat.add_comm r.v r.u] using bounds.1) (by simpa only [Nat.add_comm r.v r.u] using bounds.2)).1
    change total (step^[15] r)/(2^(wait 15 r.u)*V)=0 ∨ total (step^[15] r)/(2^(wait 15 r.u)*V)=1 ∨ total (step^[15] r)/(2^(wait 15 r.u)*V)=2 at dcap
    rw [Nat.mul_comm (2^_) V,←Nat.div_div_eq_div_mul] at dcap
    have room : H-1+total (step^[15] r)/V/2^(wait 15 r.u)<2^w := by change H+1<2^w at enough;omega
    have outcome:=HighBankSum.right17 15 r.v r.u H w (b+1) (by decide) guarded rodd short (by simpa only [Nat.add_comm r.v r.u] using bounds.1) (by simpa only [Nat.add_comm r.v r.u] using bounds.2) hH room
    rw [←shape] at outcome
    have waits : wait 15 z.u=wait 15 r.u := congrArg (wait 15) eqU.symm
    simpa only [if_neg h,decide_eq_false h,Bool.not_false,Bool.true_and,waits] using outcome


theorem near_result (b : Nat) (z : SkywalkNat.State) (close : ¬ Shadow.far b 15 z) :
    reduced b 15 z=z ∧ total (step^[15] z)/2^(b+1)<2^17 := by
  refine ⟨by simp [reduced,close],?_⟩
  have lt : (z.u+z.v)/limb b 15<2 := Nat.lt_of_not_ge close
  have lim := (Nat.div_lt_iff_lt_mul (by unfold limb;positivity)).mp lt
  rw [scale] at lim
  have noninc := iter_sum_nonincrease 15 z
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  dsimp only [total]
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveShadowRails

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run

theorem ready_after_head (j:Fin 24) (P:Program) (s:State) (a b:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (active:onRails j 0 z s.basis)
    (preserve:∀t:State,∀q∈watch j,(run P b t).basis q=t.basis q) :
    onRails j 1 (SkywalkTrace.next z) (run P b (run (routed j 0 1) a s)).basis:=
  (watch_congr j _ _ (preserve _) _ (route_frame j 0 1 (by decide) z odd s a active).2).1

def physicalCells (j:Fin 24) (s:State) := readCells (shape j) 0 15 (mappedBasis j s.basis)

/-- The previous fifteen native records plus the three real flags written by Leave.
The codec row is derived from these fields. -/
structure PastFacts (j:Fin 24) (rawPorts:ArchivePortAction.Ports) (b:Nat) (z:SkywalkNat.State)
    (g sign cross:Bool) (s:State) : Prop where
  records : physicalCells j s=SkywalkTrace.trace 15 (encode g sign z.u z.v)
  far : s.basis (rawPorts 20)=decide (Shadow.far b 15 z)
  suffix : s.basis (rawPorts 21)=(decide (Shadow.far b 15 z) && afterFlags (decide (z.v<z.u)) ((physicalCells j s).take 5))
  crossed : s.basis (rawPorts 22)=(decide (Shadow.far b 15 z) && cross)

namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255

namespace NativeJ
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-! The head of block `j`'s window (`2 ≤ j ≤ 19`): enter, the routed first tick, the pack, then the archive
of block `j-1` read from `j-1`'s records. The archive scratch must be clean after the pack (`scratch`); for
`j ≤ 13` this follows from the rails (`scratch_rails`), later blocks need D2's invariant. -/

/-- Interval form of `firstUnchanged`: the window wire is the previous-tick wire or off tick 0's ports. -/
def FirstFree (j : Fin 24) (r : Wire) : Prop :=
  r=start j+15 ∨ ¬(r=start j+1044 ∨ (start j+16≤r ∧ r≤start j+sbP (start j)+35) ∨ (786≤r ∧ r≤sbP (start j)+804) ∨
    (1556≤r ∧ r≤sbP (start j)+1573))
instance (j : Fin 24) (r : Wire) : Decidable (FirstFree j r) := by unfold FirstFree; infer_instance
end NativeJ

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic MappedCompressed Portal270Flag
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open IntegerHigh SkywalkNat Shadow HighBankSum

def actualMode (b : Nat) (z : SkywalkNat.State) := farMode (decide (far b 15 z)) (decide (2^b≤z.u)) z.u
def place (b : Nat) (z : SkywalkNat.State) := if 2^b≤z.u then 0 else wait 15 z.u

theorem modeKey (b : Nat) (z : SkywalkNat.State) (f : far b 15 z) :
    key (actualMode b z)=place b z ∧ right (actualMode b z)= !decide (2^b≤z.u) ∧ enabled (actualMode b z)=true := by
  by_cases h : 2^b≤z.u <;> simp [actualMode,farMode,ofFlags,key,place,right,enabled,f,h]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run onRails unrouted

theorem unmask (P Q:Program) (tags:List Wire) (a:∀q∈tags,q∉wires P) (b:∀q∈tags,q∉wires Q)
    (s:State) (m n:List Bool) (undo:run Q n (run P m (eraseSites tags s))=eraseSites tags s) :
    run Q n (run P m s)=s := by
  rw [erase_run _ P a,erase_run _ Q b] at undo
  apply congrArg₂ State.mk (congrArg State.phase undo)
  funext q
  by_cases h:q∈tags
  · exact (run_preserves_outside Q n _ _ (b _ h)).trans (run_preserves_outside P m s _ (a _ h))
  · simpa [eraseSites,h] using congrArg (fun x:State=>x.basis q) undo
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255

namespace NativeJ
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
end NativeJ

namespace NativeFirstJ
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
/-! First-form head (par-c2): the first block's five pre-window letters are legal from the stock stage, and its
window runs from the portal's cut (dadon's `NativePack225.original_legal/history_from_stock`). -/
end NativeFirstJ

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeavePendingHistory
open StairArchiveTrace LeaveSelector IntegerHigh

theorem traceFlags (u : Bool) (xs : List (Bool×Bool)) (n : Nat) (ok : chain u xs) :
    afterFlags u (xs.take n)=(u || (xs.take n).any Prod.snd) := by
  induction n generalizing u xs with
  | zero => simp [afterFlags]
  | succ n ih =>
    cases xs with
    | nil => simp [afterFlags]
    | cons x xs =>
      change afterFlags (u || !x.1) (xs.take n)=_
      rw [ih _ _ ok.2]
      simp only [List.take_succ_cons,List.any_cons,ok.1]
      cases u <;> cases x.1 <;> simp

theorem initialTrue (xs : List (Bool×Bool)) (ok : chain true xs) (n : Nat) :
    (xs.take n).any Prod.snd=false := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.take_succ_cons,List.any_cons,ok.1,Bool.not_true,Bool.false_and,Bool.false_or]
      exact ih _ (by simpa only [Bool.true_or] using ok.2)

theorem firstBits (xs : List Bool) (n : Nat) (hn : n≤xs.length) :
    (xs.take n).any id=decide (xs.idxOf true<n) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp at hn
    | cons x xs =>
      cases x <;> simp [ih xs (by simpa using hn)]

/-- In far mode the pending suffix flag records the orientation after five
    events. Erasing the previous orientation uses precisely the same event bits. -/
theorem flags (u : Bool) (xs : List (Bool×Bool)) (ok : chain u xs) (len : 5≤xs.length)
    (w : Fin 16) (index : u=false → (xs.map Prod.snd).idxOf true=w.val) :
    let k:=ofFlags true u w
    nearby k=afterFlags u (xs.take 5) ∧ (u ^^ (nearby k && !((xs.take 5).any Prod.snd)))=false := by
  have word:=firstBits (xs.map Prod.snd) 5 (by simpa using len)
  rw [←List.map_take,List.any_map] at word
  change (xs.take 5).any Prod.snd=decide ((xs.map Prod.snd).idxOf true<5) at word
  cases u with
  | true =>
    simp only [traceFlags true xs 5 ok,initialTrue xs ok 5]
    simp [ofFlags,nearby,enabled,key]
  | false =>
    rw [index rfl] at word
    simp only [traceFlags false xs 5 ok,word]
    simp [ofFlags,nearby,enabled,key]


theorem firstExchangeIndex (xs : List (Bool×Bool)) (k : Nat) (bound : k≤xs.length)
    (read : ∀i (h:i<xs.length),i≤k → xs[i].2=decide (i=k)) :
    (xs.map Prod.snd).idxOf true=k := by
  induction xs generalizing k with
  | nil => simp at bound; simp [bound]
  | cons p ps ih =>
    cases k with
    | zero =>
      have first:=read 0 (by simp) (by omega)
      have on:p.2=true:=by simpa using first
      simp [on]
    | succ k =>
      have first:p.2=false:=by simpa using read 0 (by simp) (by omega)
      have rest:=ih k (by simpa using bound) (fun i h early=>by
        simpa only [List.getElem_cons_succ,Nat.succ.injEq] using read (i+1) (by simpa using h) (by omega))
      simp [first,rest]


theorem pending (f u : Bool) (xs : List (Bool×Bool)) (w : Fin 16) (len : xs.length=15)
    (ok : f=true → chain u xs)
    (read : f=true → u=false → ∀i (h:i<xs.length),i≤w.val → xs[i].2=decide (i=w.val)) :
    let n:=nearby (ofFlags f u w)
    n=(f && afterFlags u (xs.take 5)) ∧
      ((f && u) ^^ (n && !(xs.take 5).any Prod.snd))=false := by
  cases f with
  | false => simp [nearby,ofFlags,enabled]
  | true =>
    have b : w.val≤xs.length := by rw [len];have h:=w.isLt;omega
    exact flags u xs (ok rfl) (by omega) w (fun off => firstExchangeIndex xs w.val b (read rfl off))

end ECDSAAdd.Entrant.StairPacket.LeavePendingHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
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
/-- window390: the released wires of the stock B rail at tick `i` are exactly `bTop(i)+1 .. 1043`. -/
theorem released_mem (i q : Nat) (lo : 257 ≤ i) (hi : i ≤ 509) (ql : 1299 - i ≤ q) (qh : q ≤ 1043) :
    q ∈ (W.compactSkywalkSignPoolB base i).released := by
  have hw : W.narrowSkywalkRouteWidth i = 513 - i := by unfold W.narrowSkywalkRouteWidth; omega
  show q ∈ (wireBlock base 770 258).drop (W.narrowSkywalkRouteWidth i)
  rw [hw, W.wireBlock_drop]
  unfold wireBlock
  exact List.mem_map.mpr ⟨q - 16, List.mem_range'_1.mpr ⟨by omega, by omega⟩, by show q - 16 + 16 = q; omega⟩
/-- window390, generic `clear_dest`: every B-rail wire above the rail top is clean in the stock stage at tick `i`. -/
theorem clear_above (i : Nat) (lo : 257 ≤ i) (hi : i ≤ 509) (d : Bool) (seed p : Nat) (raw : State)
    (stage : Rolling1588.Integer.Stage base d seed p i raw.basis) (q : Nat) (ql : 1299 - i ≤ q) (qh : q ≤ 1043) :
    raw.basis q = false :=
  dormant i d seed p raw q stage (above_history i (by omega) d q (by omega) (by omega)) (released_mem i q lo hi ql qh)

end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def L:=W.compactSkywalkTickLayout base 270
def P:=TickRanges.tick base 270
def physP:=renameProgram (OB5.sig 270) P
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic Secp256k1 MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic Secp256k1 MappedCompressed
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] run
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.EndTick

end
end
-- ==== end PrizeTail227303371 ====

-- ==== begin PrizeTail10d9efffc.a ====
section

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveBoundary240
end ArchiveBoundary240
namespace ArchiveBoundary255
end ArchiveBoundary255
namespace ArchiveBoundary270
end ArchiveBoundary270

namespace ArchiveJ
open Partial
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
end ArchiveJ

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed IntegerPacket
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
attribute [local irreducible] run
def readOnly (q:Wire) := OB5.sig 270 q∉L.wires ∨ q=285
instance (q:Wire) : Decidable (readOnly q) := by unfold readOnly;infer_instance
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket.FlipAudit
open Arithmetic
end ECDSAAdd.Entrant.StairPacket.FlipAudit

end

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

end ECDSAAdd.Entrant.StairPacket.LeaveBankEnvelope

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveCompanion
open Arithmetic

theorem thresholdBit (x h : Nat) (positive:0<h) :
    (x/h).testBit 0=decide (h≤x%(2*h)) := by
  have d : (x%(2*h))/h=(x/h)%2 := by
    rw [Nat.mul_comm 2 h,Nat.mod_mul_right_div_self]
  have limited := Nat.mod_lt (x/h) (by decide : 0<2)
  have one : ((x/h)%2=1) ↔ h≤x%(2*h) := by
    rw [←d]
    have iff : 1≤(x%(2*h))/h ↔ 1*h≤x%(2*h) := Nat.le_div_iff_mul_le positive
    simp only [one_mul] at iff
    omega
  simp [Nat.testBit_eq_decide_div_mod_eq,one]

theorem borrowBit (half u v sign : Nat) (pos:0<half) :
    (((u-sign)/half).testBit 0 && !((u+v)/half).testBit 0).toNat =
      upperBorrow half u v sign := by
  rw [thresholdBit _ _ pos,thresholdBit _ _ pos]
  unfold upperBorrow
  split_ifs with h <;> simp_all

end ECDSAAdd.Entrant.StairPacket.LeaveCompanion

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveNoSwap
open Arithmetic PortalAnd

def block (a out:Wire) : List (Wire×Wire) → Program
  | [] => [.CX a out]
  | (x,t)::ps => [.X x,.CCX a x t] ++ block t out ps ++ [.measureX t [] [.CZ a x],.X x]

theorem action (ps:List (Wire×Wire)) (a out:Wire) (s:State) (m:List Bool)
    (nd:(out::a::sites ps).Nodup) (cold:∀p∈ps,s.basis p.2=false) :
    run (block a out ps) m s=⟨s.phase,writeBit s.basis out (s.basis out ^^ (s.basis a && ps.all (fun p=> !s.basis p.1)))⟩ := by
  induction ps generalizing a s m with
  | nil => simp [block,run]
  | cons pr ps ih =>
    obtain ⟨x,t⟩:=pr
    change (out::a::x::t::sites ps).Nodup at nd
    obtain ⟨oa,ox,ot,os,ax,at',as',xt,xs,ts,ns⟩ :
      out≠a ∧ out≠x ∧ out≠t ∧ out∉sites ps ∧ a≠x ∧ a≠t ∧ a∉sites ps ∧
        x≠t ∧ x∉sites ps ∧ t∉sites ps ∧ (sites ps).Nodup := by simpa [and_assoc] using nd
    let v:State:=⟨s.phase,writeBit (writeBit s.basis x (!s.basis x)) t (s.basis a && !s.basis x)⟩
    have z:=cold (x,t) (by simp)
    change s.basis t=false at z
    have enter : run [.X x,.CCX a x t] m s=v := by simp [run,v,writeBit,Function.update,ax,xt.symm,z]
    have keep (q:Wire) (hx:q≠x) (ht:q≠t) : v.basis q=s.basis q := by simp [v,writeBit,hx,ht]
    have same (p:Wire×Wire) (hp:p∈ps) : v.basis p.1=s.basis p.1 ∧ v.basis p.2=s.basis p.2 := by
      have l:p.1∈sites ps:=List.mem_flatMap.mpr ⟨p,hp,by simp⟩
      have r:p.2∈sites ps:=List.mem_flatMap.mpr ⟨p,hp,by simp⟩
      exact ⟨keep _ (fun h=>xs (h ▸ l)) (fun h=>ts (h ▸ l)),keep _ (fun h=>xs (h ▸ r)) (fun h=>ts (h ▸ r))⟩
    have bits : ps.all (fun p=> !v.basis p.1)=ps.all (fun p=> !s.basis p.1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      constructor <;> intro H p hp
      · simpa only [(same p hp).1] using H p hp
      · rw [(same p hp).1];exact H p hp
    have act:=ih t v m (by simp [ot,os,ts,ns]) (fun p hp=>(same p hp).2.trans (cold p (by simp [hp])))
    simp only [block,run_append,run_take]
    rw [enter]
    change run [.measureX t [] [.CZ a x],.X x] _ (run (block t out ps) m v)=_
    rw [act,bits,keep out ox ot]
    have vt:v.basis t=(s.basis a && !s.basis x) := by simp [v,writeBit]
    rw [vt]
    simp only [List.all_cons,Bool.and_assoc]
    generalize (s.basis out ^^ (s.basis a && (!s.basis x && ps.all (fun p=> !s.basis p.1))))=ans
    let w:State:=⟨v.phase,writeBit v.basis out ans⟩
    have cleanup:w.basis t=(w.basis a && w.basis x) := by
      simp [w,v,writeBit,Function.update,ot.symm,oa.symm,ox.symm,at',ax,xt]
    change run ([.measureX t [] [.CZ a x]]++[.X x]) _ w=_
    rw [run_append,run_take,measure_and _ _ _ _ _ at' xt cleanup]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq:q=x <;> by_cases ht:q=t <;> by_cases ho:q=out <;> simp_all [run,w,v,writeBit,Function.update]

end ECDSAAdd.Entrant.StairPacket.LeaveNoSwap

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveReadoutFrame

def destination : Instr → Wire
  | .X q | .CX _ q | .CCX _ _ q | .measureX q _ _ => q

theorem preserved (p : Program) (s : State) (m : List Bool) (q : Wire)
    (safe : q∉p.map destination) : (run p m s).basis q=s.basis q := by
  induction p generalizing s m with
  | nil => rfl
  | cons i p ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at safe
    obtain ⟨ne,unwritten⟩:=safe
    cases i <;> simp only [run] <;> rw [ih _ _ unwritten] <;>
      simp only [destination] at ne <;> simp [measureAndCorrect,writeBit,ne]

end ECDSAAdd.Entrant.StairPacket.LeaveReadoutFrame

end

section

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic
theorem signedWords (L:SkywalkIntegerLayout) (g sg:Bool) (u v:Nat) (s:BasisState)
    (a:signedRegValue L.a s=(SkywalkRails.encode g sg u v).a)
    (b:signedRegValue L.b s=(SkywalkRails.encode g sg u v).b) (g0:s L.previous=g) :
    let e:=negative sg u
    s L.previous=g ∧ (s L.aSign ^^ s L.bSign)=e ∧
    regValue (wordPos L g) s=u+v ∧
    regValue (wordSigned L g) (fun q=>s q ^^ e)=u-e.toNat := by
  have orient (lo:List Wire) (sign:Wire) (signed:signedRegValue (lo++[sign]) s=SkywalkRails.signed sg u) :
      s sign=negative sg u ∧ regValue (lo++[sign]) (fun q=>s q ^^ negative sg u)=u-(negative sg u).toNat := by
    have h:=full lo sign s _ signed
    have n:SkywalkRails.neg (SkywalkRails.signed sg u)=negative sg u := by
      cases sg <;> simp [SkywalkRails.neg,SkywalkRails.signed,negative]
    have r:s sign=negative sg u:=h.1.trans n
    rw [r] at h
    have mag:(SkywalkRails.signed sg u).natAbs=u:=by cases sg <;> simp [SkywalkRails.signed]
    exact ⟨r,by simpa only [mag] using h.2⟩
  cases g with
  | false =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=(u:Int)+v at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=SkywalkRails.signed sg u at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using a)
    obtain ⟨s0,sv⟩:=orient _ _ b
    exact ⟨g0,by rw [p0,s0,Bool.false_xor],pv,sv⟩
  | true =>
    change signedRegValue ((L.a0::L.aMid)++[L.aSign]) s=SkywalkRails.signed sg u at a
    change signedRegValue ((L.b0::L.bMid)++[L.bSign]) s=(u:Int)+v at b
    obtain ⟨p0,pv⟩:=positive _ _ s (u+v) (by simpa only [Nat.cast_add] using b)
    obtain ⟨s0,sv⟩:=orient _ _ a
    exact ⟨g0,by rw [s0,p0,Bool.xor_false],pv,sv⟩


/-- Read the positive and signed magnitude limbs from the actual routed short
    registers at tick fifteen. The two future extension wires are no longer needed. -/
theorem scanRouted (j : Fin 24) (k a b g n : Nat) (ps : List (Wire×Wire))
    (loc : RailPair.ScanGeometry a b g n ps)
    (left : ps.map Prod.fst = ((IntegerPacket.ports (shape j) 15).a.drop k).map (windowNet j))
    (right : ps.map Prod.snd = ((IntegerPacket.ports (shape j) 15).b.drop k).map (windowNet j))
    (aTop : a=windowNet j (IntegerPacket.ports (shape j) 15).aSign)
    (bTop : b=windowNet j (IntegerPacket.ports (shape j) 15).bSign)
    (prev : g=windowNet j (IntegerPacket.ports (shape j) 15).previous)
    (s : State) (m : List Bool) (u v : Nat) (G S : Bool)
    (h : onRails j 15 (SkywalkRails.encode G S u v) s.basis) (fresh:s.basis n=false)
    (la : k≤(IntegerPacket.ports (shape j) 15).a.length) (lb : k≤(IntegerPacket.ports (shape j) 15).b.length) :
    let t:=run (RailPair.scan a b g n ps) m s
    let e:=negative S u
    t.basis n=e ∧ regValue (ps.map Prod.fst) t.basis=(u+v)/2^k ∧
      regValue (ps.map Prod.snd) t.basis=(u-e.toNat)/2^k := by
  let L:=IntegerPacket.ports (shape j) 15
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

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic

def refs : Expr → List Wire
  | .bit _ => []
  | .wire w => [w]
  | .both a b | .xor a b => refs a++refs b

theorem readAgree (e:Expr) (u v:BasisState) (agree:∀q∈refs e,u q=v q) : e.read u=e.read v := by
  induction e with
  | bit => rfl
  | wire w => exact agree _ (by simp [refs])
  | both a b ih jh =>
    exact congrArg₂ Bool.and (ih (fun q h=>agree q (List.mem_append_left _ h))) (jh (fun q h=>agree q (List.mem_append_right _ h)))
  | xor a b ih jh =>
    exact congrArg₂ Bool.xor (ih (fun q h=>agree q (List.mem_append_left _ h))) (jh (fun q h=>agree q (List.mem_append_right _ h)))

theorem simOutside (os:List Op) (v:Sym) (q:Nat) (off:q∉os.map Op.dst) : sim os v q=v q := by
  induction os generalizing v with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at off
    change sim os (symbolic o v) q=_
    rw [ih _ off.2]
    simp [symbolic,off.1]

theorem postOutside (p:Ports) (os:List Op) (k:Mode) (q:Nat)
    (free:q<1559 ∨ 1597<q) (off:q≠p.crossing → q≠p.near → q∉os.map Op.dst) :
    post p os false k q=.wire q := by
  by_cases flags : q=p.crossing ∨ q=p.near
  · simp [post,flags]
  · have both := not_or.mp flags
    have h0:q≠1559:=by omega
    have h1:q≠1560:=by omega
    have h2:¬(1561≤q ∧ q≤1575):=by omega
    have h3:¬(1576≤q ∧ q≤1597):=by omega
    simp [post,show q≠1597 by omega,simOutside _ _ _ (off both.1 both.2),start,h0,h1,h2,h3,both.1,both.2]

def cleared (v:BasisState) (q:Nat) := if 1559≤q ∧ q≤1597 then false else v q

theorem retiredBasis (p:Ports) (k:Mode) (v:BasisState)
    (far1:1597<p.crossing) (far2:1597<p.near) :
    clearKey (fun q=>(restored p false k q).read v)=cleared v := by
  funext q
  change Nat at q
  by_cases lo : 1559≤q ∧ q≤1575
  · simp [cleared,clearKey,lo,show 1559≤q ∧ q≤1597 by omega]
  by_cases hi : 1576≤q ∧ q≤1597
  · simp [cleared,clearKey,restored,start,hi,show 1559≤q ∧ q≤1597 by omega,
      show q≠1559 by omega,show q≠1560 by omega,show ¬(1561≤q ∧ q≤1575) by omega,
      (Nat.lt_of_le_of_lt hi.2 far1).ne,(Nat.lt_of_le_of_lt hi.2 far2).ne,Expr.read]
  · by_cases flags:q=p.crossing ∨ q=p.near
    · simp [cleared,clearKey,lo,restored,flags,show ¬(1559≤q ∧ q≤1597) by omega,Expr.read]
    · have both:=not_or.mp flags
      simp [cleared,clearKey,lo,restored,start,hi,show ¬(1559≤q ∧ q≤1597) by omega,
        show q≠1559 by omega,show q≠1560 by omega,show ¬(1561≤q ∧ q≤1575) by omega,both.1,both.2,Expr.read]

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveSelector
open Arithmetic RecordedQuantum HighBankFirstHit IntegerHigh

set_option maxHeartbeats 1500000

theorem allSites (p : Ports) (far u : Wire) (inv : Bool) (ops : List Op) (sw : Nat→Wire)
    (layout : Layout 1560 sw tags 0 15) (apart : ∀i<15,sw i≠1559 ∧ sw i≠1560)
    (s : State) (m : List Bool) (v : BasisState) (small : Nat)
    (fa : far≠1559) (fb : far≠1560) (a : s.basis 1559=false) (b : s.basis 1560=false)
    (k : Mode) (mode : k=farMode (s.basis far) (s.basis u) small)
    (input : ∀q,q≠1559 → q≠1560 → s.basis q=(before p inv k q).read v)
    (exchanges : right k=true → ∀i<15,i≤key k → s.basis (sw i)=decide (i=key k))
    :
    run (withHits far u inv sw (ops.map Op.enter)) m s=
      ⟨s.phase,fun q=>(sim ops (start p inv k) q).read v⟩ := by
  let fp := (flagOps far u inv).map Op.enter
  let hp := putAll 1560 sw tags 0 15
  let t := run fp m s
  let m' := m.drop (measurementCount fp)
  let r := run hp m' t
  let m'' := m'.drop (measurementCount hp)
  have init := initialized p inv far u s v m small fa fb a b (mode ▸ input)
  change t.phase=s.phase ∧ ∀q,t.basis q=(before p inv (farMode _ _ _) q).read v at init
  rw [←mode] at init
  have ex (on : right k=true) (i : Nat) (hi : i<15) (early : i≤key k) :
      t.basis (sw i)=decide (i=key k) := by
    obtain ⟨l,w⟩:=apart i hi
    dsimp only [t,fp]
    rw [flag_prepare _ _ _ _ _ fa fb a b]
    simpa [flagUpdate,l,w] using exchanges on i hi early
  have hh:=hits_ready p inv k sw layout t v m' init.2 ex
  have words := interpreted v ops (start p inv k)
  have bases : (fun q => (start p inv k q).read v)=r.basis := (funext hh.2).symm
  rw [bases] at words
  simp only [withHits,run_append,run_take]
  change run (ops.map Op.enter) m'' r=_
  rw [enter_run]
  exact congrArg₂ State.mk (hh.1.trans init.1) words.symm

end ECDSAAdd.Entrant.StairPacket.LeaveSelector

end

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
    min a.u a.v<2^b ∧ (a.u+a.v)/2^b<2^18 := by
  let r:=reduced b 15 z
  have rsmall : min r.u r.v<2^b := by
    unfold r reduced
    split_ifs <;> (try dsimp only) <;> omega
  have upper : r.u+r.v<2*limb b 15 := by
    by_cases f : far b 15 z
    · exact (represented b 15 z small f).2.2
    · have low : (z.u+z.v)/limb b 15<2 := Nat.lt_of_not_ge f
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

namespace ECDSAAdd.Entrant.StairPacket.LeaveTraceHistory
open SkywalkNat SkywalkRails IntegerHigh LeaveSelector StairArchiveTrace

theorem flags (b : Nat) (z : SkywalkNat.State) : actualMode b z =
    farMode (decide (Shadow.far b 15 z)) (decide (Shadow.far b 15 z) && decide (2^b≤z.u)) z.u := by
  by_cases f : Shadow.far b 15 z <;> simp [actualMode,farMode,ofFlags,f]

theorem orient (b : Nat) (z : SkywalkNat.State) (small : min z.u z.v < 2^b) (far : Shadow.far b 15 z) :
    decide (2^b≤z.u)=decide (z.v<z.u) := by
  have rail:=LeaveShadowRails.rail b z small far
  by_cases lhs : 2^b≤z.u
  · have hv : z.v<2^b := by omega
    simp [lhs,show z.v<z.u by omega]
  · obtain ⟨u,v,guarded⟩:=rail.2 (by omega)
    have g:=guard_gt 15 (Shadow.reduced b 15 z).u
    simp [lhs,show ¬z.v<z.u by omega]

theorem certifiedChain (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : min z.u z.v < 2^b) (odd : z.v%2=1) (far : Shadow.far b 15 z) :
    chain (decide (2^b≤z.u)) (SkywalkTrace.trace 15 (encode g s z.u z.v)) := by
  rw [orient b z small far]
  exact signed (Shadow.represented b 15 z small far).1 g s (by omega) odd

theorem swapLetters {k : Nat} {z t : SkywalkNat.State} (h : Rel k z t)
    (g s : Bool) (odd : z.v%2=1) :
    (SkywalkTrace.trace k (encode g s z.u z.v)).map Prod.snd =
      (letters k t).map (fun a => decide (a=2)) := by
  induction k generalizing z t g s with
  | zero => rfl
  | succ k ih =>
    have pos : 0<z.v := by omega
    obtain ⟨eq,tail⟩:=advance h
    simp only [SkywalkTrace.trace,letters,List.map_cons,recorded z g s pos odd (different h).1,eq,
      SkywalkTrace.next,step_reencode g s z pos odd]
    exact congrArg (_ :: ·) (ih tail _ _ (step_v_odd_pos z pos odd).2)

theorem firstSwap (b : Nat) (z : SkywalkNat.State) (g s : Bool)
    (small : min z.u z.v < 2^b) (odd : z.v%2=1) (far : Shadow.far b 15 z)
    (side : decide (2^b≤z.u)=false) :
    let xs:=SkywalkTrace.trace 15 (encode g s z.u z.v)
    ∀ i (hi : i<xs.length), i≤wait 15 z.u → xs[i].2=decide (i=wait 15 z.u) := by
  let xs:=SkywalkTrace.trace 15 (encode g s z.u z.v)
  let r:=Shadow.reduced b 15 z
  have h:= (LeaveShadowRails.rail b z small far).2 (Nat.lt_of_not_ge (of_decide_eq_false side))
  have eq : r=⟨z.u,r.v⟩:=SkywalkNat.State.ext h.1 rfl
  have guard : IntegerHigh.guard 15 z.u≤r.v:=h.1 ▸ h.2.2
  have tape:=swapLetters (Shadow.represented b 15 z small far).1 g s odd
  change xs.map Prod.snd=(letters 15 r).map _ at tape
  rw [eq] at tape
  let v : BasisState:=fun q => (xs[q]?.getD (false,false)).2
  have raw:=raw_exchange r.v z.u guard v id (by
    intro i
    have hi : i.val<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using i.isLt
    have bit:=congrArg (fun a : List Bool => a[i.val]?) tape
    have len := congrArg List.length tape
    simp only [List.length_map] at len
    have hi2 : i.val < (letters 15 ⟨z.u,r.v⟩).length := len ▸ hi
    simpa [v, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi2] using bit)
  dsimp only
  intro i hi early
  change i<xs.length at hi
  have idx : i<15 := by simpa only [xs,SkywalkTrace.trace_length] using hi
  simpa only [v,id_eq,List.getElem?_eq_getElem hi,Option.getD_some] using raw i idx early

end ECDSAAdd.Entrant.StairPacket.LeaveTraceHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveTraceLetters
open IntegerHigh SkywalkNat SkywalkRails

theorem parity (k : Nat) (z : SkywalkNat.State) (g s : Bool) (odd : z.v % 2 = 1) :
    (SkywalkTrace.trace k (encode g s z.u z.v)).map (fun pair => !pair.1) =
      oddBits (letters k z) := by
  induction k generalizing z g s with
  | zero => rfl
  | succ k ih =>
    have pos : 0 < z.v := by omega
    have bit := (SkywalkTrace.code_classified g s z pos odd).1
    have tail := (step_v_odd_pos z pos odd).2
    simp only [SkywalkTrace.trace, List.map_cons, letters, oddBits]
    rw [bit, SkywalkTrace.next, step_reencode g s z pos odd]
    congr 1
    · by_cases even : z.u%2=0 <;> by_cases lt : z.u<z.v <;> simp [letter,even,lt]
    · exact ih _ _ _ tail

end ECDSAAdd.Entrant.StairPacket.LeaveTraceLetters

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
attribute [local irreducible] run skywalkIntegerTick skywalkIntegerUntick
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
def tickSites (j:Fin 24) (a:Nat) := ((ports (shape j) a).wires.map (windowNet j))
def spanSites (j:Fin 24) (a n:Nat) := (List.range' a n).flatMap (tickSites j)
theorem route_sites (j:Fin 24) (a n:Nat) (lim:a+n≤15) (q:Wire) (inP:q∈wires (routed j a n)) :
    q∈spanSites j a n := by
  induction n generalizing a with
  | zero=>simp [routed,wires] at inP
  | succ n ih=>
    rw [routed,wires_append,Finset.mem_union] at inP
    rw [spanSites,List.range'_succ,List.flatMap_cons,List.mem_append]
    rcases inP with h|h
    · rw [renameProgram_support,Finset.mem_image] at h
      obtain ⟨t,used,eq⟩:=h
      have ht:a<15:=by omega
      have inside:=List.mem_toFinset.mp ((skywalkIntegerTick_wires_subset _ (ok (shape j) ⟨a,ht⟩)).1 used)
      exact Or.inl (List.mem_map.mpr ⟨t,inside,(stable ht inside).symm.trans eq⟩)
    · exact Or.inr (ih (a+1) (by omega) h)
theorem route_outside (j:Fin 24) (a n:Nat) (lim:a+n≤15) (q:Wire) (free:q∉spanSites j a n) (s:State) (m:List Bool) :
    (run (routed j a n) m s).basis q=s.basis q :=
  run_preserves_outside _ _ _ _ (fun used=>free (route_sites j a n lim q used))
def oldRange (t q:Nat) : Prop := (16≤q ∧ q+2≤16+t) ∨ (1044≤q ∧ q+2≤1044+t)
instance (t q:Nat) : Decidable (oldRange t q):=by unfold oldRange;infer_instance
theorem old_clear {j:Fin 24} {a n q:Nat} (lim:a+n≤15)
    (old:oldRange (start j+a) (windowNet j q)) : q∉spanSites j a n := by
  intro mem
  obtain ⟨r,hr,inside⟩:=List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w,hw,eq⟩:=List.mem_map.mp inside
  have undo:windowNet j (windowNet j w)=w:=by
    apply OB5.sig_invol
    have hj:=j.isLt;simp [start];omega
  rw [←eq,undo] at old
  have hj:=j.isLt
  simp only [IntegerPacket.ports,shape,smallBits,start,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at hw
  simp only [oldRange,start] at old
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.SavedHigh
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
theorem mapped (ps:List (Wire×Wire)) (a b:Wire×Wire→Wire) (s t:BasisState) (eq:∀p∈ps,s (a p)=t (b p)) :
    regValue (ps.map a) s=regValue (ps.map b) t:=by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>
    have head:=eq p (by simp)
    have tail:=ih (fun v h=>eq v (by simp [h]))
    change (if s (a p) then 1 else 0)+2*regValue _ s=(if t (b p) then 1 else 0)+2*regValue _ t
    rw [head,tail]
theorem stored {lo hi g n f u neg far long} {L:SkywalkIntegerLayout} {net:Wire→Wire} (bits:Nat)
    (raw cut:State) (z:SkywalkNat.State) (G S:Bool)
    (packed:PackedCut lo hi g n f u neg far long (pullState net raw) cut)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (gate:net g=L.previous) (left:(hi.map Prod.fst).map net=L.a.drop bits) (right:(hi.map Prod.snd).map net=L.b.drop bits)
    (la:bits≤L.a.length) (lb:bits≤L.b.length) : regValue (hi.map Prod.snd) cut.basis=(z.u+z.v)/2^bits:=by
  have math:=mathematical _ _ _ _ _ _ input
  have tag:(pullState net raw).basis g=G:=(congrArg raw.basis gate).trans math.1
  have select (p:Wire×Wire) (h:p∈hi):cut.basis p.2=if G then raw.basis (net p.2) else raw.basis (net p.1):=by
    have e:=(packed.upper p h).2
    rw [tag] at e;exact e
  cases G with
  | false=>
    rw [mapped hi Prod.snd Prod.fst _ (fun q=>raw.basis (net q)) (fun p h=>by simpa using select p h),
      ←unroute net _ _,left,shiftedValue _ _ la,show regValue L.a raw.basis=z.u+z.v from math.2.2.1]
  | true=>
    rw [mapped hi Prod.snd Prod.snd _ (fun q=>raw.basis (net q)) (fun p h=>by simpa using select p h),
      ←unroute net _ _,right,shiftedValue _ _ lb,show regValue L.b raw.basis=z.u+z.v from math.2.2.1]
theorem three (a b c:Wire) (s:BasisState) (row:Nat)
    (ha:s a=row.testBit 12) (hb:s b=row.testBit 13) (hc:s c=row.testBit 14) :
    regValue [a,b,c] s=row/4096%8:=by
  simp only [regValue,List.foldr_cons,List.foldr_nil,ha,hb,hc,Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
  split <;> split <;> split <;> simp_all <;> omega
theorem assemble (b k:Nat) (z:SkywalkNat.State) (G S:Bool) (s:BasisState) (a c e:Wire) (rest:List Wire)
    (ha:s a=(shadowRow b k z G S).testBit 12) (hc:s c=(shadowRow b k z G S).testBit 13)
    (he:s e=(shadowRow b k z G S).testBit 14)
    (high:regValue rest s=(z.u+z.v)/2^(b+k+1+3)) :
    regValue ([a,c,e]++rest) s=(if Shadow.far b k z then Shadow.high b k z else 0):=by
  rw [regValue_append,three _ _ _ _ _ ha hc he,(tags b k z G S).2.2.2.2, high]
  have div:(z.u+z.v)/2^(b+k+1+3)=Shadow.high b k z/8:=by
    unfold Shadow.high Shadow.limb;rw [Nat.div_div_eq_div_mul,pow_add 2 (b+k+1) 3];rfl
  rw [div]
  change (if Shadow.far b k z then Shadow.high b k z%8 else 0)%8+8*(Shadow.high b k z/8)=_
  by_cases h:Shadow.far b k z
  · simp only [h,if_true];omega
  · simp only [h,if_false];unfold Shadow.far at h;omega


end ECDSAAdd.Entrant.StairPacket.SavedHigh

end

section

namespace ECDSAAdd.Entrant.StairPacket.SharedSigned
open SkywalkRails IntegerHigh
set_option maxHeartbeats 2500000
theorem step_flags (g s:Bool) (z:SkywalkNat.State) (odd:z.v%2=1) :
    let c:=SkywalkTrace.code (encode g s z.u z.v)
    SkywalkTrace.next (encode g s z.u z.v)=
      encode c.1 (s ^^ c.2) (SkywalkNat.step z).u (SkywalkNat.step z).v:=by
  have hv:0<(z.v:Int):=by omega
  have vo:(z.v:Int)%2=1:=by omega
  rcases z with ⟨a,b⟩
  change 0<(b:Int) at hv
  change (b:Int)%2=1 at vo
  by_cases ev:a%2=0
  · have sh:=step_encode_even g s (a:Int) (b:Int) (by omega) hv vo (by omega)
    simp only [SkywalkTrace.next,SkywalkTrace.code,sh,railsOf,Bool.xor_false]
    by_cases za:a=0
    · subst a;simp [encode,SkywalkNat.step,signed]
    · simp [encode,SkywalkNat.step,za,ev]
  · have sh:=step_encode_odd g s (a:Int) (b:Int) (by omega) hv vo (by omega)
    simp only [SkywalkTrace.next,SkywalkTrace.code,sh,railsOf]
    have nz:a≠0:=by omega
    cases s <;> by_cases ab:b≤a <;> by_cases eq:a=b <;>
      simp_all [SkywalkNat.step,encode,signed] <;> (try split_ifs) <;> (try omega)
    all_goals dsimp only
    all_goals omega

def flags (g s:Bool) : List (Bool×Bool)→Bool×Bool
  | []=>(g,s)
  | c::cs=>flags c.1 (s ^^ c.2) cs
theorem lift (n:Nat) (g s:Bool) (z:SkywalkNat.State) (odd:z.v%2=1) :
    let out:=flags g s (SkywalkTrace.trace n (encode g s z.u z.v))
    SkywalkTrace.next^[n] (encode g s z.u z.v)=
      encode out.1 out.2 (SkywalkNat.step^[n] z).u (SkywalkNat.step^[n] z).v := by
  induction n generalizing z g s with
  | zero=>rfl
  | succ n ih=>
    simp only [Function.iterate_succ_apply,SkywalkTrace.trace,flags,step_flags g s z odd]
    exact ih _ _ _ (SkywalkNat.step_v_odd_pos z (by omega) odd).2
theorem same (b:Nat) (z:SkywalkNat.State) (small:min z.u z.v<2^b) (odd:z.v%2=1) (G S:Bool) :
    let t:=Shadow.reduced b 15 z
    let pair:=flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
    SkywalkTrace.next^[15] (encode G S z.u z.v)=encode pair.1 pair.2 (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v:=by
  have shadow:=lift 15 G S (Shadow.reduced b 15 z) (shadow_odd b z small odd)
  rw [true_records b z small odd G S] at shadow
  exact ⟨shadow,lift _ _ _ _ odd⟩

end ECDSAAdd.Entrant.StairPacket.SharedSigned

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
/-- The ordinary full-width native steps, before inserting any history encoder. -/
def span (i:Nat) : Nat→Program
  | 0=>[]
  | n+1=>W.compactSkywalkTick base i ++ span (i+1) n
/-- The window's first block: its old cells are the last 5 stock ticks before it, every later block's are the
15 ticks of the block before. Set per tree (dadon 225, +210 bundle 210, full window 90). -/
def firstBlock : Nat := StairPacket.start WindowParams.first
def oldStart (i:Nat) := if i=firstBlock then i-5 else i-15
def oldCount (i:Nat) := if i=firstBlock then 5 else 15
theorem oldStart_first : oldStart firstBlock=firstBlock-5 := if_pos rfl
theorem oldCount_first : oldCount firstBlock=5 := if_pos rfl
theorem oldStart_interior {i:Nat} (h:i≠firstBlock) : oldStart i=i-15 := if_neg h
theorem oldCount_interior {i:Nat} (h:i≠firstBlock) : oldCount i=15 := if_neg h
/-- The logical history cells of the ticks before the block. -/
def oldSites (i:Nat) := (List.range' (oldStart i) (oldCount i)).flatMap fun r=>[base r,base (1028+r)]
/-- The same cells at their physical places in the block's `OB5.sig (i+14)` frame. They equal `oldSites i`
up to order while those cells are fixed (blocks before 270); from 270 on the stock layout has moved the
history cells of ticks 257 and later to `3113-q`. -/
def sites (i:Nat) := (oldSites i).map (OB5.sig (i+14))
/-- The history snapshot comes from this window after its real pack/archive writes. -/
def overlay (i:Nat) (wide history:State) : State :=
  ⟨wide.phase,fun q=>if q∈sites i then history.basis q else wide.basis q⟩
def origin (i:Nat) (raw history:State) : State :=
  overlay i (pullState (OB5.sig (i+14)) (run (span i 15) [] raw)) history
def endRaw (i:Nat) (raw history:State) : State := pullState (OB5.sig (i+14)) (origin i raw history)
theorem endpoint (i:Nat) (limit:i+14≤511) (raw history:State) :
    pullState (OB5.sig (i+14)) (endRaw i raw history)=origin i raw history :=
  OB5.pull_invol _ limit _
theorem outside (i:Nat) (raw history:State) (q:Wire) (h:q∉sites i) :
    (origin i raw history).basis q=(run (span i 15) [] raw).basis (OB5.sig (i+14) q) := by
  simp [origin,overlay,h,pullState]
theorem inside (i:Nat) (raw history:State) (q:Wire) (h:q∈sites i) :
    (origin i raw history).basis q=history.basis q := by simp [origin,overlay,h]
theorem old_cell {i q:Nat} (member:q∈oldSites i) :
    ∃r,oldStart i≤r ∧ r<oldStart i+oldCount i ∧ (q=r+16 ∨ q=r+1044) := by
  obtain ⟨r,hr,he⟩:=List.mem_flatMap.mp member
  have lim:=List.mem_range'_1.mp hr
  refine ⟨r,lim.1,lim.2,?_⟩
  rcases List.mem_cons.mp he with h|h
  · exact Or.inl h
  · right
    have h':=List.mem_singleton.mp h
    change q=1028+r+16 at h'
    omega
theorem old_bound (i:Nat) : oldStart i+oldCount i≤ i+15 := by
  unfold oldStart oldCount
  split_ifs <;> omega
theorem old_window {i:Nat} (lo:15≤ i) : i-15≤oldStart i ∧ oldStart i+oldCount i=i := by
  unfold oldStart oldCount
  split_ifs <;> omega
theorem mem_sites {i:Nat} (bound:i+14≤511) (q:Wire) : q∈sites i ↔ OB5.sig (i+14) q∈oldSites i := by
  unfold sites
  constructor
  · intro h
    obtain ⟨c,hc,e⟩:=List.mem_map.mp h
    rw [←e,OB5.sig_invol _ bound]
    exact hc
  · intro h
    exact List.mem_map.mpr ⟨_,h,OB5.sig_invol _ bound q⟩
/-- Logical old cells come from the snapshot, read through the block's placement (no `Fixed` needed). -/
theorem endRaw_inside_gen (i:Nat) (bound:i+14≤511) (raw history:State) (q:Wire) (member:q∈oldSites i) :
    (endRaw i raw history).basis q=history.basis (OB5.sig (i+14) q) := by
  change (origin i raw history).basis (OB5.sig (i+14) q)=_
  apply inside
  rw [mem_sites bound,OB5.sig_invol _ bound]
  exact member
/-- Every other logical wire is the full-width reference run (no `Fixed` needed). -/
theorem endRaw_outside_gen (i:Nat) (bound:i+14≤511) (raw history:State) (q:Wire) (off:q∉oldSites i) :
    (endRaw i raw history).basis q=(run (span i 15) [] raw).basis q := by
  have invol:=OB5.sig_invol (i+14) bound q
  have out:OB5.sig (i+14) q∉sites i:=by
    rw [mem_sites bound,invol]
    exact off
  change (origin i raw history).basis (OB5.sig (i+14) q)=_
  rw [outside i raw history _ out,invol]
def Earlier (i:Nat) (q:Wire) := ∃r:Nat,r+2≤ i ∧ (q=base r ∨ q=base (1028+r))
def Coherent (i:Nat) (actual reference:State) :=
  actual.phase=reference.phase ∧ ∀q,¬Earlier i q → actual.basis q=reference.basis q
theorem earlier_mono {i j q} (le:i≤j) (h:Earlier i q) : Earlier j q := by
  obtain ⟨r,h,e⟩:=h;exact ⟨r,Nat.le_trans h le,e⟩
theorem away {i q} (hi:i<512) (h:Earlier i q) : q∉(W.compactSkywalkTickLayout base i).wires := by
  obtain ⟨r,lt,e|e⟩:=h
  all_goals subst q;have pos:i≠0:=by omega
  all_goals have width:=W.compactSkywalkTick_width_bounds i hi
  all_goals apply W.compactSkywalkStage_tick_away base i hi base_pool_nodup
  all_goals try simp [skywalkPoolPreviousId,pos]
  all_goals omega
end ECDSAAdd.Entrant.StairPacket.WideReference

end


section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3500000
set_option maxRecDepth 18000
set_option exponentiation.threshold 1024
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
attribute [local irreducible] run
def Kept (ps:Ports) (d:Bool) (row:Nat) (s:State) := ∀i:Fin 16,s.basis (ps ⟨i.val,by omega⟩)=(get (code d) i.val).testBit row
theorem body_keeps (j:Fin 24) (P:Program) (ps:Ports) (d:Bool) (row:Nat) (s:State) (m:List Bool)
    (off:∀i:Fin 16,ps ⟨i.val,by omega⟩∉spanSites j 1 14)
    (hold:Frame ps (code d) row (run P (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m s))) :
    Kept ps d row (run (body j P) m s) := by
  intro i
  simp only [body,run_append,run_take]
  exact (route_outside j 1 14 (by decide) _ (off i) _ _).trans (hold ⟨i.val,by omega⟩)
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255


end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Close
open Arithmetic Partial RailPair Leave225Relocated
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave225Close

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225InputScan
open Partial Arithmetic RailPair PortalValues LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
end ECDSAAdd.Entrant.StairPacket.Leave225InputScan

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225MaskThrough
open Arithmetic Partial LeaveCompanion LeaveCompanion225 LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

end ECDSAAdd.Entrant.StairPacket.Leave225MaskThrough

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave225Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

end ECDSAAdd.Entrant.StairPacket.Leave225Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Readout
open Arithmetic Partial LeaveCompanion225 Leave225OutputPorts LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave225Readout

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Records
open FlipAudit Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Leave225Records

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225TrueMiddle
open Arithmetic SkywalkNat IntegerHigh Shadow HighBankSum HighBankBarrel
open Leave225Join Leave225Word Leave225High Leave225Barrel Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave225TrueMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Close
open Arithmetic Partial RailPair Leave240Relocated
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave240Close

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240InputScan
open Partial Arithmetic RailPair PortalValues LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
end ECDSAAdd.Entrant.StairPacket.Leave240InputScan

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240MaskThrough
open Arithmetic Partial LeaveCompanion LeaveCompanion240 LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

end ECDSAAdd.Entrant.StairPacket.Leave240MaskThrough

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave240Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

end ECDSAAdd.Entrant.StairPacket.Leave240Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Readout
open Arithmetic Partial LeaveCompanion240 Leave240OutputPorts LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave240Readout

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Records
open FlipAudit Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Leave240Records

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240TrueMiddle
open Arithmetic SkywalkNat IntegerHigh Shadow HighBankSum HighBankBarrel
open Leave240Join Leave240Word Leave240High Leave240Barrel Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave240TrueMiddle

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Close
open Arithmetic Partial RailPair Leave255Relocated
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave255Close

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255InputScan
open Partial Arithmetic RailPair PortalValues LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
end ECDSAAdd.Entrant.StairPacket.Leave255InputScan

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255MaskThrough
open Arithmetic Partial LeaveCompanion LeaveCompanion255 LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

end ECDSAAdd.Entrant.StairPacket.Leave255MaskThrough

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Selector
open Arithmetic RecordedQuantum HighBankFirstHit LeaveSelector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

end ECDSAAdd.Entrant.StairPacket.Leave255Selector

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Readout
open Arithmetic Partial LeaveCompanion255 Leave255OutputPorts LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave255Readout

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Records
open FlipAudit Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Leave255Records

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255TrueMiddle
open Arithmetic SkywalkNat IntegerHigh Shadow HighBankSum HighBankBarrel
open Leave255Join Leave255Word Leave255High Leave255Barrel Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave255TrueMiddle

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

/-- margin 17 (T1): `sameThreshold` with the non-strict sum bound. After 15 ticks the reduced sum is only known
to be ≥ 2^(b+1); the guard s+1 ≤ B then still gives half+1 ≤ B by parity (2B ≥ 2 half + 1). -/
theorem sameThreshold17 (half e : Nat) (z r : SkywalkNat.State) (rel : Rel 0 z r)
    (en:e≤1) (sum:2*half≤r.u+r.v) :
    (half≤z.u-e ↔ half≤r.u-e) ∧ (0<z.u ↔ 0<r.u) := by
  cases rel with
  | left B s D guard =>
    dsimp only
    change s+1≤B at guard
    change 2*half≤B+s at sum
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
    have low:=sumLower 15 (2^b*2) (reduced b 15 z) (by unfold total;omega)
    apply sameThreshold17 _ _ _ _ (terminalRel _ _ _ rep.1) en
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
    let H:=high b 15 z-1
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

namespace ECDSAAdd.Entrant.StairPacket.LeaveSignedCoordinates
open Arithmetic PortalValues

theorem pair (L:SkywalkIntegerLayout) (g sg:Bool) (u v i:Nat) (s:BasisState)
    (a:signedRegValue L.a s=(SkywalkRails.encode g sg u v).a)
    (b:signedRegValue L.b s=(SkywalkRails.encode g sg u v).b)
    (prev:s L.previous=g) (la:i<L.a.length) (lb:i<L.b.length) :
    let e:=negative sg u
    let p:=(u+v).testBit i
    let n:=(u-e.toNat).testBit i ^^ e
    s (L.a.getD i 0)=(if g then n else p) ∧ s (L.b.getD i 0)=(if g then p else n) := by
  obtain ⟨_,_,pos,mag⟩:=signedWords L g sg u v s a b prev
  let e:=negative sg u
  have signedBit (x:List Wire) (hx:i<x.length) (hm:regValue x (fun q=>s q ^^ e)=u-e.toNat) :
      s (x.getD i 0)=((u-e.toNat).testBit i ^^ e) := by
    have read:=HighBankAdjust.bit_read x i (fun q=>s q ^^ e) hx
    rw [hm] at read
    change (s (x.getD i 0) ^^ e)=_ at read
    rw [←read];cases e <;> simp
  cases g
  · exact ⟨(HighBankAdjust.bit_read _ _ _ la).trans (congrArg (Nat.testBit · i) pos),signedBit _ lb mag⟩
  · exact ⟨signedBit _ la mag,(HighBankAdjust.bit_read _ _ _ lb).trans (congrArg (Nat.testBit · i) pos)⟩

theorem sharedDigit (x y b i:Nat) (modEq:x%2^(b+1)=y%2^(b+1)) (hi:i≤b) :
    x.testBit i=y.testBit i := by
  have h:=congrArg (Nat.testBit · i) modEq
  simpa only [Nat.testBit_mod_two_pow,decide_eq_true_eq.mpr (Nat.lt_succ_of_le hi),Bool.true_and] using h

end ECDSAAdd.Entrant.StairPacket.LeaveSignedCoordinates

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket
def MayTouch (j:Fin 24) (w:Wire) : Prop :=
  (start j+15≤w ∧ w≤start j+14+16+(shape j).mid+2) ∨ (786≤w ∧ w≤787+(shape j).mid) ∨
  (1556≤w ∧ w≤1556+(shape j).mid) ∨ (1044+start j≤w ∧ w<1044+start j+15)
instance (j:Fin 24) (w:Wire) : Decidable (MayTouch j w):=by unfold MayTouch;infer_instance
theorem named_range (j:Fin 24) (a n q:Nat) (lim:a+n≤15) (outside:¬MayTouch j (windowNet j q)) :
    q∉spanSites j a n:=by
  intro mem
  obtain ⟨r,hr,inside⟩:=List.mem_flatMap.mp mem
  rw [List.mem_range'_1] at hr
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp inside
  have undo:windowNet j (windowNet j w)=w:=by apply OB5.sig_invol;have hj:=j.isLt;simp [start];omega
  rw [undo] at outside
  apply outside
  simp only [ports,SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,
    SkywalkIntegerLayout.bh,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false,shape,smallBits,start] at hw
  simp only [MayTouch,shape,smallBits,start]
  repeat' first | cases_type Or | cases_type And
  all_goals try simp only [Wire] at *
  all_goals omega
theorem through_body (j:Fin 24) (P:Program) (s:State) (m:List Bool) (q:Nat)
    (free:¬MayTouch j (windowNet j q))
    (admin:let a:=run (routed j 0 1) m s
      (run P (m.drop (measurementCount (routed j 0 1))) a).basis q=a.basis q) :
    (run (body j P) m s).basis q=s.basis q:=by
  simp only [body,run_append,run_take]
  exact (route_outside j 1 14 (by decide) q (named_range j 1 14 q (by decide) free) _ _).trans
    (admin.trans (route_outside j 0 1 (by decide) q (named_range j 0 1 q (by decide) free) s m))
theorem body_cover (j:Fin 24) (P:Program) (controls effects:List Wire)
    (clean:∀q∈controls,¬MayTouch j (windowNet j q)) (apart:∀q∈controls,q∉effects)
    (cover:wires P⊆effects.toFinset) (s:State) (m:List Bool) (q:Wire) (hit:q∈controls) :
    (run (body j P) m s).basis q=s.basis q:=
  through_body j P s m q (clean q hit) (run_preserves_outside P _ _ q
    (fun used=>apart q hit (List.mem_toFinset.mp (cover used))))
theorem keep_values (a b c:Wire) (saved:List Wire) (s t:State) (H:Nat) (f u:Bool)
    (agree:∀q∈[a,b,c]++saved,t.basis q=s.basis q) (h:regValue saved s.basis=H)
    (sa:s.basis a=false) (sb:s.basis b=f) (sc:s.basis c=u) :
    regValue saved t.basis=H ∧ t.basis a=false ∧ t.basis b=f ∧ t.basis c=u:=
  ⟨(regValue_congr _ _ _ (fun q m=>agree _ (List.mem_append_right _ m))).trans h,
    (agree a (by simp)).trans sa,(agree b (by simp)).trans sb,(agree c (by simp)).trans sc⟩

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter225
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Enter225

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter240
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Enter240

end

section

namespace ECDSAAdd.Entrant.StairPacket.Enter255
open Arithmetic MappedCompressed EnterProof PortalValues
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Enter255

end

section

namespace ECDSAAdd.Entrant.StairPacket.EnterJ
open Arithmetic MappedCompressed EnterProof PortalValues Partial
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

end ECDSAAdd.Entrant.StairPacket.EnterJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
attribute [local irreducible] run
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
theorem coherent_step {i:Nat} (hi:i<512) {a b:State} (same:Coherent i a b) (m:List Bool) :
    Coherent (i+1) (run (W.compactSkywalkTick base i) m a) (run (W.compactSkywalkTick base i) m b) := by
  let P:=W.compactSkywalkTick base i
  have sub:=W.compactSkywalkTick_support base i hi base_pool_nodup
  have on:∀q∈wires P,a.basis q=b.basis q:=fun q mem=>same.2 q (fun old=>away hi old (List.mem_toFinset.mp (sub mem)))
  have ste:=run_measured_locality P (wires P) (Finset.Subset.refl _) a b m same.1 on
  refine ⟨ste.1,?_⟩
  intro q outside
  by_cases inside:q∈wires P
  · exact ste.2 q inside
  · exact (run_preserves_outside _ m a _ inside).trans ((same.2 _ (fun e=>outside (earlier_mono (by omega) e))).trans
      (run_preserves_outside _ m b _ inside).symm)
theorem coherent_span (i n:Nat) (bound:i+n≤512) (a b:State) (same:Coherent i a b) (m:List Bool) :
    Coherent (i+n) (run (span i n) m a) (run (span i n) m b):=by
  induction n generalizing i a b m with
  | zero=>simpa [span,run] using same
  | succ n ih=>
    simp only [span,run_append,run_take]
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih (i+1) (by omega) _ _ (coherent_step (by omega) same m) (m.drop _)

theorem past_slot (i q:Nat) (lo:15≤ i) (member:q∈oldSites i) : Earlier (i+15) q:=by
  obtain ⟨r,_,lt,h|h⟩:=old_cell member
  · have w:=old_window lo
    exact ⟨r,by omega,Or.inl h⟩
  · have w:=old_window lo
    exact ⟨r,by omega,Or.inr (by change q=1028+r+16;omega)⟩
theorem after_coherent_gen (i:Nat) (lo:15≤ i) (hi:i+15≤512) (raw history ref:State)
    (same:Coherent i raw ref) :
    Coherent (i+15) (endRaw i raw history) (run (span i 15) [] ref) := by
  have c:=coherent_span i 15 hi raw ref same []
  refine ⟨c.1,?_⟩
  intro q off
  have invol:=OB5.sig_invol (i+14) (by omega) q
  have out:OB5.sig (i+14) q∉sites i:=by
    rw [mem_sites (by omega),invol]
    exact fun hit=>off (past_slot i q lo hit)
  change (origin i raw history).basis (OB5.sig (i+14) q)=_
  rw [outside i raw history _ out,invol,c.2 q off]
def Domain (i x p:Nat) (s:State) := ∃ref:State,Coherent i s ref ∧
  W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i ref.basis

theorem full_span (i n x p:Nat) (hi:i+n≤512) (hp0:0<p) (hx0:0<x) (odd:p%2=1) (hp:p<2^256)
    (gap:p+2^32≤2^256) (hx:x<p) (cop:x.Coprime p) (s:State) (m:List Bool)
    (invariant:W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) (i+n) (run (span i n) m s).basis := by
  induction n generalizing i s m with
  | zero=>simpa [span,run] using invariant
  | succ n ih=>
    simp only [span,run_append,run_take]
    have tick:=(W.compactSkywalkStageStep base base_pool_nodup x p i hp0 hx0 odd hp gap hx cop (by omega) s m invariant).2
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih (i+1) (by omega) _ (m.drop _) tick

theorem advance_gen (i x p:Nat) (lo:15≤ i) (hi:i+15≤512) (hp0:0<p) (hx0:0<x) (odd:p%2=1) (hp:p<2^256)
    (gap:p+2^32≤2^256) (hx:x<p) (cop:x.Coprime p) (raw history:State) (dom:Domain i x p raw) :
    Domain (i+15) x p (endRaw i raw history) := by
  obtain ⟨ref,same,valid⟩:=dom
  exact ⟨_,after_coherent_gen i lo hi raw history ref same,
    full_span i 15 x p hi hp0 hx0 odd hp gap hx cop ref [] valid⟩
end ECDSAAdd.Entrant.StairPacket.WideReference

end



section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket
set_option maxRecDepth 30000
attribute [local irreducible] run
theorem cells_congr (j:Fin 24) (s t:State) (C:∀r:Fin 15,
    cell (shape j) r (mappedBasis j s.basis)=cell (shape j) r (mappedBasis j t.basis)) (i n:Nat) (bound:i+n≤15) :
    readCells (shape j) i n (mappedBasis j s.basis)=readCells (shape j) i n (mappedBasis j t.basis) := by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=>
    simp only [readCells,C ⟨i,by omega⟩,ih (i+1) (by omega)]

namespace Leave225Records
open ArchiveBoundary240
end Leave225Records
namespace Leave240Records
open ArchiveBoundary255
end Leave240Records
namespace Leave255Records
open ArchiveBoundary270
end Leave255Records
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3000000
set_option maxRecDepth 15000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CompanionInput
open Arithmetic PortalAnd LeaveCompanion LeaveCompanion225
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave225CompanionInput

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225NextFlagTruth
open Arithmetic SkywalkNat LeaveCompanion LeaveCompanion225 Leave225OutputPorts
open Leave225Readout
attribute [local irreducible] SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave225NextFlagTruth

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Posted
open Leave225Close Leave225Relocated LeaveSelector StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225Posted

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RetireActual
open Arithmetic LeaveSelector Leave225Selector Leave225Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave225RetireActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225SignClose
open Arithmetic Partial Leave225Middle Leave225High Leave225Barrel HighBankBarrel LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225SignClose

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates
set_option maxRecDepth 60000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225WideWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CompanionInput
open Arithmetic PortalAnd LeaveCompanion LeaveCompanion240
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave240CompanionInput

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240NextFlagTruth
open Arithmetic SkywalkNat LeaveCompanion LeaveCompanion240 Leave240OutputPorts
open Leave240Readout
attribute [local irreducible] SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave240NextFlagTruth

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Posted
open Leave240Close Leave240Relocated LeaveSelector StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240Posted

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RetireActual
open Arithmetic LeaveSelector Leave240Selector Leave240Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave240RetireActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240SignClose
open Arithmetic Partial Leave240Middle Leave240High Leave240Barrel HighBankBarrel LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240SignClose

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates
set_option maxRecDepth 60000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240WideWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CompanionInput
open Arithmetic PortalAnd LeaveCompanion LeaveCompanion255
set_option maxRecDepth 50000

end ECDSAAdd.Entrant.StairPacket.Leave255CompanionInput

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255NextFlagTruth
open Arithmetic SkywalkNat LeaveCompanion LeaveCompanion255 Leave255OutputPorts
open Leave255Readout
attribute [local irreducible] SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave255NextFlagTruth

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Posted
open Leave255Close Leave255Relocated LeaveSelector StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255Posted

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RetireActual
open Arithmetic LeaveSelector Leave255Selector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave255RetireActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255SignClose
open Arithmetic Partial Leave255Middle Leave255High Leave255Barrel HighBankBarrel LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255SignClose

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates
set_option maxRecDepth 60000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255WideWords

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

namespace ECDSAAdd.Entrant.StairPacket.LeaveTerminalBound
open SkywalkNat HighBankSum

end ECDSAAdd.Entrant.StairPacket.LeaveTerminalBound

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
attribute [local irreducible] run unrouted
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
attribute [local irreducible] run unrouted
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
attribute [local irreducible] run unrouted
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
theorem history_only (i:Nat) (hi:i≤512) (d:Bool) (q:Wire)
    (mem:q∈wires (Rolling1588.Integer.encodePrefix base d i)) : Earlier i q:=by
  rw [Rolling1588.Integer.prefix_support_eq] at mem
  obtain ⟨j,rfl,h|⟨low,high⟩⟩:=StackOB5Base.encodePrefix_mem i hi _ mem
  · exact ⟨j,h,Or.inl rfl⟩
  · exact ⟨j-1028,by omega,Or.inr (congrArg base (by omega))⟩

theorem initial (i x p:Nat) (hi:i≤512) (d:Bool) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis) : Domain i x p s:=by
  obtain ⟨raw,good,bits⟩:=stage
  refine ⟨⟨s.phase,raw.basis⟩,⟨rfl,?_⟩,good⟩
  intro q out
  change s.basis q=raw.basis q
  rw [bits];exact run_preserves_outside _ [] raw _ (fun mem=>out (history_only i hi d q mem))

theorem leaves_reference (i x p:Nat) (hi:i≤512) (d:Bool) (s:State) (dom:Domain i x p s) :
    ∃original:State,Rolling1588.Integer.Stage base d x p i original.basis ∧ Coherent i s original := by
  obtain ⟨ref,match',good⟩:=dom
  let original:State:=⟨s.phase,(run (Rolling1588.Integer.encodePrefix base d i) [] ref).basis⟩
  refine ⟨original,⟨ref,good,rfl⟩,rfl,?_⟩
  intro q off
  exact (match'.2 q off).trans (run_preserves_outside _ [] ref _ (fun mem=>off (history_only i hi d q mem))).symm

theorem reads_now {i:Nat} (hi:i<512) {s ref:State} (same:Coherent i s ref) :
    ∀q∈(W.compactSkywalkTickLayout base i).wires.toFinset,s.basis q=ref.basis q :=
  fun q hit=>same.2 q (fun earlier=>away hi earlier (List.mem_toFinset.mp hit))

theorem match_input (L:SkywalkIntegerLayout) (A B:Int) (G:Bool) (a b:BasisState)
    (eq:∀q∈L.wires.toFinset,a q=b q) (input:SkywalkIntegerInput L A B G b) : SkywalkIntegerInput L A B G a := by
  have bits (q:Wire) (h:q∈L.a ∨ q∈L.b ∨ q=L.previous ∨ q=L.ext ∨ q=L.history ∨ q∈L.carry) : a q=b q:=by
    apply eq q <| List.mem_toFinset.mpr ?_
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.a,SkywalkIntegerLayout.b,List.mem_cons,List.mem_append] at *
    tauto
  have aw:=(signedRegValue_eq_iff _ a b).mpr (fun q h=>bits q (Or.inl h))
  have bw:=(signedRegValue_eq_iff _ a b).mpr (fun q h=>bits q (Or.inr (Or.inl h)))
  have cw:=regValue_congr L.carry a b (fun q h=>bits q (by simp [h]))
  obtain ⟨va,vb,g,e,h,c⟩:=input
  exact ⟨aw.trans va,bw.trans vb,(bits _ (by simp)).trans g,(bits _ (by simp)).trans e,(bits _ (by simp)).trans h,cw.trans c⟩

end ECDSAAdd.Entrant.StairPacket.WideReference

end





section

namespace ECDSAAdd.Entrant.StairPacket.EndTick
open Arithmetic MappedCompressed Secp256k1 ArchiveBoundary270 ParkEndpoint
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Core
open Arithmetic Partial Leave225SignClose Leave225Selector LeaveSelector Leave225Barrel Leave225High Leave225Word Leave225Join
open HighBankBarrel Leave225RetireActual Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave225Core

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225EraseActual
open Arithmetic Partial PortalAnd LeaveCompanion LeaveCompanion225
set_option maxRecDepth 60000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225EraseActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Loaded
open Arithmetic LeaveSelector Leave225Selector Leave225RetireActual SkywalkNat IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225Loaded

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Restored
open Arithmetic SkywalkNat Shadow PortalValues LeaveCompanion LeaveCompanion225
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave225Restored

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225TailFlags
open Arithmetic Partial LeaveCompanion LeaveCompanion225 Leave225OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225TailFlags

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Core
open Arithmetic Partial Leave240SignClose Leave240Selector LeaveSelector Leave240Barrel Leave240High Leave240Word Leave240Join
open HighBankBarrel Leave240RetireActual Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave240Core

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240EraseActual
open Arithmetic Partial PortalAnd LeaveCompanion LeaveCompanion240
set_option maxRecDepth 60000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240EraseActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Loaded
open Arithmetic LeaveSelector Leave240Selector Leave240RetireActual SkywalkNat IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240Loaded

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Restored
open Arithmetic SkywalkNat Shadow PortalValues LeaveCompanion LeaveCompanion240
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave240Restored

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240TailFlags
open Arithmetic Partial LeaveCompanion LeaveCompanion240 Leave240OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240TailFlags

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Core
open Arithmetic Partial Leave255SignClose Leave255Selector LeaveSelector Leave255Barrel Leave255High Leave255Word Leave255Join
open HighBankBarrel Leave255RetireActual Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave255Core

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255EraseActual
open Arithmetic Partial PortalAnd LeaveCompanion LeaveCompanion255
set_option maxRecDepth 60000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255EraseActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Loaded
open Arithmetic LeaveSelector Leave255Selector Leave255RetireActual SkywalkNat IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255Loaded

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Restored
open Arithmetic SkywalkNat Shadow PortalValues LeaveCompanion LeaveCompanion255
set_option maxHeartbeats 1500000
attribute [local irreducible] SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave255Restored

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255TailFlags
open Arithmetic Partial LeaveCompanion LeaveCompanion255 Leave255OutputPorts
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255TailFlags

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem masked_body (P Q:Program) (qs tags:List Wire) (s:State) (m t:List Bool)
    (blank:∀q∈tags,q∉wires P) (away:∀q∈qs,q∉tags)
    (steady:∀s:State,∀q∈qs,(run Q t s).basis q=s.basis q) :
    ∀q∈qs,(run Q t (run P m s)).basis q=(run Q t (run P m (eraseSites tags s))).basis q:=by
  intro q h
  rw [steady _ q h,steady _ q h,erase_run tags P blank]
  simp [eraseSites,away _ h]
namespace NativePack240
end NativePack240
namespace NativePack255
end NativePack255

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint
open Arithmetic MappedCompressed IntegerPacket RailPair Portal270Flag ArchiveBoundary270
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def ordinary (q:Wire) : Prop := q∉src ∧ q∉dst ∧ q≠1700 ∧ q≠1698 ∧ q≠1699 ∧ q∉sites hiPairs
instance (q:Wire) : Decidable (ordinary q):=by unfold ordinary;infer_instance
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed SkywalkRails
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
def canonical (i x p:Nat) := SkywalkTrace.next^[i] (encode false false x p)
def unsigned (i x p:Nat) := SkywalkNat.step^[i] (SkywalkNat.init x p)
structure Bounds (x p:Nat) : Prop where
  positive : 0<p
  nonzero : 0<x
  odd : p%2=1
  cap : p<2^256
  gap : p+2^32≤2^256
  small : x<p
  coprime : x.Coprime p
def InputAt (i:Nat) (z:SkywalkRails.State) (s:State):=SkywalkIntegerInput (W.compactSkywalkTickLayout base i) z.a z.b z.g s.basis
theorem fixed_input (i x p:Nat) (hi:i<512) (good:Bounds x p) (s:State) (dom:Domain i x p s):
    InputAt i (canonical i x p) s:=by
  obtain ⟨ref,stage,match'⟩:=leaves_reference i x p (by omega) true s dom
  exact match_input _ _ _ _ _ _ (reads_now hi match')
    (original_input true x p i good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime hi ref stage)
theorem unique_input {i:Nat} {s:State} {a b:SkywalkRails.State} (left:InputAt i a s) (right:InputAt i b s):a=b:=
  SkywalkRails.State.ext (left.1.symm.trans right.1) (left.2.1.symm.trans right.2.1) (left.2.2.1.symm.trans right.2.2.1)
theorem advance_signed_gen (i b x p:Nat) (lo:15≤ i) (hi:i+15<512) (good:Bounds x p)
    (raw history:State) (dom:Domain i x p raw) (G S:Bool)
    (input:InputAt i (encode G S (unsigned i x p).u (unsigned i x p).v) raw)
    (small:min (unsigned i x p).u (unsigned i x p).v<2^b) :
    let z:=unsigned i x p
    let t:=Shadow.reduced b 15 z
    let flags:=SharedSigned.flags G S (SkywalkTrace.trace 15 (encode G S z.u z.v))
    let endState:=unsigned (i+15) x p
    SkywalkTrace.next^[15] (encode G S t.u t.v)=encode flags.1 flags.2 (SkywalkNat.step^[15] t).u (SkywalkNat.step^[15] t).v ∧
      InputAt (i+15) (encode flags.1 flags.2 endState.u endState.v) (endRaw i raw history):=by
  let z:=unsigned i x p
  have odd:z.v%2=1:=(SkywalkNat.iter_valid i (SkywalkNat.init x p) good.positive good.odd).2.1
  obtain ⟨a,b'⟩:=SharedSigned.same b z small odd G S
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

end



section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Front
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave225Front

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Mirror
open GateMirror
set_option maxRecDepth 45000
set_option maxHeartbeats 9000000
end ECDSAAdd.Entrant.StairPacket.Leave225Mirror

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Routed
open Arithmetic Partial IntegerHigh LeaveSelector Leave225Selector Leave225RetireActual Leave225Barrel Leave225High Leave225Word Leave225Join
open LeaveReadoutFrame Leave225OutputPorts HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave225Routed

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Front
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave240Front

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Mirror
open GateMirror
set_option maxRecDepth 45000
set_option maxHeartbeats 9000000
end ECDSAAdd.Entrant.StairPacket.Leave240Mirror

end
end
-- ==== w4: step 5: par-c1 Fam3/Fam4, K1 (Fam5 by renaming), Fam5 downstream, Fam6 ====
-- ---- w4 step 5: ParC1/Fam3.lean ----

/-! par-c1: generic leave families, batch 3: the entry of the leave (dadon's `Leave{s}InputScan`,
`Leave{s}CompanionInput`, `Leave{s}EraseActual`). The scan is par-b's fixed segment `leaveFix0`, identified with
dadon's `RailPair.scan` and the stock packet's ports by small decides over the window blocks. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000

/-- dadon's `Leave{s}InputScan.pairs`: the 19 low columns `(a0-1+i, b0-1+i)`. -/
def scanPairs (j : Fin 24) : List (Wire × Wire) :=
  (List.range 19).map (fun i => (a0P (start j) - 1 + i, b0P (start j) - 1 + i))

theorem scan_emitted : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    GateMirror.forward (leaveFix0 (start j) (sbP (start j))) =
      scan (a0P (start j) + 17) (b0P (start j) + 17) (start j + 30) (e0P (start j) + 5) (scanPairs j) := by
  decide +kernel

theorem scan_layout : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    ScanGeometry (a0P (start j) + 17) (b0P (start j) + 17) (start j + 30) (e0P (start j) + 5) (scanPairs j) := by
  intro j h0 h1
  constructor <;> revert j <;> decide +kernel

/-- The scan reads the stock packet's ports of block `j` (above bit `sb`). -/
theorem scan_ports : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    (scanPairs j).map Prod.fst = ((IntegerPacket.ports (shape j) 15).a.drop (sbP (start j))).map (windowNet j) ∧
    (scanPairs j).map Prod.snd = ((IntegerPacket.ports (shape j) 15).b.drop (sbP (start j))).map (windowNet j) ∧
    a0P (start j) + 17 = windowNet j (IntegerPacket.ports (shape j) 15).aSign ∧
    b0P (start j) + 17 = windowNet j (IntegerPacket.ports (shape j) 15).bSign ∧
    start j + 30 = windowNet j (IntegerPacket.ports (shape j) 15).previous ∧
    sbP (start j) ≤ (IntegerPacket.ports (shape j) 15).a.length ∧
    sbP (start j) ≤ (IntegerPacket.ports (shape j) 15).b.length := by
  decide +kernel

theorem scanPairs_getD (j : Fin 24) (i : Nat) (hi : i < 19) :
    ((scanPairs j).map Prod.fst).getD i 0 = a0P (start j) - 1 + i ∧
    ((scanPairs j).map Prod.snd).getD i 0 = b0P (start j) - 1 + i := by
  simp [scanPairs, List.getD_eq_getElem?_getD, hi]

/-- dadon's `Leave{s}InputScan.result`. -/
theorem inputScan_result (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State) (tape : List Bool) (u v : Nat)
    (G sg : Bool) (ready : onRails j 15 (SkywalkRails.encode G sg u v) s.basis) (fresh : s.basis (e0P (start j) + 5) = false) :
    let t := run (GateMirror.forward (leaveFix0 (start j) (sbP (start j)))) tape s
    let e := negative sg u
    t.phase = s.phase ∧ t.basis (e0P (start j) + 5) = e ∧
      (∀ i < 19, t.basis (a0P (start j) - 1 + i) = ((u+v)/2^(sbP (start j))).testBit i ∧
        t.basis (b0P (start j) - 1 + i) = ((u - e.toNat)/2^(sbP (start j))).testBit i) ∧
      ∀ q, q ≠ e0P (start j) + 5 → q ∉ RailPair.sites (scanPairs j) → t.basis q = s.basis q := by
  obtain ⟨pl, pr, pa, pb, pg, la, lb⟩ := scan_ports j h0 h1
  rw [scan_emitted j h0 h1]
  generalize ht : run (scan (a0P (start j) + 17) (b0P (start j) + 17) (start j + 30) (e0P (start j) + 5) (scanPairs j)) tape s = t
  have out := scanRouted j (sbP (start j)) _ _ _ _ (scanPairs j) (scan_layout j h0 h1) pl pr pa pb pg s tape u v G sg ready
    fresh la lb
  have frame := scan_run _ _ _ _ _ (scan_layout j h0 h1) s tape fresh
  rw [ht] at out frame
  refine ⟨frame.1, out.1, ?_, frame.2.2.1⟩
  intro i hi
  have g := scanPairs_getD j i hi
  have len : ((scanPairs j).map Prod.fst).length = 19 ∧ ((scanPairs j).map Prod.snd).length = 19 := by simp [scanPairs]
  rw [← g.1, ← g.2, HighBankAdjust.bit_read ((scanPairs j).map Prod.fst) i t.basis (by rw [len.1]; exact hi),
    HighBankAdjust.bit_read ((scanPairs j).map Prod.snd) i t.basis (by rw [len.2]; exact hi), out.2.1, out.2.2]
  exact ⟨rfl, rfl⟩

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step leaveFix0 leaveFix1 leaveFix2 latch Companion.erase

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 5: ParC1/Fam4.lean ----

/-! par-c1: generic leave families, batch 4: the entry block `fix0 ++ fix1 ++ fix2` (dadon's `Leave{s}Front`,
`Leave{s}FrontReady`, `Leave{s}EntryAction`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror PortalAnd RailPair PortalValues LeaveReadoutFrame LeaveCompanion LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3000000

/-- dadon's `Leave{s}Front.entry` (= `leave.take 242`). -/
def entryOps (s : Nat) : List Gate := leaveFix0 s (sbP s) ++ leaveFix1 s (sbP s) ++ leaveFix2 s (sbP s)
/-- dadon's `Leave{s}Close.history`: the block's 15 history letters `s+16 .. s+30`. -/
def history (j : Fin 24) : List Wire := (List.range 15).map (start j + 16 + ·)
/-- dadon's `Leave{s}Selector.ports`. -/
def ports (j : Fin 24) : Ports := ⟨start j + 16, a0P (start j), e0P (start j) + 6, e0P (start j) + 7⟩
/-- dadon's `Leave{s}FrontReady.watched`. -/
def watched (j : Fin 24) : List Wire := [e0P (start j) + 6, e0P (start j) + 7] ++ List.range' 1559 39

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
  exact le_trans (Nat.add_le_add_left (Nat.le_of_lt_succ hi) 1557) (by decide : 1557 + 17 ≤ 1574)

/-! Arithmetic that `entry_core` needs, proved here so `omega` never sees `onRails` or `rail_win`. -/

theorem sb_lo (s : Nat) (hs : s ≤ 390) : 61 ≤ sbP s := by
  simp only [sbP]
  have hsub : 122 ≤ 513 - s := by omega
  have : 61 * 2 ≤ 513 - s := by simpa using hsub
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr this

theorem sb_hi (s : Nat) (hs : 90 ≤ s) : sbP s ≤ 211 := by
  simp only [sbP]
  exact Nat.div_le_div_right (show 513 - s ≤ 423 by omega)

theorem run_forward_append (a b : List Gate) (m : List Bool) (s : State) :
    run (GateMirror.forward (a ++ b)) m s =
      run (GateMirror.forward b) (m.drop (measurementCount (GateMirror.forward a)))
        (run (GateMirror.forward a) m s) := by
  rw [forward_app, run_append, run_take]

attribute [local irreducible] run SkywalkNat.step leaveFix0 leaveFix1 leaveFix2 latch Companion.erase

theorem flip_dest (s h : Nat) (q : Wire) (hq : q < s + 16 ∨ s + 30 < q) :
    q ∉ (GateMirror.forward (leaveFix1 s h)).map destination := by
  rw [fix1_forward]
  simp only [notRegister, List.map_map, List.mem_map, List.mem_range, not_exists, not_and]
  intro i hi e
  simp only [Function.comp, destination] at e
  unfold Wire at *; omega

/-! EntryAction (dadon's `Leave{s}EntryAction`). -/

/-- dadon's `oddRead`: the history letters, negated. -/
def oddRead (j : Fin 24) (v : BasisState) := (List.range 15).map (fun i => !v ((ports j).g + i))

/-- The scan and the erase never write the history letters (dadon's `historyGeom`). -/
theorem history_untouched : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 → ∀ i < 15,
    start j + 16 + i ∉ (GateMirror.forward (leaveFix0 (start j) (sbP (start j)))).map destination ∧
    start j + 16 + i ∉ (GateMirror.forward (leaveFix2 (start j) (sbP (start j)))).map destination := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 5b: proof-q1542 win/src/ParC1/Fam5.lean (par-c1 Fam5 definitions + K1 as LeaveJ.SelRen + selector semantics) ----

/-! par-c1: generic leave families, batch 5: the first-hit layout and the selector (dadon's `Leave{s}Hit`,
`Leave{s}Selector`, the prepared/retired selector words). The selector op lists are functions of the block.
The symbolic certificates (`controlCert`, `cleanCert`, `tagCertificate`, `foot_ok`) are decided once, at block 10
(dadon's 225), and carried to every block by a wire renaming that the symbolic simulator commutes with
(design-w4 K1, namespace `LeaveJ.SelRen`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
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

/-! The selector words. -/

def farOps (j : Fin 24) : List Op := (1559 :: (List.range 5).map (1561 + ·)).map (fun a => .xor a (e0P (start j) + 7))
def zeroOps : List Op := [.xor 1559 1576, .xor 1561 1576]
def suffixOps (j : Fin 24) : List Op :=
  (List.range 12).map (fun i => .save (start j + 29 - i) (if i = 0 then start j + 30 else 1576 + i) (1577 + i))
def selectOps (j : Fin 24) : List Op :=
  [.save 1562 1588 1589, .save 1563 1586 1590, .save 1564 1584 1591, .save 1565 1582 1592, .save 1566 1580 1593,
   .save 1567 1578 1594, .save 1568 (start j + 30) 1595]
def crossOps (j : Fin 24) : List Op :=
  (List.range 16).map (fun i => .mix (tagsP.getD i 0) (a0P (start j) + i) (e0P (start j) + 6))
def signOps : List Op :=
  [.xor 1589 1596, .xor 1590 1596, .xor 1591 1596, .xor 1592 1596, .xor 1593 1596, .xor 1594 1596, .xor 1595 1596,
   .xor 1569 1596, .xor 1570 1596, .xor 1571 1596, .xor 1572 1596, .xor 1573 1596, .xor 1574 1596, .xor 1575 1596,
   .xor 1560 1596]
def productOps (j : Fin 24) : List Op := [.save (e0P (start j) + 6) 1596 1597]
/-- dadon's `Leave{s}Selector.prepare`. -/
def prepare (j : Fin 24) : List Op :=
  farOps j ++ zeroOps ++ suffixOps j ++ selectOps j ++ crossOps j ++ signOps ++ productOps j
/-- dadon's `Leave{s}Selector.retire`. -/
def retire (j : Fin 24) : List Op :=
  (productOps j).reverse ++ signOps ++ (selectOps j).reverse ++ (suffixOps j).reverse ++ zeroOps

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

/-! The symbolic simulator commutes with a wire renaming that is injective on the selector wires. -/
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.SelRen
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

end ECDSAAdd.Entrant.StairPacket.LeaveJ.SelRen
end

/-! Block 10 to block j. -/
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.SelRen
open Arithmetic RecordedQuantum Partial GateMirror HighBankFirstHit
open ECDSAAdd.Entrant.StairPacket.LeaveJ
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1000000

/-- block 10's selector wires. -/
def D (q : Nat) : Prop :=
  (1559 ≤ q ∧ q ≤ 1597) ∨ (241 ≤ q ∧ q ≤ 255) ∨ (401 ≤ q ∧ q ≤ 416) ∨ q = 1724 ∨ q = 1725
instance (q : Nat) : Decidable (D q) := by unfold D; infer_instance

/-- block 10 → block j. -/
def ren (j : Fin 24) (q : Nat) : Nat :=
  if 241 ≤ q ∧ q ≤ 255 then q - 225 + start j
  else if 401 ≤ q ∧ q ≤ 416 then q - 401 + a0P (start j)
  else if q = 1724 then e0P (start j) + 6
  else if q = 1725 then e0P (start j) + 7
  else q

theorem geo (j : Fin 24) : a0P (start j) = start j + (513 - start j) / 2 + 32 ∧
    e0P (start j) = 1574 + (513 - start j) / 2 ∧ start j = 75 + 15 * j.val := ⟨rfl, rfl, rfl⟩

theorem ren_inj (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : InjOn D (ren j) := by
  intro a b ha hb h
  obtain ⟨g1, g2, g3⟩ := geo j
  unfold ren at h
  unfold D at ha hb
  split_ifs at h <;> omega

theorem ren_const (j : Fin 24) (q : Nat) (h : 1559 ≤ q ∧ q ≤ 1597) : ren j q = q := by
  unfold ren; split_ifs <;> omega
theorem ren_g (j : Fin 24) (q : Nat) (h : 241 ≤ q ∧ q ≤ 255) : ren j q = q - 225 + start j := by
  unfold ren; rw [if_pos h]
theorem ren_u (j : Fin 24) (q : Nat) (h : 401 ≤ q ∧ q ≤ 416) : ren j q = q - 401 + a0P (start j) := by
  unfold ren; rw [if_neg (by omega), if_pos h]
theorem ren_cross (j : Fin 24) : ren j 1724 = e0P (start j) + 6 := by unfold ren; simp
theorem ren_near (j : Fin 24) : ren j 1725 = e0P (start j) + 7 := by unfold ren; simp

theorem s10 : start 10 = 225 := rfl
theorem a10 : a0P 225 = 401 := rfl
theorem e10 : e0P 225 = 1718 := rfl

/-! `prepare` and `retire` of block j are block 10's, renamed. -/

theorem farOps_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : (farOps 10).map (rOp (ren j)) = farOps j := by
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

theorem suffixOps_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
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

theorem crossOps_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    (crossOps 10).map (rOp (ren j)) = crossOps j := by
  unfold crossOps; rw [List.map_map]; apply List.map_congr_left; intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_apply, rOp, s10, a10, e10, LeaveSelector.Op.mix.injEq]
  refine ⟨ren_const j _ (tags_range i hi), ?_, ren_cross j⟩
  rw [ren_u j _ (by omega)]; unfold Wire; omega

theorem productOps_ren (j : Fin 24) : (productOps 10).map (rOp (ren j)) = productOps j := by
  simp only [productOps, List.map_cons, List.map_nil, rOp, s10, e10, ren_cross j, ren_const j 1596 (by omega),
    ren_const j 1597 (by omega)]

theorem prepare_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    (prepare 10).map (rOp (ren j)) = prepare j := by
  simp only [prepare, List.map_append, farOps_ren j h0 h1, zeroOps_ren j, suffixOps_ren j h0 h1, selectOps_ren j,
    crossOps_ren j h0 h1, signOps_ren j, productOps_ren j]

theorem retire_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    (retire 10).map (rOp (ren j)) = retire j := by
  simp only [retire, List.map_append, List.map_reverse, zeroOps_ren j, suffixOps_ren j h0 h1, selectOps_ren j,
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

theorem start_rel (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : LeaveSelector.Mode) :
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

theorem crossing_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : LeaveSelector.Mode) :
    rE (ren j) (LeaveSelector.crossing (ports 10) k) = LeaveSelector.crossing (ports j) k := by
  unfold LeaveSelector.crossing
  by_cases h : LeaveSelector.enabled k = true
  · simp only [h, ↓reduceIte, rE, ports, s10, a10]
    have := key_le k
    rw [ren_u j _ (by omega), LeaveSelector.Expr.wire.injEq]; unfold Wire; omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]; rfl

theorem suffix_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) : ∀ (l : List Nat), (∀ x ∈ l, x < 15) →
    rE (ren j) (l.foldr (fun x rest => LeaveSelector.conj (.wire (start 10 + 16 + x)) rest) (.bit true)) =
      l.foldr (fun x rest => LeaveSelector.conj (.wire (start j + 16 + x)) rest) (.bit true)
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.foldr_cons]
    rw [rE_conj, suffix_ren j h0 h1 xs (fun y hy => h y (by simp [hy]))]
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

theorem signExpr_ren (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : LeaveSelector.Mode) :
    rE (ren j) (LeaveSelector.signExpr (ports 10) k) = LeaveSelector.signExpr (ports j) k := by
  unfold LeaveSelector.signExpr LeaveSelector.suffixExpr
  by_cases h : (LeaveSelector.right k && decide (0 < LeaveSelector.key k)) = true
  · simp only [h, ↓reduceIte, ports]
    exact suffix_ren j h0 h1 _ (fun x hx => List.mem_range.mp (List.mem_of_mem_drop hx))
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

theorem cn_iff (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (q : Nat) (hq : D q) :
    (ren j q = (ports j).crossing ∨ ren j q = (ports j).near) ↔ (q = (ports 10).crossing ∨ q = (ports 10).near) := by
  have hσ := ren_inj j h0 h1
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

theorem post_rel (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.post (ports j) (prepare j) false k)
      (LeaveSelector.post (ports 10) (prepare 10) false k) := by
  have hσ := ren_inj j h0 h1
  have hs := (sim_rel hσ (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 h1 k)).1
  intro q hq
  have i1 := cn_iff j h0 h1 q hq
  have i2 : ren j q = 1597 ↔ q = 1597 := by
    constructor
    · intro e; exact hσ _ _ hq (by decide) (e.trans (ren_const j 1597 (by omega)).symm)
    · intro e; rw [e]; exact ren_const j 1597 (by omega)
  rw [← prepare_ren j h0 h1]
  simp only [LeaveSelector.post, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  by_cases c1 : q = (ports 10).crossing ∨ q = (ports 10).near
  · rw [if_pos (i1.mpr c1), if_pos c1]; rfl
  · rw [if_neg (fun h => c1 (i1.mp h)), if_neg c1]
    by_cases c2 : q = 1597
    · rw [if_pos (i2.mpr c2), if_pos c2, rE_conj, signExpr_ren j h0 h1 k]
      simp only [rE, cross_eq j]
    · rw [if_neg (fun h => c2 (i2.mp h)), if_neg c2]
      exact hs q hq

theorem restored_good (k : LeaveSelector.Mode) : Good D (LeaveSelector.restored (ports 10) false k) := by
  intro q hq
  simp only [LeaveSelector.restored, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  split_ifs
  · exact hq
  · exact start_good k q hq

theorem restored_rel (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : LeaveSelector.Mode) :
    Rel D (ren j) (LeaveSelector.restored (ports j) false k) (LeaveSelector.restored (ports 10) false k) := by
  intro q hq
  have i1 := cn_iff j h0 h1 q hq
  simp only [LeaveSelector.restored, Bool.not_false, Bool.true_and, decide_eq_true_eq]
  by_cases c1 : q = (ports 10).crossing ∨ q = (ports 10).near
  · rw [if_pos (i1.mpr c1), if_pos c1]; rfl
  · rw [if_neg (fun h => c1 (i1.mp h)), if_neg c1]
    exact start_rel j h0 h1 k q hq

theorem affected_ren (j : Fin 24) :
    (LeaveSelector.affected (ports 10)).map (ren j) = LeaveSelector.affected (ports j) := by
  simp only [LeaveSelector.affected, List.map_append, List.map_cons, List.map_nil, cross_eq j, near_eq j]
  congr 1

end ECDSAAdd.Entrant.StairPacket.LeaveJ.SelRen
end

/-! The seven selector theorems for every block. -/
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.SelRen
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

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ.controlCert (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : Mode) :
    reads (ports j) (sim (prepare j) (LeaveSelector.start (ports j) false k)) = controls (ports j) k := by
  have hσ := ren_inj j h0 h1
  have hs := (sim_rel hσ (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 h1 k)).1
  have c := cert10_control k
  rw [← prepare_ren j h0 h1]
  simp only [reads, controls, List.cons.injEq] at c ⊢
  obtain ⟨c1, c2, c3, c4, -⟩ := c
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · rw [← near_eq j, hs _ (by decide), c1]; rfl
  · rw [← cross_eq j, hs _ (by decide), c2, crossing_ren j h0 h1 k]
  · have e := hs 1596 (by decide)
    rw [ren_const j 1596 (by omega)] at e
    rw [e, c3, signExpr_ren j h0 h1 k]
  · have e := hs 1597 (by decide)
    rw [ren_const j 1597 (by omega)] at e
    rw [e, c4, rE_conj, crossing_ren j h0 h1 k, signExpr_ren j h0 h1 k]

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ.cleanCert (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : Mode) :
    targetCert (ports j) (prepare j) (retire j) false k = true := by
  have hσ := ren_inj j h0 h1
  obtain ⟨v, r, gd⟩ := exits_rel hσ (retire 10) retire10_in _ _ (post_good k) (post_rel j h0 h1 k)
  have c := cert10_clean k
  simp only [targetCert] at c ⊢
  rw [← retire_ren j h0 h1, v, ← affected_ren j, List.all_map]
  refine Eq.trans ?_ c
  refine congrArg (and _) ?_
  apply all_congr_mem
  intro q hq
  have hqD : D q := affected10_in q hq
  simp only [Function.comp_apply]
  rw [r q hqD, restored_rel j h0 h1 k q hqD]
  apply decide_eq_decide.mpr
  exact ⟨rE_inj hσ _ _ (gd q hqD) (restored_good k q hqD), fun e => by rw [e]⟩

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ.tagCertificate (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : Mode) (i : Fin 16) :
    sim (prepare j) (LeaveSelector.start (ports j) false k) (tagsP.getD i 0) =
      .bit (enabled k && decide (i.val = key k)) := by
  have hs := (sim_rel (ren_inj j h0 h1) (prepare 10) prep10_in _ _ (start_good k) (start_rel j h0 h1 k)).1
  have ht := tags_range i i.isLt
  have e := hs (tagsP.getD i 0) (Or.inl ht)
  rw [ren_const j _ ht] at e
  rw [← prepare_ren j h0 h1, e, cert10_tag k i]; rfl

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ.foot_ok (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    (prepare j ++ retire j).all (fun o => decide (o.dst ∈ affected (ports j))) = true := by
  have hσ := ren_inj j h0 h1
  rw [← prepare_ren j h0 h1, ← retire_ren j h0 h1, ← List.map_append, List.all_map, ← cert10_foot]
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

theorem _root_.ECDSAAdd.Entrant.StairPacket.LeaveJ.prefix_parts : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    GateMirror.forward (leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j)) ++
      leaveFix5 (start j) (sbP (start j))) =
      withHits (e0P (start j) + 3) (e0P (start j) + 4) false (swaps j) ((prepare j).map Op.enter) := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.LeaveJ.SelRen
end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-! Selector semantics (dadon's `preparedState`, `selected`, `complete`, `clear`, `retiredFull`). -/

def fullPrefix (j : Fin 24) : List Gate :=
  leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j)) ++ leaveFix5 (start j) (sbP (start j))

/-- dadon's `Leave{s}Selector.clear` (forward): the retired selector word restores the selector wires. -/
theorem clear (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : Mode) (s : State) (m : List Bool) (v : BasisState)
    (input : ∀ q, s.basis q = (post (ports j) (prepare j) false k q).read v) :
    run ((retire j).map Op.exit) m s = ⟨s.phase, fun q => (restored (ports j) false k q).read v⟩ :=
  cleanup (ports j) (prepare j) (retire j) false k s m v input (cleanCert j h0 h1 k)
    (fun o h => of_decide_eq_true (List.all_eq_true.mp (foot_ok j h0 h1) o h))

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 5: ParC1/Fam6.lean ----

/-! par-c1: generic leave families, batch 6: the true middle (dadon's `Leave{s}NearMiddle`, `Leave{s}OutputPorts`,
`Leave{s}TrueMiddle`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror HighBankJoin HighBankReassemble SkywalkNat IntegerHigh Shadow HighBankSum LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-! OutputPorts. -/

/-- dadon's `Leave{s}OutputPorts.live`: the output register's wires. -/
def live (j : Fin 24) (i : Nat) : Wire := if i < lowsP (start j) then a0P (start j) + i else bankW (start j) i

theorem live_row (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (i : Fin 18) : live j i.val = (row j i).keep := by
  have g := row_eq j i
  unfold Column.keep live
  rw [g.2.2.1]
  by_cases h : i.val < lowsP (start j)
  · simp [h, g.1]
  · simp [h, g.2.1]

/-! TrueMiddle (dadon's `Leave{s}TrueMiddle`): the actual word-update values. -/

namespace TrueMiddle
abbrev r (j : Fin 24) (z : SkywalkNat.State) := reduced (sbP (start j)) 15 z
def key (j : Fin 24) (z : SkywalkNat.State) : Fin 16 :=
  ⟨if 2^(sbP (start j)) ≤ z.u then 0 else wait 15 z.u, by have h := wait_le 15 z.u; split <;> omega⟩
def X (j : Fin 24) (z : SkywalkNat.State) := total (step^[15] (r j z)) / 2^(sbP (start j) + 1)
def F (j : Fin 24) (z : SkywalkNat.State) := total (step^[15] z) / 2^(sbP (start j) + 1)
def d (j : Fin 24) (z : SkywalkNat.State) := X j z / 2^(key j z).val
def neg (j : Fin 24) (z : SkywalkNat.State) :=
  cross (d j z) && (!(decide (2^(sbP (start j)) ≤ z.u)) && negative (oddBits (letters 15 (r j z))))
end TrueMiddle

/-! Loaded (dadon's `Leave{s}Loaded`) and SignClose (dadon's `Leave{s}SignClose`). -/

/-- dadon's `Leave{s}RetireActual.prior`: the selector state after the prepared word. -/
def prior (j : Fin 24) (k : Mode) : Sym := sim (prepare j) (LeaveSelector.start (ports j) false k)

theorem tags_inj (i i' : Nat) (hi : i < 16) (hi' : i' < 16) (e : tagsP.getD i 0 = tagsP.getD i' 0) : i = i' := by
  have h : ∀ a b : Fin 16, tagsP.getD a 0 = tagsP.getD b 0 → a = b := by decide
  exact congrArg Fin.val (h ⟨i, hi⟩ ⟨i', hi'⟩ e)

theorem physicalTags (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : Mode) (q : Wire) (hq : q ∈ tagsP) :
    prior j k q = .bit (enabled k && decide (q = tagsP.getD (LeaveSelector.key k) 0)) := by
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 16 ∧ tagsP.getD i 0 = q := by
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hq
    exact ⟨i, by simpa [tagsP] using hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩
  rw [prior, tagCertificate j h0 h1 k ⟨i, hi⟩]
  congr 2
  by_cases hk : LeaveSelector.key k < 16
  · exact Bool.eq_iff_iff.mpr ⟨fun h => by simp_all, fun h => by
      simp only [decide_eq_true_eq] at h ⊢; exact tags_inj _ _ hi hk h⟩
  · have hne : i ≠ LeaveSelector.key k := fun eq => hk (eq ▸ hi)
    have hk' : tagsP.getD (LeaveSelector.key k) 0 = 0 := by
      rw [List.getD_eq_default]
      simp only [tagsP, List.length]
      exact Nat.not_lt.mp hk
    rw [hk']
    have nz : tagsP.getD i 0 ≠ 0 := by
      have t := tags_range' _ (tags_mem i hi)
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1556) t.1)
    simp only [decide_eq_false hne, decide_eq_false nz, Bool.and_false]

theorem loaded_tags (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (z : SkywalkNat.State) (v : BasisState) (q : Wire)
    (hq : q ∈ tagsP) :
    (prior j (actualMode (sbP (start j)) z) q).read v =
      if far (sbP (start j)) 15 z then hot (TrueMiddle.key j z) q else false := by
  rw [physicalTags j h0 h1 _ _ hq]
  by_cases f : far (sbP (start j)) 15 z
  · rw [if_pos f]
    obtain ⟨idx, _, on⟩ := modeKey (sbP (start j)) z f
    simp only [Expr.read, on, Bool.true_and, idx]
    rfl
  · simp [f, Expr.read, actualMode, farMode, ofFlags, enabled]

theorem controlsAt (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : Mode) :
    prior j k (e0P (start j) + 6) = crossing (ports j) k ∧
      prior j k 1597 = conj (crossing (ports j) k) (signExpr (ports j) k) := by
  have h := controlCert j h0 h1 k
  simp only [reads, LeaveSelector.controls, List.cons.injEq, and_true] at h
  exact ⟨h.2.1, h.2.2.2⟩

theorem dest_forward (gs : List Gate) : (GateMirror.forward gs).map LeaveReadoutFrame.destination = gs.map target := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [GateMirror.forward, List.map_cons] at ih ⊢
    rw [ih]; cases g <;> rfl

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 5b: proof-q1542 win/src/ParC1/Fam7.lean (K5) ----

/-! par-c1: generic leave families, batch 7: retiring the selector and the core of the leave (dadon's
`Leave{s}RetireActual`, `Leave{s}Core`). The core program is `middleOps ++ fix10 ++ fix11 ++ fix12 ++ lowSign`
(dadon's `work`, cuts 8..27). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror HighBankJoin SkywalkNat IntegerHigh Shadow HighBankSum LeaveSelector RecordedQuantum
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}RetireActual.paritySites` (= the history letters). -/
def paritySites (j : Fin 24) : List Wire := List.range' (start j + 16) 15

/-- Destinations of `prepare`, read off the op list. Not a selector simulation. -/
theorem prepare_dst : ∀ (j : Fin 24), 1 ≤ j.val → j.val ≤ 21 →
    ∀ t ∈ (prepare j).map Op.dst, (1559 ≤ t ∧ t ≤ 1597) ∨ t = (ports j).crossing ∨ t = (ports j).near := by
  decide +kernel

/-! The selector word after `prepare` reads only the history letters: an invariant of the symbolic
simulator, proved from the shape of the op list (no simulation, no decide over the modes). -/

/-- The hit and tag bits `1559..1575`. -/
abbrev InBits (q : Nat) : Prop := 1559 ≤ q ∧ q ≤ 1575
/-- The prepared word `1576..1596`. -/
abbrev InBand (q : Nat) : Prop := 1576 ≤ q ∧ q ≤ 1596
/-- The block's history letters. -/
abbrev IsHist (j : Fin 24) (q : Nat) : Prop := start j + 16 ≤ q ∧ q ≤ start j + 30

/-- Wires a band write may read. -/
abbrev ArgOK (j : Fin 24) (a : Nat) : Prop := InBits a ∨ IsHist j a ∨ InBand a

/-- An op does not write the history or the bit wires, and a band write reads only `ArgOK` wires. -/
abbrev OpGood (j : Fin 24) (o : Op) : Prop :=
  ¬ IsHist j o.dst ∧ ¬ InBits o.dst ∧ (InBand o.dst → ∀ a ∈ o.args, ArgOK j a)

structure SelClean (j : Fin 24) (k : Mode) (g : Sym) : Prop where
  bits : ∀ q : Nat, InBits q → g q = LeaveSelector.start (ports j) false k q
  hist : ∀ q : Nat, IsHist j q → g q = .wire q
  band : ∀ q : Nat, InBand q → ∀ r ∈ refs (g q), r ∈ paritySites j

theorem start_bit_refs (p : Ports) (k : Mode) (q : Nat) (h1 : 1559 ≤ q) (h2 : q ≤ 1575) :
    refs (LeaveSelector.start p false k q) = [] := by
  by_cases h : q = 1559
  · simp [LeaveSelector.start, h, refs]
  · by_cases h0 : q = 1560
    · simp [LeaveSelector.start, h, h0, refs]
    · have hr : 1561 ≤ q ∧ q ≤ 1575 := by omega
      simp [LeaveSelector.start, h, h0, hr, refs]

theorem refs_conj_sub {a b : Expr} {q : Wire} (hq : q ∈ refs (conj a b)) : q ∈ refs a ∨ q ∈ refs b := by
  rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    first | exact Or.inr hq | exact Or.inl hq | exact List.mem_append.mp hq

theorem refs_xor_sub {a b : Expr} {q : Wire} (hq : q ∈ refs (LeaveSelector.xor a b)) : q ∈ refs a ∨ q ∈ refs b := by
  unfold LeaveSelector.xor at hq
  split at hq
  · exact absurd hq List.not_mem_nil
  · rcases a with (_ | _) | w | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases b with (_ | _) | v | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      first | exact Or.inr hq | exact Or.inl hq | exact List.mem_append.mp hq

theorem refs_foldr (p : Ports) : ∀ xs : List Nat,
    ∀ q ∈ refs (xs.foldr (fun j rest => conj (.wire (p.g + j)) rest) (.bit true)), ∃ t ∈ xs, q = p.g + t := by
  intro xs
  induction xs with
  | nil => intro q hq; exact absurd hq List.not_mem_nil
  | cons j js ih =>
    intro q hq
    rcases refs_conj_sub hq with h | h
    · exact ⟨j, List.mem_cons_self, List.mem_singleton.mp h⟩
    · obtain ⟨t, ht, e⟩ := ih q h
      exact ⟨t, List.mem_cons_of_mem _ ht, e⟩

theorem arg_refs (j : Fin 24) (k : Mode) {g : Sym} (hc : SelClean j k g) {a : Nat} (ha : ArgOK j a) :
    ∀ r ∈ refs (g a), r ∈ paritySites j := by
  intro r hr
  rcases ha with hbit | hh | hin
  · rw [hc.bits a hbit, start_bit_refs _ _ _ hbit.1 hbit.2] at hr
    exact absurd hr List.not_mem_nil
  · rw [hc.hist a hh] at hr
    have e : r = a := List.mem_singleton.mp hr
    rw [e, paritySites, List.mem_range'_1]
    exact ⟨hh.1, Nat.lt_succ_of_le hh.2⟩
  · exact hc.band a hin r hr

theorem symbolic_clean (j : Fin 24) (k : Mode) (o : Op) (g : Sym) (hc : SelClean j k g) (hg : OpGood j o) :
    SelClean j k (symbolic o g) := by
  obtain ⟨nh, nb, hargs⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    have hne : ¬ q = o.dst := fun e => nb (e ▸ hq)
    rw [show symbolic o g q = g q from if_neg hne]
    exact hc.bits q hq
  · intro q hq
    have hne : ¬ q = o.dst := fun e => nh (e ▸ hq)
    rw [show symbolic o g q = g q from if_neg hne]
    exact hc.hist q hq
  · intro q hq r hr
    by_cases hd : q = o.dst
    · cases o with
      | xor a t =>
        have hx : symbolic (.xor a t) g q = LeaveSelector.xor (g q) (g a) := if_pos hd
        rw [hx] at hr
        rcases refs_xor_sub hr with hsub | hsub
        · exact hc.band q hq r hsub
        · exact arg_refs j k hc (hargs (hd ▸ hq) a (by simp [Op.args])) r hsub
      | mix a b t =>
        have hx : symbolic (.mix a b t) g q = LeaveSelector.xor (g q) (conj (g a) (g b)) := if_pos hd
        rw [hx] at hr
        rcases refs_xor_sub hr with hsub | hsub
        · exact hc.band q hq r hsub
        · rcases refs_conj_sub hsub with h2 | h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) a (by simp [Op.args])) r h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) b (by simp [Op.args])) r h2
      | save a b t =>
        have hx : symbolic (.save a b t) g q = LeaveSelector.xor (g q) (conj (g a) (g b)) := if_pos hd
        rw [hx] at hr
        rcases refs_xor_sub hr with hsub | hsub
        · exact hc.band q hq r hsub
        · rcases refs_conj_sub hsub with h2 | h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) a (by simp [Op.args])) r h2
          · exact arg_refs j k hc (hargs (hd ▸ hq) b (by simp [Op.args])) r h2
    · rw [show symbolic o g q = g q from if_neg hd] at hr
      exact hc.band q hq r hr

theorem sim_selClean (j : Fin 24) (k : Mode) : ∀ (os : List Op) (g : Sym),
    SelClean j k g → (∀ o ∈ os, OpGood j o) → SelClean j k (sim os g) := by
  intro os
  induction os with
  | nil => intro g hc _; exact hc
  | cons o os ih =>
    intro g hc ho
    exact ih (symbolic o g) (symbolic_clean j k o g hc (ho o List.mem_cons_self))
      (fun o' h => ho o' (List.mem_cons_of_mem _ h))

/-- Every op of `prepare` keeps the selector-symbol invariant. Read off the op list, not a simulation. -/
theorem prepare_good : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 → ∀ o ∈ prepare j, OpGood j o := by
  decide +kernel

/-- `fix11 ++ fix12 ++ lowSign` = dadon's `fullPostfix false` (the retired word, the hits, the flags). -/
theorem postfix_parts : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    GateMirror.forward (leaveFix11 (start j) (sbP (start j)) ++ leaveFix12 (start j) (sbP (start j)) ++ lowSign (start j)) =
      (retire j).map Op.exit ++ (HighBankFirstHit.dropAll 1560 (swaps j) LeaveSelector.tags 0 15 ++
        (flagOps (e0P (start j) + 3) (e0P (start j) + 4) true).reverse.map Op.exit) := by
  decide +kernel

/-! Core (dadon's `Leave{s}Core.result`). -/

def workOps (s : Nat) : List Gate :=
  middleOps s ++ leaveFix10 s (sbP s) ++ (leaveFix11 s (sbP s) ++ leaveFix12 s (sbP s) ++ lowSign s)

/-! Routed (dadon's `Leave{s}Routed.result`): `body` = `fullPrefix ++ work` (cuts 5..27). -/

theorem prefix_dest : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 → ∀ q ∈ (GateMirror.forward (fullPrefix j)).map LeaveReadoutFrame.destination,
    (1559 ≤ q ∧ q ≤ 1597) ∨ q = e0P (start j) + 6 ∨ q = e0P (start j) + 7 := by
  decide +kernel

theorem prefix_keep (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (q : Nat)
    (hq : ¬ ((1559 ≤ q ∧ q ≤ 1597) ∨ q = e0P (start j) + 6 ∨ q = e0P (start j) + 7)) (s : State) (tape : List Bool) :
    (run (GateMirror.forward (fullPrefix j)) tape s).basis q = s.basis q :=
  LeaveReadoutFrame.preserved _ s tape q (fun h => hq (prefix_dest j h0 h1 q h))

def bodyOps (j : Fin 24) : List Gate := fullPrefix j ++ workOps (start j)

/-! Restored / RoutedRestore (dadon's `Leave{s}Restored`, `Leave{s}RoutedRestore`). -/

theorem smallM_length (j : Fin 24) : (smallM j).length = lowsP (start j) := by simp [smallM]

/-- dadon's `Leave{s}Restored.result`. -/
theorem restored_result (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (z : SkywalkNat.State) (sg : Bool) (s : State)
    (m : List Bool) (small : min z.u z.v < 2^(sbP (start j))) (clean : ∀ q ∈ smallC j, s.basis q = false)
    (cleared : regValue (smallM j) s.basis = 0)
    (input : let r := step^[15] (reduced (sbP (start j)) 15 z)
      let F := step^[15] z
      let e := (PortalValues.negative sg r.u).toNat
      s.basis 1556 = decide (2^(sbP (start j)) ≤ r.u - e) ∧
        (s.basis 1558).toNat = LeaveCompanion.upperBorrow (2^(sbP (start j))) r.u r.v e ∧
        regValue (smallA j) s.basis = ((F.u+F.v)/2^(sbP (start j) + 1)) % 2^(lowsP (start j))) :
    let F := step^[15] z
    let e := (PortalValues.negative sg F.u).toNat
    let out := run (Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558) m s
    out.phase = s.phase ∧ (∀ q, q ∉ smallM j → out.basis q = s.basis q) ∧
      regValue (smallM j) out.basis = ((F.u - e)/2^(sbP (start j) + 1)) % 2^(lowsP (start j)) := by
  have hardware := restore_run j h0 h1 s m clean cleared
  refine ⟨hardware.1, hardware.2.1, hardware.2.2.trans ?_⟩
  dsimp only at input ⊢
  have math := LeaveRestoreTruth.restored (sbP (start j)) (lowsP (start j)) z small sg
  have sign := (LeaveRestoreTruth.truth (sbP (start j)) z small sg).2.2.2
  rw [smallM_length, copyValue, input.1, input.2.1, input.2.2, sign]
  simpa only [decide_eq_true_eq] using math


/-! Target footprint of the body (for the families that read wires the body never writes). -/

/-- Targets of the work part of the body (adjust, barrel, join, the fixed tail): the A word, the B bank, and the
scratch below the anchored block `e0..e0+9` or the pool above it (never `e0+3 .. e0+9`, never the history cells). -/
def workT (j : Fin 24) (t : Nat) : Prop :=
  (a0P (start j) ≤ t ∧ t ≤ a0P (start j) + 17) ∨ (b0P (start j) + 18 ≤ t ∧ t ≤ 1043) ∨
    (1559 ≤ t ∧ (t ≤ e0P (start j) + 2 ∨ (e0P (start j) + 10 ≤ t ∧ t ≤ 1606 + wpP (start j))))
/-- Targets of the body: the work part plus the selector's (`fullPrefix`: `1559..1597`, `e0+6`, `e0+7`). -/
def midT (j : Fin 24) (t : Nat) : Prop := workT j t ∨ t = e0P (start j) + 6 ∨ t = e0P (start j) + 7

/-- The fixed tail of the work part writes only scratch below the anchored block (one decide, fixed segments). -/
theorem tail_dest : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    (leaveFix10 (start j) (sbP (start j)) ++ (leaveFix11 (start j) (sbP (start j)) ++ leaveFix12 (start j) (sbP (start j)) ++
      lowSign (start j))).all (fun g => decide (1559 ≤ target g) && decide (target g ≤ e0P (start j) + 2)) = true := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ==== end PrizeTail10d9efffc.a ====

-- ==== part Window2 ====
-- Window2 = PrizeTail10d9efffc.b ++ PrizeTail752d1574c ++ PrizeTail2024ba497
-- ==== begin PrizeTail10d9efffc.b ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Routed
open Arithmetic Partial IntegerHigh LeaveSelector Leave240Selector Leave240RetireActual Leave240Barrel Leave240High Leave240Word Leave240Join
open LeaveReadoutFrame Leave240OutputPorts HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave240Routed

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Front
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

end ECDSAAdd.Entrant.StairPacket.Leave255Front

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Mirror
open GateMirror
set_option maxRecDepth 45000
set_option maxHeartbeats 9000000
end ECDSAAdd.Entrant.StairPacket.Leave255Mirror

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Routed
open Arithmetic Partial IntegerHigh LeaveSelector Leave255Selector Leave255RetireActual Leave255Barrel Leave255High Leave255Word Leave255Join
open LeaveReadoutFrame Leave255OutputPorts HighBankBarrel
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave255Routed

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
theorem native_carry (j:Fin 24) (z:SkywalkRails.State) (s:State) (ready:onRails j 15 z s.basis) (q:Wire)
    (mem:q∈((ports (shape j) 15).carry.map (windowNet j))) : s.basis q=false:=by
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp mem
  exact (regValue_zero _ _).mp ready.2.2.2.1 _ hw
set_option maxHeartbeats 2000000
set_option maxRecDepth 18000
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic IntegerPacket MappedCompressed SkywalkRails StairArchiveRaw StairArchiveTrace ArchiveBoundary270 ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed SkywalkRails
set_option maxHeartbeats 2300000
set_option maxRecDepth 18000
attribute [local irreducible] run
theorem fixed_step (lo i:Nat) (hlo:lo ≤ i) (hi:i<512) {a b:State} (same:Coherent lo a b) (m:List Bool) :
    Coherent lo (run (W.compactSkywalkTick base i) m a) (run (W.compactSkywalkTick base i) m b):=by
  let P:=W.compactSkywalkTick base i
  have sub:=W.compactSkywalkTick_support base i hi base_pool_nodup
  have eq:=run_measured_locality P (wires P) (Finset.Subset.refl _) a b m same.1 (fun q mem=>
    same.2 q (fun old=>away hi (earlier_mono hlo old) (List.mem_toFinset.mp (sub mem))))
  refine ⟨eq.1,?_⟩
  intro q fresh
  by_cases used:q∈wires P
  · exact eq.2 q used
  · exact (run_preserves_outside _ _ _ _ used).trans ((same.2 _ fresh).trans (run_preserves_outside _ _ _ _ used).symm)
theorem fixed_span (lo i n:Nat) (hlo:lo ≤ i) (lim:i+n≤512) (a b:State) (m:List Bool) (same:Coherent lo a b) :
    Coherent lo (run (span i n) m a) (run (span i n) m b):=by
  induction n generalizing i a b m with
  | zero=>simpa [span,run] using same
  | succ n ih=>
    simp only [span,run_append,run_take]
    exact ih (i+1) (by omega) (by omega) _ _ _ (fixed_step lo i hlo (by omega) same m)
theorem trace_sites (i n x p:Nat) (lim:i+n≤512) (good:Bounds x p) (raw:State) (m:List Bool) (domain:Domain i x p raw)
    (r:Nat) (first:i≤r) (last:r < i+n) :
    let out:=run (span i n) m raw
    let cell:=SkywalkTrace.code (canonical r x p)
    out.basis (base r)=cell.1 ∧ out.basis (base (1028+r))=cell.2:=by
  obtain ⟨ref,match',stage⟩:=domain
  have final:=full_span i n x p lim good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime ref m stage
  have bits:=(W.compactSkywalkStage_fields_iff base _ (i+n) lim base_pool_nodup _).mp final
  have hist:=bits.2.2.2.1 r last
  have link:=fixed_span i i n (Nat.le_refl _) lim raw ref m match'
  have unmarked:∀q∈[base r,base (1028+r)],¬Earlier i q:=by
    intro q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> rintro ⟨t,ht,h|h⟩ <;> simp only [base,Wire] at h <;> omega
  exact ⟨(link.2 _ (unmarked _ (by simp))).trans hist.1,(link.2 _ (unmarked _ (by simp))).trans hist.2⟩

end ECDSAAdd.Entrant.StairPacket.WideReference

end



section

namespace ECDSAAdd.Entrant.StairPacket.Leave225EntryAction
open Arithmetic Partial LeaveSelector Leave225Selector Leave225Close Leave225InputScan Leave225Front LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225EntryAction

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FrontReady
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open Leave225Front LeaveSelector Leave225Selector

end ECDSAAdd.Entrant.StairPacket.Leave225FrontReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RoutedRestore
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225OutputPorts LeaveReadoutFrame
open Leave225Routed SkywalkNat
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225RoutedRestore

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240EntryAction
open Arithmetic Partial LeaveSelector Leave240Selector Leave240Close Leave240InputScan Leave240Front LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240EntryAction

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FrontReady
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open Leave240Front LeaveSelector Leave240Selector

end ECDSAAdd.Entrant.StairPacket.Leave240FrontReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RoutedRestore
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240OutputPorts LeaveReadoutFrame
open Leave240Routed SkywalkNat
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240RoutedRestore

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255EntryAction
open Arithmetic Partial LeaveSelector Leave255Selector Leave255Close Leave255InputScan Leave255Front LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255EntryAction

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FrontReady
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255InputScan LeaveReadoutFrame
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

open Leave255Front LeaveSelector Leave255Selector

end ECDSAAdd.Entrant.StairPacket.Leave255FrontReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RoutedRestore
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255OutputPorts LeaveReadoutFrame
open Leave255Routed SkywalkNat
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255RoutedRestore

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
attribute [local irreducible] run

theorem span_phase (i n x p:Nat) (bounds:i+n≤512) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    (run (span i n) m s).phase=s.phase := by
  induction n generalizing i s m with
  | zero => simp [span,run]
  | succ n ih =>
    have first:=W.compactSkywalkStageStep base base_pool_nodup x p i good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime (by omega) s m stage
    rw [span,run_append,run_take]
    exact (ih (i+1) (by omega) _ _ first.2).trans first.1

theorem origin_phase (i x p:Nat) (bounds:i+15≤512) (good:Bounds x p) (raw history:State)
    (dom:Domain i x p raw) : (origin i raw history).phase=raw.phase := by
  obtain ⟨ref,same,stage⟩:=dom
  have match':=fixed_span i i 15 (Nat.le_refl _) bounds raw ref [] same
  exact match'.1.trans ((span_phase _ _ _ _ bounds good ref [] stage).trans same.1.symm)
theorem endRaw_phase (i x p:Nat) (bounds:i+15≤512) (good:Bounds x p) (raw history:State)
    (dom:Domain i x p raw) : (endRaw i raw history).phase=raw.phase :=
  origin_phase i x p bounds good raw history dom
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
namespace NativePack225
end NativePack225
namespace NativePack255
end NativePack255

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
def endSlice (d:Bool) := EndTick.physP ++ (program d ++ Partial.archiveLoad270 d)
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed IntegerPacket SkywalkRails StairArchiveRaw
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem read_trace (n r:Nat) (h:r<n) (s:SkywalkRails.State) :
    read (SkywalkTrace.trace n s) r=SkywalkTrace.code (SkywalkTrace.next^[r] s):=by
  induction n generalizing r s with
  | zero=>omega
  | succ n ih=>
    cases r with
    | zero=>rfl
    | succ r=>
      simpa only [SkywalkTrace.trace,StairArchiveRaw.read,List.getElem?_cons_succ,Function.iterate_succ_apply] using ih r (by omega) (SkywalkTrace.next s)
def Geometry (i:Nat) (j:Fin 24) := ∀r:Fin 15,
  let q:=windowNet j (ports (shape j) r).a0
  let w:=windowNet j (ports (shape j) r).history
  q∉sites i ∧ w∉sites i ∧ OB5.sig (i+14) q=base (i+r.val) ∧ OB5.sig (i+14) w=base (1028+(i+r.val))
/-- Every block's narrow ports avoid its physical old cells and land on its own stock cells. -/
theorem places (j:Fin 24) : Geometry (StairPacket.start j) j:=by
  have hj:=j.isLt
  have lo:15≤StairPacket.start j:=by change 15≤75+15*(j:Nat);omega
  have lim:StairPacket.start j+14≤511:=by change 75+15*(j:Nat)+14≤511;omega
  have w:=old_window lo
  have back (q:Wire):OB5.sig (StairPacket.start j+14) (windowNet j q)=q:=OB5.sig_invol _ lim q
  unfold Geometry
  intro r
  have hr:=r.isLt
  dsimp only
  refine ⟨?_,?_,(back _).trans rfl,(back _).trans ?_⟩
  · rw [mem_sites lim,back]
    intro hit
    obtain ⟨t,a,b,h|h⟩:=old_cell hit <;> change StairPacket.start j+r.val+16=_ at h <;> omega
  · rw [mem_sites lim,back]
    intro hit
    obtain ⟨t,a,b,h|h⟩:=old_cell hit <;> change StairPacket.start j+r.val+16+1028=_ at h <;> omega
  · change StairPacket.start j+r.val+16+1028=1028+(StairPacket.start j+r.val)+16
    omega
theorem reference_cells (i:Nat) (j:Fin 24) (x p:Nat) (lim:i+15≤512) (place:Geometry i j) (good:Bounds x p)
    (raw history:State) (r:Fin 15) (domain:Domain i x p raw):
    cell (shape j) r (mappedBasis j (origin i raw history).basis)=SkywalkTrace.code (canonical (i+r.val) x p):=by
  have hist:=trace_sites i 15 x p lim good raw [] domain (i+r.val) (by omega) (by have hr:=r.isLt;omega)
  obtain ⟨noA,noB,a,b⟩:=place r
  unfold cell mappedBasis
  rw [outside i raw history _ noA,outside i raw history _ noB,a,b]
  exact Prod.ext hist.1 hist.2
theorem recorded_equal (i:Nat) (j:Fin 24) (x p:Nat) (lim:i+15≤512) (place:Geometry i j) (good:Bounds x p)
    (raw history:State) (domain:Domain i x p raw) (G S:Bool)
    (input:InputAt i (encode G S (unsigned i x p).u (unsigned i x p).v) raw)
    (trace:physicalCells j history=SkywalkTrace.trace 15 (encode G S (unsigned i x p).u (unsigned i x p).v)) (r:Fin 15) :
    cell (shape j) r (mappedBasis j history.basis)=cell (shape j) r (mappedBasis j (origin i raw history).basis):=by
  have eq:=unique_input input (fixed_input _ _ _ (by omega) good raw domain)
  rw [eq] at trace
  have seen:=congrArg (fun xs=>read xs r) trace
  change read (readCells (shape j) 0 15 (mappedBasis j history.basis)) r=read (SkywalkTrace.trace 15 (canonical i x p)) r at seen
  rw [read_cells _ _ _ _ _ r.isLt,Nat.zero_add,read_trace _ _ r.isLt] at seen
  rw [reference_cells i j x p lim place good raw history r domain]
  have reorder:canonical (i+r.val) x p=SkywalkTrace.next^[r.val] (canonical i x p):=by
    rw [Nat.add_comm];exact Function.iterate_add_apply _ _ _ _
  exact seen.trans (congrArg _ reorder.symm)

end ECDSAAdd.Entrant.StairPacket.WideReference

end


section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
def RawRead (k q:Nat) :=
  let n:=W.compactSkywalkTickPreWidth k
  (k+16≤q ∧ q≤k+16+n) ∨ (786≤q ∧ q<786+n) ∨ q=1044+k ∨ q=base (skywalkPoolPreviousId k) ∨
  (1556≤q ∧ q+1<1556+n)
instance (k q:Nat) : Decidable (RawRead k q):=by unfold RawRead;infer_instance
theorem member_block (a n q:Nat) (m:q∈wireBlock base a n) : a+16≤q ∧ q<a+n+16:=by
  obtain ⟨r,hit,rfl⟩:=List.mem_map.mp m
  have b:=List.mem_range'_1.mp hit
  change a+16≤r+16 ∧ r+16<a+n+16;omega
theorem layout_choices (L:SkywalkIntegerLayout) (q:Wire) (h:q∈L.wires) :
    q=L.previous ∨ q=L.ext ∨ q=L.history ∨ q∈L.a ∨ q∈L.b ∨ q∈L.carry := by
  simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.a,SkywalkIntegerLayout.b,List.mem_cons,List.mem_append] at h ⊢
  tauto
theorem contained (k q:Nat) (lim:k<512) (used:q∈wires (W.compactSkywalkTick base k)) : RawRead k q:=by
  have h:=List.mem_toFinset.mp (W.compactSkywalkTick_support base k lim base_pool_nodup used)
  have cases':=layout_choices _ q h
  rw [W.compactSkywalkTick_a base k lim,W.compactSkywalkTick_b base k lim] at cases'
  let n:=W.compactSkywalkTickPreWidth k
  have positive:3≤n:=(W.compactSkywalkTick_width_bounds k lim).1
  change (k+16≤q ∧ q≤k+16+n) ∨ (786≤q ∧ q<786+n) ∨ q=1044+k ∨ q=base (skywalkPoolPreviousId k) ∨ (1556≤q ∧ q+1<1556+n)
  rcases cases' with prev|ext|hist|ha|hb|hc
  · exact Or.inr (Or.inr (Or.inr (Or.inl prev)))
  · apply Or.inl;change q=k+n+16 at ext;omega
  · apply Or.inr <| Or.inr <| Or.inl ?_;change q=1028+k+16 at hist;omega
  · apply Or.inl;have lim:=member_block k n q ha;omega
  · apply Or.inr <| Or.inl ?_;have lim:=member_block 770 n q hb;omega
  · apply Or.inr <| Or.inr <| Or.inr <| Or.inr ?_;have lim:=member_block 1540 (n-1) q hc;omega
theorem span_unchanged (i n q:Nat) (bound:i+n≤512) (clear:∀a<n,¬RawRead (i+a) q) (s:State) (m:List Bool) :
    (run (span i n) m s).basis q=s.basis q:=by
  induction n generalizing i s m with
  | zero=>simp [span,run]
  | succ n ih=>
    simp only [span,run_append,run_take]
    have tail:∀a<n,¬RawRead (i+1+a) q:=by intro a h;simpa only [Nat.add_assoc,Nat.add_comm 1 a] using clear (a+1) (by omega)
    rw [ih (i+1) (by omega) tail]
    exact run_preserves_outside _ _ _ _ (fun used=>clear 0 (by omega) (by simpa only [Nat.add_zero] using contained i q (by omega) used))

end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270 ParkEndpoint Portal270Flag StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
def lastWindow (d:Bool) := Partial.park270 ++ (Partial.portal270Inv ++ endSlice d)
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FrontPrepare
open Arithmetic Partial RecordedQuantum PortalValues LeaveCompanion LeaveCompanion225
open Leave225Front Leave225FrontReady LeaveSelector Leave225Selector Leave225Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225FrontPrepare

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225FullArithmetic

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RecordedParity
open Arithmetic IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225RecordedParity

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FrontPrepare
open Arithmetic Partial RecordedQuantum PortalValues LeaveCompanion LeaveCompanion240
open Leave240Front Leave240FrontReady LeaveSelector Leave240Selector Leave240Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240FrontPrepare

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240FullArithmetic

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RecordedParity
open Arithmetic IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240RecordedParity

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FrontPrepare
open Arithmetic Partial RecordedQuantum PortalValues LeaveCompanion LeaveCompanion255
open Leave255Front Leave255FrontReady LeaveSelector Leave255Selector Leave255Hit
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255FrontPrepare

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FullArithmetic
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255FullArithmetic

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RecordedParity
open Arithmetic IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255RecordedParity

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket ArchivePortAction
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount
theorem after_encoded (j:Fin 24) (P:Program) (outPorts:Ports) (d:Bool) (row:Nat) (src:State) (m:List Bool)
    (final:Frame outPorts (code d) row (run P (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m src)))
    (i:Fin 157) (hi:16 ≤ i.val) (q:Wire) (slot:outPorts i=q) (free:¬MayTouch j (windowNet j q)) :
    (run (body j P) m src).basis q=false:=by
  simp only [body,run_append,run_take]
  apply (route_outside j 1 14 (by decide) q (named_range j 1 14 q (by decide) free) _ _).trans
  rw [←slot,final,archive_blank _ _ hi,Nat.zero_testBit]
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run measurementCount
theorem from_append {P Q:Program} {s:State} {t:List Bool} {prop:State→Prop}
    (after:prop (run Q (t.drop (measurementCount P)) (run P t s))) : prop (run (P++Q) t s):=by
  rwa [run_append,run_take]
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Join Leave225Word

end ECDSAAdd.Entrant.StairPacket.Leave225CoreCheckpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FlagScratch
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Join
end ECDSAAdd.Entrant.StairPacket.Leave225FlagScratch

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion225 Leave225InputScan Leave225Front
open LeaveReadoutFrame Leave225MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave225MaskCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225RecordedEvents
open Arithmetic IntegerPacket IntegerHigh SkywalkRails LeaveSelector
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225RecordedEvents

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Join Leave240Word

end ECDSAAdd.Entrant.StairPacket.Leave240CoreCheckpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FlagScratch
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Join
end ECDSAAdd.Entrant.StairPacket.Leave240FlagScratch

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion240 Leave240InputScan Leave240Front
open LeaveReadoutFrame Leave240MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave240MaskCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240RecordedEvents
open Arithmetic IntegerPacket IntegerHigh SkywalkRails LeaveSelector
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240RecordedEvents

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CoreCheckpoint
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Join Leave255Word

end ECDSAAdd.Entrant.StairPacket.Leave255CoreCheckpoint

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FlagScratch
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Join
end ECDSAAdd.Entrant.StairPacket.Leave255FlagScratch

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255MaskCut
open Arithmetic Partial PortalValues LeaveCompanion LeaveCompanion255 Leave255InputScan Leave255Front
open LeaveReadoutFrame Leave255MaskThrough
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave255MaskCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255RecordedEvents
open Arithmetic IntegerPacket IntegerHigh SkywalkRails LeaveSelector
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255RecordedEvents

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
theorem outside_between {i q:Nat} (lo:i+16<q) (hi:q<1044) : ¬ Earlier i q:=by
  rintro ⟨t,ht,h|h⟩
  · change q=t+16 at h;omega
  · change q=1028+t+16 at h;omega
theorem outside_above {i q:Nat} (hi:1044+i≤q) : ¬ Earlier i q:=by
  rintro ⟨t,ht,h|h⟩
  · change q=t+16 at h;omega
  · change q=1028+t+16 at h;omega
/-- window390: the released wires of the stock B rail (`bTop(i)+1 .. 1043`) are clean in every domain state. The
archive scratch beyond the stock carry is hosted there (`Partial.scratchS`, loaders at 375 and 390). -/
theorem released_clear {i x p:Nat} (lo:257 ≤ i) (hi:i ≤ 509) {s:State} (dom:Domain i x p s) (q:Nat)
    (ql:1299-i≤q) (qh:q≤1043) : s.basis q=false:=by
  obtain ⟨ref,stage,link⟩:=leaves_reference i x p (by omega) true s dom
  exact (link.2 _ (outside_between (by omega) (by omega))).trans
    (ParkEndpoint.clear_above i lo hi true x p ref stage q ql qh)
theorem future_history {i j x p:Nat} (h:i≤j) (hj:j<512) {s:State} (dom:Domain i x p s) :
    s.basis (base (1028+j))=false:=by
  obtain ⟨ref,stage,link⟩:=leaves_reference i x p (by omega) true s dom
  have lim:1044+i≤base (1028+j):=by change 1044+i≤1028+j+16;omega
  exact (link.2 _ (outside_above lim)).trans (stock_history true x p i ref stage j h hj)
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
/-- The carry and mirror bank `[1556,1812]` is clean in every domain state. -/
theorem domain_carry {i x p:Nat} (hi:i≤512) {raw:State} (dom:Domain i x p raw) (q:Nat) (low:1556≤q) (high:q≤1812) :
    raw.basis q=false:=by
  obtain ⟨ref,same,stage⟩:=dom
  have fields:=(W.compactSkywalkStage_fields_iff base _ i hi base_pool_nodup _).mp stage
  apply (same.2 q (outside_above (by omega))).trans
  apply (regValue_zero _ _).mp fields.2.2.2.2.2.1
  exact List.mem_map.mpr ⟨q-16,List.mem_range'_1.mpr (by omega),by change (q-16)+16=q;omega⟩
/-- Block `j`'s history ports, pulled back to the frame before the block, are clean: before tick 257 they are the
stock history cells, from 257 on the placement sends them into the clean carry top `2069-t`. -/
theorem pulled_history {i x p:Nat} (j:Fin 24) (hs:i=StairPacket.start j) {raw:State} (dom:Domain i x p raw) :
    ∀r:Fin 15,raw.basis (OB5.sig (i-1) (windowNet j (IntegerPacket.ports (shape j) r).history))=false:=by
  intro r
  subst hs
  have hj:=j.isLt
  have hr:=r.isLt
  have st:StairPacket.start j=75+15*(j:Nat):=rfl
  have w:OB5.sig (StairPacket.start j-1) (windowNet j (IntegerPacket.ports (shape j) r).history)=
      (if StairPacket.start j+r.val<257 then 1044+(StairPacket.start j+r.val) else 2069-(StairPacket.start j+r.val):Nat):=by
    change OB5.sigNat (StairPacket.start j-1) (OB5.sigNat (StairPacket.start j+14) (StairPacket.start j+r.val+16+1028))=_
    unfold OB5.sigNat
    split_ifs <;> omega
  rw [w]
  split_ifs
  · have old:=future_history (j:=StairPacket.start j+r.val) (Nat.le_add_right _ _) (by omega) dom
    change raw.basis (1028+(StairPacket.start j+r.val)+16)=false at old
    rwa [show 1028+(StairPacket.start j+r.val)+16=1044+(StairPacket.start j+r.val) by omega] at old
  · exact domain_carry (by omega) dom _ (by omega) (by omega)
end ECDSAAdd.Entrant.StairPacket.WideReference


end

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open Arithmetic MappedCompressed IntegerPacket
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
attribute [local irreducible] run unrouted renameProgram portal225 enter225 enter240 enter255 leave225 leave240 leave255
  portal225Inv enter225Inv enter240Inv enter255Inv leave225Inv leave240Inv leave255Inv park270 park270Inv portal270 portal270Inv
  archiveLoad240 archiveLoad255 archiveLoad270 archiveRestore240 archiveRestore255 archiveRestore270
end ECDSAAdd.Entrant.StairPacket.Partial

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
attribute [local irreducible] run measurementCount
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225BeforeStore

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240BeforeStore

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BeforeStore
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255BeforeStore

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270 ParkEndpoint Portal270Flag StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction StairArchiveTrace StairArchiveRaw CodecBitSliceVerify
attribute [local irreducible] onRails run measurementCount
def RowTruth (past:SkywalkNat.State) (g sg:Bool) (row:Nat) : Prop :=
  ∀q:Fin 20,(rawCol q).testBit row=letterBit (read ((SkywalkTrace.trace 15 (encode g sg past.u past.v)).drop 5) (q.val/2)) q

theorem row_truth (j:Fin 24) (ps:Ports) (chron:∀i:Fin 20,ps ⟨i,by omega⟩=nativeRawPort j i)
    (row:Nat) (past:SkywalkNat.State) (g sg:Bool) (before out:State)
    (rec:physicalCells j before=SkywalkTrace.trace 15 (encode g sg past.u past.v))
    (bk:∀i:Fin 23,out.basis (ps ⟨i,by omega⟩)=before.basis (ps ⟨i,by omega⟩))
    (frame:Frame ps raw row out):RowTruth past g sg row:=by
  intro q
  let i:Fin 157:=⟨q,by omega⟩
  have eq:(rawCol q).testBit row=out.basis (ps i):=
    (congrArg (fun n:Nat=>n.testBit row) (io true true i).1).trans (frame i).symm
  have h:=native_raw_read j before q q.isLt
  change before.basis (nativeRawPort j q)=letterBit (read ((physicalCells j before).drop 5) (q.val/2)) q at h
  rw [rec] at h
  exact eq.trans ((bk ⟨q,by omega⟩).trans ((congrArg before.basis (chron q)).trans h))
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255
end ECDSAAdd.Entrant.StairPacket

end

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify EnterProof PortalValues SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! NativeJ, part 3 (Tail10d9): what block `j`'s window keeps (`2 ≤ j ≤ 19`). -/

end ECDSAAdd.Entrant.StairPacket.NativeJ

end

-- ==== w4: build-w4b B2-b cleared_holes (b2b/Window_ClearedHoles.lean) ====
-- BEGIN build-w4b NativeJ.cleared_holes (B2-b part 4)
-- Window (w4r): after the NativeJ section holding `real_receipt` (par-c2, Window ~32538), before its `end`.
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount onRails

end ECDSAAdd.Entrant.StairPacket.NativeJ

end
-- END build-w4b NativeJ.cleared_holes
-- ==== w4: end cleared_holes ====

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! The leave of block `j` writes only inside par-c1's box (dadon's `NativePack{s}.writes/exterior`, which
decided 37 leave parts per block); generic from `Partial.leaveOps_box`. -/
end ECDSAAdd.Entrant.StairPacket.NativeJ


section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed IntegerPacket Partial
set_option maxRecDepth 16000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
/-- `OB5.sig i` fixes `q` when `q` is outside both moved intervals. Not an identity on `[1301,1556]`. -/
theorem sig_fixed {i : Nat} {q : Wire}
    (band : ¬(1301 ≤ (q : Nat) ∧ (q : Nat) ≤ 1044 + i))
    (mirror : ¬(2069 ≤ (q : Nat) + i ∧ (q : Nat) ≤ 1812)) : OB5.sig i q = q := by
  rw [OB5.sig_nat]
  unfold OB5.sigNat
  rw [if_neg]
  · intro h
    rcases h with h | h
    · exact band (by simpa only [Wire] using h)
    · exact mirror (by simpa only [Wire] using h)
/-- A-rail wires at or below 529 are never moved (`q ≤ 529`, tick `≤ start+14`). -/
theorem sig_rail (j : Fin 24) (q : Wire) (top : (q : Nat) ≤ 529) (i : Nat) (hi : i ≤ start j + 14) :
    OB5.sig i q = q := by
  have f := EnterJ.frame j
  refine sig_fixed ?_ ?_
  · intro h; simp only [Wire] at *; omega
  · intro h; simp only [Wire] at *; omega
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
theorem incoming_free_A (i x p:Nat) (lim:i≤512) (raw:State) (domain:Domain i x p raw)
    (q:Nat) (lower:i+16<q) (upper:q<1044)
    (free:q∈(W.compactSkywalkSignPoolA base i).released ∨ (i+274≤q ∧ q<786)) :
    raw.basis q=false:=by
  obtain ⟨ref,match',stage⟩:=domain
  apply (match'.2 _ (outside_between lower upper)).trans
  rcases free with sign|later
  · exact stage.2.1 q sign
  · let j:=q-274
    have hj:i≤j ∧ j<512:=by dsimp [j];omega
    have eq:q=base (j+258):=by change q=j+258+16;dsimp [j];omega
    rw [eq]
    exact ((W.compactSkywalkStage_fields_iff base _ i lim base_pool_nodup _).mp stage).2.2.2.2.1 j hj.1 hj.2 |>.1
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.tailTemps/tail_clean`, generic: after the window head, the wires above the anchored block
(`e0+9 ..`) are clean. From `s ≥ 270` the wires `2055-s..1812` hold the block's own history cells (windowNet
mirror), so the tail stops below them (dadon's 255: `1712..1799`). Late blocks' archive scratch reaches into the
tail; those wires are clean as unused code ports (`after_encoded`). -/
end ECDSAAdd.Entrant.StairPacket.NativeJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.upperA/upper_clear`, generic: the A rail above the block's own ticks (`s+h+50 .. top`,
`top = min (s+30+R(s+14)) 529`, par-a's exact span top) is clean after the window head: the parked bank's A side is zeroed by the cut, the
wires above the bank (`s+R+16 ..`) are free in the stock domain. -/
end ECDSAAdd.Entrant.StairPacket.NativeJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction CodecBitSliceVerify EnterProof PortalValues SkywalkRails Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! First-form window head (par-c2): what the first block's window keeps (pack only, no archive). -/
end ECDSAAdd.Entrant.StairPacket.NativeFirstJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! First-form tail and upper rail (par-c2): as `NativeJ.tail_clean/upper_clear` without archive and pending
(the first block's `e0+6..8` are spare, so its tail starts at `e0+6`, dadon's 225: `1724..1812`). -/
end ECDSAAdd.Entrant.StairPacket.NativeFirstJ

end


section

namespace ECDSAAdd.Entrant.StairPacket.Leave225StoreCoordinates
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave225StoreCoordinates

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240StoreCoordinates
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave240StoreCoordinates

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255StoreCoordinates
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave255StoreCoordinates

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225StoreMapped
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225StoreMapped

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240StoreMapped
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240StoreMapped

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255StoreMapped
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255StoreMapped

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open ArchiveBoundary270 ParkEndpoint Portal270Flag Secp256k1 SkywalkRails StairArchiveTrace
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Partial WideReference CodecBitSliceVerify
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave225FullArithmetic Leave225Word Leave225Join Leave225Close
end ECDSAAdd.Entrant.StairPacket.Leave225HighZero

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225PostReady
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave225PostReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave240FullArithmetic Leave240Word Leave240Join Leave240Close
end ECDSAAdd.Entrant.StairPacket.Leave240HighZero

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240PostReady
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave240PostReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255HighZero
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

open Leave255FullArithmetic Leave255Word Leave255Join Leave255Close
end ECDSAAdd.Entrant.StairPacket.Leave255HighZero

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255PostReady
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

end ECDSAAdd.Entrant.StairPacket.Leave255PostReady

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
namespace NativePack225
end NativePack225
namespace NativePack240
end NativePack240
namespace NativePack255
end NativePack255

end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave225Roundtrip

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Whole
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave225Whole

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave240Roundtrip

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Whole
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave240Whole

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Roundtrip
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave255Roundtrip

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Whole
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

end ECDSAAdd.Entrant.StairPacket.Leave255Whole

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
theorem full_carry (i n x p:Nat) (lim:i+n≤512) (good:Bounds x p) (raw:State) (domain:Domain i x p raw)
    (m:List Bool) (q:Nat) (low:1556≤q) (high:q≤1812) :
    (run (span i n) m raw).basis q=false:=by
  obtain ⟨ref,match',stage⟩:=domain
  have finish:=full_span i n x p lim good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime ref m stage
  have fields:=(W.compactSkywalkStage_fields_iff base _ (i+n) lim base_pool_nodup _).mp finish
  have outside:=outside_above (q:=q) (i:=i) (by omega)
  have link:=fixed_span i i n (Nat.le_refl _) lim raw ref m match'
  apply (link.2 q outside).trans
  apply (regValue_zero _ _).mp fields.2.2.2.2.2.1
  exact List.mem_map.mpr ⟨q-16,List.mem_range'_1.mpr (by omega),by change (q-16)+16=q;omega⟩
theorem carry_origin {i upper x p:Nat} (limit:i+15≤512) (upper_ok:upper≤1812) (good:Bounds x p) (raw history:State)
    (domain:Domain i x p raw)
    (fixed:∀q:Nat,1556≤q → q≤upper → OB5.sig (i+14) q=q)
    (q:Nat) (low:1556≤q) (high:q≤upper) : (origin i raw history).basis q=false:=by
  have clear:q∉sites i:=by
    intro hit
    have old:=(mem_sites (by omega) q).mp hit
    rw [fixed _ low high] at old
    have top:=old_bound i
    obtain ⟨r,_,lt,h|h⟩:=old_cell old <;> omega
  rw [outside i raw history q clear,fixed _ low high]
  exact full_carry i 15 x p limit good raw domain [] q low (Nat.le_trans high upper_ok)
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
/-- Every wire block `s`'s 15 reference ticks may touch (the exact footprint of `span s 15`): the A rail up to the
extension wire `s+30+W(s+14)` of tick `s+14` (`s+288` on the 258-wide rails before 225, `s+287` at 225 and 240, `529`
from 255 on), the B rail to `785+W(s)` (`1043` before 225, `1042` up to 256, `1298-s` after), the carry bank up to
`min 1812 (2069-s)` (the older moved history slots `[2070-s,1812]` stay outside), and the history cells
`s+1044 .. s+1058`. Matches par-c1's `leaveBox`. -/
def Box (s q:Nat):Prop :=
  (s+15≤q ∧ q≤s+30+W.narrowSkywalkRouteWidth (s+14) ∧ q≤529) ∨ (786≤q ∧ q≤785+W.narrowSkywalkRouteWidth s) ∨
  (1556≤q ∧ q≤1812 ∧ q+s≤2069) ∨ (1044+s≤q ∧ q<1059+s)
instance (s q:Nat) : Decidable (Box s q):=by unfold Box;infer_instance
/-- The route width of tick `k` in closed form: 258 before 225, 257 up to 256, `513-k` after. -/
theorem route_width (k:Nat) (hk:k≤510) :
    (k<225 ∧ W.narrowSkywalkRouteWidth k=258) ∨ (225≤k ∧ k≤256 ∧ W.narrowSkywalkRouteWidth k=257) ∨
    (257≤k ∧ W.narrowSkywalkRouteWidth k=513-k) := by
  have h:W.narrowSkywalkRouteWidth k=min (min 258 (514-k) - (min 1 (511-k) - min 1 (256-k))) (257 + min 1 (225-k)):=by
    unfold W.narrowSkywalkRouteWidth;rfl
  generalize W.narrowSkywalkRouteWidth k=n at h ⊢
  rw [Nat.min_def,Nat.min_def,Nat.min_def,Nat.min_def,Nat.min_def] at h
  split_ifs at h <;> omega
/-- The route width in `railP`'s form (par-b/par-c1), so `railP k=W.narrowSkywalkRouteWidth k` is `(route_eq k hk).symm`
after unfolding `railP`. -/
theorem route_eq (k:Nat) (hk:k≤510) : W.narrowSkywalkRouteWidth k=(if k<225 then 258 else if k<257 then 257 else 513-k) := by
  rcases route_width k hk with ⟨a,h⟩|⟨a,b,h⟩|⟨a,h⟩ <;> rw [h] <;> split_ifs <;> omega
theorem box_away {s:Nat} (lo:0<s) (hi:s+15≤511) {q:Wire} (out:¬Box s q) : ∀a<15,¬RawRead (s+a) q := by
  intro a ha hit
  apply out
  have pos:s+a≠0:=by omega
  have w:=route_width (s+a) (by omega)
  have w':=route_width (s+14) (by omega)
  have w0:=route_width s (by omega)
  unfold RawRead at hit
  simp only [W.compactSkywalkTickPreWidth,skywalkPoolPreviousId,if_neg pos,base,Wire] at hit
  unfold Box
  omega
/-- `exterior_origin` for every block start `s` of the window range: outside `Box s`, the window's snapshot agrees
with the reference origin wherever it agrees with the pre-block state. Outside `Box s` the placements before and after
the block agree, and their common image is again outside `Box s`, which the reference ticks leave alone; this covers
the band `[1301,1043+s]` and the older moved slots `[2070-s,1812]` too. -/
theorem box_origin {s:Nat} (lo:1≤ s) (hi:s≤420) {q:Wire} (out:¬Box s q) (raw history:State)
    (same:q∉sites s → history.basis q=(pullState (OB5.sig (s-1)) raw).basis q) :
    history.basis q=(origin s raw history).basis q:=by
  by_cases h:q∈sites s
  · exact (inside s raw history q h).symm
  rw [same h,outside s raw history q h]
  change raw.basis (OB5.sig (s-1) q)=_
  have box:=out
  unfold Box at box
  have w0:=route_width s (by omega)
  have agree:OB5.sig (s-1) q=OB5.sig (s+14) q:=by
    rw [OB5.sig_nat,OB5.sig_nat]
    unfold OB5.sigNat
    split_ifs <;> first | rfl | omega
  have away:¬Box s (OB5.sig (s+14) q):=by
    rw [OB5.sig_nat]
    unfold Box OB5.sigNat
    split_ifs <;> omega
  rw [agree,span_unchanged s 15 _ (by omega) (box_away (by omega) (by omega) away)]
/-- `box_origin` at block `j`. -/
theorem box_origin_j (j:Fin 24) {q:Wire} (out:¬Box (StairPacket.start j) q) (raw history:State)
    (same:q∉sites (StairPacket.start j) → history.basis q=(pullState (OB5.sig (StairPacket.start j-1)) raw).basis q) :
    history.basis q=(origin (StairPacket.start j) raw history).basis q:=
  box_origin (by have h:=j.isLt;change 1≤75+15*(j:Nat);omega) (by have h:=j.isLt;change 75+15*(j:Nat)≤420;omega)
    out raw history same
end ECDSAAdd.Entrant.StairPacket.WideReference


end

-- ==== w4: step 8: proof-q1542 nj/src/NJ/Two.lean (NativeJ.admin_outside, agree_origin keyed on firstBlock) ====
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3500000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! `NativePack{s}.agree_origin` for an interior block, on wires `OB5.sig (s+14)` does not move.
    The band `[1301,1044+s+14]` is excluded by `still`: `sig` is not the identity there.
    Comparison is `box_origin_j`; the unmoved frame is `sig_fixed`. -/
/-! The first block of the window (`WideReference.firstBlock`) keeps only the last five stock ticks in
    `oldSites`, so the `rawHead`/`support` wires of the ten ticks before those are in neither `Box` nor `sites`.
    Every other block has the full 15. -/
end ECDSAAdd.Entrant.StairPacket.NativeJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
end ECDSAAdd.Entrant.StairPacket.WideReference

end

-- a relocation leaves every wire that no move mentions in place (used by the `routed` proofs).
theorem ECDSAAdd.Entrant.WSlimV3.source_fix (xs : List (Nat × Nat)) (q : Nat)
    (h1 : q ∉ xs.map Prod.fst) (h2 : q ∉ xs.map Prod.snd) :
    ECDSAAdd.Entrant.StairPacket.LeaveRelocation.source xs q = q := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h1 h2
    have e : ECDSAAdd.Entrant.StairPacket.LeaveRelocation.source (p :: ps) q =
        ECDSAAdd.Entrant.StairPacket.LeaveRelocation.flip p.1 p.2
          (ECDSAAdd.Entrant.StairPacket.LeaveRelocation.source ps q) := rfl
    rw [e, ih h1.2 h2.2]
    unfold ECDSAAdd.Entrant.StairPacket.LeaveRelocation.flip
    rw [if_neg h1.1, if_neg h2.1]
namespace ECDSAAdd.Entrant.WSlimV3
/-- `source xs q = q` is decided without evaluating `source` when no move mentions `q` -/
scoped instance (priority := high) decSourceFix (xs : List (Nat × Nat)) (q : Nat) :
    Decidable (ECDSAAdd.Entrant.StairPacket.LeaveRelocation.source xs q = q) :=
  if h : q ∉ xs.map Prod.fst ∧ q ∉ xs.map Prod.snd then isTrue (source_fix xs q h.1 h.2)
  else Nat.decEq _ _
end ECDSAAdd.Entrant.WSlimV3

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave225Word

end ECDSAAdd.Entrant.StairPacket.Leave225BoundaryClean

end
end
-- ==== w4: step 6: par-c3 Reloc, Wide, Adm, Rel (scratch-real) ====
-- ---- w4 step 6: ParC3/Reloc.lean ----

/-! par-c3: closed form of the leave's relocation `LeaveRelocation.source (movesP s)` for every window block
(replaces dadon's per-block decides `Leave{s}Relocated.upperMap` and the `routed` part of `Leave{s}BoundaryClean`).

`movesP s` = the bank pairs `(a i, d i)`, `i < n = wpP (s+15) - 3`, then six flag pairs. With `D0 = 805 + sbP (s+15)`:
`d i = D0 + i` (the next tick's B words) and `a i = bankW s (L+i)`, which is `D0 + 15 + i` on the B branch
(`L + i < wpP s`) and a pool wire `1598..1612` after it. So the bank pairs form a shift chain of step 15:
`source (D0 + i) = a i` and, for the `a i` that are not a `d` (freed B top, pool), `source (a i) = D0 + i % 15`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.Relocated
open Partial LeaveRelocation
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem flip_ne {a b q : Wire} (ha : q ≠ a) (hb : q ≠ b) : LeaveRelocation.flip a b q = q := by
  unfold LeaveRelocation.flip; rw [if_neg ha, if_neg hb]
theorem flip_fst (a b : Wire) : LeaveRelocation.flip a b a = b := by unfold LeaveRelocation.flip; rw [if_pos rfl]
theorem flip_snd {a b : Wire} (h : b ≠ a) : LeaveRelocation.flip a b b = a := by unfold LeaveRelocation.flip; rw [if_neg h, if_pos rfl]

/-- Peel the last pair of a range-indexed relocation. -/
theorem src_succ (p : Nat → Wire × Wire) (k : Nat) (q : Wire) :
    source ((List.range (k+1)).map p) q = source ((List.range k).map p) (LeaveRelocation.flip (p k).1 (p k).2 q) := by
  simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, LeaveRelocation.append]
  rfl

theorem src_untouched (p : Nat → Wire × Wire) (k : Nat) (q : Wire) (h : ∀ i < k, q ≠ (p i).1 ∧ q ≠ (p i).2) :
    source ((List.range k).map p) q = q := by
  apply LeaveRelocation.outside
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i (List.mem_range.mp hi)

theorem src_above (p : Nat → Wire × Wire) (k : Nat) (q : Wire) : ∀ n : Nat, k ≤ n →
    (∀ i, k ≤ i → i < n → q ≠ (p i).1 ∧ q ≠ (p i).2) →
    source ((List.range n).map p) q = source ((List.range k).map p) q := by
  intro n
  induction n with
  | zero => intro hk _; rw [Nat.le_zero.mp hk]
  | succ n ih =>
    intro hk h
    by_cases e : k = n + 1
    · rw [e]
    · rw [src_succ, flip_ne (h n (by omega) (by omega)).1 (h n (by omega) (by omega)).2]
      exact ih (by omega) (fun i a b => h i a (by omega))

/-- The bank pairs of `movesP s`. -/
def bankPair (s i : Nat) : Wire × Wire := (bankW s (lowsP s + i), bTopP (s+15) + 4 + i - wpP (s+15))
/-- The six flag pairs of `movesP s`. -/
def flagPairs (s : Nat) : List (Wire × Wire) :=
  [(1557, e0P (s+15) + 3), (1558, e0P (s+15) + 4), (e0P s + 5, e0P (s+15) + 5),
   (e0P s + 3, e0P (s+15) + 6), (e0P s + 7, e0P (s+15) + 7), (e0P s + 6, e0P (s+15) + 8)]

theorem moves_split (s : Nat) :
    movesP s = (List.range (wpP (s+15) - 3)).map (bankPair s) ++ flagPairs s := rfl

end ECDSAAdd.Entrant.StairPacket.LeaveJ.Relocated

end

-- ---- w4 step 6: ParC3/Wide.lean ----

/-! par-c3: generic `Leave{s}WideWords` (Tail10d9): where the next tick's stock rails (`L`, tick s+15) and the block's
short rails (`shortL`) sit, and what they read. dadon decides `shortMapping` (Fin 144) and `wideMapping` (Fin 257)
per block; here both are closed forms (`IntegerPacket.ports` and `W.compactSkywalkTick_a/_b`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.WideWords
open Arithmetic MappedCompressed PortalValues LeaveSignedCoordinates Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- dadon's `Leave{s}WideWords.L`: the stock layout of tick s+15. -/
abbrev L (j : Fin 24) := W.compactSkywalkTickLayout MappedCompressed.base (start j + 15)
/-- dadon's `Leave{s}WideWords.shortL`: the block's last packet port. -/
abbrev shortL (j : Fin 24) := IntegerPacket.ports (shape j) 15

end ECDSAAdd.Entrant.StairPacket.LeaveJ.WideWords

end

-- ---- w4 step 6: ParC3/Adm.lean ----

/-! par-c3: generic `Leave{s}Admission` (Tail10d9), part 1: the numeric envelope, the native carry, the admission
geometry and `assemble`, for every window block `j ∈ [1,21]` (s = 90..390).

dadon's `actualNumbers` uses the tick-independent envelope `u+v ≤ 2^256+2^255`. That gives `room` only while the
rail is at least 257 wide (s < 257). From 257 on (R = 513-s) it uses the product bound instead: with `x.Coprime p`,
either u = 0 and v = 1, or `u+v ≤ uv+1 ≤ 2^(512-s)`. So the generic `actualNumbers` takes `good : Bounds x p`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The true walk's sum from the first tick on: `u+v ≤ 2^256+2^255` (dadon's `after_first`). -/
theorem sum_early (x p t : Nat) (hx : x < 2^256) (hp : p < 2^256) (ht : 1 ≤ t) :
    (step^[t] (init x p)).u + (step^[t] (init x p)).v ≤ 2^256 + 2^255 := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have h : (step^[k+1] (init x p)).u + (step^[k+1] (init x p)).v ≤ 2^256 + 2^256/2 :=
    LeaveBankEnvelope.after_first x p (2^256) hx.le hp.le k
  have e : (2:Nat)^256/2 = 2^255 := by norm_num
  rw [e] at h
  exact h

set_option exponentiation.threshold 600 in
/-- The true walk's sum at tick `t` for coprime inputs: `u+v ≤ 2^(512-t)` (product bound). -/
theorem sum_late (x p t : Nat) (good : WideReference.Bounds x p) (ht : t ≤ 512) :
    (step^[t] (init x p)).u + (step^[t] (init x p)).v ≤ 2^(512-t) := by
  have hb := iter_product_bound t (init x p)
  have hv := iter_valid t (init x p) good.positive good.odd
  generalize hz : step^[t] (init x p) = z at hb hv ⊢
  have hxp : x * p < 2^512 := by
    calc x * p ≤ x * 2^256 := Nat.mul_le_mul_left _ (Nat.le_of_lt good.cap)
         _ < 2^256 * 2^256 := Nat.mul_lt_mul_of_pos_right (lt_trans good.small good.cap) (by positivity)
         _ = 2^512 := (pow_add (2 : Nat) 256 256).symm
  change 2^t*(z.u*z.v) ≤ x*p at hb
  by_cases hu : z.u = 0
  · have g := hv.2.2
    rw [hu, Nat.gcd_zero_left] at g
    have one : z.v = 1 := g.trans good.coprime
    rw [hu, one]
    have := Nat.one_le_two_pow (n := 512 - t)
    omega
  · have split : (2 : Nat)^512 = 2^t * 2^(512 - t) := by rw [← pow_add, Nat.add_sub_cancel' ht]
    have h2 : 2^t * (z.u * z.v) < 2^t * 2^(512 - t) := by rw [← split]; exact lt_of_le_of_lt hb hxp
    have hprod : z.u * z.v < 2^(512-t) := Nat.lt_of_mul_lt_mul_left h2
    have hu1 : 1 ≤ z.u := Nat.pos_of_ne_zero hu
    have hv1 : 1 ≤ z.v := hv.1
    have hsum : z.u + z.v ≤ z.u * z.v + 1 := by nlinarith
    omega

namespace Admission

/-- dadon's `Leave{s}Admission.Numeric` (225: sb 144, Wp 97, next sb 136, W 112). -/
structure Numeric (j : Fin 24) (z : SkywalkNat.State) : Prop where
  small : min z.u z.v < 2^(sbP (start j))
  odd : z.v % 2 = 1
  room : Shadow.high (sbP (start j)) 15 z + 1 < 2^(wpP (start j))
  nextSmall : min (SkywalkNat.step^[15] z).u (SkywalkNat.step^[15] z).v < 2^(sbP (start j + 15))
  bound : TrueMiddle.F j z < 2^(wpP (start j) + 15)

/-- dadon's `Leave{s}Admission.flags` (block-independent). -/
def flags (z : SkywalkNat.State) (g0 s0 : Bool) : Bool × Bool :=
  SharedSigned.flags g0 s0 (SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v))

end Admission

namespace Admission

/-- dadon's `Leave{s}Admission.Inputs`. The `extra` field (dadon's 255 form) is vacuous when the overflow is empty. -/
structure Inputs (j : Fin 24) (s : State) (z : SkywalkNat.State) (g0 s0 : Bool) : Prop extends Numeric j z where
  ready : onRails j 15 (SkywalkRails.encode (flags z g0 s0).1 (flags z g0 s0).2
    (SkywalkNat.step^[15] (Shadow.reduced (sbP (start j)) 15 z)).u
    (SkywalkNat.step^[15] (Shadow.reduced (sbP (start j)) 15 z)).v) s.basis
  fresh : s.basis (e0P (start j) + 5) = false
  scratch : ∀ q ∈ 1556::1557::1558::fullC, s.basis q = false
  temp : ∀ p ∈ longPairs j, s.basis p.2 = false
  clean : ∀ q ∈ carries j, s.basis q = false
  padding : ∀ t : Nat, wpP (start j) ≤ t → t < wpP (start j) + 15 → s.basis (bankW (start j) t) = false
  bank : regValue (ys j) s.basis =
    if Shadow.far (sbP (start j)) 15 z then Shadow.high (sbP (start j)) 15 z else 0
  zero : ∀ q ∈ watched j, s.basis q = false
  far : s.basis (e0P (start j) + 3) = decide (Shadow.far (sbP (start j)) 15 z)
  side : s.basis (e0P (start j) + 4) = (decide (Shadow.far (sbP (start j)) 15 z) && decide (2^(sbP (start j)) ≤ z.u))
  record : IntegerPacket.readCells (shape j) 0 15 (mappedBasis j s.basis) =
    SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  extra : ∀ q, e0P (start j) + 10 ≤ q → q < e0P (start j) + 10 + (wpP (start j) - 1 - (e0P (start j) - 1598)) →
    s.basis q = false

end Admission

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ==== w4: build-w4b B2-b admitted (b2b/Window_Admitted.lean) ====
-- BEGIN build-w4b NativeJ.admitted (B2-b part 4)
-- Window (w4r): after par-c3's `LeaveJ.Admission` sections (Window ~36063, before `namespace ...WideReference`).
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount onRails

end ECDSAAdd.Entrant.StairPacket.NativeJ

end
-- END build-w4b NativeJ.admitted
-- ==== w4: end admitted ====

-- ==== w4: build-w4b B2-b from_domain (b2b/Window_FromDomain.lean) ====
-- BEGIN build-w4b NativeJ.from_domain (B2-b part 4)
-- Window (w4r): right after build-w4b's NativeJ.admitted section.
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step onRails measurementCount

end ECDSAAdd.Entrant.StairPacket.NativeJ

end
-- END build-w4b NativeJ.from_domain
-- ==== w4: end from_domain ====

-- ---- w4 step 6: ParC3/Rel.lean ----

/-! par-c3: generic `Leave{s}ReleasedOrigin` (Tail10d9; dadon has it at 255 only, build-window2 at 210).
The wires a block hands back to the stock layout when the rail narrows from `R(s)` to `R(s+15)` (A top wire,
B top band) and the sig-moved band `[1301, s+1058]` are clean in the reference `origin`.
Needs par-a's WideReference (`sites` in the `OB5.sig (i+14)` frame, `mem_sites`, `old_cell`, `old_bound`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 2500000
attribute [local irreducible] run

/-- par-a's `band_origin`, widened from `1043+i` to `1058+i` (the block's own sig-moved history cells, dadon's
255 mirror case `1301..1313`). -/
theorem band_origin_wide {i x p : Nat} (limit : i+15 ≤ 512) (good : Bounds x p) (raw history : State)
    (domain : Domain i x p raw) (q : Nat) (low : 1301 ≤ q) (high : q ≤ 1058+i) :
    (origin i raw history).basis q = false := by
  have map : OB5.sig (i+14) q = (3113-q:Nat) := by
    unfold OB5.sig
    rw [if_pos (by (try simp only [Wire]); omega)]
  have clear : q ∉ sites i := by
    intro hit
    have old := (mem_sites (by omega) q).mp hit
    rw [map] at old
    have top := old_bound i
    obtain ⟨r, _, lt, h|h⟩ := old_cell old <;> omega
  rw [outside i raw history q clear, map]
  exact full_carry i 15 x p limit good raw domain [] _ (by omega) (by omega)

/-- The released part of the A pool of tick `t`: `t+16+R(t) .. t+273`. -/
theorem poolA_released (t q : Nat) (hn : W.narrowSkywalkRouteWidth t ≤ 258)
    (lo : t + 16 + W.narrowSkywalkRouteWidth t ≤ q) (hi : q < t + 274) :
    q ∈ (W.compactSkywalkSignPoolA base t).released := by
  have e := wireBlock_append base t (W.narrowSkywalkRouteWidth t) (258 - W.narrowSkywalkRouteWidth t)
  rw [show W.narrowSkywalkRouteWidth t + (258 - W.narrowSkywalkRouteWidth t) = 258 by omega] at e
  show q ∈ (skywalkPoolA base t).drop (W.narrowSkywalkRouteWidth t)
  unfold skywalkPoolA
  rw [← e, List.drop_left' (wireBlock_length _ _ _)]
  refine List.mem_map.mpr ⟨q - 16, List.mem_range'_1.mpr ⟨by omega, by omega⟩, ?_⟩
  unfold base; ((try unfold Wire at *); omega)

/-- The released part of the B pool of tick `t`: `786+R(t) .. 1043`. -/
theorem poolB_released (t q : Nat) (hn : W.narrowSkywalkRouteWidth t ≤ 258)
    (lo : 786 + W.narrowSkywalkRouteWidth t ≤ q) (hi : q < 1044) :
    q ∈ (W.compactSkywalkSignPoolB base t).released := by
  have e := wireBlock_append base 770 (W.narrowSkywalkRouteWidth t) (258 - W.narrowSkywalkRouteWidth t)
  rw [show W.narrowSkywalkRouteWidth t + (258 - W.narrowSkywalkRouteWidth t) = 258 by omega] at e
  show q ∈ (skywalkPoolB base).drop (W.narrowSkywalkRouteWidth t)
  unfold skywalkPoolB
  rw [← e, List.drop_left' (wireBlock_length _ _ _)]
  refine List.mem_map.mpr ⟨q - 16, List.mem_range'_1.mpr ⟨by omega, by omega⟩, ?_⟩
  unfold base; ((try unfold Wire at *); omega)

/-- A wire released by the stock pools at tick `i+15` (and outside the old history) is clean in `origin i`. -/
theorem pool_origin {i x p : Nat} (limit : i+15 ≤ 512) (good : Bounds x p) (raw history : State)
    (dom : Domain i x p raw) (q : Nat) (hq1 : i + 31 ≤ q) (hq2 : q < 1044)
    (rel : q ∈ (W.compactSkywalkSignPoolA base (i+15)).released ∨ q ∈ (W.compactSkywalkSignPoolB base (i+15)).released) :
    (origin i raw history).basis q = false := by
  have ident : OB5.sig (i+14) q = q := by
    unfold OB5.sig; rw [if_neg (by (try simp only [Wire] at *); omega)]
  have clear : q ∉ sites i := by
    intro hit
    have old := (mem_sites (by omega) q).mp hit
    rw [ident] at old
    have top := old_bound i
    obtain ⟨r, _, lt, h|h⟩ := old_cell old <;> ((try unfold Wire at *); omega)
  rw [outside i raw history q clear, ident]
  obtain ⟨reference, same, stage⟩ := dom
  have finish := full_span i 15 x p limit good.positive good.nonzero good.odd good.cap good.gap good.small
    good.coprime reference [] stage
  have offHist : ¬ Earlier i q := outside_between (by omega) (by omega)
  have link := fixed_span i i 15 (Nat.le_refl _) limit raw reference [] same
  apply (link.2 q offHist).trans
  rcases rel with a | b
  · exact finish.2.1 q a
  · exact finish.2.2 q b

end ECDSAAdd.Entrant.StairPacket.WideReference

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.ReleasedOrigin
open Arithmetic MappedCompressed WideReference Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- dadon's `Leave{s}ReleasedOrigin.releasedSite`: the A wire and B band freed when the rail narrows from `R(s)` to
`R(s+15)`, the sig-moved band `[1301, s+1058]`, and (window390, blocks 375 and 390) the released B-rail wires
`[1302-s, 933]` that host the archive scratch beyond the stock carry: used by the block's loader, blank after it and
clean in the stock state. 210: {498, 1043}; 225, 240: {}; 255: {529, 1029..1042, 1301..1313}. -/
def releasedSite (j : Fin 24) (q : Nat) : Prop :=
  (railP (start j + 15) < railP (start j) ∧ q = start j + 31 + railP (start j + 15)) ∨
  (785 + railP (start j + 15) < q ∧ q ≤ 785 + railP (start j)) ∨ (1301 ≤ q ∧ q ≤ 1058 + start j) ∨
  (369 ≤ start j ∧ 1302 ≤ q + start j ∧ q ≤ 933)
instance (j : Fin 24) (q : Nat) : Decidable (releasedSite j q) := by unfold releasedSite; infer_instance

end ECDSAAdd.Entrant.StairPacket.LeaveJ.ReleasedOrigin

end

-- ==== w4: step 10: P2 leave chain (proof-q1542 Fam8..11, Dest, Wrap1..7; build-w4b Records, PreservedA/B, EndWords) ====
-- ---- w4 step 10: proof-q1542/win/src/ParC1/Fam8.lean (md5 e738bba82905) ----

/-! par-c1: generic leave families, batch 8: the full arithmetic (dadon's `Leave{s}FullArithmetic`, cut 0..2318 =
entry ++ body ++ companion restore). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

theorem entry_dest : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 → (entryOps (start j)).all (fun g =>
    (decide (a0P (start j) - 1 ≤ target g) && decide (target g ≤ a0P (start j) + 17)) ||
    (decide (b0P (start j) - 1 ≤ target g) && decide (target g ≤ b0P (start j) + 17)) ||
    (decide (start j + 16 ≤ target g) && decide (target g ≤ start j + 30)) ||
    (decide (1556 ≤ target g) && decide (target g ≤ 1575)) || decide (target g = e0P (start j) + 5)) = true := by
  decide +kernel

theorem entry_keep (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (q : Nat)
    (hq : ¬ ((a0P (start j) - 1 ≤ q ∧ q ≤ a0P (start j) + 17) ∨ (b0P (start j) - 1 ≤ q ∧ q ≤ b0P (start j) + 17) ∨
      (start j + 16 ≤ q ∧ q ≤ start j + 30) ∨ (1556 ≤ q ∧ q ≤ 1575) ∨ q = e0P (start j) + 5)) (s : State) (m : List Bool) :
    (run (GateMirror.forward (entryOps (start j))) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  intro hm
  rw [dest_forward] at hm
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
  have := List.all_eq_true.mp (entry_dest j h0 h1) g hg
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rw [e] at this
  exact hq (by unfold Wire at *; omega)

/-- dadon's `Leave{s}FullArithmetic.program`. -/
def fullProgram (j : Fin 24) : Program :=
  GateMirror.forward (entryOps (start j) ++ bodyOps j) ++ Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558

/-! FlagScratch (dadon's `Leave{s}FlagScratch`). -/

/-- dadon's `LeaveCompanion{s}.pendingPairs` (the StoreMapped chain: top, then the bank above the low columns). -/
def pendingPairs (j : Fin 24) : List (Wire × Wire) :=
  (List.range (wpP (start j) + 15 - lowsP (start j) + 1)).map (fun i =>
    (if i = 0 then a0P (start j) + lowsP (start j) - 1 else bankW (start j) (lowsP (start j) + i - 1), storeW (i+1)))
/-- dadon's `LeaveCompanion{s}.clearFlagPairs`. -/
def clearFlagPairs (j : Fin 24) : List (Wire × Wire) :=
  (List.range (lowsP (start j) + 1)).map (fun i => (b0P (start j) - 1 + i, 1559 + i))
/-- dadon's `Leave{s}FlagScratch.targets`. -/
def flagTargets (j : Fin 24) : List Wire := (pendingPairs j ++ clearFlagPairs j).map Prod.snd

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Fam9.lean (md5 4191811e3865) ----

/-! par-c1: generic leave families, batch 9: the StoreMapped segment as dadon's gadgets (pending threshold, nextU,
clear-flag latch), the scanned output register, and the readout of the next flag (dadon's `LeaveCompanion{s}`
pending/clearFlag parts, `Leave{s}OutputPorts.outputRegisters`, `Leave{s}Readout`, `Leave{s}NextFlagTruth`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror PortalAnd SkywalkNat IntegerHigh Shadow LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-! Gate-level chains are dadon's `PortalAnd.chain`. -/

theorem forward_xsG (xs : List Wire) : GateMirror.forward (xsG xs) = notRegister xs := forward_xsG' xs

theorem forward_cons' (g : Gate) (gs : List Gate) : GateMirror.forward (g :: gs) = front g :: GateMirror.forward gs := rfl
theorem forward_nil' : GateMirror.forward [] = [] := rfl

theorem forward_chainG (c seq : Nat → Wire) (out : Wire) : ∀ (i n : Nat),
    GateMirror.forward (chainG c seq [.cx (c (i+n)) out, .x out] i n) =
      PortalAnd.chain true none out (c i) ((List.range n).map (fun k => (seq (i+k), c (i+k+1))))
  | i, 0 => by simp [chainG, PortalAnd.chain, PortalAnd.target, GateMirror.forward, front]
  | i, n+1 => by
    have ih := forward_chainG c seq out (i+1) n
    rw [show i + 1 + n = i + (n+1) by omega] at ih
    have el : (List.range (n+1)).map (fun k => (seq (i+k), c (i+k+1))) =
        (seq i, c (i+1)) :: (List.range n).map (fun k => (seq (i+1+k), c (i+1+k+1))) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ List.cons rfl (List.map_congr_left (fun k _ => ?_))
      show (seq (i+(k+1)), c (i+(k+1)+1)) = (seq (i+1+k), c (i+1+k+1))
      rw [show i + (k+1) = i + 1 + k by omega]
    show GateMirror.forward (.make (c i) (seq i) (c (i+1)) ::
      (chainG c seq [.cx (c (i+(n+1))) out, .x out] (i+1) n ++ [.pop (c i) (seq i) (c (i+1))])) = _
    rw [forward_cons', forward_app, ih, el]
    rfl

theorem sites_perm : ∀ ps : List (Wire × Wire), (PortalAnd.sites ps).Perm (ps.map Prod.fst ++ ps.map Prod.snd)
  | [] => by simp [PortalAnd.sites]
  | p::ps => by
    have ih := sites_perm ps
    change (p.1 :: p.2 :: PortalAnd.sites ps).Perm (p.1 :: (ps.map Prod.fst ++ p.2 :: ps.map Prod.snd))
    exact (List.Perm.cons _ ((List.Perm.cons _ ih).trans List.perm_middle.symm))

/-- The StoreMapped pairs (dadon's `pendingPairs`, defined in Fam8): first components. -/
theorem pending_fst (j : Fin 24) : (pendingPairs j).map Prod.fst =
    (a0P (start j) + lowsP (start j) - 1) ::
      (List.range (wpP (start j) + 15 - lowsP (start j))).map (fun i => bankW (start j) (lowsP (start j) + i)) := by
  simp only [pendingPairs, List.map_map, Function.comp]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp, if_pos, Nat.succ_ne_zero, if_false]
  congr 1

theorem forward_chainG0 (c seq : Nat → Wire) (out : Wire) (n : Nat) :
    GateMirror.forward (chainG c seq [.cx (c n) out, .x out] 0 n) =
      PortalAnd.chain true none out (c 0) ((List.range n).map (fun k => (seq k, c (k+1)))) := by
  have h := forward_chainG c seq out 0 n
  simp only [Nat.zero_add] at h
  exact h

theorem clearFlag_fst (j : Fin 24) :
    (clearFlagPairs j).map Prod.fst = (List.range (lowsP (start j) + 1)).map (b0P (start j) - 1 + ·) := by
  simp only [clearFlagPairs, List.map_map]; rfl

theorem storeMapped_parts (j : Fin 24) :
    GateMirror.forward (leaveStoreMapped (start j)) =
      threshold (a0P (start j) + lowsP (start j) - 1 - 2) (a0P (start j) + lowsP (start j) - 1 - 1) 1558 1557 (pendingPairs j) ++
        ([.CCX 1556 1557 1558] ++ latch true none 1556 1558 (clearFlagPairs j)) := by
  have ch1 : GateMirror.forward (chainG storeW
      (fun i => if i = 0 then a0P (start j) + lowsP (start j) - 1 else bankW (start j) (lowsP (start j) + i - 1))
      [.cx (storeW (wpP (start j) + 15 - lowsP (start j) + 1)) 1557, .x 1557] 0 (wpP (start j) + 15 - lowsP (start j) + 1)) =
      PortalAnd.chain true none 1557 1558 (pendingPairs j) := forward_chainG0 _ _ _ _
  have ch2 : GateMirror.forward (chainG (fun i => (1558 + i : Wire)) (fun i => b0P (start j) - 1 + i)
      [.cx (1558 + (lowsP (start j) + 1)) 1556, .x 1556] 0 (lowsP (start j) + 1)) =
      PortalAnd.chain true none 1556 1558 (clearFlagPairs j) := by
    have h := forward_chainG0 (fun i => (1558 + i : Wire)) (fun i => b0P (start j) - 1 + i) 1556 (lowsP (start j) + 1)
    have e : (List.range (lowsP (start j) + 1)).map (fun k => (b0P (start j) - 1 + k, (1558 + (k+1) : Wire))) =
        clearFlagPairs j := by
      simp only [clearFlagPairs]; apply List.map_congr_left; intro k _; simp only [Prod.mk.injEq, true_and]
      unfold Wire; omega
    rw [← e]; exact h
  simp only [leaveStoreMapped, forward_app, forward_xsG, ch1, ch2, threshold, PortalAnd.latch, PortalAnd.digits,
    pending_fst, clearFlag_fst, forward_cons', forward_nil', front, erase, notRegister, List.map_cons, List.map_nil,
    List.map_append, List.reverse_cons, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    if_true, ↓reduceIte]


/-! The scanned output register (dadon's `OutputPorts.scanned`, `outputRegisters` high part). -/

def scanned (j : Fin 24) : List Wire :=
  (a0P (start j) + lowsP (start j) - 1 - 2) :: (a0P (start j) + lowsP (start j) - 1 - 1) :: (pendingPairs j).map Prod.fst

theorem scanned_eq (j : Fin 24) : scanned j =
    (a0P (start j) + lowsP (start j) - 1 - 2) :: (a0P (start j) + lowsP (start j) - 1 - 1) :: (a0P (start j) + lowsP (start j) - 1) ::
      (List.range (wpP (start j) + 15 - lowsP (start j))).map (fun i => bankW (start j) (lowsP (start j) + i)) := by
  rw [scanned, pending_fst]

/-! The pending threshold (dadon's `LeaveCompanion{s}.pending_three`). -/

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Fam10.lean (md5 2ddd74c9a921) ----

/-! par-c1: generic leave families, batch 10: the tail flags (dadon's `Leave{s}NextFlagTruth`, the clear-flag latch
and nextU of `LeaveCompanion{s}`, `Leave{s}TailFlags`). The StoreMapped segment is `threshold ++ nextU ++ latch`
(`storeMapped_parts`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror PortalAnd SkywalkNat IntegerHigh Shadow LeaveCompanion
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-! NextFlagTruth. -/

/-! nextU and the clear-flag latch. -/

theorem nextU_run (s : State) (m : List Bool) (fresh : s.basis 1558 = false) :
    run ([.CCX 1556 1557 1558] : Program) m s = ⟨s.phase, writeBit s.basis 1558 (s.basis 1556 && s.basis 1557)⟩ := by
  simp [run, fresh]

theorem clearFlag_digits (j : Fin 24) : PortalAnd.digits 1558 (clearFlagPairs j) = 1558 :: (b0P (start j) - 1) :: smallM j := by
  simp only [PortalAnd.digits, clearFlagPairs, smallM, List.map_map, Function.comp]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp, Nat.add_zero]
  congr 2
  apply List.map_congr_left; intro i _
  show b0P (start j) - 1 + (i + 1) = b0P (start j) + i
  unfold b0P; omega

/-! TailFlags (dadon's `Leave{s}TailFlags.result`: the StoreMapped segment). -/

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Fam11.lean (md5 7795c5b1a450) ----

/-! par-c1: generic leave families, batch 11: the mask through the full arithmetic and the leave up to the store
(dadon's `Leave{s}MaskThrough`, `Leave{s}MaskCut`, `Leave{s}BeforeStore`). The mask interior's destinations are
generic (the companion erase/restore are forwards of `addG` gate lists); no new decide. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-! MaskThrough. -/

/-- The full arithmetic before the mask opens (dadon's `MaskCut.beforeOpen`, cut 169). -/
def beforeOpen (j : Fin 24) : Program :=
  GateMirror.forward (leaveFix0 (start j) (sbP (start j)) ++ leaveFix1 (start j) (sbP (start j))) ++
    PortalAnd.latch true none 1556 (b0P (start j) - 1) (longPairs j)

/-- The part of the full arithmetic between the mask open and its release (dadon's `MaskThrough.interior`). -/
def interior (j : Fin 24) : Program :=
  Companion.erase (fullA j) (fullM j) fullC 1556 1558 ++ (GateMirror.forward (bodyOps j) ++
    Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558)

/-- dadon's `MaskCut.split`. -/
theorem full_split (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    fullProgram j = beforeOpen j ++ (maskP j ++ interior j) := by
  simp only [fullProgram, beforeOpen, interior, entryOps, forward_app, fix2_parts j h0 h1, List.append_assoc]

theorem erase_gates (j : Fin 24) : Companion.erase (fullA j) (fullM j) fullC 1556 1558 =
    GateMirror.forward (addG (fullM j) fullC 1558 ++
      (List.range 18).map (fun i => Gate.ccx 1556 (a0P (start j) + i) (b0P (start j) + i))) := by
  have hc : GateMirror.forward ((List.range 18).map (fun i => Gate.ccx 1556 (a0P (start j) + i) (b0P (start j) + i))) =
      copyRegister (some 1556) (fullA j) (fullM j) := by
    rw [fullA, fullM, copy_map]; simp only [GateMirror.forward, List.map_map]; rfl
  rw [forward_app, forward_addG, hc]; rfl

/-- The companion restore of the low columns as gates (`lowRest` without the mask release). -/
def restoreG (s : Nat) : List Gate :=
  (List.range (lowsP s)).map (fun i => .ccx 1556 (a0P s + i) (b0P s + i)) ++ xsG ((List.range (lowsP s)).map (b0P s + ·)) ++
  addG ((List.range (lowsP s)).map (b0P s + ·)) ((List.range (lowsP s - 1)).map (1559 + ·)) 1558 ++
  xsG ((List.range (lowsP s)).map (b0P s + ·))

theorem restore_gates (j : Fin 24) :
    Companion.restore (smallA j) (smallM j) (smallC j) 1556 1558 = GateMirror.forward (restoreG (start j)) := by
  have h := lowRest_parts j
  have e : lowRest (start j) = restoreG (start j) ++
      [.pop (b0P (start j) - 1) 1557 1558, .cx (a0P (start j) - 1) 1557, .x 1557] := by
    simp only [lowRest, restoreG, List.append_assoc]
  rw [e, forward_app] at h
  exact (List.append_cancel_right h).symm

/-- The companion region: the magnitude limbs and the carries. -/
def compT (j : Fin 24) (t : Nat) : Prop := (b0P (start j) ≤ t ∧ t ≤ b0P (start j) + 17) ∨ (1559 ≤ t ∧ t ≤ 1575)

theorem erase_dest (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    ∀ q ∈ (Companion.erase (fullA j) (fullM j) fullC 1556 1558).map LeaveReadoutFrame.destination, compT j q := by
  have ea : AllAT (fun _ => True) (compT j) (addG (fullM j) fullC 1558 ++
      (List.range 18).map (fun i => Gate.ccx 1556 (a0P (start j) + i) (b0P (start j) + i))) := by
    refine allAT_append (allAT_addG _ _ _ (fun y hy => ⟨trivial, ?_⟩) (fun c hc => ⟨trivial, ?_⟩) trivial)
      (allAT_map _ _ (fun i hi => ok_ccx trivial trivial ?_))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy; rw [List.mem_range] at hi; left; unfold Wire at *; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc; rw [List.mem_range] at hi; right; unfold Wire at *; omega
    · rw [List.mem_range] at hi; left; unfold Wire at *; omega
  intro q h
  rw [erase_gates, dest_forward] at h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
  exact (ea g hg).2

/-! MaskCut. -/

/-! BeforeStore. -/

/-- dadon's `Leave{s}BeforeStore.program` (cut 2788 at 225). -/
def beforeStoreProgram (j : Fin 24) : Program :=
  fullProgram j ++ (releaseMaskP j ++ GateMirror.forward (leaveStoreMapped (start j)))

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Dest.lean (md5 ddb6001208ec) ----

/-! par-c1: operand footprint of the leave avoiding the stock words (for par-c3's BoundaryRails/HighZero): every operand
(so every destination) of `leaveOps s` lies in `leaveBox s` and outside the A low words `[s+31, a0-1)`, the B low words
`[786, b0-1)` and the A high words `[a0+18, 785]`, the wire `s+15`, and the raw history band `[1301, s+1058]`
(the moved cells are in the scratch range). -/

section

namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- The leave's wires: the A rail `s+15 .. min (s + 30 + railP (s+14)) 529`, the B rail `786..785 + railP s`, the scratch `1556..min 1812 (2069-s)`, and the
history cells `s+1044 .. s+1058` (in the `OB5.sig (s+14)` frame the moved cells land in the scratch range). -/
def leaveBox2 (s q : Nat) : Prop :=
  ((s+15 ≤ q ∧ q ≤ min (s + 30 + railP (s+14)) 529) ∨ (786 ≤ q ∧ q ≤ 785 + railP s) ∨ (1556 ≤ q ∧ q ≤ min 1812 (2069 - s)) ∨ (1044+s ≤ q ∧ q < 1059+s)) ∧
  ¬ (s+31 ≤ q ∧ q < a0P s - 1) ∧ ¬ (786 ≤ q ∧ q < b0P s - 1) ∧ ¬ (a0P s + 18 ≤ q ∧ q ≤ 785) ∧ q ≠ s + 15 ∧
  ¬ (1301 ≤ q ∧ q ≤ 1058 + s) ∧ ¬ (2070 ≤ q + s ∧ q ≤ 1812)
/-! The box is five plain intervals. Each is proved once; everything below goes through them. -/

theorem rail14 (s : Nat) : railP (s+15) ≤ railP (s+14) := by unfold railP; split_ifs <;> omega

/-- Boolean test of the five intervals (scratch first: most wires of the fixed segments are there). -/
def inBox2B (s q : Nat) : Bool :=
  (Nat.ble 1556 q && (Nat.ble q 1812 && Nat.ble (q + s) 2069)) ||
  ((Nat.ble (a0P s) (q + 1) && Nat.ble q (a0P s + 17)) ||
  ((Nat.ble (b0P s) (q + 1) && Nat.ble q (785 + railP s)) ||
  ((Nat.ble (s + 16) q && Nat.ble q (s + 30)) ||
  (Nat.ble (1044 + s) q && (Nat.ble q (1058 + s) && Nat.ble q 1300)))))

def segBox2 (s : Nat) (gs : List Gate) : Bool := gs.all (fun g => g.wires.all (inBox2B s))
theorem allW_iff_flat2 {P : Wire → Prop} {gs : List Gate} : AllW P gs ↔ ∀ q ∈ gs.flatMap Gate.wires, P q := by
  constructor
  · intro h q hq; obtain ⟨g, hg, hq⟩ := List.mem_flatMap.mp hq; exact h g hg q hq
  · intro h g hg q hq; exact h q (List.mem_flatMap.mpr ⟨g, hg, hq⟩)

theorem fixed_box2 : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    segBox2 (start j) (leaveFix0 (start j) (sbP (start j)) ++ leaveFix1 (start j) (sbP (start j)) ++
      leaveFix2 (start j) (sbP (start j)) ++ leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j)) ++
      leaveFix5 (start j) (sbP (start j)) ++ leaveFix8 (start j) (sbP (start j)) ++ leaveFix10 (start j) (sbP (start j)) ++
      leaveFix11 (start j) (sbP (start j)) ++ leaveFix12 (start j) (sbP (start j)) ++ lowSign (start j)) = true := by
  decide +kernel

section Main
attribute [local irreducible] leaveBox2

end Main

end ECDSAAdd.Entrant.StairPacket.Partial

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Wrap2.lean (md5 2da707d26ae1) ----

/-! par-c1 real wrappers, part 2: `LeaveJ.CoreCheckpoint` (dadon's `Leave{s}CoreCheckpoint`), with the statements of
`WrapStub.lean`. The checkpoint program is `leaveHeadOps` = entry ++ body (cut 2260 of the leave). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- The head of the leave is the entry followed by the body. -/
theorem head_eq (j : Fin 24) : entryOps (start j) ++ bodyOps j = leaveHeadOps (start j) := by
  simp only [entryOps, bodyOps, fullPrefix, workOps, middleOps, leaveHeadOps, List.append_assoc]

namespace CoreCheckpoint

/-- dadon's `Leave{s}CoreCheckpoint.program` (`leave.take 2260`). -/
abbrev program (j : Fin 24) : Program := GateMirror.forward (leaveHeadOps (start j))
/-- dadon's `rawSites`: the pool below the anchored block and the scratch above it. -/
def rawSites (j : Fin 24) : List Wire :=
  List.range' 1613 (e0P (start j) - 1613) ++ List.range' (e0P (start j) + 8) (min 1813 (2055 - start j) - (e0P (start j) + 8))
abbrev magSites (j : Fin 24) : List Wire := LeaveJ.fullM j
def targets (j : Fin 24) : List Wire :=
  List.range' 1559 39 ++ (List.finRange 18).map (fun i => (LeaveJ.row j i).free) ++ rawSites j ++ magSites j

theorem raw_range (j : Fin 24) (q : Nat) (hq : q ∈ rawSites j) :
    (1613 ≤ q ∧ q < e0P (start j)) ∨ (e0P (start j) + 8 ≤ q ∧ q ≤ 1812 ∧ q + start j ≤ 2054) := by
  simp only [rawSites, List.mem_append, List.mem_range'_1] at hq
  omega

end CoreCheckpoint

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Wrap3.lean (md5 bcf27c88e053) ----

/-! par-c1 real wrappers, part 3: the programs of the later families (`Routed.body`, `FullArithmetic.program`,
`BeforeStore.program`, `StoreMapped.program`), `BeforeStore.result`, and `LeaveJ.Roundtrip.result` (dadon's
`Leave{s}Roundtrip.result`): the leave is undone by its mirror. Statements as in `WrapStub.lean`.

The Mirror (`Partial.leave_inverts`) asks for two facts on the run from `s`: the five core wires are clean after the
head (`CoreCheckpoint.oracle`), and wire 1556 is clean after the head and the mid segment. The second one is read off
`beforeStore_result` (1556 is cleared by the clear-flag latch); the low close that follows never writes 1556. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

namespace Routed
end Routed

namespace FullArithmetic
/-- dadon's `Leave{s}FullArithmetic.program`. -/
abbrev program (j : Fin 24) : Program := LeaveJ.fullProgram j
theorem restoreShape (j : Fin 24) :
    program j = CoreCheckpoint.program j ++ Companion.restore (LeaveJ.smallA j) (LeaveJ.smallM j) (LeaveJ.smallC j) 1556 1558 := by
  simp only [program, LeaveJ.fullProgram, CoreCheckpoint.program, head_eq]
end FullArithmetic

namespace BeforeStore
/-- dadon's `Leave{s}BeforeStore.program`. -/
abbrev program (j : Fin 24) : Program :=
  LeaveJ.fullProgram j ++ (LeaveJ.releaseMaskP j ++ GateMirror.forward (leaveStoreMapped (start j)))

end BeforeStore

namespace StoreMapped
/-- dadon's `Leave{s}StoreMapped.program` (the leave up to the low close). -/
abbrev program (j : Fin 24) : Program := BeforeStore.program j ++ GateMirror.forward (leaveLowClose (start j))
theorem program_eq (j : Fin 24) :
    program j = GateMirror.forward (leaveHeadOps (start j) ++ leaveMidOps (start j)) := by
  simp only [program, BeforeStore.program, LeaveJ.fullProgram, leaveMidOps, forward_app, LeaveJ.lowRest_parts, ← head_eq,
    List.append_assoc]
end StoreMapped

namespace Roundtrip
end Roundtrip

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Wrap4.lean (md5 124873e32f6b) ----

/-! par-c1 real wrappers, part 4: `LeaveJ.Close` (dadon's `Leave{s}Close`), low part: the low close is the history
flip followed by dadon's `RailPair.store` on the low columns, generic in the block. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector RailPair
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

namespace Close

/-- dadon's `Leave{s}Close.history`. -/
abbrev history (j : Fin 24) : List Wire := LeaveJ.history j
/-- dadon's `Leave{s}Close.low`: the low columns, A side and B side. -/
def low (j : Fin 24) : List (Wire × Wire) :=
  (List.range (lowsP (start j) + 1)).map (fun i => (a0P (start j) - 1 + i, b0P (start j) - 1 + i))
/-- dadon's `Leave{s}Close.events`. -/
def events (j : Fin 24) : List (Wire × Wire) :=
  [(LeaveJ.swaps j 0, 1556), (LeaveJ.swaps j 1, 1559), (LeaveJ.swaps j 2, 1560), (LeaveJ.swaps j 3, 1561), (LeaveJ.swaps j 4, 1562)]
/-- dadon's `Leave{s}Close.afterLow`. -/
abbrev afterLow (j : Fin 24) : Program := GateMirror.forward (leaveClose (start j))

/-- dadon's `Leave{s}Close.lowShape`. -/
theorem lowShape (j : Fin 24) : GateMirror.forward (leaveLowClose (start j)) =
    notRegister (history j) ++ store (start j + 30) (e0P (start j) + 5) (low j) [] := by
  have e1 : GateMirror.forward ((List.range (lowsP (start j) + 1)).map
      (fun i => Gate.cx (e0P (start j) + 5) (b0P (start j) - 1 + i))) =
      signComplement (e0P (start j) + 5) ((low j).map Prod.snd) := by
    simp only [GateMirror.forward, signComplement, low, List.map_map]; rfl
  have e2 : GateMirror.forward ((List.range (lowsP (start j) + 1)).flatMap
      (fun i => cswapG (start j + 30) (b0P (start j) - 1 + i) (a0P (start j) - 1 + i))) =
      exchange (start j + 30) (low j) := by
    simp only [GateMirror.forward, exchange, low, List.map_flatMap, List.flatMap_map]; rfl
  simp only [leaveLowClose, forward_app, forward_xsG', e1, e2, store, transfer, List.flatMap_nil, List.nil_append,
    List.append_assoc]
  rfl

theorem mem_low_sites (j : Fin 24) (q : Wire) : q ∈ RailPair.sites (low j) ↔
    ∃ i, i < lowsP (start j) + 1 ∧ (q = a0P (start j) - 1 + i ∨ q = b0P (start j) - 1 + i) := by
  simp only [RailPair.sites, low, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · rintro ⟨p, ⟨i, hi, rfl⟩, h⟩; exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨_, ⟨i, hi, rfl⟩, h⟩

theorem low_fst (j : Fin 24) : (low j).map Prod.fst = (List.range (lowsP (start j) + 1)).map (fun i => (a0P (start j) - 1 + i : Wire)) := by
  simp only [low, List.map_map]; rfl
theorem low_snd (j : Fin 24) : (low j).map Prod.snd = (List.range (lowsP (start j) + 1)).map (fun i => (b0P (start j) - 1 + i : Wire)) := by
  simp only [low, List.map_map]; rfl

theorem low_fst_nodup (j : Fin 24) : ((low j).map Prod.fst).Nodup := by
  rw [low_fst]
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have e' : a0P (start j) - 1 + x = a0P (start j) - 1 + y := e
  (try unfold Wire at *); omega
theorem low_snd_nodup (j : Fin 24) : ((low j).map Prod.snd).Nodup := by
  rw [low_snd]
  refine List.Nodup.map_on (fun x _ y _ e => ?_) List.nodup_range
  have e' : b0P (start j) - 1 + x = b0P (start j) - 1 + y := e
  (try unfold Wire at *); omega

end Close

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Wrap5.lean (md5 911f5eaae6b6) ----

/-! par-c1 real wrappers, part 5: `LeaveJ.StoreCoordinates.result` and `LeaveJ.StoreMapped.result` (dadon's
`Leave{s}StoreCoordinates`, `Leave{s}StoreMapped`), generic in the block.

What dadon reads off slices of the literal program by `decide` (`q ∉ afterFront.map destination`) comes here from the
frame of `beforeStore_result` (only 1556..1558 change after the full arithmetic) and the destination footprints of the
body and the companion restore (`body_dest`, `restore_dest`); the flipped history letters come from `entry_parity`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

namespace StoreCoordinates
end StoreCoordinates

namespace StoreMapped
end StoreMapped

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Wrap6.lean (md5 8244e64ffbca) ----

/-! par-c1 real wrappers, part 6: `LeaveJ.PostReady.result` (dadon's `Leave{s}PostReady`): after the store, the two
window flags and the five event cells are as before the leave, the near flag and the crossing bit hold the selector's
values, and the five event targets are clean.

dadon's `rawLayout` / `keptLayout` (decides on slices of the literal leave) are replaced by the frames of
`StoreMapped.result` and `beforeStore_result`, the footprints `work_dest`, `restore_dest`, `prefix_keep`,
`entry_keep`, and the exact position of the history cells (`swaps_exact`). -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] run SkywalkNat.step

/-- The near flag of the prepared selector word. -/
theorem prior_near (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (k : Mode) :
    prior j k (e0P (start j) + 7) = .bit (nearby k) := by
  have h := controlCert j h0 h1 k
  simp only [reads, LeaveSelector.controls, List.cons.injEq, and_true] at h
  exact h.1

namespace PostReady

end PostReady

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: proof-q1542/win/src/ParC1/Wrap7.lean (md5 73ddd4a26450) ----

/-! par-c1 real wrappers, part 7: the end of the leave. `LeaveJ.Relocated.{moves,lastPart,forward,src_back,upperMap}`
(on par-c3's closed form of the relocation), `LeaveJ.Close.{tailShape,after}`, `LeaveJ.Posted.result`,
`LeaveJ.Whole.result` (dadon's `Leave{s}Relocated`, `Leave{s}Close`, `Leave{s}Posted`, `Leave{s}Whole`), generic in the
block. Statements as in `WrapStub.lean`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.Relocated
open Partial LeaveRelocation GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- dadon's `Leave{s}Relocated.moves`. -/
abbrev moves (j : Fin 24) : List (Wire × Wire) := movesP (start j)
/-- dadon's `Leave{s}Relocated.lastPart`. -/
abbrev lastPart (j : Fin 24) : Program := GateMirror.forward (swapsG (movesP (start j)))

theorem lastPart_eq (s : Nat) : GateMirror.forward (swapsG (movesP s)) = LeaveRelocation.program (movesP s) := by
  simp only [swapsG, LeaveRelocation.program, GateMirror.forward, List.map_flatMap]; rfl

end ECDSAAdd.Entrant.StairPacket.LeaveJ.Relocated

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
attribute [local irreducible] run SkywalkNat.step

namespace Relocated
end Relocated

theorem forward_eventsG : ∀ (ps : List (Wire × Wire)) (a out : Wire),
    GateMirror.forward (eventsG a out ps) = LeaveNoSwap.block a out ps
  | [], a, out => rfl
  | (x, t) :: ps, a, out => by
    show GateMirror.forward ([.x x, .make a x t] ++ (eventsG t out ps ++ [.pop a x t, .x x])) = _
    rw [forward_app, forward_app, forward_eventsG ps t out]
    rfl

namespace Close

/-- dadon's `Leave{s}Close.tailShape`. -/
theorem tailShape (j : Fin 24) : afterLow j =
    LeaveNoSwap.block (e0P (start j) + 7) (e0P (start j) + 4) (events j) ++ Relocated.lastPart j := by
  show GateMirror.forward (leaveClose (start j)) = _
  unfold leaveClose
  rw [forward_app, forward_eventsG]
  rfl

end Close

namespace Posted
open StairArchiveTrace

end Posted

/-- The leave is the store part followed by the close. -/
theorem leave_split (j : Fin 24) : leaveP j = StoreMapped.program j ++ Close.afterLow j := by
  rw [StoreMapped.program_eq, leaveP, leaveOps_split, forward_app]

namespace Whole

end Whole

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

-- ---- w4 step 10: build-w4b/p2/src/W4BP2/Records.lean (md5 5475d2248e64) ----

/-! build-w4b (B2, owner's P2 split): `LeaveJ.RecordedParity.result`, `LeaveJ.RecordedEvents.result` for every window
block, from dadon's `Leave{225,240,255}Recorded{Parity,Events}` (PrizeScopeLeaveTickPreservedRecordsbaa4). The only
per-block content of dadon's proofs was the `rfl` reading the packet's history cells; here it is `cells_eq`.
Statements = WrapStub's, plus dadon's two hypotheses `small` and `odd` (WrapStub dropped them; without them the
recorded trace of `z` and of the shadow `Shadow.reduced sb 15 z` need not agree, `true_records` needs both). -/

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial IntegerPacket IntegerHigh SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The packet's 15 history cells as the window reads them: letter `start j+16+i`, swap flag `swaps j i`. -/
theorem cells_eq (j : Fin 24) (h1 : j.val ≤ 21) (v : BasisState) :
    ∀ (a n : Nat), a+n ≤ 15 → readCells (shape j) a n (mappedBasis j v) =
      (List.range' a n).map (fun i => (v (start j+16+i), v (swaps j i)))
  | _, 0, _ => rfl
  | a, n+1, h => by
    rw [readCells, cells_eq j h1 v (a+1) n (by omega), List.range'_succ, List.map_cons]
    congr 1
    simp only [cell, IntegerPacket.ports, mappedBasis, windowNet, net, swaps, shape]
    have e1 : OB5.sig (start j+14) (start j+a+16) = start j+16+a := by
      unfold OB5.sig start; split <;> (try unfold Wire at *) <;> omega
    have e2 : start j+a+16+1028 = start j+1044+a := by omega
    rw [e1, e2]

namespace RecordedParity
theorem result (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^(sbP (start j))) (odd : z.v % 2 = 1)
    (record : IntegerPacket.readCells (shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)) :
    LeaveJ.oddRead j s.basis = IntegerHigh.oddBits (IntegerHigh.letters 15 (Shadow.reduced (sbP (start j)) 15 z)) := by
  have ports : LeaveJ.oddRead j s.basis =
      (readCells (shape j) 0 15 (mappedBasis j s.basis)).map (fun pair => !pair.1) := by
    rw [cells_eq j h1 s.basis 0 15 (by omega), List.map_map]
    simp only [LeaveJ.oddRead, LeaveJ.ports, List.range_eq_range', Function.comp_def]
  rw [ports, record, ←true_records (sbP (start j)) z small odd g sg]
  exact LeaveTraceLetters.parity _ _ _ _ (shadow_odd _ _ small odd)
end RecordedParity

namespace RecordedEvents
open LeaveSelector
theorem result (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) (s : State) (z : SkywalkNat.State) (g sg : Bool)
    (small : min z.u z.v < 2^(sbP (start j))) (odd : z.v % 2 = 1)
    (record : IntegerPacket.readCells (shape j) 0 15 (mappedBasis j s.basis) =
      SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)) :
    let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v)
    (Close.events j).map (fun p => s.basis p.1) = (xs.take 5).map Prod.snd ∧
    (LeaveSelector.right (actualMode (sbP (start j)) z) = true → ∀ i < 15, i ≤ LeaveSelector.key (actualMode (sbP (start j)) z) →
      s.basis (LeaveJ.swaps j i) = decide (i = LeaveSelector.key (actualMode (sbP (start j)) z))) := by
  intro xs
  have cells := cells_eq j h1 s.basis 0 15 (by omega)
  have tape : (List.range 15).map (fun i => s.basis (LeaveJ.swaps j i)) = xs.map Prod.snd := by
    change _ = (SkywalkTrace.trace 15 _).map _
    rw [←record, cells, List.map_map, List.range_eq_range']
    rfl
  constructor
  · have five : (Close.events j).map (fun p => s.basis p.1) =
        ((List.range 15).map (fun i => s.basis (LeaveJ.swaps j i))).take 5 := by
      simp only [Close.events, List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
        List.cons_append, List.take_succ_cons, List.take_zero]
    rw [five, tape, List.map_take]
  · intro rightSide i hi early
    have far : Shadow.far (sbP (start j)) 15 z := by
      by_contra h
      simp [actualMode,farMode,ofFlags,right,h] at rightSide
    obtain ⟨keyEq,orientation,_⟩ := modeKey (sbP (start j)) z far
    have side : decide (2^(sbP (start j))≤z.u)=false := by rw [orientation] at rightSide; simpa using rightSide
    have keyWait : key (actualMode (sbP (start j)) z)=wait 15 z.u := by
      rw [keyEq,place,if_neg (of_decide_eq_false side)]
    have hlen : i<xs.length := by simpa only [xs,SkywalkTrace.trace_length] using hi
    have phys := congrArg (fun a : List Bool => a[i]?) tape
    have before := LeaveTraceHistory.firstSwap (sbP (start j)) z g sg small odd far side i hlen (keyWait ▸ early)
    rw [keyWait]
    exact Eq.trans (by simpa [List.getElem?_eq_getElem hlen,hi] using phys) before
end RecordedEvents

end ECDSAAdd.Entrant.StairPacket.LeaveJ
end

-- ---- w4 step 10: build-w4b/p2/src/W4BP2/PreservedA.lean (md5 b873c5376dd0) ----

/-! build-w4b (B2, owner's P2 split): `LeaveJ.PreservedRecords.result` for every window block (dadon's
`Leave{225,240,255}PreservedRecords`). dadon's per-block `swapPolarity` (a `decide` of `parityAt` on the whole leave)
becomes: the gadget segments and the relocation moves never touch the swap cells (`gadgets_free`, a copy of par-c1's
`leaveOps_box` proof with the box `hfree`), the fixed segments never target them (`fixed_targets`, one decide over the
blocks, like par-c1's `fixed_box`), and the event chain flips each of the first five twice (`events_parity`, one small
decide). -/

section
namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

/-- par-c1's leave box without the swap cells: below the history band, or above 1300 and below where the moved
history cells land (`OB5.sig (s+14) (s+1044+i) ≥ 2055-s` once moved). -/
def hfree (s q : Nat) : Prop := leaveBox s q ∧ (q < s+1044 ∨ (1300 < q ∧ q+s < 2055))

theorem swap_not_free (s i : Nat) (w1 : 75 ≤ s) (w2 : s ≤ 390) (hi : i < 15) : ¬ hfree s (OB5.sig (s+14) (s+1044+i)) := by
  unfold hfree OB5.sig; intro h; split at h <;> ((try unfold Wire at *); omega)

/-- Targets of a gate list, as the instructions see them. -/
theorem front_target_mem (g : Gate) : CodecBitSliceVerify.target (front g) ∈ g.wires := by
  cases g <;> simp [front,erase,Gate.wires,CodecBitSliceVerify.target]

theorem notarget_of_free {s : Nat} {gs : List Gate} (h : AllW (hfree s) gs) (w1 : 75 ≤ s) (w2 : s ≤ 390) (i : Nat) (hi : i < 15) :
    ∀ ins ∈ GateMirror.forward gs, CodecBitSliceVerify.target ins ≠ OB5.sig (s+14) (s+1044+i) := by
  intro ins hins e
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hins
  exact swap_not_free s i w1 w2 hi (e ▸ h g hg _ (front_target_mem g))

/-- The fixed segments of the head never target a swap cell (their controls may read one: `leaveFix4`): every target
is below the history band, or above 1300 and below the moved cells. -/
def tgtOK (s q : Nat) : Bool := decide (q < s+1044) || (decide (1300 < q) && decide (q+s < 2055))
def segT (s : Nat) (gs : List Gate) : Bool := gs.all (fun g => tgtOK s (CodecBitSliceVerify.target (front g)))
theorem swap_not_ok (s i : Nat) (w1 : 75 ≤ s) (w2 : s ≤ 390) (hi : i < 15) : tgtOK s (OB5.sig (s+14) (s+1044+i)) = false := by
  unfold tgtOK OB5.sig
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  split <;> ((try unfold Wire at *); omega)
theorem fixed_targets : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 →
    segT (start j) (leaveFix0 (start j) (sbP (start j)) ++ leaveFix1 (start j) (sbP (start j)) ++
      leaveFix2 (start j) (sbP (start j)) ++ leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j)) ++
      leaveFix5 (start j) (sbP (start j)) ++ leaveFix8 (start j) (sbP (start j)) ++ leaveFix10 (start j) (sbP (start j)) ++
      leaveFix11 (start j) (sbP (start j)) ++ leaveFix12 (start j) (sbP (start j)) ++ lowSign (start j)) = true := by
  decide +kernel

/-- The event chain of the close flips each of the first five swap cells twice and targets no other. -/
theorem events_parity : ∀ j : Fin 24, 1 ≤ j.val → j.val ≤ 21 → ∀ i : Fin 15,
    LeaveSelector.parityAt (OB5.sig (start j+14) (start j+1044+i.val))
      (GateMirror.forward (eventsG (e0P (start j) + 7) (e0P (start j) + 4)
        [(OB5.sig (start j+14) (start j+1044), 1556), (OB5.sig (start j+14) (start j+1045), 1559),
         (OB5.sig (start j+14) (start j+1046), 1560), (OB5.sig (start j+14) (start j+1047), 1561),
         (OB5.sig (start j+14) (start j+1048), 1562)])) = some false := by
  decide +kernel

end ECDSAAdd.Entrant.StairPacket.Partial
end

-- ---- w4 step 10: build-w4b/p2/src/W4BP2/PreservedB.lean (md5 25300300f485) ----

section
namespace ECDSAAdd.Entrant.StairPacket.Partial
open GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run measurementCount leaveFix0 leaveFix1 leaveFix2 leaveFix3 leaveFix4 leaveFix5 leaveFix8
  leaveFix10 leaveFix11 leaveFix12 lowSign leaveAdjust leaveBarrel leaveJoin lowRest leaveStoreMapped leaveLowClose
  eventsG swapsG movesP

theorem keep_append (P Q : Program) (q : Wire) (hP : ∀ m s, (run P m s).basis q = s.basis q)
    (hQ : ∀ m s, (run Q m s).basis q = s.basis q) (m : List Bool) (s : State) : (run (P ++ Q) m s).basis q = s.basis q := by
  rw [run_append, hQ, hP]

end ECDSAAdd.Entrant.StairPacket.Partial
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial IntegerPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] leaveP run
namespace PreservedRecords
end PreservedRecords
end ECDSAAdd.Entrant.StairPacket.LeaveJ
end

-- ---- w4 step 10: build-w4b/p2/src/W4BP2/EndWords.lean (md5 56b6fdb1398c) ----

/-! build-w4b (B2, owner's P2 split): `LeaveJ.EndWords.result` for every window block (dadon's `Leave{s}EndWords`),
from the prover's `Whole.result`, `StoreMapped.result`, `BeforeStore.result`, `StoreCoordinates.result` (ParC1.Wrap3..7)
and par-c3's relocation closed forms (`src_out`, `Relocated.upperMap`). dadon's per-block `decide`s on
`LeaveRelocation.source moves` become `src_back` (the three flag sites) and `src_out` (the untouched sites). -/

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.Relocated
open Partial LeaveRelocation
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

end ECDSAAdd.Entrant.StairPacket.LeaveJ.Relocated
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial SkywalkNat LeaveSelector IntegerHigh
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
attribute [local irreducible] run SkywalkNat.step

namespace EndWords
end EndWords

end ECDSAAdd.Entrant.StairPacket.LeaveJ
end

-- ==== end PrizeTail10d9efffc.b ====

-- ==== begin PrizeTail752d1574c ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225EndWords
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave225EndWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave240Word

end ECDSAAdd.Entrant.StairPacket.Leave240BoundaryClean

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240EndWords
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave240EndWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BoundaryClean
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open Leave255Word

end ECDSAAdd.Entrant.StairPacket.Leave255BoundaryClean

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255EndWords
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave255EndWords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ReleasedOrigin
open Arithmetic MappedCompressed WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave255ReleasedOrigin

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket EnterProof WideReference
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
namespace NativePack225
end NativePack225
namespace NativePack240
end NativePack240
namespace NativePack255
end NativePack255



end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave225BoundaryRails

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225PreservedRecords
open LeaveSelector LeaveReadoutFrame Arithmetic IntegerPacket Partial LeaveCompanion LeaveCompanion225 Leave225Front Leave225Selector
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave225PreservedRecords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave240BoundaryRails

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240PreservedRecords
open LeaveSelector LeaveReadoutFrame Arithmetic IntegerPacket Partial LeaveCompanion LeaveCompanion240 Leave240Front Leave240Selector
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave240PreservedRecords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BoundaryRails
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open MappedCompressed
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave255BoundaryRails

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255PreservedRecords
open LeaveSelector LeaveReadoutFrame Arithmetic IntegerPacket Partial LeaveCompanion LeaveCompanion255 Leave255Front Leave255Selector
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

end ECDSAAdd.Entrant.StairPacket.Leave255PreservedRecords

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave225ActualHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave225AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave240ActualHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave240AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ActualHistory
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000

open IntegerPacket
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave255ActualHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255AssembleCut
open Arithmetic WideReference RailPair
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.Leave255AssembleCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ReleasedActual
open Arithmetic MappedCompressed IntegerPacket WideReference EnterProof NativePack255 Partial LeaveReadoutFrame
set_option maxRecDepth 32000
set_option maxHeartbeats 2700000

end ECDSAAdd.Entrant.StairPacket.Leave255ReleasedActual

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave225Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

end ECDSAAdd.Entrant.StairPacket.Leave225FrameHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave240Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

end ECDSAAdd.Entrant.StairPacket.Leave240FrameHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
open IntegerPacket
open MappedCompressed IntegerPacket SkywalkRails
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave255Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

end ECDSAAdd.Entrant.StairPacket.Leave255FrameHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion225 PortalValues Leave225Barrel Leave225High HighBankBarrel
open Leave225Front LeaveSelector Leave225Selector Leave225OutputPorts LeaveReadoutFrame IntegerHigh Leave225Close
open Leave225Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave225Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave225CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion240 PortalValues Leave240Barrel Leave240High HighBankBarrel
open Leave240Front LeaveSelector Leave240Selector Leave240OutputPorts LeaveReadoutFrame IntegerHigh Leave240Close
open Leave240Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave240Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave240CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255Admission
open Arithmetic Partial LeaveCompanion LeaveCompanion255 PortalValues Leave255Barrel Leave255High HighBankBarrel
open Leave255Front LeaveSelector Leave255Selector Leave255OutputPorts LeaveReadoutFrame IntegerHigh Leave255Close
open Leave255Relocated StairArchiveTrace
open IntegerPacket
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.Leave255Admission

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option maxRecDepth 40000
set_option maxHeartbeats 4500000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave255CertifiedCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run measurementCount onRails
end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run measurementCount onRails
open ArchiveBoundary240
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof
set_option maxRecDepth 25000
attribute [local irreducible] run measurementCount onRails
open ArchiveBoundary255
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Leave225ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Leave240ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 2300000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Leave255ArchiveCut

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference
attribute [local irreducible] run SkywalkNat.step onRails
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference
attribute [local irreducible] run SkywalkNat.step onRails
namespace NativePack240
open ArchiveBoundary240
end NativePack240
namespace NativePack255
open ArchiveBoundary255
end NativePack255
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockRows
open Arithmetic IntegerPacket SkywalkRails WideReference StairArchiveRaw StairArchiveTrace CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 16000

def Chronology (i x p row:Nat) : Prop :=
  ∀q:Fin 20,(rawCol q).testBit row=letterBit (read ((SkywalkTrace.trace 15 (WideReference.canonical i x p)).drop 5) (q.val/2)) q

end ECDSAAdd.Entrant.StairPacket.ArchiveStockRows

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffix
open Arithmetic MappedCompressed
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
end ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffix

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave225BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack225 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave225BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave240BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack240 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave240BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.Leave255BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial NativePack255 LeaveSelector
set_option maxRecDepth 35000
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.Leave255BodyCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchivePersistence
open Arithmetic MappedCompressed IntegerPacket EnterProof ArchivePortAction ArchiveStockSuffix WideReference CodecBitSliceVerify Partial
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.ArchivePersistence

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack225
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed
set_option maxRecDepth 35000
set_option maxHeartbeats 3500000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativePack225

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack240
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference Partial ArchiveBoundary240
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.NativePack240

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack255
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference Partial ArchiveBoundary255
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run SkywalkNat.step
end ECDSAAdd.Entrant.StairPacket.NativePack255

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveWindowPreserve
open Arithmetic IntegerPacket Partial ArchivePortAction WideReference LeaveReadoutFrame
set_option maxRecDepth 60000
set_option maxHeartbeats 5000000

def bank (ps:Ports):List Wire:=(List.finRange 16).map (fun j=>ps ⟨j.val,by omega⟩)
theorem keep {d:Bool} {row:Nat} {s t:State} {ps:Ports} (h:Kept ps d row s)
    (stable:∀q∈bank ps,t.basis q=s.basis q) : Kept ps d row t := by
  intro i
  rw [stable _ (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩),h i]

end ECDSAAdd.Entrant.StairPacket.ArchiveWindowPreserve

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 25000
attribute [local irreducible] run SkywalkNat.step

def signedAt (i x p:Nat) (g s:Bool) := encode g s (unsigned i x p).u (unsigned i x p).v
def flagNeg (i x p:Nat) (sg:Bool) := PortalValues.negative sg (unsigned i x p).u
def farAt (b i x p:Nat) := Shadow.far b 15 (unsigned i x p)
instance (b i x p:Nat) : Decidable (farAt b i x p) := by unfold farAt;infer_instance

theorem readInput (i x p:Nat) (raw:State) (g sg:Bool) (h:InputAt i (signedAt i x p g sg) raw) :
    SkywalkIntegerInput (W.compactSkywalkTickLayout base i) (signedAt i x p g sg).a (signedAt i x p g sg).b g raw.basis := by
  have eq:(signedAt i x p g sg).g=g:=by cases g <;> rfl
  unfold InputAt at h
  rwa [eq] at h

theorem stepInput_gen (i b x p:Nat) (lo:15 ≤ i) (hi:i+15<512) (good:Bounds x p)
    (raw v:State) (g sg:Bool) (domain:Domain i x p raw) (input:InputAt i (signedAt i x p g sg) raw)
    (small:min (unsigned i x p).u (unsigned i x p).v<2^b) :
    let next:=SharedSigned.flags g sg (SkywalkTrace.trace 15 (signedAt i x p g sg))
    Domain (i+15) x p (endRaw i raw v) ∧ InputAt (i+15) (signedAt (i+15) x p next.1 next.2) (endRaw i raw v) := by
  exact ⟨advance_gen i x p lo (Nat.le_of_lt hi) good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw v domain,
    (advance_signed_gen i b x p lo hi good raw v domain g sg input small).2⟩
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed
attribute [local irreducible] run measurementCount

def Checked (F R:Program) (pre post:State→Prop) := ∀s m,pre s →
  let out:=run F m s
  out.phase=s.phase ∧ post out ∧ ∀n,run R n out=s

theorem composition {F R F' R':Program} {A B C:State→Prop}
    (left:Checked F R A B) (right:Checked F' R' B C) : Checked (F++F') (R'++R) A C := by
  intro s m h
  obtain ⟨ph,mid,undo⟩:=left s m h
  obtain ⟨ph',post,undo'⟩:=right _ (m.drop (measurementCount F)) mid
  dsimp only
  rw [run_append,run_take]
  refine ⟨ph'.trans ph,post,?_⟩
  intro n
  rw [run_append,run_take,undo',undo]

theorem pair {F R F' R':Program} {A B:State→Prop}
    (law:∀s m, A s →
      let first:=run F m s
      let out:=run F' (m.drop (measurementCount F)) first
      out.phase=s.phase ∧ B out ∧ (∀k,run R' k out=first) ∧ (∀k,run R k first=s)) :
    Checked (F++F') (R'++R) A B := by
  intro s m h
  obtain ⟨ph,post,inv,inv'⟩:=law s m h
  dsimp only
  rw [run_append,run_take]
  refine ⟨ph,post,?_⟩
  intro n
  rw [run_append,run_take,inv,inv']

theorem cutPhase {lo hi:List (Wire×Wire)} {g n f u:Wire} {neg far long:Bool}
    {sig:Wire→Wire} {raw s:State} {pending:List Wire}
    (cut:PackedCut lo hi g n f u neg far long (pullState sig raw) (eraseSites pending s)) :
    s.phase=raw.phase := cut.phase

end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end


end
-- ==== end PrizeTail752d1574c ====

-- ==== begin PrizeTail2024ba497 ====
section



end
-- ==== w4: build-w4b B2-a WindowChain + StrongChainW (b2a/src) ====
-- BEGIN par-d WindowChain
section

namespace ECDSAAdd.Entrant.StairPacket.WindowChain
open Arithmetic MappedCompressed WindowFold StockWindowTicket
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! The window's stock chain as a fold over its blocks (par-d, Job D). Block steps come from the generic
per-block families (par-c2): `Ready t` is the hand-off predicate at the start tick `t` of a block (or at the exit
tick), the first form opens the window at `start j`, the last form closes it at `exitTick`. -/

theorem checked_nil (A : State → Prop) : Checked [] [] A A := by
  intro s m h
  exact ⟨rfl,h,fun _ => rfl⟩

theorem chain_checked (P : Pieces Program) (d : Bool) (Ready : Nat → State → Prop) :
    ∀ (i : Fin 24) (js : List (Fin 24)), Consec i js →
    (∀ i k : Fin 24, k ∈ js → k.val=i.val+1 →
      Checked (nextF P d i k).flatten (nextR P d i k).flatten (Ready (start k)) (Ready (start k+15))) →
      Checked (chainF P d i js).flatten (chainR P d i js).flatten (Ready (start i+15)) (Ready (lastStart i js+15))
  | i, [], _, _ => by
    simp only [chainF,chainR,List.flatten_nil,lastStart]
    exact checked_nil _
  | i, j :: js, ⟨next,rest⟩, step => by
    have here : start i+15=start j := by simp only [StairPacket.start]; omega
    have tail := chain_checked P d Ready j js rest
      (fun a b hb hab => step a b (List.mem_cons.mpr (Or.inr hb)) hab)
    simp only [chainF,chainR,List.flatten_append,lastStart]
    rw [here]
    exact composition (step i j (List.mem_cons.mpr (Or.inl rfl)) next) tail

/-- The window from its three forms: first block (with the entry portal), the interior/last block chain, exit. -/
theorem window_checked (P : Pieces Program) (d : Bool) (Ready : Nat → State → Prop) (Before Final : State → Prop)
    (j : Fin 24) (js : List (Fin 24)) (consec : Consec j js)
    (first : Checked (P.portal (start j) :: firstF P d j).flatten (firstR P d j ++ [P.portalInv (start j)]).flatten
      Before (Ready (start j+15)))
    (step : ∀ i k : Fin 24, k ∈ js → k.val=i.val+1 →
      Checked (nextF P d i k).flatten (nextR P d i k).flatten (Ready (start k)) (Ready (start k+15)))
    (last : Checked (exitF P d (exitTick j js)).flatten (exitR P d (exitTick j js)).flatten
      (Ready (exitTick j js)) Final) :
    Checked (forwardW P d j js) (reverseW P d j js) Before Final := by
  have chain := chain_checked P d Ready j js consec step
  have all := composition first (composition chain last)
  have f : forwardW P d j js = (P.portal (start j) :: firstF P d j).flatten ++
      ((chainF P d j js).flatten ++ (exitF P d (exitTick j js)).flatten) := by
    simp only [forwardW,forwardL,List.flatten_cons,List.flatten_append,List.append_assoc]
  have r : reverseW P d j js = ((exitR P d (exitTick j js)).flatten ++ (chainR P d j js).flatten) ++
      (firstR P d j ++ [P.portalInv (start j)]).flatten := by
    simp only [reverseW,reverseL,List.flatten_append,List.append_assoc]
  rw [f,r]
  exact all

end ECDSAAdd.Entrant.StairPacket.WindowChain

end

-- BEGIN par-d2 StrongChainW (Tail2024, after par-d's WindowChain)
section

namespace ECDSAAdd.Entrant.StairPacket.WindowChain
open Arithmetic MappedCompressed WindowFold StockWindowTicket
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! par-d2 (job D2): dadon's `StockStrongChain`, generic over the window's blocks. The strong chain is par-d's
`window_checked` run with a richer hand-off predicate: `ReadyS t` is `Ready t` together with the saved keys of
every block whose archive was loaded before tick `t`. That is block `i` with `i+2 ≤ blockOf t`, since block
`i`'s archive is loaded inside block `i+1`. The per-block obligations are:
- `receipt`: block `k = i+1` saves the key of block `i`. This is par-c2's `selected_receipt` plus the keep
  through `leave k`.
- `keep`: the step of block `k` keeps the older keys (`ArchiveWindowPreserve`, generic through par-c1's leave
  footprint).
- `keepLast`: the exit pieces keep all keys.
dadon's `selected225/240/255` and `final` are these steps at n = 3 and 4. -/

/-- Block index of a block start tick. -/
def blockOf (t : Nat) : Nat := (t-75)/15
/-- Keys saved by tick `t`: blocks `j1 ≤ i` whose archive was loaded before `t`. -/
def SavedAt (Key : Fin 24 → State → Prop) (j1 t : Nat) (s : State) : Prop :=
  ∀ i : Fin 24, j1 ≤ i.val → i.val+2 ≤ blockOf t → Key i s
def ReadyS (Ready : Nat → State → Prop) (Key : Fin 24 → State → Prop) (j1 t : Nat) (s : State) : Prop :=
  Ready t s ∧ SavedAt Key j1 t s

theorem blockOf_start (j : Fin 24) : blockOf (start j)=j.val := by simp only [blockOf,start]; omega
theorem blockOf_next (j : Fin 24) : blockOf (start j+15)=j.val+1 := by simp only [blockOf,start]; omega

/-- First block: no archive has been loaded yet. -/
theorem first_strong {F R : Program} {Before : State → Prop} (Ready : Nat → State → Prop)
    (Key : Fin 24 → State → Prop) (j : Fin 24) (first : Checked F R Before (Ready (start j+15))) :
    Checked F R Before (ReadyS Ready Key j.val (start j+15)) := by
  intro s m h
  obtain ⟨ph,post,undo⟩:=first s m h
  refine ⟨ph,⟨post,?_⟩,undo⟩
  intro i h1 h2
  rw [blockOf_next] at h2
  omega

/-- Block `k = i+1`: saves block `i`'s key and keeps the older ones, on top of its plain step. -/
theorem step_strong (P : Pieces Program) (d : Bool) (Ready : Nat → State → Prop) (Key : Fin 24 → State → Prop)
    (j1 : Nat) (i k : Fin 24) (hk : k.val=i.val+1)
    (step : Checked (nextF P d i k).flatten (nextR P d i k).flatten (Ready (start k)) (Ready (start k+15)))
    (receipt : ∀ s m, Ready (start k) s → Key i (run (nextF P d i k).flatten m s))
    (keep : ∀ s m, Ready (start k) s → ∀ i' : Fin 24, j1 ≤ i'.val → i'.val< i.val → Key i' s →
      Key i' (run (nextF P d i k).flatten m s)) :
    Checked (nextF P d i k).flatten (nextR P d i k).flatten (ReadyS Ready Key j1 (start k))
      (ReadyS Ready Key j1 (start k+15)) := by
  intro s m h
  obtain ⟨ph,post,undo⟩:=step s m h.1
  refine ⟨ph,⟨post,?_⟩,undo⟩
  intro i' h1 h2
  rw [blockOf_next] at h2
  by_cases e:i'.val=i.val
  · have same:i'=i:=Fin.ext e
    subst same
    exact receipt s m h.1
  · apply keep s m h.1 i' h1 (by omega)
    apply h.2 i' h1
    rw [blockOf_start]
    omega

/-- The exit: the keys stay through the exit pieces. -/
theorem last_strong {F R : Program} {Final : State → Prop} (Ready : Nat → State → Prop)
    (Key : Fin 24 → State → Prop) (j1 e : Nat) (last : Checked F R (Ready e) Final)
    (keep : ∀ s m, Ready e s → ∀ i : Fin 24, j1 ≤ i.val → i.val+2 ≤ blockOf e → Key i s → Key i (run F m s)) :
    Checked F R (ReadyS Ready Key j1 e) (fun s=>Final s ∧ SavedAt Key j1 e s) := by
  intro s m h
  obtain ⟨ph,post,undo⟩:=last s m h.1
  exact ⟨ph,⟨post,fun i h1 h2=>keep s m h.1 i h1 h2 (h.2 i h1 h2)⟩,undo⟩

/-- `StockStrongChain` for any window: the window keeps every block's key up to the exit. -/
theorem window_strong (P : Pieces Program) (d : Bool) (Ready : Nat → State → Prop) (Key : Fin 24 → State → Prop)
    (Before Final : State → Prop) (j : Fin 24) (js : List (Fin 24)) (consec : Consec j js)
    (first : Checked (P.portal (start j) :: firstF P d j).flatten (firstR P d j ++ [P.portalInv (start j)]).flatten
      Before (Ready (start j+15)))
    (step : ∀ i k : Fin 24, k ∈ js → k.val=i.val+1 →
      Checked (nextF P d i k).flatten (nextR P d i k).flatten (Ready (start k)) (Ready (start k+15)))
    (receipt : ∀ i k : Fin 24, k ∈ js → k.val=i.val+1 → ∀ s m, Ready (start k) s →
      Key i (run (nextF P d i k).flatten m s))
    (keep : ∀ i k : Fin 24, k ∈ js → k.val=i.val+1 → ∀ s m, Ready (start k) s → ∀ i' : Fin 24, j.val ≤ i'.val →
      i'.val< i.val → Key i' s → Key i' (run (nextF P d i k).flatten m s))
    (last : Checked (exitF P d (exitTick j js)).flatten (exitR P d (exitTick j js)).flatten
      (Ready (exitTick j js)) Final)
    (keepLast : ∀ s m, Ready (exitTick j js) s → ∀ i : Fin 24, j.val ≤ i.val → i.val+2 ≤ blockOf (exitTick j js) →
      Key i s → Key i (run (exitF P d (exitTick j js)).flatten m s)) :
    Checked (forwardW P d j js) (reverseW P d j js) Before (fun s=>Final s ∧ SavedAt Key j.val (exitTick j js) s) :=
  window_checked P d (ReadyS Ready Key j.val) Before _ j js consec
    (first_strong Ready Key j first)
    (fun i k hm hk=>step_strong P d Ready Key j.val i k hk (step i k hm hk) (receipt i k hm hk) (keep i k hm hk))
    (last_strong Ready Key j.val _ last keepLast)

theorem checked_mono {F R : Program} {A B C : State → Prop} (h : Checked F R A B) (imp : ∀ s, B s → C s) :
    Checked F R A C := by
  intro s m pre
  obtain ⟨ph,post,undo⟩:=h s m pre
  exact ⟨ph,imp _ post,undo⟩

end ECDSAAdd.Entrant.StairPacket.WindowChain

end
-- END par-d2 StrongChainW
-- END par-d WindowChain
-- ==== w4: end strongchain ====

-- ==== end PrizeTail2024ba497 ====

-- ===== odd division cell on packets 1..45 =====
-- Odd-word half-cell laws and odd packets (P1Life, DirectPass, RouteA), the odd division slice on packets 1..45
-- (slice45) with its frames, counts and slots, and the cell lemmas used by the window.
-- Credit: odd-word cell spariev (8572aff9); window code dadon (0923a0d6 / 3b1a7f50).

-- ===== P1Cell =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Junction =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassCoherent =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassLiteral =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassMapped =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldFlags =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldWindow =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassContracts =====
section
namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldMath =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFold =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassShift =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassUnfold =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassUnshift =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareLeaf =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareChain =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareWindow =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCarryHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRawHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRaw =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRawTriple =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompare =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassComparePrepare =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareModes =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareView =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassFoldView =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassLowFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassCompareBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassUnbias =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassDependent =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassDependentPrefix =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassDependentLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubHead =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubLayout =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubInner =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRawBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass

end -- ticket 8 pasted module

-- ===== PassSubFinish =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSubBoundary =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSignedMagnitude =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassPrepareSign =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField

end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassRestoreSign =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== PassSeed =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1OddRep =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


end ECDSAAdd.Entrant.P1Life



end -- ticket 8 pasted module

-- ===== P1FoldMath =====
section
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1CompareMath =====
section
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1ShortMath =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


end ECDSAAdd.Entrant.P1Life


end -- ticket 8 pasted module

-- ===== P1BiasMath =====
section
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1RawMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Raw =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1RawBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Seed =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1SignFrames =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Chunks =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassShortLiteral =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1Short =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1ShortBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassFlipBias =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1FoldView =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1CompareBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Unbias =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1InverseBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1FoldBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1UnfoldBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1SubBoundary =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1Kernel =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== PassKernelFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1KernelFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== PassHalfFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.DirectPass
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.DirectPass
end -- ticket 8 pasted module

-- ===== P1HalfFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1RecodeMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1RecodeBits =====
section
namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1RecodeCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1RecodeLayout =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1RecodeTriple =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


























































end ECDSAAdd.Entrant.P1Life



end -- ticket 8 pasted module

-- ===== P1JunctionMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionViews =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionPasses =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1JunctionChains =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionKernelFrame =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionCompose =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1CountCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1PassCounts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Counts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1JunctionCountCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1JunctionCounts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1ResourceCoherent =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceTop =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceCompare =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceLayout =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceEnds =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceActive =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceData =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceSmall =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceViews =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceTails =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceRaw =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceSub =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceComparePass =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceFold =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1ResourceChains =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1Resources =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1ResourcePorts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life


end -- ticket 8 pasted module

-- ===== P1CenterMath =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== P1CenterViews =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end -- ticket 8 pasted module

-- ===== P1CenterCorrect =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life

end -- ticket 8 pasted module

-- ===== RouteASlotCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines


end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotChains =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines


end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotShape =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic


end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotPasses =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines
attribute [local irreducible] Q6LifetimeResearch.half Q6LifetimeResearch.forward Q6LifetimeResearch.inverse


end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotBodies =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines
attribute [local irreducible] Q6LifetimeResearch.half Q6LifetimeResearch.forward Q6LifetimeResearch.inverse


end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotJunctions =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines MappedCompressed
attribute [local irreducible] Q6LifetimeResearch.half Q6LifetimeResearch.forward Q6LifetimeResearch.inverse


end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASlotShift =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines
attribute [local irreducible] gateSlots


end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteASchedule =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed
open ECDSAAdd.Entrant.Rolling1588


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
  MappedCompressed Challenge RecordedQuantum Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAStageFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteACutFrames =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
  MappedCompressed Challenge RecordedQuantum Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteABodyFacts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAHalfLoan =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteASelected =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteACell =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
  OffsetBorrowedCanonical Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588


end -- ticket 8 pasted module

-- ===== RouteARegularCell =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteARegularPacket =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteASupport =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAGroups =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteALastDivide =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteADivideGroups =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 BalancedField CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteASupportOld =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum
attribute [local irreducible] wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAFreeWires =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteARegularFree =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAResourcePhysical =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField MappedCompressed Challenge Baselines RecordedQuantum
attribute [local irreducible] GatePhysical
attribute [local irreducible] JointForward1588.paddedGD JointInverse1588.paddedD


namespace Rolling1588
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] entryField exitField entryTail exitHead


section
attribute [local irreducible] SW.selW FrontierSW1591.swapBody
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.triple
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.e3 ECDSAAdd.Entrant.Rolling1588.d3
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.e3short ECDSAAdd.Entrant.Rolling1588.d3short


end


end Rolling1588
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteAResourceSupportCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical DirectSkywalk Challenge RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires run
attribute [local irreducible] ControlLoan1589.cell ControlLoan1589.halfWindow ControlLoan1589.groups








end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAResourceCounts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] toffoliCount measurementCount


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAFieldSlotDeltas =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed BalancedCircuit BalancedField Challenge Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] gateSlots


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module


-- ===== RouteAOddPrefix (M1a: odd division slice, packets 1..84) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== RouteARecordHalfLower (support bridge: footprint minus 760 inside the record half) =====
section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum
attribute [local irreducible] ECDSAAdd.wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


-- ===== odd45: the odd division slice on packets 1..45 =====
/-
# odd45: odd division slice on packets 1..45

The window needs standard words in the first staircase group's packets 46..53.  The odd division slice
therefore runs `dstart` in packet 1, ordinary odd packets 2..44 and `dend` in packet 45 (`slice45`),
followed by the record packets 46..84 (`dslice`).  It saves 164 T / 389 M against the record packets.
`dendBasePacket` is the division packet with its last cell on `dend`, generic in `j` (`basePacket`
fixes the `dend` packet at `j = 84`).
-/
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== cell support: the hosted odd45 slice is physical, stays inside the
-- record packets 1..45 and, on a record cut frame at cut 1, ends where the record packets 1..45 end =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Challenge RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] GatePhysical

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairLoanGroupSupport
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
attribute [local irreducible] wires StairLoan.half760Loan StairGroups.halfWindow StairGroups.cell Rolling1588.onPacket

end ECDSAAdd.Entrant.StairLoanGroupSupport
end

-- ===== end odd division cell =====

-- ==== part MCell ====
/-!
# Multiplication junction half `mstart`: standard words in, odd words out

The mirror of `P1Life.mend`.  The recoder first puts `Y` into the odd-word code; the word `X`
is accepted in the standard code by the record's sign preparation and literal normalisation,
followed by one complement of the low register (the standard normalised value and the odd
normalised value of the same field element are complements of each other); the rest of the
half is the odd-word comparison, unfolding and raw subtraction of `P1Life.inverse`.

Cost: 254 (recoder) + 254 (literal normalisation) + 766 = 1,274 Toffolis.
-/

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField

end ECDSAAdd.Entrant.P1Life
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField

end ECDSAAdd.Entrant.P1Life
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField




end ECDSAAdd.Entrant.P1Life
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines MappedCompressed




end ECDSAAdd.Entrant.RouteA
end


/-!
# Multiplication junction half `mstart`: standard words in, odd words out

The mirror of `P1Life.mend`.  The recoder first puts `Y` into the odd-word code; the word `X`
is accepted in the standard code by the record's sign preparation and literal normalisation,
followed by one complement of the low register (the standard normalised value and the odd
normalised value of the same field element are complements of each other); the rest of the
half is the odd-word comparison, unfolding and raw subtraction of `P1Life.inverse`.

Cost: 254 (recoder) + 254 (literal normalisation) + 766 = 1,274 Toffolis.
-/

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField










end ECDSAAdd.Entrant.P1Life
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


end ECDSAAdd.Entrant.P1Life
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField

end ECDSAAdd.Entrant.P1Life
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField Challenge Baselines MappedCompressed

end ECDSAAdd.Entrant.RouteA
end


/-!
# Kernel checks for the odd-word head

Static facts about the odd-word cells used by the head and the tail (`P1Life.half`,
`P1Life.dstart`, `P1Life.dend`, `P1Life.mstart`, `P1Life.mend`, all at the record placement
`base 760`):

* the zero tracker of `StairField13V3ZT` on the 44 exclusive roles.  Only the resetting
  suffix of each cell is evaluated (its last ripple pass; for the ordinary half the last two,
  because the short constant adder does not use the two highest roles);
* the record half `R2Life760.half760 true` mentions every wire of the cell footprint.  Only
  five top-level pieces of the record half are scanned, into one bit mask.

No program run is evaluated.
-/

section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ECDSAAdd.Entrant.StairOddHead

open ECDSAAdd Arithmetic Challenge MappedCompressed
open StairField13V3Clean

end ECDSAAdd.Entrant.StairOddHead

end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 BalancedField CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


-- ===== mslice45: the odd multiplication slice on packets 45..1 =====
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed BalancedField
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires onPacket

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] toffoliCount measurementCount

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] toffoliCount measurementCount



end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed BalancedCircuit BalancedField Challenge Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] gateSlots

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Challenge Baselines RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] GatePhysical

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Challenge Baselines RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed BalancedField
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires onPacket

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed BalancedField
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires onPacket

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ==== build-chain: par-c3 Glue first half (proof-q1542 GlueA) ====
/-! The first half of par-c3's generic Glue on the relocated tree (proof-q1542): helpers, ActualHistory,
HighZero, BoundaryRails. Body copied from helpers/proof-q1542/win/src/ParC3/GlueA.lean (which compiles real on the
dadon-388 base); the second half (BoundaryClean, FrameHistory, ReleasedActual, Admission.roundtrip) is build-w4b's.
-/
section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial SkywalkNat GateMirror
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

theorem row_free (j : Fin 24) (i : Nat) (hi : i < 18) :
    (LeaveJ.row j ⟨i, hi⟩).free = if i < lowsP (start j) then bankW (start j) i else a0P (start j) + i := by
  simp only [LeaveJ.row, LeaveJ.cols, columnsP, HighBankJoin.Column.free, List.getElem_map, List.getElem_range]
  by_cases h : i < lowsP (start j) <;> simp [h]

theorem not_low (j : Fin 24) (q : Wire)
    (h : (q < a0P (start j) - 1 ∨ a0P (start j) + lowsP (start j) ≤ q) ∧ (q < b0P (start j) - 1 ∨ b0P (start j) + lowsP (start j) ≤ q)) :
    q ∉ RailPair.sites (Close.low j) := by
  intro hm
  obtain ⟨i, hi, e⟩ := (Close.mem_low_sites j q).mp hm
  have ha : 1 ≤ a0P (start j) := by unfold a0P; omega
  have hb : 1 ≤ b0P (start j) := by unfold b0P; omega
  unfold Wire at *
  omega

theorem not_history (j : Fin 24) (q : Wire) (h : q < start j + 16 ∨ start j + 30 < q) : q ∉ Close.history j := by
  intro hm
  simp only [Close.history, LeaveJ.history, List.mem_map, List.mem_range] at hm
  obtain ⟨i, hi, e⟩ := hm
  ((try unfold Wire at *); omega)

end ECDSAAdd.Entrant.StairPacket.LeaveJ


namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.ActualHistory
open Arithmetic Partial SkywalkNat StairArchiveTrace
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.ActualHistory


namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.HighZero
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.HighZero


namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.BoundaryRails
open Arithmetic Partial SkywalkNat MappedCompressed
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.BoundaryRails

end

-- ==== build-chain: par-c3 Glue second half (build-w4b GlueB, finished by build-chain) ====
/-! par-c3 glue, second half: `LeaveJ.BoundaryClean`, `AssembleCut.leftovers`, `LeaveJ.FrameHistory`,
`LeaveJ.ReleasedActual`, `LeaveJ.Admission.Inputs.roundtrip`. From `helpers/par-c3/src/ParC3/Glue.lean`. -/

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.BoundaryClean
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

/-- dadon's `Leave{s}BoundaryClean.zeros` (225: 1556..1712, 1719..1812; 255 adds the freed B top 1029..1042 and
stops below its own moved history at 2055-s). -/
def zeros (j : Fin 24) : List Nat :=
  List.range' 1556 (e0P ((start j) + 15) + 3 - 1556) ++
  List.range' (e0P ((start j) + 15) + 9) (min 1813 (2055 - (start j)) - (e0P ((start j) + 15) + 9)) ++
  List.range' (bTopP ((start j) + 15) + 1) (bTopP (start j) - bTopP ((start j) + 15))

/-- dadon's `retired` (255/210: plus the live bank sites above the next rail, `F < 2^(R(s+15)-sb-1)`). -/
def retired (j : Fin 24) (q : Nat) : Prop :=
  q = e0P (start j) + 4 ∨ (q ≠ e0P (start j) + 4 ∧ q ∉ RailPair.sites (Close.low j) ∧ q ∉ Close.history j ∧
  (q = 1556 ∨ (q ≠ 1556 ∧ q ≠ 1557 ∧ q ≠ 1558 ∧
   ((q ∈ CoreCheckpoint.targets j ∧ q ∉ LeaveJ.smallM j) ∨
    ∃ i : Fin (railP (start j) - railP ((start j) + 15)), q = LeaveJ.live j (wpP (start j) + 15 - (railP (start j) - railP ((start j) + 15)) + i.val)))))

end ECDSAAdd.Entrant.StairPacket.LeaveJ.BoundaryClean


namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.AssembleCut
/-- TEMP copy of par-c2's generic `Leave{s}AssembleCut.leftovers` (agreed 23:30Z); delete when par-c2's lands. -/
def leftovers (j : Fin 24) (q : Wire) : Prop :=
  ((start j) + 15 ≤ q ∧ q < (start j) + 31) ∨ (1044 + (start j) ≤ q ∧ q < 1059 + (start j)) ∨ ReleasedOrigin.releasedSite j q ∨
  (2055 ≤ q + (start j) ∧ q + (start j) ≤ 2069 ∧ q ≤ 1812)
end ECDSAAdd.Entrant.StairPacket.LeaveJ.AssembleCut

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.FrameHistory
open Arithmetic IntegerPacket MappedCompressed WideReference SkywalkRails Partial LeaveSelector
attribute [local irreducible] run SkywalkNat.step
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.LeaveJ.FrameHistory

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.ReleasedActual
open Arithmetic MappedCompressed WideReference Partial
attribute [local irreducible] run SkywalkNat.step
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.LeaveJ.ReleasedActual

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.Admission
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.Admission

end

-- ==== leave-move: c9cc6a76 R1 on the generic leave — the move bridge from the leave input ====
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror RecordedQuantum HighBankFirstHit LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

theorem moveA_split (s : Nat) : moveA s =
    entryOps s ++ ((leaveFix3 s (sbP s) ++ leaveFix4 s (sbP s)) ++ (leaveFix5 s (sbP s)).take 27) := by
  unfold moveA entryOps; simp only [List.append_assoc]

theorem fullPrefix_split (j : Fin 24) : fullPrefix j =
    ((leaveFix3 (start j) (sbP (start j)) ++ leaveFix4 (start j) (sbP (start j))) ++
      (leaveFix5 (start j) (sbP (start j))).take 27) ++ (leaveFix5 (start j) (sbP (start j))).drop 27 := by
  unfold fullPrefix; rw [List.append_assoc _ ((leaveFix5 _ _).take 27), List.take_append_drop]

/-- In front of the mux: the crossing wire is still clean (nothing in the selector prefix writes it). -/
theorem prefix302_targets (s h : Nat) : ((leaveFix3 s h ++ leaveFix4 s h) ++ (leaveFix5 s h).take 27).map target =
    [1559, 1560, 1560, 1561, 1560, 1562, 1560, 1563, 1560, 1564, 1560, 1565, 1560, 1566, 1560, 1567, 1560, 1568, 1560,
     1569, 1560, 1570, 1560, 1571, 1560, 1572, 1560, 1573, 1560, 1574, 1560, 1575, 1560,
     h+1581, h+1581, h+1581, h+1581, h+1581, h+1581, 1576, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584,
     1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595] := rfl

theorem cross_kept (s h : Nat) (hh : 16 ≤ h) (q : Wire) (hq : q = h + 1580) (st : State) (o : List Bool) :
    (run (GateMirror.forward ((leaveFix3 s h ++ leaveFix4 s h) ++ (leaveFix5 s h).take 27)) o st).basis q =
      st.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward, prefix302_targets]
  subst hq
  intro hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  (try unfold Wire at *)
  omega

/-- Behind the mux: the rest of the selector never writes a tag. -/
theorem tags_kept (s h : Nat) (i : Nat) (hi : i < 16) (st : State) (o : List Bool) :
    (run (GateMirror.forward ((leaveFix5 s h).drop 27)) o st).basis (tagsP.getD i 0) = st.basis (tagsP.getD i 0) := by
  have t := tags_range i hi
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  simp only [leaveFix5, List.drop, List.map_cons, List.map_nil, target, List.mem_cons, List.not_mem_nil, or_false]
  unfold Wire at *
  omega

end ECDSAAdd.Entrant.StairPacket.LeaveJ
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.Admission
open Arithmetic Partial GateMirror LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.Admission
end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ
open Arithmetic Partial GateMirror SkywalkNat IntegerHigh Shadow LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

namespace Roundtrip
end Roundtrip

end ECDSAAdd.Entrant.StairPacket.LeaveJ

end

section

namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.Admission
open Arithmetic Partial SkywalkNat
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.Admission

end

-- ==== build-chain: par-d2 ScratchClean + ScratchWrap ====
-- BEGIN par-d2 ScratchClean (place after the section holding NativeJ.next_window, PrizeTail227303371)
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2 (job D2): the archive scratch of block `j-1` is clean after block `j`'s head (enter, routed first tick,
pack), for every loader `2 ≤ j ≤ 19`. Each scratch wire `scratchW (start j) kk` is either
- below the live anchored block `e0..e0+9`: a carry wire of block `j`'s tick 1, clean on the rails; or
- above it (`e0+10 .. 1699`, only for loaders from 285 on: the old anchored blocks of blocks 270..j-1): a carry
  wire of the stock tick `start j`. The hand-off cut keeps it at its stock value (`PackedCut.frame`, it is no flag,
  pending flag or rail-pair site), `SkywalkIntegerInput` says that value is zero, and neither the enter, the first
  tick nor the pack touch it.
So no chain invariant is needed: the cut of `At{s}` already carries it. All geometry is `omega` over `j`. -/


end ECDSAAdd.Entrant.StairPacket.NativeJ

end
-- END par-d2 ScratchClean

-- BEGIN par-d2 ScratchWrap (Tail10d9, after WideReference.full_carry / future_history; uses Tail227's NativeJ)
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2: D2's invariant for the 90..390 target, loaders `2 ≤ j ≤ 21`, for `Partial.scratchS` (window390: the
ports beyond the stock carry are re-hosted on released B-rail wires). With `w := scratchW t kk`, `t = start j`:
- `w` below `e0`: a tick-1 carry wire (as in `scratch_clean`).
- `w ≥ e0+10` and `w+t < 2068`: the port is `w`. The cut keeps it at its stock value, and the stock state has
  the whole 257-wire carry `1556..1812` clean (`WideReference.full_carry` from `Domain`).
- `w+t ≥ 2068` (only `t = 375, 390`): the port is the host `w-766 ∈ [1302-t, 933]`, a released wire of the stock
  B rail. The cut keeps it at its stock value, clean by `WideReference.released_clear`.
Enter, first tick and pack never touch these ports. -/

end ECDSAAdd.Entrant.StairPacket.NativeJ

end
-- END par-d2 ScratchWrap

-- ==== build-chain: the generic Cut families and NativeJ.stock_endpoint (build-chain) ====
/-! build-chain: the generic Cut families (ArchiveCut, AssembleCut, CertifiedCut, BodyCut) and the interior
`NativeJ.stock_endpoint`. -/
section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.ArchiveCut
open Arithmetic IntegerPacket SkywalkRails Partial WideReference
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.ArchiveCut
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.AssembleCut
open Arithmetic WideReference RailPair Partial
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000

/-- The route widths are `railP` on the window. -/
theorem route_rail (k : Nat) (hk : k ≤ 510) : W.narrowSkywalkRouteWidth k = railP k := by
  rw [WideReference.route_eq k hk]; rfl

end ECDSAAdd.Entrant.StairPacket.LeaveJ.AssembleCut
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.CertifiedCut
open Arithmetic WideReference SkywalkRails IntegerPacket Partial IntegerHigh LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
private theorem both (P Q:Prop) [Decidable P] [Decidable Q] : (decide P && decide Q)=decide (P ∧ Q) := by
  by_cases a:P <;> by_cases b:Q <;> simp [a,b]

/-- The rail of a window block narrows by at most one wire per tick, never widens, and when it narrows over the
block it narrows at the block's last tick. -/
theorem rail_step (j : Fin 24) (h0 : 1 ≤ j.val) (h1 : j.val ≤ 21) :
    railP (start j+14) ≤ railP (start j+15) + 1 ∧ railP (start j+14) ≤ railP (start j) ∧
    railP (start j+15) ≤ railP (start j) ∧ start j + 30 + railP (start j+15) ≤ 529 ∧
    (railP (start j+15) < railP (start j) → railP (start j+14) = railP (start j+15) + 1 ∧
      start j + 31 + railP (start j+15) ≤ 529) := by
  have e : start j = 75 + 15 * j.val := rfl
  rw [e]
  unfold railP; refine ⟨?_,?_,?_,?_,?_⟩ <;> (try intro) <;> split_ifs at * <;> omega

end ECDSAAdd.Entrant.StairPacket.LeaveJ.CertifiedCut
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.BodyCut
end

section
namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeJ
end

-- ==== build-chain: the generic stock chain of the window 120..255 (exit 270) ====
-- ==== build-chain: skeleton: FinalW (from Main), hand-off AtJ/ReadyW, the leaf statements, the three step forms ====
/-! build-chain skeleton: the 120..255 stock chain (exit 270) over the generic fold, with every missing leaf as a
named hypothesis (`*Spec`). Part A (the restated fold chain) and Part B (generic hand-off, FinalW) go into Window;
the leaves are proved one by one and the `Leaves` bundle disappears. -/

-- Part A (the restated fold chain) is in Window since w4r 4295495.

-- ===== Part B: FinalW (moved from Main), the generic hand-off and the window's Before =====
section
namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockRows
open Arithmetic IntegerPacket SkywalkRails WideReference StairArchiveRaw StairArchiveTrace CodecBitSliceVerify ArchivePortAction

/-- par-d2: `Final` for the window of blocks `j1 .. jn`, whose exit tick is `start jn+15` (moved here from Main). -/
structure FinalW (j1 jn : Fin 24) (exitPorts : Ports) (d:Bool) (x p:Nat) (out:State) : Prop where
  saved : ∀ k : Fin 24, j1.val ≤ k.val → k.val < jn.val →
    ∃row<63145,Chronology (start k) x p row ∧ Kept (ArchiveJ.codePorts k) d row out
  last : ∃row<63145,Chronology (start jn) x p row ∧ Frame exitPorts (code d) row out

/-- The code ports of bank `b` of the window `j1 .. jn` (`j1+b ≤ jn`). -/
def bankPorts (j1 jn : Fin 24) (exitPorts : Ports) (b : Nat) : Ports :=
  if h : j1.val+b < jn.val then ArchiveJ.codePorts ⟨j1.val+b,by omega⟩ else exitPorts

/-- `StockArchiveBanks.keptAt`, generic: every bank's 16 code cells are kept with their block's chronology. -/
theorem FinalW.bank {j1 jn : Fin 24} {exitPorts : Ports} {d:Bool} {x p:Nat} {out:State}
    (res : FinalW j1 jn exitPorts d x p out) (b : Nat) (hb : j1.val+b ≤ jn.val) :
    ∃row<63145,Chronology (start j1+15*b) x p row ∧ Kept (bankPorts j1 jn exitPorts b) d row out := by
  unfold bankPorts
  by_cases h:j1.val+b<jn.val
  · rw [dif_pos h]
    have e:start j1+15*b=start ⟨j1.val+b,by omega⟩:=by simp only [start]; omega
    rw [e]
    exact res.saved ⟨j1.val+b,by omega⟩ (Nat.le_add_right _ _) h
  · rw [dif_neg h]
    have e:start j1+15*b=start jn:=by simp only [start]; omega
    obtain ⟨r,l,t,f⟩:=res.last
    refine ⟨r,l,?_,fun j=>f ⟨j,by omega⟩⟩
    rw [e]; exact t


end ECDSAAdd.Entrant.StairPacket.ArchiveStockRows
end

section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== build-chain: the exit at 270 is the record exit ====
/-! build-chain leaves L7 (ExitProg) and L8 (ExitBridge): the generic exit at 270 is dadon's. -/
section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== build-chain: archive-key footprints ====
/-! build-chain: the archive-key footprint leaves L4 (KeepLeave), L5 (KeepOlder), L6 (KeepExit). A saved key of
block `i` sits on the 16 code cells of `cellsRestoreP (start i+15)`: the cells of ticks `t-10..t-1` and their
history cells (`t = start i+15 ≤ 255`, where `OB5.sig t` fixes them). -/

section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== build-chain: endpoint, scratch, roundtrip ====
/-! build-chain: the skeleton's leaves L1 (Endpoint), L2 (Scratch), L3 (Roundtrip). -/

section
namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeJ
end

section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== w4entry: the entry portal at 90 ====
/-! w4entry: the entry portal at tick 90 (Portal225Flag family rendered at 90 by portal/render.py). -/

section
namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
end ECDSAAdd.Entrant.StairPacket.Portal90Flag

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Portal90Flag

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Portal90Flag

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Portal90Flag

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Portal90Flag

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal90Flag

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end ECDSAAdd.Entrant.StairPacket.Portal90Flag

namespace ECDSAAdd.Entrant.StairPacket.Portal90Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal90Flag
end

-- ==== build-chain: the first block at 90 (block 1) ====
/-! build-chain: the first block at 90 (block 1) (first form, after the entry portal): leaves L9 (First) and L10 (FirstBack). -/

section
namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ
end

section
namespace ECDSAAdd.Entrant.StairPacket.NativeFirstJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeFirstJ
end

section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== build-chain (120..345): the chain generic in the last block J, and the leaves up to block 18 ====
-- ==== build-chain: SkelG ====
/-! build-chain: the window chain generic in its last block `J` (exit tick `start J+15`); the ship is `J = 12`
(exit 270), the 120..345 window `J = 18` (exit 360). The exit enters through `ExitLeaves`. -/

section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== build-chain: Late ====
/-! build-chain (120..345): the head-state facts of an interior block up to `j = 18` (`start j ≤ 345`) that the
Cut needs and that were vacuous up to 255: the older moved history agrees with the origin (`mirror_origin`) and the
sig band is clean before the leave (`band_clean_gen`). -/

section
namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeJ
end

section
namespace ECDSAAdd.Entrant.StairPacket.LeaveJ.BodyCut
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial LeaveSelector
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxRecDepth 35000
set_option maxHeartbeats 4000000
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.LeaveJ.BodyCut
end

section
namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial ArchivePortAction WideReference
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run SkywalkNat.step

end ECDSAAdd.Entrant.StairPacket.NativeJ
end

-- ==== build-chain: KeepsG ====
/-! build-chain (120..345): the archive-key footprints up to block 18. From tick 267 on, part of a bank's B-side
code cells is moved by the sig frame to the fold `[2071-t, 2079-t]`. -/
section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== build-chain: LeavesG ====
/-! build-chain: the leaves of the 120..345 window (`J = 18`). -/
section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

-- ==== window405 (90..390): the exit at 405 (build-chain's render360.py at 405 via helpers/window405/exit/render_x.py:
-- the exit archive's scratch is SA's scratchX 405: 1556+k while a carry wire of the stock tick, the released B-rail
-- wire 790+k beyond, with the end tick's host case from exit/hostpatch.py) ====
-- ==== window405: Exit405 ====
/-! build-chain: dadon's exit-270 families rendered at the exit tick 405 (render360.py): the entry-side portal flags,
the park, the stock end tick, the last-form pack and archive, and the terminal reference. Lists are the closed
formulas at 405; programs are par-b's generic pieces at 405. -/

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic PortalAnd
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic PortalAnd
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
def railA : List Wire := [491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528]
def railB : List Wire := [856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893]
def bulkA := railA.drop 3
def bulkB := railB.drop 3
end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 7000000
end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary405
open ArchivePortAction StairArchiveIntegerHook CodecBitSliceVerify
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary405

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveBoundary405
open ArchivePortAction CodecBitSliceVerify StairArchiveRaw StairArchiveGates
end ECDSAAdd.Entrant.StairPacket.ArchiveBoundary405

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic MappedCompressed PortalValues
set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
def hiPairs := bulkA.zip bulkB
end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket.Portal405Flag
open Arithmetic MappedCompressed PortalValues RailPair
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

end ECDSAAdd.Entrant.StairPacket.Portal405Flag

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket SkywalkRails StairArchiveTrace StairArchiveRaw ArchivePortAction
namespace ArchiveBoundary405
end ArchiveBoundary405
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack405
end NativePack405
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket ArchivePortAction
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
attribute [local irreducible] run unrouted onRails
namespace NativePack405
end NativePack405
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed RailPair
namespace Portal405Flag
set_option exponentiation.threshold 1024
end Portal405Flag
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic IntegerPacket MappedCompressed StairArchiveRaw StairArchiveTrace SkywalkRails ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run onRails
namespace NativePack405
open ArchiveBoundary405
end NativePack405
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint405
open Arithmetic ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
def src : List Wire := [1634,1635,1636]
def dst : List Wire := [894,895,896]
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint405

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint405
open Arithmetic MappedCompressed Portal405Flag
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint405

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint405
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint405

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint405
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint405

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
def L:=W.compactSkywalkTickLayout base 405
end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic Secp256k1 MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic Secp256k1 MappedCompressed
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic MappedCompressed Secp256k1
attribute [local irreducible] run
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic ArchivePortAction StairArchiveIntegerHook
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
namespace ArchiveBoundary405
end ArchiveBoundary405
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic MappedCompressed IntegerPacket
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
attribute [local irreducible] run
def readOnly (q:Wire) := OB5.sig 405 q∉L.wires ∨ q=420
instance (q:Wire) : Decidable (readOnly q) := by unfold readOnly;infer_instance
end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3500000
set_option maxRecDepth 18000
set_option exponentiation.threshold 1024
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic MappedCompressed Secp256k1
set_option maxHeartbeats 3000000
set_option maxRecDepth 15000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket.EndTick405
open Arithmetic MappedCompressed Secp256k1 ArchiveBoundary405 ParkEndpoint405
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.EndTick405

end

section

namespace ECDSAAdd.Entrant.StairPacket.ParkEndpoint405
open Arithmetic MappedCompressed IntegerPacket RailPair Portal405Flag ArchiveBoundary405
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def ordinary (q:Wire) : Prop := q∉src ∧ q∉dst ∧ q≠1633 ∧ q≠1631 ∧ q≠1632 ∧ q∉sites hiPairs
instance (q:Wire) : Decidable (ordinary q):=by unfold ordinary;infer_instance
end ECDSAAdd.Entrant.StairPacket.ParkEndpoint405

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack405
open Arithmetic IntegerPacket MappedCompressed SkywalkRails StairArchiveRaw StairArchiveTrace ArchiveBoundary405 ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.NativePack405

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack405
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary405
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.NativePack405

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack405
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary405 ParkEndpoint405 Portal405Flag StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.NativePack405

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack405
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary405 ParkEndpoint405 Portal405Flag StairArchiveTrace SkywalkRails
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
set_option exponentiation.threshold 1024
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.NativePack405

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed Secp256k1
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000
end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack405
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary405
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open ArchiveBoundary405 ParkEndpoint405 Portal405Flag Secp256k1 SkywalkRails StairArchiveTrace
end ECDSAAdd.Entrant.StairPacket.NativePack405

end

-- ==== window405: LExit405 ====
/-! window405 stage 2: the exit of the window at 405 (`ExitLeaves ⟨20⟩ ArchiveBoundary405.codePorts`), from build-chain's
LExit360.lean with the block-21 hand-off, the last block 20 and the 405 numbers (helpers/window405/exit/lexit.py). -/
section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowW
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.StockWindowW
end

/- Inlined from ShadowGates; provenance retained from022799f6. -/
section

/-! Integer-walk blocks with a seven-bit reduction in both active rails.
The 15-tick block and the archive's public representation are shared with the stock window. -/
namespace ECDSAAdd.Entrant.StairPacket.Shadow7
open Arithmetic MappedCompressed GateMirror Partial StairArchiveGates

def sbP (s : Nat) : Nat := (498 - s - (1 - (91 - s) - s / 391))/2

def smallBits (j : Fin 24) := Shadow7.sbP (start j)

def shape (j : Fin 24) : IntegerPacket.Shape where
  start := start j
  length := 15
  mid := Shadow7.smallBits j+16
  rangeEnd := by have h:=j.isLt; simp [start]; omega
  extent := by have h:=j.isLt; simp [start,Shadow7.smallBits,Shadow7.sbP]; omega
  midBound := by simp [Shadow7.smallBits,Shadow7.sbP,start]; omega

def routed (j : Fin 24) (a : Nat) : Nat → Program
  | 0 => []
  | n+1 => renameProgram (net j a) (skywalkIntegerTick (IntegerPacket.ports (Shadow7.shape j) a)) ++
    Shadow7.routed j (a+1) n

def unrouted (j : Fin 24) (a : Nat) : Nat → Program
  | 0 => []
  | n+1 => Shadow7.unrouted j (a+1) n ++
    renameProgram (net j a) (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (IntegerPacket.ports (Shadow7.shape j) a)
      (IntegerPacket.ports (Shadow7.shape j) a).half.length)

def wpP (s : Nat) : Nat := railP s - Shadow7.sbP s - 16

def e0P (s : Nat) : Nat := 1574 + Shadow7.sbP s

def lowsP (s : Nat) : Nat := 17 + Shadow7.sbP (s+15) - Shadow7.sbP s

def a0P (s : Nat) : Nat := s + Shadow7.sbP s + 32

def b0P (s : Nat) : Nat := 787 + Shadow7.sbP s

def bankW (s i : Nat) : Wire :=
  if i < 3 then Shadow7.e0P s + i else if i < Shadow7.wpP s then bTopP s + 1 + i - Shadow7.wpP s else 1598 + i - Shadow7.wpP s

/-- Above the anchored block the pool stays below the tick-`s+14` mirror cells (`q + s < 2055`); the rest (block 22
only) sits in the zero high A columns `a0P s + 17 ..`. -/

def poolW (s i : Nat) : Wire :=
  if 1598 + i < Shadow7.e0P s then 1598 + i else if 1608 + i + s < 2055 then 1608 + i
  else Shadow7.a0P s + 17 + (1608 + i + s - 2055)

/-- The leave head scan at margin 17: signs at register row 16, rows -1..16 (stock `Shadow7.fix0P` minus the top row). -/
def fix0P (s h : Nat) : List Gate := [
  .cx (s+h+48) (h+1579),
  .cx (h+803) (h+1579),
  .cx (s+h+31) (h+786),
  .ccx (s+30) (h+786) (s+h+31),
  .cx (s+h+31) (h+786),
  .cx (s+h+32) (h+787),
  .ccx (s+30) (h+787) (s+h+32),
  .cx (s+h+32) (h+787),
  .cx (s+h+33) (h+788),
  .ccx (s+30) (h+788) (s+h+33),
  .cx (s+h+33) (h+788),
  .cx (s+h+34) (h+789),
  .ccx (s+30) (h+789) (s+h+34),
  .cx (s+h+34) (h+789),
  .cx (s+h+35) (h+790),
  .ccx (s+30) (h+790) (s+h+35),
  .cx (s+h+35) (h+790),
  .cx (s+h+36) (h+791),
  .ccx (s+30) (h+791) (s+h+36),
  .cx (s+h+36) (h+791),
  .cx (s+h+37) (h+792),
  .ccx (s+30) (h+792) (s+h+37),
  .cx (s+h+37) (h+792),
  .cx (s+h+38) (h+793),
  .ccx (s+30) (h+793) (s+h+38),
  .cx (s+h+38) (h+793),
  .cx (s+h+39) (h+794),
  .ccx (s+30) (h+794) (s+h+39),
  .cx (s+h+39) (h+794),
  .cx (s+h+40) (h+795),
  .ccx (s+30) (h+795) (s+h+40),
  .cx (s+h+40) (h+795),
  .cx (s+h+41) (h+796),
  .ccx (s+30) (h+796) (s+h+41),
  .cx (s+h+41) (h+796),
  .cx (s+h+42) (h+797),
  .ccx (s+30) (h+797) (s+h+42),
  .cx (s+h+42) (h+797),
  .cx (s+h+43) (h+798),
  .ccx (s+30) (h+798) (s+h+43),
  .cx (s+h+43) (h+798),
  .cx (s+h+44) (h+799),
  .ccx (s+30) (h+799) (s+h+44),
  .cx (s+h+44) (h+799),
  .cx (s+h+45) (h+800),
  .ccx (s+30) (h+800) (s+h+45),
  .cx (s+h+45) (h+800),
  .cx (s+h+46) (h+801),
  .ccx (s+30) (h+801) (s+h+46),
  .cx (s+h+46) (h+801),
  .cx (s+h+47) (h+802),
  .ccx (s+30) (h+802) (s+h+47),
  .cx (s+h+47) (h+802),
  .cx (s+h+48) (h+803),
  .ccx (s+30) (h+803) (s+h+48),
  .cx (s+h+48) (h+803),
  .cx (h+1579) (h+786),
  .cx (h+1579) (h+787),
  .cx (h+1579) (h+788),
  .cx (h+1579) (h+789),
  .cx (h+1579) (h+790),
  .cx (h+1579) (h+791),
  .cx (h+1579) (h+792),
  .cx (h+1579) (h+793),
  .cx (h+1579) (h+794),
  .cx (h+1579) (h+795),
  .cx (h+1579) (h+796),
  .cx (h+1579) (h+797),
  .cx (h+1579) (h+798),
  .cx (h+1579) (h+799),
  .cx (h+1579) (h+800),
  .cx (h+1579) (h+801),
  .cx (h+1579) (h+802),
  .cx (h+1579) (h+803)]

/-- Long latch, mask and companion erase over 17 register rows (stock `Shadow7.fix2P` minus the top row). -/
def fix2P (s h : Nat) : List Gate := [
  .x (h+786),
  .x (h+787),
  .x (h+788),
  .x (h+789),
  .x (h+790),
  .x (h+791),
  .x (h+792),
  .x (h+793),
  .x (h+794),
  .x (h+795),
  .x (h+796),
  .x (h+797),
  .x (h+798),
  .x (h+799),
  .x (h+800),
  .x (h+801),
  .x (h+802),
  .x (h+803),
  .make (h+786) (h+787) 1557,
  .make 1557 (h+788) 1558,
  .make 1558 (h+789) 1559,
  .make 1559 (h+790) 1560,
  .make 1560 (h+791) 1561,
  .make 1561 (h+792) 1562,
  .make 1562 (h+793) 1563,
  .make 1563 (h+794) 1564,
  .make 1564 (h+795) 1565,
  .make 1565 (h+796) 1566,
  .make 1566 (h+797) 1567,
  .make 1567 (h+798) 1568,
  .make 1568 (h+799) 1569,
  .make 1569 (h+800) 1570,
  .make 1570 (h+801) 1571,
  .make 1571 (h+802) 1572,
  .make 1572 (h+803) 1573,
  .cx 1573 1556,
  .x 1556,
  .pop 1572 (h+803) 1573,
  .pop 1571 (h+802) 1572,
  .pop 1570 (h+801) 1571,
  .pop 1569 (h+800) 1570,
  .pop 1568 (h+799) 1569,
  .pop 1567 (h+798) 1568,
  .pop 1566 (h+797) 1567,
  .pop 1565 (h+796) 1566,
  .pop 1564 (h+795) 1565,
  .pop 1563 (h+794) 1564,
  .pop 1562 (h+793) 1563,
  .pop 1561 (h+792) 1562,
  .pop 1560 (h+791) 1561,
  .pop 1559 (h+790) 1560,
  .pop 1558 (h+789) 1559,
  .pop 1557 (h+788) 1558,
  .pop (h+786) (h+787) 1557,
  .x (h+803),
  .x (h+802),
  .x (h+801),
  .x (h+800),
  .x (h+799),
  .x (h+798),
  .x (h+797),
  .x (h+796),
  .x (h+795),
  .x (h+794),
  .x (h+793),
  .x (h+792),
  .x (h+791),
  .x (h+790),
  .x (h+789),
  .x (h+788),
  .x (h+787),
  .x (h+786),
  .x 1557,
  .cx (s+h+31) 1557,
  .make (h+786) 1557 1558,
  .make (h+787) 1558 1559,
  .make (h+788) 1559 1560,
  .make (h+789) 1560 1561,
  .make (h+790) 1561 1562,
  .make (h+791) 1562 1563,
  .make (h+792) 1563 1564,
  .make (h+793) 1564 1565,
  .make (h+794) 1565 1566,
  .make (h+795) 1566 1567,
  .make (h+796) 1567 1568,
  .make (h+797) 1568 1569,
  .make (h+798) 1569 1570,
  .make (h+799) 1570 1571,
  .make (h+800) 1571 1572,
  .make (h+801) 1572 1573,
  .make (h+802) 1573 1574,
  .cx 1574 (h+803),
  .pop (h+802) 1573 1574,
  .cx 1573 (h+802),
  .pop (h+801) 1572 1573,
  .cx 1572 (h+801),
  .pop (h+800) 1571 1572,
  .cx 1571 (h+800),
  .pop (h+799) 1570 1571,
  .cx 1570 (h+799),
  .pop (h+798) 1569 1570,
  .cx 1569 (h+798),
  .pop (h+797) 1568 1569,
  .cx 1568 (h+797),
  .pop (h+796) 1567 1568,
  .cx 1567 (h+796),
  .pop (h+795) 1566 1567,
  .cx 1566 (h+795),
  .pop (h+794) 1565 1566,
  .cx 1565 (h+794),
  .pop (h+793) 1564 1565,
  .cx 1564 (h+793),
  .pop (h+792) 1563 1564,
  .cx 1563 (h+792),
  .pop (h+791) 1562 1563,
  .cx 1562 (h+791),
  .pop (h+790) 1561 1562,
  .cx 1561 (h+790),
  .pop (h+789) 1560 1561,
  .cx 1560 (h+789),
  .pop (h+788) 1559 1560,
  .cx 1559 (h+788),
  .pop (h+787) 1558 1559,
  .cx 1558 (h+787),
  .pop 1556 (s+h+32) (h+787),
  .pop 1556 (s+h+33) (h+788),
  .pop 1556 (s+h+34) (h+789),
  .pop 1556 (s+h+35) (h+790),
  .pop 1556 (s+h+36) (h+791),
  .pop 1556 (s+h+37) (h+792),
  .pop 1556 (s+h+38) (h+793),
  .pop 1556 (s+h+39) (h+794),
  .pop 1556 (s+h+40) (h+795),
  .pop 1556 (s+h+41) (h+796),
  .pop 1556 (s+h+42) (h+797),
  .pop 1556 (s+h+43) (h+798),
  .pop 1556 (s+h+44) (h+799),
  .pop 1556 (s+h+45) (h+800),
  .pop 1556 (s+h+46) (h+801),
  .pop 1556 (s+h+47) (h+802),
  .pop 1556 (s+h+48) (h+803)]

/-- Margin 17 sign bit before the join: `1613 := cin xor signExpr xor (d0 ∧ signExpr)` = bit 1 of the far digit
(`cin = d0 xor far` sits on the far-flag wire `e0+3` during the adjust), then `e0+3` back to the far flag.
The crossing wire `e0+6` is only read (MoveChain's `quiet`). The second argument is unused (call shape of `Shadow7.fix8P`). -/
def fix8P (s _h : Nat) : List Gate := [
  .cx (Shadow7.e0P s + 3) 1613,
  .cx 1596 1613,
  .cx 1597 1613,
  .cx (Shadow7.e0P s + 6) (Shadow7.e0P s + 3)]

/-- Clears `1613` after the join: `far xor d0 xor signExpr xor (d0 ∧ signExpr)`. -/
def fix10P (s _h : Nat) : List Gate := [
  .cx (Shadow7.e0P s + 3) 1613,
  .cx (Shadow7.e0P s + 6) 1613,
  .cx 1596 1613,
  .cx 1597 1613]

/-- The adjust proper at margin 17: carry-in on the far-flag wire `e0+3` (holding `d0 xor far`), sign read from `1596`
(= signExpr; irrelevant when the carry-in is 0). -/
def leaveAdjustCore (s : Nat) : List Gate :=
  adjustG ((List.range (Shadow7.wpP s)).map (Shadow7.bankW s)) ((List.range (Shadow7.wpP s - 1)).map (Shadow7.poolW s)) (Shadow7.e0P s + 3) 1596

/-- Margin 17: the far digit is d ∈ {0,1,2} and the carry-in is `d ≠ 1` = `d0 xor far`: the first gate folds the crossing
bit `e0+6` into the far flag `e0+3` (undone by the last gate of `fix8P`). -/
def leaveAdjust (s : Nat) : List Gate :=
  [.cx (Shadow7.e0P s + 6) (Shadow7.e0P s + 3)] ++ Shadow7.leaveAdjustCore s

def leaveBarrel (s : Nat) : List Gate :=
  stageG 1613 (Shadow7.bankW s) controlsP0 1 (Shadow7.wpP s) ++ stageG 1613 (Shadow7.bankW s) controlsP1 2 (Shadow7.wpP s + 1) ++
  stageG 1613 (Shadow7.bankW s) controlsP2 4 (Shadow7.wpP s + 3) ++ stageG 1613 (Shadow7.bankW s) controlsP3 8 (Shadow7.wpP s + 7)

def columnsP (s : Nat) : List HighBankJoin.Column :=
  (List.range 17).map fun i =>
    ⟨decide (i < Shadow7.lowsP s), if i < 16 then some (tagsP.getD i 0) else none, Shadow7.a0P s + i, Shadow7.bankW s i⟩

def leaveLowStore (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let bs := (List.range L).map (Shadow7.b0P s + ·)
  [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559] ++
  (List.range L).map (fun i => .make 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG bs ++
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
  [.x 1558, .x top] ++ xsG hi ++
  chainG (Shadow7.storeW s) seq [.cx (Shadow7.storeW s (H+1)) 1557, .x 1557] 0 (H+1) ++
  xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++
  xsG seq2 ++ chainG (1558 + ·) (Shadow7.b0P s - 1 + ·) [.cx (1558+(L+1)) 1556, .x 1556] 0 (L+1) ++
  xsG seq2.reverse ++ [.x 1558]

def leaveLowClose (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s
  xsG ((List.range 15).map (s+16+·)) ++
  (List.range (L+1)).map (fun i => .cx (Shadow7.e0P s + 5) (Shadow7.b0P s - 1 + i)) ++
  (List.range (L+1)).flatMap (fun i => cswapG (s+30) (Shadow7.b0P s - 1 + i) (Shadow7.a0P s - 1 + i))

def movesP (s : Nat) : List (Wire × Wire) :=
  (List.range (Shadow7.wpP (s+15) - 2)).map (fun i => (Shadow7.bankW s (Shadow7.lowsP s + i), bTopP (s+15) + 3 + i - Shadow7.wpP (s+15))) ++
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
  keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s + i) 1613 0 16 ++ wordGM 1614 (Shadow7.columnsP s)

def leaveMoveOps (s : Nat) : List Gate :=
  Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
  leaveFix4 s (Shadow7.sbP s) ++ Shadow7.leaveFix5Move s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.leaveJoinMove s ++ Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def leaveMoveP (j : Fin 24) : Program := GateMirror.forward (Shadow7.leaveMoveOps (start j))

def leaveMoveInvP (j : Fin 24) : Program := inverse (Shadow7.leaveMoveOps (start j))

def portalOps (t : Nat) : List Gate :=
  let w := Shadow7.wpP t; let aBot := Shadow7.a0P t; let bBot := 802 + Shadow7.sbP t
  let rA := (List.range w).map (aBot + ·); let rB := (List.range w).map (bBot + ·)
  let bA := (List.range (w-2)).map (aBot + 2 + ·); let bB := (List.range (w-2)).map (bBot + 2 + ·)
  let sgn := Shadow7.e0P t + 5; let G := t + 15; let f3 := Shadow7.e0P t + 3; let f4 := Shadow7.e0P t + 4
  [.cx (aBot + w - 1) sgn, .cx (bTopP t) sgn] ++ exchangeG G (rA.zip rB) ++ cxsG sgn rB ++
  latchG true none 1556 (aBot+1) ((List.range (w-2)).map (fun i => (aBot+2+i, 1558+i))) ++
  [.cx 1556 f3, .cx f3 1556] ++
  latchG false (some f3) f4 bBot ((List.range (w-1)).map (fun i => (bBot+1+i, 1556+i))) ++
  [.x (aBot+1), .make (bBot+1) (aBot+1) 1556] ++ addG bB ((List.range (w-3)).map (1557 + ·)) 1556 ++
  (bA.zip bB).map (fun p => .ccx f4 p.1 p.2) ++ [.pop (bBot+1) (aBot+1) 1556, .x (aBot+1)] ++
  transferG (bA.zip bB) ++ cxsG sgn [bBot, bBot+1] ++
  exchangeG G [(aBot, bBot), (aBot+1, bBot+1)]

def parkOps (e : Nat) : List Gate :=
  swapsG [(Shadow7.e0P e + 6, bTopP e + 1), (Shadow7.e0P e + 7, bTopP e + 2), (Shadow7.e0P e + 8, bTopP e + 3)]

def enterOps (s : Nat) : List Gate := enterFix17 s (Shadow7.sbP s)



def enterP (j : Fin 24) : Program := GateMirror.forward (Shadow7.enterOps (start j))
def enterInvP (j : Fin 24) : Program := inverse (Shadow7.enterOps (start j))

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

def archiveLoadP (j : Fin 24) (d : Bool) : Program :=
  renameProgram (fun q => (Shadow7.loadPortsWP (start j + 15) (Shadow7.e0P (start j + 15) + 6)).getD q 0)
    (if d then ReducedWindowArchives.load0 else ReducedWindowArchives.load1) ++ moveLoadP (start j + 15)

def archiveRestoreP (j : Fin 24) (d : Bool) : Program :=
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

end
