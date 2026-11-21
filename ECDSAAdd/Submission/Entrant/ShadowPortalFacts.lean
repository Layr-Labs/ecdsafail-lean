import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.ShadowBounds

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
