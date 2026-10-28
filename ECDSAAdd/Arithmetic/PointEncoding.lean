import ECDSAAdd.Arithmetic.PointFlagProof

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 与finite::x++y一致的小端完整点编码，O编码为零。 -/
def pointCode (R : Point) : Nat := (pointFinite R).toNat+2*(pointX R+2^256*pointY R)

theorem pointCode_lt (R : Point) : pointCode R<2^513 := by
  have bound (k x y f : Nat) (hk : 0<k) (hx : x<k) (hy : y<k) (hf : f≤1) :
      f+2*(x+k*y)<2*k*k := by nlinarith
  have hp : p<2^256 := by norm_num [p]
  have hf : (pointFinite R).toNat≤1 := by cases pointFinite R <;> decide
  have hb := bound (2^256) (pointX R) (pointY R) (pointFinite R).toNat
    (Nat.two_pow_pos _) ((point_coordinates_lt R).1.trans hp) ((point_coordinates_lt R).2.trans hp) hf
  have power (n : Nat) : 2*2^n*2^n=2^(n+n+1) := by
    rw [Nat.pow_succ,Nat.pow_add]
    ac_rfl
  have he := power 256
  simp only [Nat.reduceAdd] at he
  exact lt_of_lt_of_eq hb he

theorem pointCode_injective : Function.Injective pointCode := by
  intro R C h
  have hp : p<2^256 := by norm_num [p]
  have hx := (point_coordinates_lt R).1.trans hp
  have hc := (point_coordinates_lt C).1.trans hp
  have hf : pointFinite R=pointFinite C := by
    dsimp only [pointCode] at h
    cases hr : pointFinite R <;> cases hc : pointFinite C <;> simp_all only [Bool.toNat_false,Bool.toNat_true] <;> omega
  have hv : pointX R+2^256*pointY R=pointX C+2^256*pointY C := by
    dsimp only [pointCode] at h
    rw [hf] at h
    omega
  have hxx : pointX R=pointX C := by
    have hm := congrArg (fun a => a%2^256) hv
    simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,
      Nat.add_zero,Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hc] using hm
  have hyy : pointY R=pointY C := by
    rw [hxx] at hv
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel hv)
  cases R with
  | zero => cases C <;> simp_all [pointFinite,coordinates]
  | @some x y hr =>
    cases C with
    | zero => simp [pointFinite,coordinates] at hf
    | @some u v hc =>
      have heX : x=u := ZMod.val_injective p hxx
      have heY : y=v := ZMod.val_injective p hyy
      subst u; subst v; rfl

/-- 合法点在513位完整寄存器中的读取值。 -/
theorem pointCode_register (r : PointReg) (R : Point) (s : BasisState)
    (hx : r.x.length=256) (h : Holds.holds s r R) :
    regValue (PointAddLayout.pointWires r) s=pointCode R := by
  have hv := (point_holds r R s).mp h
  change (if s r.finite then 1 else 0)+2*regValue (r.x++r.y) s=_
  rw [regValue_append,hx,hv.1,hv.2.1,hv.2.2]
  dsimp only [pointCode]
  cases pointFinite R <;> rfl

/-- 规范编码上的可判定相等；在合法点上恰好是点相等。 -/
def pointEqual (R C : Point) : Bool := decide (pointCode R=pointCode C)

theorem pointEqual_true_iff (R C : Point) : pointEqual R C=true ↔ R=C := by
  simp only [pointEqual,decide_eq_true_eq,pointCode_injective.eq_iff]

/-- 全点相等检测可以区分O与所有有限点，不需坐标非零假设。 -/
theorem equalPoint_correct (c t : Wire) (r : PointReg) (work : List Wire) (R C : Point)
    (hx : r.x.length=256) (hy : r.y.length=256) (hw : work.length=513)
    (hn : (c::t::PointAddLayout.pointWires r++work).Nodup)
    (s : State) (m : List Bool) (hp : Holds.holds s.basis r R) (hz : regValue work s.basis=0) :
    run (equalConstant c t (zeroPorts (PointAddLayout.pointWires r) work) (pointCode C)) m s=
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis c && pointEqual R C))⟩ := by
  have hl : (PointAddLayout.pointWires r).length=513 := by simp [PointAddLayout.pointWires,hx,hy]
  have hc := equalPorts_correct c t (PointAddLayout.pointWires r) work (pointCode C)
    (hl.trans hw.symm) hn (by rw [hl]; exact pointCode_lt C) s m hz
  rw [pointCode_register r R s.basis hx hp] at hc
  exact hc

end ECDSAAdd.Arithmetic
