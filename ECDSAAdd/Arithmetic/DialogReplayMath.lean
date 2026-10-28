import ECDSAAdd.Arithmetic.ReplayField
import ECDSAAdd.Math.ValueTrace

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- 最终K的比较与逐步值走活动性一致，不能从00记录推断停止。 -/
theorem replayControls_trace (rs : List RoundRecord) (ref : BasisState) (i : Nat) (z : ValueState)
    (hk : z.k ≤ i ∧ (z.v ≠ 0 → z.k=i))
    (ht : TapeValues rs ((valueTrace rs.length z).map Prod.snd) ref) :
    replayControls (valueStep^[rs.length] z).k i ref rs=valueTrace rs.length z := by
  induction rs generalizing i z with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.length_cons,valueTrace,List.map_cons,TapeValues] at ht
    have htail := ih (i+1) (valueStep z) (valueStep_count i z hk) ht.2.2
    have ha : decide (i<(valueStep^[rs.length+1] z).k)=decide (z.v ≠ 0) := by
      simp only [value_active_final rs.length i z hk]
    rw [Function.iterate_succ_apply] at ha
    simp only [List.length_cons,replayControls,valueTrace,ht.1,ht.2.1,
      Function.iterate_succ_apply,htail,ha]

theorem dialogReplay_division (rs : List RoundRecord) (ref : BasisState) (x y : Nat)
    (hl : rs.length=512) (hx0 : 0<x) (hx : x<p) (hy : y<p)
    (ht : TapeValues rs ((valueTrace 512 (valueInit p x)).map Prod.snd) ref) :
    replayNatLoop p (valueStep^[512] (valueInit p x)).k 0 ref rs (0,y)=
      (((y:Fp)/(x:Fp)).val,0) := by
  have hc := replayControls_trace rs ref 0 (valueInit p x) (by simp [valueInit]) (by simpa [hl] using ht)
  rw [hl] at hc
  have hf := replayNatLoop_field (valueStep^[512] (valueInit p x)).k 0 ref rs 0 y (by decide) hy
  rw [hc,Nat.cast_zero,dialog_quotient x (y:Fp) hx0 hx] at hf
  have hb := replayNatLoop_bound p (valueStep^[512] (valueInit p x)).k 0 ref rs 0 y (by decide) (by decide) hy
  apply Prod.ext
  · have h := congrArg (fun v : Fp×Fp => v.1.val) hf
    simpa only [ZMod.val_natCast_of_lt hb.1] using h
  · have h := congrArg (fun v : Fp×Fp => v.2.val) hf
    simpa only [ZMod.val_natCast_of_lt hb.2,ZMod.val_zero] using h

theorem dialogReplay_multiplication (rs : List RoundRecord) (ref : BasisState) (x y : Nat)
    (hl : rs.length=512) (hx0 : 0<x) (hx : x<p) (hy : y<p)
    (ht : TapeValues rs ((valueTrace 512 (valueInit p x)).map Prod.snd) ref) :
    replayNatUnloop p (valueStep^[512] (valueInit p x)).k 0 ref rs (y,0)=
      (0,((y:Fp)*(x:Fp)).val) := by
  have hc := replayControls_trace rs ref 0 (valueInit p x) (by simp [valueInit]) (by simpa [hl] using ht)
  rw [hl] at hc
  have hf := replayNatUnloop_field (valueStep^[512] (valueInit p x)).k 0 ref rs y 0
  rw [hc,Nat.cast_zero,dialog_product x (y:Fp) hx0 hx] at hf
  have hb := replayNatUnloop_bound p (valueStep^[512] (valueInit p x)).k 0 ref rs y 0 (by decide) hy (by decide)
  apply Prod.ext
  · have h := congrArg (fun v : Fp×Fp => v.1.val) hf
    simpa only [ZMod.val_natCast_of_lt hb.1,ZMod.val_zero] using h
  · have h := congrArg (fun v : Fp×Fp => v.2.val) hf
    simpa only [ZMod.val_natCast_of_lt hb.2] using h

end ECDSAAdd.Arithmetic
