import ECDSAAdd.Arithmetic.NarrowSkywalkRouteTick
import ECDSAAdd.Math.SkywalkTerminationBudget

/-! Tighter integer-pass width schedule.

The Skywalk integer passes size tick `i` by `min 258 (514-i)` (route) and
`min 258 (513-i)` (adder), derived from the product cap `u+v ≤ 2^(512-i)`.
Iterating the exponent budget of `SkywalkTerminationBudget` gives the strict
witnesses `u < 2^a`, `v < 2^b` with `a+b = 512-i`, hence `u+v ≤ 2^(511-i)`:
one bit tighter.  The route and the adder of every tick from 256 to 510 are
one bit narrower; the widths at stages 0, 1 and 512 are unchanged. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option exponentiation.threshold 512

namespace ECDSAAdd.Entrant.W
open ECDSAAdd.Arithmetic

/-- Stage/route width: `min 258 (514-i)` lowered by one on ticks 256–510. -/
@[irreducible] def narrowSkywalkRouteWidth (i : Nat) : Nat :=
  min 258 (514-i) - (min 1 (511-i) - min 1 (256-i))

/-- Adder width of tick `i`, equal to the next stage width. -/
@[irreducible] def narrowSkywalkWidth (i : Nat) : Nat :=
  min 258 (513-i) - (min 1 (510-i) - min 1 (255-i))

theorem narrowSkywalkRouteWidth_bounds (i : Nat) (hi : i<512) :
    3≤narrowSkywalkRouteWidth i ∧ narrowSkywalkRouteWidth i≤258 ∧
    narrowSkywalkRouteWidth i≤min 258 (514-i) := by
  unfold narrowSkywalkRouteWidth
  omega

theorem narrowSkywalkWidth_bounds (i : Nat) (hi : i<512) :
    2≤narrowSkywalkWidth i ∧ narrowSkywalkWidth i≤258 ∧
    narrowSkywalkWidth i≤min 258 (513-i) := by
  unfold narrowSkywalkWidth
  omega

theorem narrowSkywalkRouteWidth_zero : narrowSkywalkRouteWidth 0=258 := by
  unfold narrowSkywalkRouteWidth; rfl

theorem narrowSkywalkRouteWidth_one : narrowSkywalkRouteWidth 1=258 := by
  unfold narrowSkywalkRouteWidth; rfl

theorem narrowSkywalkRouteWidth_512 : narrowSkywalkRouteWidth 512=2 := by
  unfold narrowSkywalkRouteWidth; rfl

theorem narrowSkywalkWidth_zero : narrowSkywalkWidth 0=258 := by
  unfold narrowSkywalkWidth; rfl

/-- The schedule agrees with the original one at the shared endpoints. -/
theorem narrowSkywalkRouteWidth_endpoints :
    narrowSkywalkRouteWidth 0=Arithmetic.narrowSkywalkRouteWidth 0 ∧
    narrowSkywalkRouteWidth 1=Arithmetic.narrowSkywalkRouteWidth 1 ∧
    narrowSkywalkRouteWidth 512=Arithmetic.narrowSkywalkRouteWidth 512 ∧
    narrowSkywalkWidth 0=Arithmetic.narrowSkywalkWidth 0 := by
  rw [narrowSkywalkRouteWidth_zero,narrowSkywalkRouteWidth_one,narrowSkywalkRouteWidth_512,
    narrowSkywalkWidth_zero]
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem pow_pair (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2^a+2^b ≤ 2^(a+b-1)+2 := by
  obtain ⟨c,rfl⟩ : ∃ c, a=c+1 := ⟨a-1,by omega⟩
  obtain ⟨d,rfl⟩ : ∃ d, b=d+1 := ⟨b-1,by omega⟩
  have e : c+1+(d+1)-1=(c+d)+1 := by omega
  rw [e,pow_succ,pow_succ,pow_succ,pow_add]
  have hc : 1 ≤ 2^c := Nat.one_le_two_pow
  have hd : 1 ≤ 2^d := Nat.one_le_two_pow
  nlinarith

/-- Exponent-budget sum cap: after `i` rounds from strict widths `a,b` the
sum is at most `2^(a+b-1-i)`. -/
theorem iter_sum_budget : ∀ (i a b : Nat) (z : SkywalkNat.State),
    0<z.v → z.v%2=1 → z.u.Coprime z.v → z.u<2^a → z.v<2^b → i+1 ≤ a+b →
      (SkywalkNat.step^[i] z).u+(SkywalkNat.step^[i] z).v ≤ 2^(a+b-1-i) := by
  intro i
  induction i with
  | zero =>
    intro a b z hv0 _ hc hu hv _
    simp only [Function.iterate_zero,id_eq,Nat.sub_zero]
    by_cases hz : z.u=0
    · have h1 : z.v=1 := by
        have g : z.u.gcd z.v=1 := hc
        rwa [hz,Nat.gcd_zero_left] at g
      rw [hz,h1]
      exact Nat.one_le_two_pow
    · have ha : 1 ≤ a := by
        by_contra h
        have : a=0 := by omega
        rw [this,pow_zero] at hu
        omega
      have hb : 1 ≤ b := by
        by_contra h
        have : b=0 := by omega
        rw [this,pow_zero] at hv
        omega
      have := pow_pair a b ha hb
      omega
  | succ i ih =>
    intro a b z hv0 hvo hc hu hv hab
    by_cases hz : z.u=0
    · rw [SkywalkNat.iter_fixed_of_u_zero z (i+1) hz]
      have h1 : z.v=1 := by
        have g : z.u.gcd z.v=1 := hc
        rwa [hz,Nat.gcd_zero_left] at g
      rw [hz,h1]
      exact Nat.one_le_two_pow
    · obtain ⟨a',b',he,hu',hv'⟩ :=
        SkywalkNat.step_exponent_budget z a b (Nat.pos_of_ne_zero hz) hv0 hu hv
      have valid := SkywalkNat.step_v_odd_pos z hv0 hvo
      have cop := SkywalkNat.step_coprime z hvo hc
      have rest := ih a' b' (SkywalkNat.step z) valid.1 valid.2 cop hu' hv' (by omega)
      rw [Function.iterate_succ_apply]
      have e : a'+b'-1-i=a+b-1-(i+1) := by omega
      rw [e] at rest
      exact rest

/-- Complete-trajectory form for 256-bit inputs. -/
theorem iter_sum_width (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpo : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) (hi : i ≤ 511) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v ≤ 2^(511-i) := by
  have _ := hx0
  have h := iter_sum_budget i 256 256 (SkywalkNat.init x p) hp0 hpo hc (hx.trans hp) hp (by omega)
  have e : 256+256-1-i=511-i := by omega
  rw [e] at h
  exact h

/-- Universal input fit for the route at the tighter stage width. -/
theorem narrowSkywalkRoute_iter_fit (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpo : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    let n := narrowSkywalkRouteWidth i;
    -((2^(n-1):Nat):Int)≤r.a ∧ r.a<((2^(n-1):Nat):Int) ∧
    -((2^(n-1):Nat):Int)≤r.b ∧ r.b<((2^(n-1):Nat):Int) := by
  dsimp only
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at he
  rw [he]
  have hb := SkywalkRails.encode_abs_sum_bound G S z.u z.v (z.u+z.v) (Nat.le_refl _)
  have hsum : z.u+z.v<2^(narrowSkywalkRouteWidth i-1) := by
    by_cases hi0 : i≤255
    · have hn : narrowSkywalkRouteWidth i=258 := by unfold narrowSkywalkRouteWidth; omega
      rw [hn]
      exact SkywalkNat.iter_sum_initial_width p x 256 i hp hx
    · have hw := iter_sum_width x p i hp0 hx0 hpo hp hx hc (by omega)
      change z.u+z.v≤2^(511-i) at hw
      have hn : narrowSkywalkRouteWidth i-1=(511-i)+1 ∨ (i=511 ∧ narrowSkywalkRouteWidth i-1=2) := by
        unfold narrowSkywalkRouteWidth; omega
      rcases hn with hn|⟨h511,hn⟩
      · rw [hn,pow_succ]
        have hpos : 0<2^(511-i) := by positivity
        omega
      · rw [hn]
        subst h511
        norm_num at hw
        omega
  have hsum' : ((z.u+z.v:Nat):Int)<((2^(narrowSkywalkRouteWidth i-1):Nat):Int) := by
    exact_mod_cast hsum
  have ha := abs_le.mp hb.1
  have hb' := abs_le.mp hb.2
  change -((2^(narrowSkywalkRouteWidth i-1):Nat):Int)≤(SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a ∧
    (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a<((2^(narrowSkywalkRouteWidth i-1):Nat):Int) ∧
    -((2^(narrowSkywalkRouteWidth i-1):Nat):Int)≤(SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b ∧
    (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b<((2^(narrowSkywalkRouteWidth i-1):Nat):Int)
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- Universal input fit for the narrowed adder of tick `i`. -/
theorem narrowSkywalk_iter_fit (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x)
    (hpo : p%2=1) (hp : p<2^256) (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
    let n := narrowSkywalkWidth i
    (r.a+r.b)%2=1 ∧
    -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route r.a r.b).1/2 ∧
    (SkywalkRails.route r.a r.b).1/2 < ((2^(n-1):Nat):Int) ∧
    -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route r.a r.b).2 ∧
    (SkywalkRails.route r.a r.b).2 < ((2^(n-1):Nat):Int) := by
  dsimp only
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  let k := narrowSkywalkWidth i-1
  have hk : 0<k := by dsimp only [k]; unfold narrowSkywalkWidth; omega
  have hn : narrowSkywalkWidth i-1=k := rfl
  have hsum : z.u+z.v≤2^k := by
    by_cases he : i≤254
    · have hk' : k=257 := by dsimp only [k]; unfold narrowSkywalkWidth; omega
      rw [hk']
      exact Nat.le_of_lt (SkywalkNat.iter_sum_initial_width p x 256 i hp hx)
    · have hw := iter_sum_width x p i hp0 hx0 hpo hp hx hc (by omega)
      change z.u+z.v≤2^(511-i) at hw
      have hle : 511-i≤k := by dsimp only [k]; unfold narrowSkywalkWidth; omega
      exact hw.trans (Nat.pow_le_pow_right (by norm_num) hle)
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at he
  rw [he]
  have hvalid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  have hpar := SkywalkRails.encode_odd_sum G S (z.u:Int) (z.v:Int) (by
    have hodd := hvalid.2.1
    exact_mod_cast hodd)
  have hb := SkywalkRails.encode_abs_sum_bound G S z.u z.v (2^k) hsum
  have hr := SkywalkRails.route_half_width _ _ k hk hpar hb.1 hb.2
  have hpw : (2^k:Nat)=2^(k-1)*2 := by
    calc
      2^k=2^((k-1)+1) := by congr 1; omega
      _=2^(k-1)*2 := pow_succ 2 (k-1)
  have hpw' : ((2^k:Nat):Int)=((2^(k-1):Nat):Int)*2 := by
    exact_mod_cast hpw
  have hpositive : 0<((2^(k-1):Nat):Int) := by positivity
  have hH := abs_le.mp hr.2
  have hO := abs_lt.mp hr.1
  rw [hn]
  change ((SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a+
    (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b)%2=1 ∧
    -((2^k:Nat):Int)≤(SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).1/2 ∧
    (SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).1/2<((2^k:Nat):Int) ∧
    -((2^k:Nat):Int)≤(SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).2 ∧
    (SkywalkRails.route (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).a
      (SkywalkRails.encode G S (z.u:Int) (z.v:Int)).b).2<((2^k:Nat):Int)
  exact ⟨hpar,by omega,by omega,by omega,hO.2⟩

end ECDSAAdd.Entrant.W
