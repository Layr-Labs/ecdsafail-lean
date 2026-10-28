import ECDSAAdd.Arithmetic.NarrowSkywalkRoute
import ECDSAAdd.Arithmetic.NarrowSkywalkLoopCore

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic

private theorem route_take_msb (r : List Wire) (n : Nat) (hn : 0<n) (hle : n≤r.length) :
    r.take (n-1)++[r.getD (n-1) 0]=r.take n := by
  have hidx : n-1<r.length := by omega
  have he : n=(n-1)+1 := by omega
  conv_rhs => rw [he]
  rw [List.getD_eq_getElem _ _ hidx,List.take_add_one,List.getElem?_eq_getElem hidx]
  rfl

/-- A reused carry bit supplies delta; the reference signs are retained bits,
so all omitted high bits and the signs themselves use the Clifford fanout. -/
def narrowSkywalkRouteLayout (L : SkywalkIntegerLayout) (n : Nat) : NarrowSkywalkSwapLayout :=
  {g:=L.a0,delta:=L.carry.headD 0,
   sx:=L.ah.getD (n-2) 0,sy:=L.bh.getD (n-2) 0,
   xlow:=L.ah.take (n-2),ylow:=L.bh.take (n-2),
   xhigh:=L.ah.drop (n-1),yhigh:=L.bh.drop (n-1)}

theorem narrowSkywalkRoute_views (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 2≤n) (hle : n≤L.a.length) :
    (narrowSkywalkRouteLayout L n).x=L.ah ∧ (narrowSkywalkRouteLayout L n).y=L.bh := by
  have hl := L.high_lengths hv
  have hal : L.a.length=L.ah.length+1 := by simp [SkywalkIntegerLayout.a]
  have he : (n-1)-1=n-2 := by omega
  have hx := route_take_msb L.ah (n-1) (by omega) (by omega)
  have hy := route_take_msb L.bh (n-1) (by omega) (by omega)
  rw [he] at hx hy
  simp only [narrowSkywalkRouteLayout,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
    NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank]
  constructor
  · calc
      _ = (L.ah.take (n-2)++[L.ah.getD (n-2) 0])++L.ah.drop (n-1) := by rw [List.append_assoc,List.singleton_append]
      _ = L.ah := by rw [hx,List.take_append_drop]
  · calc
      _ = (L.bh.take (n-2)++[L.bh.getD (n-2) 0])++L.bh.drop (n-1) := by rw [List.append_assoc,List.singleton_append]
      _ = L.bh := by rw [hy,List.take_append_drop]

theorem narrowSkywalkRoute_delta_mem (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.carry.headD 0∈L.carry := by
  have hl := L.record_lengths hv
  have hpos : 0<L.ah.length := by simp [SkywalkIntegerLayout.ah]
  have hc : L.carry.length=L.ah.length := by
    simp only [SkywalkIntegerLayout.half,List.length_append,List.length_singleton] at hl
    omega
  cases he : L.carry with
  | nil => simp only [he,List.length_nil] at hc; omega
  | cons a r => simp

theorem narrowSkywalkRoute_valid (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 2≤n) (hle : n≤L.a.length) : (narrowSkywalkRouteLayout L n).Valid := by
  have hl := L.high_lengths hv
  have vv := narrowSkywalkRoute_views L hv n hn hle
  constructor
  · simp [narrowSkywalkRouteLayout,List.length_take,hl]
  · simp [narrowSkywalkRouteLayout,List.length_drop,hl]
  · simp only [NarrowSkywalkSwapLayout.wires,vv.1,vv.2]
    change (L.a0::L.carry.headD 0::(L.ah++L.bh)).Nodup
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp hv.nodup q
    have hhead : (if L.carry.headD 0==q then 1 else 0)≤L.carry.count q := by
      by_cases he : L.carry.headD 0=q
      · have hp := List.count_pos_iff.mpr (he ▸ narrowSkywalkRoute_delta_mem L hv)
        simp only [he,beq_self_eq_true,if_true]
        omega
      · simp only [beq_iff_eq,if_neg he,Nat.zero_le]
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hc ⊢
    omega

/-- A signed full rail fitting the retained width has its exact prefix value
and every omitted bit equal to the retained sign reference. -/
theorem narrowSkywalkRoute_copies (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 2≤n) (hle : n≤L.a.length) (A B : Int) (s : BasisState)
    (ha : signedRegValue L.a s=A) (hb : signedRegValue L.b s=B)
    (ha0 : -((2^(n-1):Nat):Int)≤A) (ha1 : A<((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int)≤B) (hb1 : B<((2^(n-1):Nat):Int)) :
    (narrowSkywalkRouteLayout L n).Copies s := by
  let R := narrowSkywalkRouteLayout L n
  have vv := narrowSkywalkRoute_views L hv n hn hle
  have hal : L.a.length=L.ah.length+1 := by simp [SkywalkIntegerLayout.a]
  have hxlen : (L.a0::R.xlow++[R.sx]).length=n := by
    simp only [R,narrowSkywalkRouteLayout,List.length_append,List.length_cons,
      List.length_nil,List.length_take]
    omega
  have hylen : (L.b0::R.ylow++[R.sy]).length=n := by
    have hl := L.high_lengths hv
    simp only [R,narrowSkywalkRouteLayout,List.length_append,List.length_cons,
      List.length_nil,List.length_take]
    omega
  have hax : signedRegValue ((L.a0::R.xlow++[R.sx])++R.xhigh) s=A := by
    simp only [List.append_assoc]
    change signedRegValue (L.a0::R.x) s=A
    rw [vv.1]
    exact ha
  have hby : signedRegValue ((L.b0::R.ylow++[R.sy])++R.yhigh) s=B := by
    simp only [List.append_assoc]
    change signedRegValue (L.b0::R.y) s=B
    rw [vv.2]
    exact hb
  have hxa := narrow_signed_prefix (L.a0::R.xlow++[R.sx]) R.xhigh s A (by omega)
    hax (by simpa only [hxlen] using ha0) (by simpa only [hxlen] using ha1)
  have hyb := narrow_signed_prefix (L.b0::R.ylow++[R.sy]) R.yhigh s B (by omega)
    hby (by simpa only [hylen] using hb0) (by simpa only [hylen] using hb1)
  have hsx := signedRegValue_sign (L.a0::R.xlow) R.sx s
  have hsy := signedRegValue_sign (L.b0::R.ylow) R.sy s
  rw [hxa.1] at hsx
  rw [hyb.1] at hsy
  constructor
  · intro q hq
    rcases List.mem_cons.mp hq with he|hq
    · subst q; rfl
    · exact (hxa.2 q hq).trans hsx.symm
  · intro q hq
    rcases List.mem_cons.mp hq with he|hq
    · subst q; rfl
    · exact (hyb.2 q hq).trans hsy.symm

/-- One extra signed input bit protects the inclusive pre-half product cap. -/
def narrowSkywalkRouteWidth (i : Nat) : Nat := min 258 (514-i)

theorem narrowSkywalkRouteWidth_bounds (i : Nat) (hi : i<512) :
    3≤narrowSkywalkRouteWidth i ∧ narrowSkywalkRouteWidth i≤258 ∧
    narrowSkywalkRouteWidth i-1=min 257 (513-i) := by
  unfold narrowSkywalkRouteWidth
  omega

/-- Complete universal input fit for the route. Early states use the strict
initial sum; late states double the inclusive product/sum cap. -/
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
    by_cases hi0 : i≤256
    · have hn : narrowSkywalkRouteWidth i=258 := by unfold narrowSkywalkRouteWidth; omega
      rw [hn]
      exact SkywalkNat.iter_sum_initial_width p x 256 i hp hx
    · have hn : narrowSkywalkRouteWidth i-1=(512-i)+1 := by unfold narrowSkywalkRouteWidth; omega
      rw [hn,pow_succ]
      have hc := SkywalkNat.iter_sum_product_width p x 256 i hp0 hx0 hpo hp hx hc (by omega)
      change z.u+z.v≤2^(512-i) at hc
      have hpos : 0<2^(512-i) := by positivity
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

/-- Replacing a zero-M prefix by an exactly equal one-M prefix shifts only the
remaining stream. The reference record list is never falsely aligned. -/
private theorem route_measured_prefix (p q tail : Program) (hp : measurementCount p=1)
    (hq : measurementCount q=0) (s : State) (m : List Bool)
    (he : ∀ rec,run p rec s=run q [] s) :
    run (p++tail) m s=run (q++tail) (m.drop 1) s := by
  rw [run_append,run_append,hp,hq,List.take_zero,List.drop_zero,he]

/-- The complete full-half/narrow-adder suffix is untouched. -/
def narrowSkywalkRoutedTick (L : SkywalkIntegerLayout) (nr na : Nat) : Program :=
  narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0 ++
    (skywalkSignedHalf L.aSign L.ext ++
      narrowSignedRecord (narrowSkywalkRecordLayout L na) na ++ [.CX L.previous L.a0])

/-- Whole-State tick equality with the accepted narrow-adder path; exactly
one prefix measurement is consumed before its independent arithmetic stream. -/
theorem narrowSkywalkRoutedTick_eq (L : SkywalkIntegerLayout) (hv : L.Valid) (nr na : Nat)
    (hn : 2≤nr) (hle : nr≤L.a.length) (s : State) (m : List Bool)
    (hd : s.basis (L.carry.headD 0)=false)
    (hc : (narrowSkywalkRouteLayout L nr).Copies s.basis) :
    run (narrowSkywalkRoutedTick L nr na) m s=run (narrowSkywalkTick L na) (m.drop 1) s := by
  have vv := narrowSkywalkRoute_views L hv nr hn hle
  have hvR := narrowSkywalkRoute_valid L hv nr hn hle
  have hh := narrowSkywalkRoute_counts _ hvR L.b0
  have hm := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh (L.high_lengths hv) (L.route_nodup hv)).2
  have he : ∀ rec,run (narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0) rec s=
      run (skywalkRoute L.a0 L.b0 L.ah L.bh) [] s := by
    intro rec
    have ho := narrowSkywalkRoute_eq _ hvR L.b0 s rec [] hd hc
    simpa only [vv.1,vv.2] using ho
  simp only [narrowSkywalkRoutedTick,narrowSkywalkTick,List.append_assoc]
  exact route_measured_prefix _ _ _ hh.2 hm s m he

end ECDSAAdd.Arithmetic
