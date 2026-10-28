import ECDSAAdd.Arithmetic.NarrowSkywalkTick

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic

/-- Exact universal retained arithmetic width; all512 ticks remain present. -/
def narrowSkywalkWidth (i : Nat) : Nat := min 258 (513-i)

theorem narrowSkywalkWidth_bounds (i : Nat) (hi : i<512) :
    2≤narrowSkywalkWidth i ∧ narrowSkywalkWidth i≤258 ∧
    narrowSkywalkWidth i-1=min 257 (512-i) := by
  unfold narrowSkywalkWidth
  omega

/-- Derived from the complete coprime logical trajectory, not a sampled
profile. The strict signed operands are O and E/2 after the full-width route. -/
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
  let k := min 257 (512-i)
  have hk : 0<k := by dsimp only [k]; omega
  have hn := (narrowSkywalkWidth_bounds i hi).2.2
  have hsum : z.u+z.v≤2^k := by
    by_cases he : 257≤512-i
    · have hk' : k=257 := by dsimp only [k]; omega
      rw [hk']
      exact Nat.le_of_lt (SkywalkNat.iter_sum_initial_width p x 256 i hp hx)
    · have hk' : k=512-i := by dsimp only [k]; omega
      rw [hk']
      exact SkywalkNat.iter_sum_product_width p x 256 i hp0 hx0 hpo hp hx hc (by omega)
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


def narrowSkywalkLoop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => narrowSkywalkTick (skywalkPoolTick w i) (narrowSkywalkWidth i) ++
      narrowSkywalkLoop w (i+1) n

def narrowSkywalkUnloop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => narrowSkywalkUnloop w (i+1) n ++
      narrowSkywalkUntick (skywalkPoolTick w i) (narrowSkywalkWidth i)

attribute [local irreducible] narrowSkywalkTick narrowSkywalkUntick
attribute [local irreducible] narrowSkywalkLoop narrowSkywalkUnloop run
attribute [local irreducible] SkywalkTrace.next Nat.iterate

/-- Narrow ticks advance the identical complete physical pool and actual
history as the accepted wide path, under the canonical nonzero input contract. -/
theorem narrowSkywalkStage_step (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkRails.encode false false (x:Int) (p:Int)
    Triple (SkywalkIntegerStage w r i)
      (narrowSkywalkTick (skywalkPoolTick w i) (narrowSkywalkWidth i))
      (SkywalkIntegerStage w r (i+1)) := by
  dsimp only
  intro s m hin
  let r := SkywalkRails.encode false false (x:Int) (p:Int)
  let ri := SkywalkTrace.next^[i] r
  let L := skywalkPoolTick w i
  have hv := skywalkPool_valid w i hi hn
  have hf := narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  have hw := narrowSkywalkWidth_bounds i hi
  have hlength : L.half.length=258 := by
    rw [skywalkPool_half,skywalkPoolA,wireBlock_length]
  have fresh := hin.2.2.2.2.1 i (Nat.le_refl i) hi
  have hnative : SkywalkIntegerInput L ri.a ri.b ri.g s.basis := by
    refine ⟨?_,?_,hin.2.2.1,fresh.1,fresh.2,hin.2.2.2.2.2.1⟩
    · rw [skywalkPool_a]
      exact hin.1
    · rw [skywalkPool_b]
      exact hin.2.1
  have heq := narrowSkywalkTick_eq L hv (narrowSkywalkWidth i) (by omega)
    (by omega) ri.a ri.b ri.g hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 s m hnative
  rw [heq]
  exact skywalkIntegerStage_step w hn r i hi hf.1 s m hin

section LoopSpec
attribute [local irreducible] SkywalkIntegerStage

/-- Actual narrowed512 execution preserves the complete stage assertion. -/
theorem narrowSkywalkLoop_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i+n≤512) :
    let r := SkywalkRails.encode false false (x:Int) (p:Int)
    Triple (SkywalkIntegerStage w r i) (narrowSkywalkLoop w i n)
      (SkywalkIntegerStage w r (i+n)) := by
  dsimp only
  induction n generalizing i with
  | zero =>
    rw [narrowSkywalkLoop,Nat.add_zero]
    intro s m h
    simpa only [run] using (And.intro (rfl : s.phase=s.phase) h)
  | succ n ih =>
    have hstep := narrowSkywalkStage_step w hn x p i hp0 hx0 hpo hp hx hc (by omega)
    have htail := ih (i+1) (by omega)
    have hall := hstep.seq htail
    have hindex : i+(n+1)=(i+1)+n := by omega
    rw [narrowSkywalkLoop,hindex]
    exact hall

end LoopSpec

/-- Entire physical State restoration with independent fresh inverse records. -/
theorem narrowSkywalkLoop_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i+n≤512)
    (s : State) (m₁ m₂ : List Bool)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (narrowSkywalkUnloop w i n) m₂ (run (narrowSkywalkLoop w i n) m₁ s)=s := by
  induction n generalizing i s m₁ m₂ with
  | zero => simp only [narrowSkywalkLoop,narrowSkywalkUnloop,run]
  | succ n ih =>
    have hbound : i<512 := by omega
    have hv := skywalkPool_valid w i hbound hn
    have hw := narrowSkywalkWidth_bounds i hbound
    have hlength : (skywalkPoolTick w i).half.length=258 := by
      rw [skywalkPool_half,skywalkPoolA,wireBlock_length]
    let tick := narrowSkywalkTick (skywalkPoolTick w i) (narrowSkywalkWidth i)
    simp only [narrowSkywalkLoop,narrowSkywalkUnloop]
    rw [run_append,run_append]
    generalize htick : run tick (m₁.take (measurementCount tick)) s=t
    have ht := narrowSkywalkStage_step w hn x p i hp0 hx0 hpo hp hx hc hbound
      s (m₁.take (measurementCount tick)) hs
    rw [htick] at ht
    have htail := ih (i+1) (by omega) t (m₁.drop (measurementCount tick))
      (m₂.take (measurementCount (narrowSkywalkUnloop w (i+1) n))) ht.2
    have fresh := hs.2.2.2.2.1 i (Nat.le_refl i) hbound
    have hrestore := narrowSkywalkTick_roundtrip (skywalkPoolTick w i) hv (narrowSkywalkWidth i)
      (by omega) (by omega) s (m₁.take (measurementCount tick))
      (m₂.drop (measurementCount (narrowSkywalkUnloop w (i+1) n))) fresh.2 hs.2.2.2.2.2.1
    rw [htick] at hrestore
    rw [htail]
    exact hrestore

def narrowSkywalkAdderCount (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (narrowSkywalkWidth i-1)+narrowSkywalkAdderCount (i+1) n

theorem narrowSkywalkLoop_counts (w : Nat → Wire) (i n : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i+n≤512) :
    toffoliCount (narrowSkywalkLoop w i n)=257*n+narrowSkywalkAdderCount i n ∧
    measurementCount (narrowSkywalkLoop w i n)=narrowSkywalkAdderCount i n ∧
    toffoliCount (narrowSkywalkUnloop w i n)=257*n+narrowSkywalkAdderCount i n ∧
    measurementCount (narrowSkywalkUnloop w i n)=narrowSkywalkAdderCount i n := by
  induction n generalizing i with
  | zero => simp [narrowSkywalkLoop,narrowSkywalkUnloop,narrowSkywalkAdderCount,toffoliCount,measurementCount]
  | succ n ih =>
    have hbound : i<512 := by omega
    have hv := skywalkPool_valid w i hbound hn
    have hw := narrowSkywalkWidth_bounds i hbound
    have hlength : (skywalkPoolTick w i).half.length=258 := by
      rw [skywalkPool_half,skywalkPoolA,wireBlock_length]
    have hc := narrowSkywalkTick_counts _ hv (narrowSkywalkWidth i) (by omega) (by omega)
    rw [skywalkPool_ah,wireBlock_length] at hc
    have ht := ih (i+1) (by omega)
    simp only [narrowSkywalkLoop,narrowSkywalkUnloop,narrowSkywalkAdderCount,toffoliCount_append,
      measurementCount_append,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
    exact ⟨by ring,trivial,by ring,Nat.add_comm _ _⟩

theorem narrowSkywalkLoop_support (w : Nat → Wire) (i n : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i+n≤512) :
    wires (narrowSkywalkLoop w i n)⊆(skywalkPoolWires w).toFinset ∧
    wires (narrowSkywalkUnloop w i n)⊆(skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [narrowSkywalkLoop,narrowSkywalkUnloop,wires]
  | succ n ih =>
    have hbound : i<512 := by omega
    have hv := skywalkPool_valid w i hbound hn
    have hw := narrowSkywalkWidth_bounds i hbound
    have hlength : (skywalkPoolTick w i).half.length=258 := by
      rw [skywalkPool_half,skywalkPoolA,wireBlock_length]
    have hc := narrowSkywalkTick_wires_subset _ hv (narrowSkywalkWidth i) (by omega) (by omega)
    have h1 := skywalkPool_program_support w i hbound _ hc.1
    have h2 := skywalkPool_program_support w i hbound _ hc.2
    have ht := ih (i+1) (by omega)
    simp only [narrowSkywalkLoop,narrowSkywalkUnloop,wires_append,Finset.union_subset_iff]
    exact ⟨⟨h1,ht.1⟩,ht.2,h2⟩

end ECDSAAdd.Arithmetic
