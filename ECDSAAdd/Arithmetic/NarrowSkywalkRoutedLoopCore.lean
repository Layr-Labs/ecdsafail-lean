import ECDSAAdd.Arithmetic.NarrowSkywalkRouteInverse

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- Keep the original zero-M route at full width; only profitable late routes
use the exact sign-bank helper. All512 actual ticks are still emitted. -/
def narrowSkywalkScheduledTick (w : Nat → Wire) (i : Nat) : Program :=
  if narrowSkywalkRouteWidth i=258 then
    narrowSkywalkTick (skywalkPoolTick w i) (narrowSkywalkWidth i)
  else narrowSkywalkRoutedTick (skywalkPoolTick w i)
    (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i)

def narrowSkywalkScheduledUntick (w : Nat → Wire) (i : Nat) : Program :=
  if narrowSkywalkRouteWidth i=258 then
    narrowSkywalkUntick (skywalkPoolTick w i) (narrowSkywalkWidth i)
  else narrowSkywalkRoutedUntick (skywalkPoolTick w i)
    (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i)

def narrowSkywalkRoutedLoop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => narrowSkywalkScheduledTick w i ++ narrowSkywalkRoutedLoop w (i+1) n

def narrowSkywalkRoutedUnloop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => narrowSkywalkRoutedUnloop w (i+1) n ++ narrowSkywalkScheduledUntick w i

attribute [local irreducible] narrowSkywalkTick narrowSkywalkUntick
attribute [local irreducible] narrowSkywalkRoutedTick narrowSkywalkRoutedUntick
attribute [local irreducible] narrowSkywalkScheduledTick narrowSkywalkScheduledUntick
attribute [local irreducible] narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run
attribute [local irreducible] SkywalkTrace.next Nat.iterate

private theorem routed_index_lengths (w : Nat → Wire) (i : Nat) :
    (skywalkPoolTick w i).a.length=258 ∧ (skywalkPoolTick w i).half.length=258 := by
  constructor
  · rw [skywalkPool_a,skywalkPoolA,wireBlock_length]
  · rw [skywalkPool_half,skywalkPoolA,wireBlock_length]

private theorem routed_index_copies (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i<512) (s : BasisState)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s) :
    (narrowSkywalkRouteLayout (skywalkPoolTick w i) (narrowSkywalkRouteWidth i)).Copies s := by
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  have hv := skywalkPool_valid w i hi hn
  have hr := narrowSkywalkRouteWidth_bounds i hi
  have hl := routed_index_lengths w i
  have hf := narrowSkywalkRoute_iter_fit x p i hp0 hx0 hpo hp hx hc hi
  apply narrowSkywalkRoute_copies _ hv _ (by omega) (by omega) r.a r.b s
  · rw [skywalkPool_a]
    exact hs.1
  · rw [skywalkPool_b]
    exact hs.2.1
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2

/-- Exact complete Stage advancement for the actual full-route/late-route
schedule; every parity/sign history and clean future site is retained. -/
theorem narrowSkywalkRoutedStage_step (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i<512) :
    let r := SkywalkRails.encode false false (x:Int) (p:Int)
    Triple (SkywalkIntegerStage w r i) (narrowSkywalkScheduledTick w i)
      (SkywalkIntegerStage w r (i+1)) := by
  dsimp only
  by_cases he : narrowSkywalkRouteWidth i=258
  · rw [narrowSkywalkScheduledTick,if_pos he]
    exact narrowSkywalkStage_step w hn x p i hp0 hx0 hpo hp hx hc hi
  · intro s m hs
    rw [narrowSkywalkScheduledTick,if_neg he]
    have hv := skywalkPool_valid w i hi hn
    have hr := narrowSkywalkRouteWidth_bounds i hi
    have hl := routed_index_lengths w i
    have hcopy := routed_index_copies w hn x p i hp0 hx0 hpo hp hx hc hi s.basis hs
    have hd : s.basis ((skywalkPoolTick w i).carry.headD 0)=false :=
      (regValue_zero _ _).mp hs.2.2.2.2.2.1 _ (narrowSkywalkRoute_delta_mem _ hv)
    rw [narrowSkywalkRoutedTick_eq _ hv _ _ (by omega) (by omega) s m hd hcopy]
    exact narrowSkywalkStage_step w hn x p i hp0 hx0 hpo hp hx hc hi s (m.drop 1) hs

theorem narrowSkywalkScheduledTick_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i<512) (s : State) (m₁ m₂ : List Bool)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (narrowSkywalkScheduledUntick w i) m₂ (run (narrowSkywalkScheduledTick w i) m₁ s)=s := by
  have hv := skywalkPool_valid w i hi hn
  have hr := narrowSkywalkRouteWidth_bounds i hi
  have ha := narrowSkywalkWidth_bounds i hi
  have hl := routed_index_lengths w i
  have fresh := hs.2.2.2.2.1 i (Nat.le_refl i) hi
  by_cases he : narrowSkywalkRouteWidth i=258
  · simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,if_pos he]
    exact narrowSkywalkTick_roundtrip (skywalkPoolTick w i) hv (narrowSkywalkWidth i) (by omega) (by omega) s m₁ m₂ fresh.2 hs.2.2.2.2.2.1
  · simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,if_neg he]
    exact narrowSkywalkRoutedTick_roundtrip (skywalkPoolTick w i) hv (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i) (by omega) (by omega) (by omega) (by omega)
      s m₁ m₂ fresh.2 hs.2.2.2.2.2.1
      (routed_index_copies w hn x p i hp0 hx0 hpo hp hx hc hi s.basis hs)

section LoopSpec
attribute [local irreducible] SkywalkIntegerStage

theorem narrowSkywalkRoutedLoop_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i+n≤512) :
    let r := SkywalkRails.encode false false (x:Int) (p:Int)
    Triple (SkywalkIntegerStage w r i) (narrowSkywalkRoutedLoop w i n)
      (SkywalkIntegerStage w r (i+n)) := by
  dsimp only
  induction n generalizing i with
  | zero =>
    rw [narrowSkywalkRoutedLoop,Nat.add_zero]
    intro s m h
    simpa only [run] using (And.intro (rfl : s.phase=s.phase) h)
  | succ n ih =>
    have hstep := narrowSkywalkRoutedStage_step w hn x p i hp0 hx0 hpo hp hx hc (by omega)
    have htail := ih (i+1) (by omega)
    have hall := hstep.seq htail
    have hindex : i+(n+1)=(i+1)+n := by omega
    rw [narrowSkywalkRoutedLoop,hindex]
    exact hall

end LoopSpec

/-- All physical bits, caller phase, and workspace restore with a fresh
independent inverse record list for the actual concrete512 tick program. -/
theorem narrowSkywalkRoutedLoop_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0<p) (hx0 : 0<x) (hpo : p%2=1) (hp : p<2^256)
    (hx : x<p) (hc : x.Coprime p) (hi : i+n≤512)
    (s : State) (m₁ m₂ : List Bool)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (narrowSkywalkRoutedUnloop w i n) m₂ (run (narrowSkywalkRoutedLoop w i n) m₁ s)=s := by
  induction n generalizing i s m₁ m₂ with
  | zero => simp only [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,run]
  | succ n ih =>
    have hbound : i<512 := by omega
    let tick := narrowSkywalkScheduledTick w i
    simp only [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop]
    rw [run_append,run_append]
    generalize htick : run tick (m₁.take (measurementCount tick)) s=t
    have ht := narrowSkywalkRoutedStage_step w hn x p i hp0 hx0 hpo hp hx hc hbound
      s (m₁.take (measurementCount tick)) hs
    rw [htick] at ht
    have htail := ih (i+1) (by omega) t (m₁.drop (measurementCount tick))
      (m₂.take (measurementCount (narrowSkywalkRoutedUnloop w (i+1) n))) ht.2
    have hrestore := narrowSkywalkScheduledTick_roundtrip w hn x p i hp0 hx0 hpo hp hx hc hbound
      s (m₁.take (measurementCount tick))
      (m₂.drop (measurementCount (narrowSkywalkRoutedUnloop w (i+1) n))) hs
    rw [htick] at hrestore
    rw [htail]
    exact hrestore

/-- Actual gate and cleanup count at each physical pool index. -/
theorem narrowSkywalkScheduledTick_counts (w : Nat → Wire) (i : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i<512) :
    toffoliCount (narrowSkywalkScheduledTick w i)=
      (narrowSkywalkRouteWidth i-1)+(narrowSkywalkWidth i-1) ∧
    measurementCount (narrowSkywalkScheduledTick w i)=
      (narrowSkywalkWidth i-1)+(if narrowSkywalkRouteWidth i=258 then 0 else 1) ∧
    toffoliCount (narrowSkywalkScheduledUntick w i)=
      (narrowSkywalkRouteWidth i-1)+(narrowSkywalkWidth i-1) ∧
    measurementCount (narrowSkywalkScheduledUntick w i)=
      (narrowSkywalkWidth i-1)+(if narrowSkywalkRouteWidth i=258 then 0 else 1) := by
  have hv := skywalkPool_valid w i hi hn
  have hr := narrowSkywalkRouteWidth_bounds i hi
  have ha := narrowSkywalkWidth_bounds i hi
  have hl := routed_index_lengths w i
  by_cases he : narrowSkywalkRouteWidth i=258
  · have ht := narrowSkywalkTick_counts (skywalkPoolTick w i) hv (narrowSkywalkWidth i) (by omega) (by omega)
    rw [skywalkPool_ah,wireBlock_length] at ht
    simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,he]
    simpa using ht
  · have ht := narrowSkywalkRoutedTick_counts (skywalkPoolTick w i) hv (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i) (by omega) (by omega) (by omega) (by omega)
    simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,if_neg he]
    rw [ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
    and_intros <;> first | rfl | trivial | omega

def narrowSkywalkRouteCount (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (narrowSkywalkRouteWidth i-1)+narrowSkywalkRouteCount (i+1) n

def narrowSkywalkCleanupCount (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (if narrowSkywalkRouteWidth i=258 then 0 else 1)+narrowSkywalkCleanupCount (i+1) n

theorem narrowSkywalkRoutedLoop_counts (w : Nat → Wire) (i n : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i+n≤512) :
    toffoliCount (narrowSkywalkRoutedLoop w i n)=narrowSkywalkRouteCount i n+narrowSkywalkAdderCount i n ∧
    measurementCount (narrowSkywalkRoutedLoop w i n)=narrowSkywalkAdderCount i n+narrowSkywalkCleanupCount i n ∧
    toffoliCount (narrowSkywalkRoutedUnloop w i n)=narrowSkywalkRouteCount i n+narrowSkywalkAdderCount i n ∧
    measurementCount (narrowSkywalkRoutedUnloop w i n)=narrowSkywalkAdderCount i n+narrowSkywalkCleanupCount i n := by
  induction n generalizing i with
  | zero => simp [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,narrowSkywalkRouteCount,
      narrowSkywalkAdderCount,narrowSkywalkCleanupCount,toffoliCount,measurementCount]
  | succ n ih =>
    have hc := narrowSkywalkScheduledTick_counts w i hn (by omega)
    have ht := ih (i+1) (by omega)
    simp only [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,narrowSkywalkRouteCount,
      narrowSkywalkAdderCount,narrowSkywalkCleanupCount,toffoliCount_append,measurementCount_append,
      hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
    and_intros <;> first | rfl | trivial | omega

theorem narrowSkywalkScheduledTick_support (w : Nat → Wire) (i : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i<512) :
    wires (narrowSkywalkScheduledTick w i)⊆(skywalkPoolTick w i).wires.toFinset ∧
    wires (narrowSkywalkScheduledUntick w i)⊆(skywalkPoolTick w i).wires.toFinset := by
  have hv := skywalkPool_valid w i hi hn
  have hr := narrowSkywalkRouteWidth_bounds i hi
  have ha := narrowSkywalkWidth_bounds i hi
  have hl := routed_index_lengths w i
  by_cases he : narrowSkywalkRouteWidth i=258
  · simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,if_pos he]
    exact narrowSkywalkTick_wires_subset (skywalkPoolTick w i) hv (narrowSkywalkWidth i) (by omega) (by omega)
  · simp only [narrowSkywalkScheduledTick,narrowSkywalkScheduledUntick,if_neg he]
    exact narrowSkywalkRoutedTick_support (skywalkPoolTick w i) hv (narrowSkywalkRouteWidth i) (narrowSkywalkWidth i) (by omega) (by omega) (by omega) (by omega)

theorem narrowSkywalkRoutedLoop_support (w : Nat → Wire) (i n : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i+n≤512) :
    wires (narrowSkywalkRoutedLoop w i n)⊆(skywalkPoolWires w).toFinset ∧
    wires (narrowSkywalkRoutedUnloop w i n)⊆(skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,wires]
  | succ n ih =>
    have hbound : i<512 := by omega
    have hc := narrowSkywalkScheduledTick_support w i hn hbound
    have h1 := skywalkPool_program_support w i hbound _ hc.1
    have h2 := skywalkPool_program_support w i hbound _ hc.2
    have ht := ih (i+1) (by omega)
    simp only [narrowSkywalkRoutedLoop,narrowSkywalkRoutedUnloop,wires_append,Finset.union_subset_iff]
    exact ⟨⟨h1,ht.1⟩,ht.2,h2⟩

end ECDSAAdd.Arithmetic
