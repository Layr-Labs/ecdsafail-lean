import ECDSAAdd.Arithmetic.SkywalkIntegerTick
import ECDSAAdd.Arithmetic.SkywalkPool

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic

def skywalkIntegerLoop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => skywalkIntegerTick (skywalkPoolTick w i) ++ skywalkIntegerLoop w (i+1) n

def skywalkIntegerUnloop (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => skywalkIntegerUnloop w (i+1) n ++ skywalkIntegerUntick (skywalkPoolTick w i)

attribute [local irreducible] skywalkIntegerTick skywalkIntegerUntick
attribute [local irreducible] skywalkIntegerLoop skywalkIntegerUnloop run

/-- Complete concrete-pool stage: current rails and orientation, actual past
records, all future fresh sites, reused carry, and the seed orientation. -/
def SkywalkIntegerStage (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (s : BasisState) : Prop :=
  let ri := SkywalkTrace.next^[i] r
  signedRegValue (skywalkPoolA w i) s=ri.a ∧
  signedRegValue (skywalkPoolB w) s=ri.b ∧
  s (w (skywalkPoolPreviousId i))=ri.g ∧
  (∀ j,j < i → s (w j)=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).1 ∧
    s (w (1028+j))=(SkywalkTrace.code (SkywalkTrace.next^[j] r)).2) ∧
  (∀ j,i≤j → j<512 → s (w (j+258))=false ∧ s (w (1028+j))=false) ∧
  regValue (wireBlock w 1540 257) s=0 ∧ s (w 1797)=false

private theorem pool_index_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<512) (hj : j<1798) (hm : j∉skywalkPoolTickIds i) :
    w j∉(skywalkPoolTick w i).wires := by
  rw [skywalkPool_wires_map]
  intro h
  obtain ⟨k,hk,he⟩ := List.mem_map.mp h
  have hkj := skywalkPool_index_inj w hn k j (skywalkPool_id_bound i k hi hk) hj he
  subst k
  exact hm hk

private theorem past_orientation_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<512) (hj : j+1< i) :
    w j∉(skywalkPoolTick w i).wires := by
  apply pool_index_outside w hn i j hi (by omega)
  have hz : i≠0 := by omega
  simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
    List.mem_append,List.mem_range'_1]
  omega

private theorem past_sign_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i j : Nat) (hi : i<512) (hj : j < i) :
    w (1028+j)∉(skywalkPoolTick w i).wires := by
  apply pool_index_outside w hn i (1028+j) hi (by omega)
  by_cases hz : i=0
  · omega
  · simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
      List.mem_append,List.mem_range'_1]
    omega

private theorem initial_orientation_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) (hz : i≠0) :
    w 1797∉(skywalkPoolTick w i).wires := by
  apply pool_index_outside w hn i 1797 hi (by omega)
  simp only [skywalkPoolTickIds,skywalkPoolPreviousId,if_neg hz,List.mem_cons,
    List.mem_append,List.mem_range'_1]
  omega

private theorem tick_outside (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (i : Nat) (hi : i<512) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉(skywalkPoolTick w i).wires) :
    (run (skywalkIntegerTick (skywalkPoolTick w i)) m s).basis q=s.basis q := by
  have hs := skywalkIntegerTick_wires_subset (skywalkPoolTick w i) (skywalkPool_valid w i hi hn)
  exact run_preserves_outside (skywalkIntegerTick (skywalkPoolTick w i)) m s q
    (fun hm => hq (List.mem_toFinset.mp (hs.1 hm)))

/-- One concrete tick advances the complete pool partition and extends the
actual transcript while preserving every earlier record and future zero site. -/
theorem skywalkIntegerStage_step (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (r : SkywalkRails.State) (i : Nat) (hi : i<512)
    (hodd : ((SkywalkTrace.next^[i] r).a+(SkywalkTrace.next^[i] r).b)%2=1) :
    Triple (SkywalkIntegerStage w r i) (skywalkIntegerTick (skywalkPoolTick w i))
      (SkywalkIntegerStage w r (i+1)) := by
  intro s m hin
  let L := skywalkPoolTick w i
  let ri := SkywalkTrace.next^[i] r
  let t := SkywalkRails.step ri
  generalize hout : run (skywalkIntegerTick L) m s = out
  have hv := skywalkPool_valid w i hi hn
  have fresh := hin.2.2.2.2.1 i (Nat.le_refl i) hi
  have hnative : SkywalkIntegerInput L ri.a ri.b ri.g s.basis := by
    refine ⟨?_,?_,hin.2.2.1,fresh.1,fresh.2,hin.2.2.2.2.2.1⟩
    · rw [skywalkPool_a]
      exact hin.1
    · rw [skywalkPool_b]
      exact hin.2.1
  obtain ⟨hf,ho⟩ := skywalkIntegerTick_spec L hv ri.a ri.b ri.g hodd s m hnative
  rw [hout] at hf ho
  have hframe : ∀ q, q∉L.wires → out.basis q=s.basis q := by
    intro q hq
    have hh := tick_outside w hn i hi s m q hq
    change (run (skywalkIntegerTick L) m s).basis q=s.basis q at hh
    rw [hout] at hh
    exact hh
  change signedRegValue L.half out.basis=t.h ∧ signedRegValue L.b out.basis=t.k ∧
    out.basis L.a0=t.g ∧ out.basis L.history=t.s ∧ out.basis L.previous=ri.g ∧
    regValue L.carry out.basis=0 at ho
  have hnext : SkywalkTrace.next^[i+1] r=SkywalkRails.railsOf t := by
    rw [Function.iterate_succ_apply']
    rfl
  refine ⟨hf,?_⟩
  dsimp only [SkywalkIntegerStage]
  rw [hnext]
  refine ⟨?_,?_,?_,?_,?_,ho.2.2.2.2.2,?_⟩
  · have hh := ho.1
    rw [skywalkPool_half] at hh
    exact hh
  · have hh := ho.2.1
    rw [skywalkPool_b] at hh
    exact hh
  · change out.basis (skywalkPoolTick w (i+1)).previous=t.g
    rw [(skywalkPool_chain w i).2.2]
    exact ho.2.2.1
  · intro j hj
    by_cases heq : j=i
    · subst j
      exact ⟨ho.2.2.1,ho.2.2.2.1⟩
    · have hji : j < i := by omega
      have priorValues := hin.2.2.2.1 j hji
      have kg : out.basis (w j)=s.basis (w j) := by
        by_cases hlast : j+1=i
        · have hiz : i≠0 := by omega
          have hpidx : skywalkPoolPreviousId i=j := by
            rw [skywalkPoolPreviousId,if_neg hiz]
            omega
          have hh := ho.2.2.2.2.1.trans hin.2.2.1.symm
          simpa only [L,skywalkPoolTick,hpidx] using hh
        · exact hframe (w j)
            (past_orientation_outside w hn i j hi (by omega))
      have ks := hframe (w (1028+j))
        (past_sign_outside w hn i j hi hji)
      exact ⟨kg.trans priorValues.1,ks.trans priorValues.2⟩
  · intro j hj hjmax
    have priorValues := hin.2.2.2.2.1 j (by omega) hjmax
    have hnew := skywalkPool_fresh_previous w j i hjmax (by omega) hn
    have ke := hframe (w (j+258)) hnew.1
    have ks := hframe (w (1028+j)) hnew.2
    exact ⟨ke.trans priorValues.1,ks.trans priorValues.2⟩
  · by_cases hz : i=0
    · subst i
      exact (ho.2.2.2.2.1.trans hin.2.2.1.symm).trans hin.2.2.2.2.2.2
    · exact (hframe (w 1797)
        (initial_orientation_outside w hn i hi hz)).trans hin.2.2.2.2.2.2

private theorem encoded_iter_odd (i : Nat) (x p : Nat) (hp0 : 0<p) (hpo : p%2=1) :
    let r := SkywalkRails.encode false false (x : Int) (p : Int)
    ((SkywalkTrace.next^[i] r).a+(SkywalkTrace.next^[i] r).b)%2=1 := by
  dsimp only
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded i false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at he
  rw [he]
  have hv := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at hv
  exact SkywalkRails.encode_odd_sum G S _ _ (by omega)

attribute [local irreducible] SkywalkTrace.next Nat.iterate

section LoopSpec
attribute [local irreducible] SkywalkIntegerStage

/-- All512 physical ticks are instantiated by the concrete1798-wire pool.
The stage conclusion describes the complete integer pool, not only its rails. -/
theorem skywalkIntegerLoop_spec (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0<p) (hpo : p%2=1) (hi : i+n≤512) :
    let r := SkywalkRails.encode false false (x : Int) (p : Int)
    Triple (SkywalkIntegerStage w r i) (skywalkIntegerLoop w i n)
      (SkywalkIntegerStage w r (i+n)) := by
  dsimp only
  induction n generalizing i with
  | zero =>
    rw [skywalkIntegerLoop,Nat.add_zero]
    intro s m h
    simpa only [run] using (And.intro (rfl : s.phase=s.phase) h)
  | succ n ih =>
    have hstep := skywalkIntegerStage_step w hn _ i (by omega) (encoded_iter_odd i x p hp0 hpo)
    have htail := ih (i+1) (by omega)
    have hall := hstep.seq htail
    have hindex : i+(n+1)=(i+1)+n := by omega
    rw [skywalkIntegerLoop,hindex]
    exact hall

end LoopSpec

private theorem block_member (w : Nat → Wire) (start len j : Nat)
    (hlo : start≤j) (hhi : j<start+len) : w j∈wireBlock w start len := by
  apply List.mem_map.mpr
  exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

/-- The stage assertion uniquely determines every one of the1798 pool bits.
External registers and the global input phase are intentionally unrestricted. -/
theorem skywalkIntegerStage_agrees (w : Nat → Wire) (r : SkywalkRails.State) (i : Nat)
    (hi : i≤512) (s t : BasisState) (hs : SkywalkIntegerStage w r i s)
    (ht : SkywalkIntegerStage w r i t) : ∀ q∈skywalkPoolWires w,s q=t q := by
  have hA := (signedRegValue_eq_iff (skywalkPoolA w i) s t).mp (hs.1.trans ht.1.symm)
  have hB := (signedRegValue_eq_iff (skywalkPoolB w) s t).mp (hs.2.1.trans ht.2.1.symm)
  intro q hq
  change q∈(List.range' 0 1798).map w at hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hj
  by_cases hpast : j < i
  · exact (hs.2.2.2.1 j hpast).1.trans (ht.2.2.2.1 j hpast).1.symm
  by_cases ha : j < i+258
  · exact hA (w j) (block_member w i 258 j (by omega) ha)
  by_cases hf : j<770
  · have hk0 : i≤j-258 := by omega
    have hk1 : j-258<512 := by omega
    have he : j-258+258=j := by omega
    have h1 := (hs.2.2.2.2.1 (j-258) hk0 hk1).1
    have h2 := (ht.2.2.2.2.1 (j-258) hk0 hk1).1
    rw [he] at h1 h2
    exact h1.trans h2.symm
  by_cases hb : j<1028
  · exact hB (w j) (block_member w 770 258 j (by omega) hb)
  by_cases hps : j<1028+i
  · have hk : j-1028< i := by omega
    have he : 1028+(j-1028)=j := by omega
    have h1 := (hs.2.2.2.1 (j-1028) hk).2
    have h2 := (ht.2.2.2.1 (j-1028) hk).2
    rw [he] at h1 h2
    exact h1.trans h2.symm
  by_cases hfs : j<1540
  · have hk0 : i≤j-1028 := by omega
    have hk1 : j-1028<512 := by omega
    have he : 1028+(j-1028)=j := by omega
    have h1 := (hs.2.2.2.2.1 (j-1028) hk0 hk1).2
    have h2 := (ht.2.2.2.2.1 (j-1028) hk0 hk1).2
    rw [he] at h1 h2
    exact h1.trans h2.symm
  by_cases hc : j<1797
  · have hm := block_member w 1540 257 j (by omega) hc
    have h1 := (regValue_zero _ _).mp hs.2.2.2.2.2.1 (w j) hm
    have h2 := (regValue_zero _ _).mp ht.2.2.2.2.2.1 (w j) hm
    exact h1.trans h2.symm
  have he : j=1797 := by omega
  subst j
  exact hs.2.2.2.2.2.2.trans ht.2.2.2.2.2.2.symm

/-- A record pass followed by its reverse recovers the full physical State
with fresh independent measurement records, using concrete pool layouts. -/
theorem skywalkIntegerLoop_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i n : Nat) (hp0 : 0<p) (hpo : p%2=1) (hi : i+n≤512)
    (s : State) (m₁ m₂ : List Bool)
    (hs : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) i s.basis) :
    run (skywalkIntegerUnloop w i n) m₂ (run (skywalkIntegerLoop w i n) m₁ s)=s := by
  induction n generalizing i s m₁ m₂ with
  | zero => simp only [skywalkIntegerLoop,skywalkIntegerUnloop,run]
  | succ n ih =>
    have hbound : i<512 := by omega
    have hv := skywalkPool_valid w i hbound hn
    let tick := skywalkIntegerTick (skywalkPoolTick w i)
    simp only [skywalkIntegerLoop,skywalkIntegerUnloop]
    rw [run_append,run_append]
    generalize htick : run tick (m₁.take (measurementCount tick)) s = t
    have ht := skywalkIntegerStage_step w hn _ i hbound (encoded_iter_odd i x p hp0 hpo)
      s (m₁.take (measurementCount tick)) hs
    rw [htick] at ht
    have htail := ih (i+1) (by omega) t (m₁.drop (measurementCount tick))
      (m₂.take (measurementCount (skywalkIntegerUnloop w (i+1) n))) ht.2
    have fresh := hs.2.2.2.2.1 i (Nat.le_refl i) hbound
    have hrestore := skywalkIntegerTick_roundtrip (skywalkPoolTick w i) hv s
      (m₁.take (measurementCount tick))
      (m₂.drop (measurementCount (skywalkIntegerUnloop w (i+1) n))) fresh.2 hs.2.2.2.2.2.1
    rw [htick] at hrestore
    rw [htail]
    exact hrestore

theorem skywalkIntegerLoop_counts (w : Nat → Wire) (i n : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i+n≤512) :
    toffoliCount (skywalkIntegerLoop w i n)=514*n ∧
    measurementCount (skywalkIntegerLoop w i n)=257*n ∧
    toffoliCount (skywalkIntegerUnloop w i n)=514*n ∧
    measurementCount (skywalkIntegerUnloop w i n)=257*n := by
  induction n generalizing i with
  | zero => simp [skywalkIntegerLoop,skywalkIntegerUnloop,toffoliCount,measurementCount]
  | succ n ih =>
    have hv := skywalkPool_valid w i (by omega) hn
    have hc := skywalkIntegerTick_counts _ hv
    rw [skywalkPool_ah,wireBlock_length] at hc
    have ht := ih (i+1) (by omega)
    simp only [skywalkIntegerLoop,skywalkIntegerUnloop,toffoliCount_append,
      measurementCount_append,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,
      ht.1,ht.2.1,ht.2.2.1,ht.2.2.2]
    omega

theorem skywalkIntegerLoop_support (w : Nat → Wire) (i n : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hi : i+n≤512) :
    wires (skywalkIntegerLoop w i n)⊆(skywalkPoolWires w).toFinset ∧
    wires (skywalkIntegerUnloop w i n)⊆(skywalkPoolWires w).toFinset := by
  induction n generalizing i with
  | zero => simp [skywalkIntegerLoop,skywalkIntegerUnloop,wires]
  | succ n ih =>
    have hbound : i<512 := by omega
    have hv := skywalkPool_valid w i hbound hn
    have hc := skywalkIntegerTick_wires_subset _ hv
    have h1 := skywalkPool_program_support w i hbound _ hc.1
    have h2 := skywalkPool_program_support w i hbound _ hc.2
    have ht := ih (i+1) (by omega)
    simp only [skywalkIntegerLoop,skywalkIntegerUnloop,wires_append,Finset.union_subset_iff]
    exact ⟨⟨h1,ht.1⟩,ht.2,h2⟩

private theorem pool_write_agrees (W : Finset Wire) (s t : BasisState) (q : Wire) (v : Bool)
    (h : ∀ w∈W, s w=t w) :
    ∀ w∈W, writeBit s q v w=writeBit t q v w := by
  intro w hw
  by_cases he : w=q
  · subst w; simp [writeBit]
  · simp [writeBit,Function.update,he,h w hw]

private theorem pool_correct_agrees (cs : List Correction) (W : Finset Wire)
    (hc : correctionWires cs ⊆ W) (s t : State) (hp : s.phase=t.phase)
    (hb : ∀ w∈W, s.basis w=t.basis w) :
    (correct cs s).phase=(correct cs t).phase ∧
    ∀ w∈W, (correct cs s).basis w=(correct cs t).basis w := by
  induction cs generalizing s t with
  | nil => exact ⟨hp,hb⟩
  | cons c cs ih =>
    have ht : correctionWires cs ⊆ W := by
      intro w h
      apply hc
      cases c <;> exact Finset.mem_union_right _ h
    cases c with
    | Z q =>
      apply ih ht
      · simp only [hp,hb q (hc (by simp [correctionWires]))]
      · exact hb
    | CZ a b =>
      apply ih ht
      · simp only [hp,hb a (hc (by simp [correctionWires])),hb b (hc (by simp [correctionWires]))]
      · exact hb

theorem pool_run_agrees (p : Program) (W : Finset Wire) (hw : wires p ⊆ W)
    (m : List Bool) (s t : State) (hp : s.phase=t.phase)
    (hb : ∀ w∈W, s.basis w=t.basis w) :
    (run p m s).phase=(run p m t).phase ∧
    ∀ w∈W, (run p m s).basis w=(run p m t).basis w := by
  induction p generalizing m s t with
  | nil => simpa only [run] using (And.intro hp hb)
  | cons c p ih =>
    have ht : wires p ⊆ W := fun _ h => hw (Finset.mem_union_right _ h)
    have hi : c.wires ⊆ W := fun _ h => hw (Finset.mem_union_left _ h)
    cases c with
    | X q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires]))]
        exact pool_write_agrees W s.basis t.basis q _ hb
    | CX a q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires])),hb a (hi (by simp [Instr.wires]))]
        exact pool_write_agrees W s.basis t.basis q _ hb
    | CCX a b q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires])),hb a (hi (by simp [Instr.wires])),
          hb b (hi (by simp [Instr.wires]))]
        exact pool_write_agrees W s.basis t.basis q _ hb
    | measureX q c0 c1 =>
      simp only [run]
      have hc : correctionWires (if m.headD false then c1 else c0) ⊆ W := by
        split <;> intro w hw <;> apply hi <;> simp_all [Instr.wires]
      have he := pool_correct_agrees _ W hc
        ⟨s.phase ^^ (m.headD false && s.basis q),writeBit s.basis q false⟩
        ⟨t.phase ^^ (m.headD false && t.basis q),writeBit t.basis q false⟩
        (by simp only [hp,hb q (hi (by simp [Instr.wires]))])
        (pool_write_agrees W s.basis t.basis q false hb)
      exact ih ht _ _ _ he.1 he.2

end ECDSAAdd.Arithmetic
