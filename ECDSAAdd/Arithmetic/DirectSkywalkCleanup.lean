import ECDSAAdd.Arithmetic.DirectSkywalkInput

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic.DirectSkywalk
open Secp256k1
attribute [local irreducible] skywalkSeed skywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run

/-- PairFrame plus a source that starts and ends zero is a numerator-only frame. -/
theorem arith_field_frame (L : ModInPlaceLayout) (base s : BasisState) (Z : Nat)
    (ha : regValue L.a base=0) (hf : PairFrame L.z L.a base Z 0 s) :
    ∀ q,q∉L.z → s q=base q := by
  have he := (regValue_eq_iff L.a s base).mp (hf.2.1.trans ha.symm)
  intro q hq
  by_cases hs : q∈L.a
  · exact he q hs
  · exact hf.2.2 q hq hs

theorem arith_pool_away_z (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (q : Wire) (hq : q∈skywalkPoolWires w) : q∉(skywalkSharedField w).z := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [skywalkShared_field_z]
  exact arith_block_away w hn i 2056 257 (by omega) (by omega) (by omega)

theorem arith_loop_outside (back : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (if back then narrowSkywalkRoutedUnloop w 0 512 else narrowSkywalkRoutedLoop w 0 512) m s).basis q=s.basis q := by
  have hp := narrowSkywalkRoutedLoop_support w 0 512 (skywalkShared_integer_nodup w hn) (by omega)
  apply run_preserves_outside
  intro hm
  cases back
  · exact hq (List.mem_toFinset.mp (hp.1 hm))
  · exact hq (List.mem_toFinset.mp (hp.2 hm))

theorem arith_record_outside (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (narrowSkywalkRoutedLoop w 0 512) m s).basis q=s.basis q := by
  simpa only [Bool.false_eq_true,if_false] using arith_loop_outside false w hn s m q hq

theorem arith_unrecord_outside (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (narrowSkywalkRoutedUnloop w 0 512) m s).basis q=s.basis q := by
  simpa only [if_true] using arith_loop_outside true w hn s m q hq

theorem arith_clear_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉skywalkPoolWires w) :
    (run (skywalkArithmeticClear w) m s).basis q=s.basis q := by
  apply (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s m).2.1
  · intro he; subst q; exact hq (arith_mem w 0 1798 512 (by omega) (by omega))
  · intro he; subst q; exact hq (arith_mem w 0 1798 770 (by omega) (by omega))

theorem arith_stage_congr (w : Nat → Wire) (r : SkywalkRails.State)
    (s t : BasisState) (hs : SkywalkIntegerStage w r 512 s)
    (he : ∀ q∈skywalkPoolWires w,t q=s q) : SkywalkIntegerStage w r 512 t := by
  have read (a n : Nat) (hb : a+n ≤ 1798) :
      regValue (wireBlock w a n) t=regValue (wireBlock w a n) s := by
    apply regValue_congr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact he _ (arith_mem w 0 1798 j (by omega) (by omega))
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · unfold signedRegValue skywalkPoolA
    rw [read 512 258 (by omega)]
    exact hs.1
  · unfold signedRegValue skywalkPoolB
    rw [read 770 258 (by omega)]
    exact hs.2.1
  · exact (he _ (arith_mem w 0 1798 511 (by omega) (by omega))).trans hs.2.2.1
  · intro j hj
    exact ⟨(he _ (arith_mem w 0 1798 j (by omega) (by omega))).trans (hs.2.2.2.1 j hj).1,
      (he _ (arith_mem w 0 1798 (1028+j) (by omega) (by omega))).trans (hs.2.2.2.1 j hj).2⟩
  · intro j hj hjmax; omega
  · exact (read 1540 257 (by omega)).trans hs.2.2.2.2.2.1
  · exact (he _ (arith_mem w 0 1798 1797 (by omega) (by omega))).trans hs.2.2.2.2.2.2

theorem arith_clear_transport (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (r f : State) (m1 m2 : List Bool)
    (he : ∀ q,q∉(skywalkSharedField w).z →
      f.basis q=(run (skywalkArithmeticClear w) m1 r).basis q) :
    ∀ q,q∉(skywalkSharedField w).z →
      (run (skywalkArithmeticClear w) m2 f).basis q=r.basis q := by
  let c := run (skywalkArithmeticClear w) m1 r
  have hn' := arith_clear_gates w hn
  have h1 := skywalkTerminalClear_correct _ _ _ hn' f m2
  have h2 := skywalkTerminalClear_correct _ _ _ hn' c m2
  have away (j : Nat) (hj : j=511 ∨ j=512 ∨ j=770) : w j∉(skywalkSharedField w).z := by
    rw [skywalkShared_field_z]
    exact arith_block_away w hn j 2056 257 (by omega) (by omega) (by omega)
  have undo := skywalkTerminalClear_twice _ _ _ hn' r m1 m2
  intro q hq
  have same : (run (skywalkArithmeticClear w) m2 f).basis q=
      (run (skywalkArithmeticClear w) m2 c).basis q := by
    by_cases ha : q=w 512
    · subst q
      unfold skywalkArithmeticClear
      rw [h1.2.2.1,h2.2.2.1,he _ (away _ (Or.inr (Or.inl rfl))),he _ (away _ (Or.inl rfl))]
    by_cases hb : q=w 770
    · subst q
      unfold skywalkArithmeticClear
      rw [h1.2.2.2,h2.2.2.2,he _ (away _ (Or.inr (Or.inr rfl))),he _ (away _ (Or.inl rfl))]
    exact ((h1.2.1 q ha hb).trans (he q hq)).trans (h2.2.1 q ha hb).symm
  exact same.trans (congrArg (fun st : State => st.basis q) undo)

theorem arith_z_input (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s) :
    regValue (skywalkSharedField w).z s=y := by
  change regValue (wireBlock w 2056 256++[w 2312]) s=y
  rw [regValue_append]
  change regValue (skywalkArithmeticNumerator w) s+_=_
  rw [h.2.1]
  simp [regValue,arith_input_bit w hn x y s h 2312 (by omega) (by omega) (by omega)]

theorem arith_preparation_frame (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (s : State) (m1 m2 m3 : List Bool) (q : Wire) (hq : q∈(skywalkSharedField w).z) :
    (run (skywalkArithmeticClear w) m3
      (run (narrowSkywalkRoutedLoop w 0 512) m2
        (run (skywalkSeed (skywalkSharedSeed w) p) m1 s))).basis q=s.basis q := by
  generalize hs1 : run (skywalkSeed (skywalkSharedSeed w) p) m1 s=s1
  generalize hs2 : run (narrowSkywalkRoutedLoop w 0 512) m2 s1=s2
  generalize hs3 : run (skywalkArithmeticClear w) m3 s2=s3
  rw [skywalkShared_field_z] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  have hp := arith_block_away w hn i 0 1798 (by omega) (by omega) (by omega)
  have hs := arith_seed_outside w hn i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc := arith_clear_outside w hn s2 m3 (w i) hp
  rw [hs3] at hc
  have hl := arith_record_outside w hn s1 m2 (w i) hp
  rw [hs2] at hl
  have hf := (skywalkSeed_frame (skywalkSharedSeed w) 258 p
    (skywalkShared_seed_widths w) s m1 (w i) hs).1
  rw [hs1] at hf
  exact hc.trans (hl.trans hf)

theorem arith_clean_preparation (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx0 : 0 < x) (hx : x < p) (s : State) (m1 m2 m3 : List Bool)
    (h : SkywalkArithmeticInput w x y s.basis) :
    SkywalkSharedClean w (run (skywalkArithmeticClear w) m3
      (run (narrowSkywalkRoutedLoop w 0 512) m2
        (run (skywalkSeed (skywalkSharedSeed w) p) m1 s))).basis := by
  generalize hs1 : run (skywalkSeed (skywalkSharedSeed w) p) m1 s=seed
  generalize hs2 : run (narrowSkywalkRoutedLoop w 0 512) m2 seed=recorded
  generalize hs3 : run (skywalkArithmeticClear w) m3 recorded=cleared
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hst0 := arith_seed_stage0 w hn x y hx s m1 h
  rw [hs1] at hst0
  have hstFull := narrowSkywalkRouted512_spec w (skywalkShared_integer_nodup w hn) x p hp0 hx0 hpo arith_modulus_bound hx (arith_coprime x hx0 hx) seed m2 hst0
  rw [hs2] at hstFull
  have hst := hstFull.2
  have hr := arith_clear_words w hn x hx0 hx recorded m3 hst
  rw [hs3] at hr
  have keep (j : Nat) (hj : 1798 ≤ j) (hjmax : j < 2314) : cleared.basis (w j)=seed.basis (w j) := by
    have ho := arith_block_away w hn j 0 1798 hjmax (by omega) (by omega)
    have hc := arith_clear_outside w hn recorded m3 _ ho
    have hl := arith_record_outside w hn seed m2 _ ho
    rw [hs3] at hc
    rw [hs2] at hl
    exact hc.trans hl
  have hp : p < 2^256 := by norm_num [p]
  have hseedFull := skywalkSeed_spec _ 258 p x (skywalkShared_seed_widths w)
    (skywalkShared_seed_nodup w hn) (by omega) hp (hx.trans hp) s m1
      (arith_seed_input w hn x y s.basis h)
  rw [hs1] at hseedFull
  have hseed := hseedFull.2
  have hconst : regValue (wireBlock w 1798 258) cleared.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hseed.constant
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact keep j (by omega) (by omega)
  have hcarry : regValue (wireBlock w 1540 257) cleared.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hst.2.2.2.2.2.1
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have hk := (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) recorded m3).2.1
    change ∀ q,q≠w 512 → q≠w 770 → (run (skywalkArithmeticClear w) m3 recorded).basis q=recorded.basis q at hk
    rw [hs3] at hk
    apply hk
    · intro he; have hi := skywalkShared_index_inj w hn j 512 (by omega) (by omega) he; omega
    · intro he; have hi := skywalkShared_index_inj w hn j 770 (by omega) (by omega) he; omega
  have horient : cleared.basis (w 1797)=false := by
    have hk := (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) recorded m3).2.1
    change ∀ q,q≠w 512 → q≠w 770 → (run (skywalkArithmeticClear w) m3 recorded).basis q=recorded.basis q at hk
    rw [hs3] at hk
    apply Eq.trans (hk _ ?_ ?_) hst.2.2.2.2.2.2
    · intro he; have hi := skywalkShared_index_inj w hn 1797 512 (by omega) (by omega) he; omega
    · intro he; have hi := skywalkShared_index_inj w hn 1797 770 (by omega) (by omega) he; omega
  exact ⟨hr.1,hr.2,hcarry,hconst,horient,(keep 2313 (by omega) (by omega)).trans hseed.cin⟩

theorem arith_tape_clear (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (s : State) (m : List Bool) :
    skywalkTapeControls (run (skywalkArithmeticClear w) m s).basis (skywalkSharedTape w)=
      skywalkTapeControls s.basis (skywalkSharedTape w) := by
  simp only [skywalkTapeControls,skywalkSharedTape,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hib := List.mem_range.mp hi
  have keep (j : Nat) (hj : j=i ∨ j=1028+i) :
      (run (skywalkArithmeticClear w) m s).basis (w j)=s.basis (w j) := by
    apply (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s m).2.1
    · intro he; have hh := skywalkShared_index_inj w hn j 512 (by omega) (by omega) he; omega
    · intro he; have hh := skywalkShared_index_inj w hn j 770 (by omega) (by omega) he; omega
  exact Prod.ext (keep _ (Or.inl rfl)) (keep _ (Or.inr rfl))

theorem arith_seed_components (L : SkywalkSeedLayout) :
    L.a⊆L.usedWires ∧ L.b⊆L.usedWires ∧ L.constant⊆L.usedWires ∧ L.carry⊆L.usedWires := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro q hq <;>
    simp only [SkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append] <;> tauto

theorem arith_seed_away (L : SkywalkSeedLayout) (q : Wire)
    (hi : q≠L.cin) (ha : q∉L.a) (hb : q∉L.b) (hc : q∉L.constant) (hd : q∉L.carry) :
    q∉L.usedWires := by
  simp only [SkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
  tauto

theorem arith_block_subset_shared (w : Nat → Wire) (a n : Nat)
    (hb : a+n ≤ 2314) : wireBlock w a n ⊆ skywalkSharedWires w := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hj
  exact arith_mem w 0 2314 j (by omega) (by omega)

theorem arith_seed_subset_shared (w : Nat → Wire) :
    (skywalkSharedSeed w).usedWires ⊆ skywalkSharedWires w := by
  intro q hq
  change q∈w 2313::(wireBlock w 0 258++wireBlock w 770 258++
    wireBlock w 1798 258++wireBlock w 1540 257) at hq
  rcases List.mem_cons.mp hq with rfl|hr
  · exact arith_mem w 0 2314 2313 (by omega) (by omega)
  · simp only [List.mem_append,or_assoc] at hr
    rcases hr with hq|hq|hq|hq
    · exact arith_block_subset_shared w 0 258 (by omega) hq
    · exact arith_block_subset_shared w 770 258 (by omega) hq
    · exact arith_block_subset_shared w 1798 258 (by omega) hq
    · exact arith_block_subset_shared w 1540 257 (by omega) hq

end ECDSAAdd.Arithmetic.DirectSkywalk
