import ECDSAAdd.Arithmetic.SkywalkArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic.DirectSkywalk
open Secp256k1
attribute [local irreducible] skywalkSeed skywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop run

theorem arith_coprime (x : Nat) (hx0 : 0 < x) (hx : x < p) : x.Coprime p := by
  apply Nat.Coprime.symm
  apply p_prime.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)

theorem arith_modulus_bound : p < 2^256 := by norm_num [p]

theorem arith_mem (w : Nat → Wire) (start len j : Nat)
    (hlo : start ≤ j) (hhi : j < start+len) : w j∈wireBlock w start len := by
  apply List.mem_map.mpr
  exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem arith_block_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i start len : Nat) (hi : i < 2314) (hb : start+len ≤ 2314)
    (ha : i < start ∨ start+len ≤ i) : w i∉wireBlock w start len := by
  intro hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  simp only [List.mem_range'_1] at hj
  have hh := skywalkShared_index_inj w hn j i (by omega) hi he
  omega

theorem arith_input_bit (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s)
    (i : Nat) (hi : i < 2314) (hx : i < 770 ∨ 1026 ≤ i) (hy : i < 2056 ∨ 2312 ≤ i) :
    s (w i)=false :=
  h.2.2 _ (arith_mem w 0 2314 i (by omega) hi)
    (arith_block_away w hn i 770 256 hi (by omega) hx)
    (arith_block_away w hn i 2056 256 hi (by omega) hy)

theorem arith_input_zero (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y start len : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s)
    (hb : start+len ≤ 2314) (hx : start+len ≤ 770 ∨ 1026 ≤ start)
    (hy : start+len ≤ 2056 ∨ 2312 ≤ start) : regValue (wireBlock w start len) s=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact arith_input_bit w hn x y s h i (by omega) (by omega) (by omega)

theorem arith_seed_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i : Nat) (hi : i < 2314) (ha : 258 ≤ i)
    (hb : i < 770 ∨ 1028 ≤ i) (hc : i < 1798 ∨ 2056 ≤ i)
    (hd : i < 1540 ∨ 1797 ≤ i) (hcin : i≠2313) :
    w i∉(skywalkSharedSeed w).usedWires := by
  have hA := arith_block_away w hn i 0 258 hi (by omega) (by omega)
  have hB := arith_block_away w hn i 770 258 hi (by omega) hb
  have hC := arith_block_away w hn i 1798 258 hi (by omega) hc
  have hD := arith_block_away w hn i 1540 257 hi (by omega) hd
  have hI : w i≠w 2313 := by
    intro he
    exact hcin (skywalkShared_index_inj w hn i 2313 hi (by omega) he)
  intro hm
  change w i∈w 2313::(wireBlock w 0 258++wireBlock w 770 258++
    wireBlock w 1798 258++wireBlock w 1540 257) at hm
  rcases List.mem_cons.mp hm with he|hr
  · exact hI he
  · simp only [List.mem_append,or_assoc] at hr
    rcases hr with he|he|he|he
    · exact hA he
    · exact hB he
    · exact hC he
    · exact hD he

theorem arith_seed_input (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s) :
    SkywalkSeedValues (skywalkSharedSeed w) 0 x 0 s := by
  have hpad := arith_input_zero w hn x y 1026 2 s h (by omega) (by omega) (by omega)
  have hp := wireBlock_append w 770 256 2
  have hb : regValue (wireBlock w 770 258) s=x := by
    rw [←hp,regValue_append]
    change regValue (skywalkArithmeticDivisor w) s+2^256*regValue (wireBlock w 1026 2) s=x
    rw [h.1,hpad]
    omega
  refine ⟨arith_input_zero w hn x y 0 258 s h (by omega) (by omega) (by omega),hb,
    arith_input_zero w hn x y 1798 258 s h (by omega) (by omega) (by omega),
    arith_input_zero w hn x y 1540 257 s h (by omega) (by omega) (by omega),
    arith_input_bit w hn x y s h 2313 (by omega) (by omega) (by omega),
    arith_input_bit w hn x y s h 1797 (by omega) (by omega) (by omega)⟩

set_option exponentiation.threshold 258 in
theorem arith_seed_stage0 (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (hx : x < p) (s : State) (m : List Bool)
    (h : SkywalkArithmeticInput w x y s.basis) :
    SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 0
      (run (skywalkSeed (skywalkSharedSeed w) p) m s).basis := by
  generalize hs : run (skywalkSeed (skywalkSharedSeed w) p) m s=t
  have hp : p < 2^256 := by norm_num [p]
  have hw := skywalkShared_seed_widths w
  have htFull := skywalkSeed_spec _ 258 p x hw (skywalkShared_seed_nodup w hn)
    (by omega) hp (hx.trans hp) s m (arith_seed_input w hn x y s.basis h)
  rw [hs] at htFull
  have ht := htFull.2
  have hsum : p+x < 2^257 := by
    have hxp0 := hx.trans hp
    change _ < 2^(256+1)
    rw [pow_succ]
    omega
  have hxp : x < 2^257 := by
    have hxp0 := hx.trans hp
    change _ < 2^(256+1)
    rw [pow_succ]
    omega
  have ha : signedRegValue (skywalkPoolA w 0) t.basis=(x:Int)+(p:Int) := by
    change signedDecode 258 (regValue (skywalkSharedSeed w).a t.basis)=_
    rw [ht.a]
    simp only [signedDecode,if_pos hsum]
    omega
  have hb : signedRegValue (skywalkPoolB w) t.basis=(x:Int) := by
    change signedDecode 258 (regValue (skywalkSharedSeed w).b t.basis)=_
    rw [ht.b]
    simp only [signedDecode,if_pos hxp]
  unfold SkywalkIntegerStage
  rw [Function.iterate_zero_apply]
  change signedRegValue (skywalkPoolA w 0) t.basis=(x:Int)+(p:Int) ∧
    signedRegValue (skywalkPoolB w) t.basis=(x:Int) ∧ t.basis (w 1797)=false ∧ _
  refine ⟨ha,hb,ht.orientation,?_,?_,ht.carry,ht.orientation⟩
  · intro j hj; omega
  · intro j hj hjmax
    have keep (i : Nat) (hi : i=j+258 ∨ i=1028+j) :
        t.basis (w i)=false := by
      have hout := arith_seed_outside w hn i (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      have hk := (skywalkSeed_frame _ 258 p hw s m _ hout).1
      rw [hs] at hk
      exact hk.trans (arith_input_bit w hn x y s.basis h i (by omega) (by omega) (by omega))
    exact ⟨keep _ (Or.inl rfl),keep _ (Or.inr rfl)⟩

attribute [local irreducible] SkywalkTrace.next Nat.iterate

theorem arith_trace_map (n : Nat) (r : SkywalkRails.State) :
    SkywalkTrace.trace n r=(List.range n).map
      (fun i => SkywalkTrace.code (SkywalkTrace.next^[i] r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [SkywalkTrace.trace,ih,List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.iterate_zero_apply]
    congr 1
    apply List.map_congr_left
    intro i hi
    change SkywalkTrace.code (SkywalkTrace.next^[i] (SkywalkTrace.next r))=
      SkywalkTrace.code (SkywalkTrace.next^[i+1] r)
    rw [Function.iterate_succ_apply]

theorem arith_tape (w : Nat → Wire) (x : Nat) (s : BasisState)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s) :
    skywalkTapeControls s (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := by
  rw [arith_trace_map]
  simp only [skywalkTapeControls,skywalkSharedTape,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hh := h.2.2.2.1 i (List.mem_range.mp hi)
  exact Prod.ext hh.1 hh.2

theorem arith_terminal (x : Nat) (hx0 : 0 < x) (hx : x < p) :
    let r := SkywalkTrace.next^[512] (SkywalkRails.encode false false (x : Int) (p : Int))
    r.a=(if r.g then 0 else 1) ∧ r.b=(if r.g then 1 else 0) := by
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p < 2^256 := by norm_num [p]
  have hc : x.Coprime p := by
    apply Nat.Coprime.symm
    apply p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have ht := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpo hp (hx.trans hp) hc
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded 512 false false (SkywalkNat.init x p) hp0 hpo
  change (SkywalkNat.step^[512] (SkywalkNat.init x p)).u=0 ∧
    (SkywalkNat.step^[512] (SkywalkNat.init x p)).v=1 at ht
  rw [ht.1,ht.2] at he
  change SkywalkTrace.next^[512] (SkywalkRails.encode false false (x:Int) (p:Int))=
    SkywalkRails.encode G S (0:Int) (1:Int) at he
  dsimp only
  rw [he]
  cases G <;> simp [SkywalkRails.encode,SkywalkRails.zero_sign]

theorem arith_signed_read_nat (r : List Wire) (s : BasisState) (N : Nat)
    (hs : signedRegValue r s=(N : Int)) (hn : N < 2^r.length) : regValue r s=N := by
  have hh := congrArg (fun a : Int => a%(2^r.length:Nat)) hs
  change signedDecode r.length (regValue r s)%(2^r.length:Nat)=(N:Int)%(2^r.length:Nat) at hh
  rw [signedDecode_emod] at hh
  have hv := regValue_lt r s
  rw [Int.emod_eq_of_lt (by omega) (Int.ofNat_lt.mpr hv),
    Int.emod_eq_of_lt (by omega) (Int.ofNat_lt.mpr hn)] at hh
  omega

theorem arith_terminal_words (w : Nat → Wire) (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : BasisState)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s) :
    regValue (wireBlock w 512 258) s=(if s (w 511) then 0 else 1) ∧
    regValue (wireBlock w 770 258) s=(if s (w 511) then 1 else 0) := by
  have ht := arith_terminal x hx0 hx
  dsimp only at ht
  have hg : s (w 511)=(SkywalkTrace.next^[512]
      (SkywalkRails.encode false false (x : Int) (p : Int))).g := h.2.2.1
  refine ⟨?_,?_⟩
  · apply arith_signed_read_nat _ s (if s (w 511) then 0 else 1)
    · rw [hg]
      simpa only [skywalkPoolA,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] using h.1.trans ht.1
    · rw [wireBlock_length]; split <;> norm_num
  · apply arith_signed_read_nat _ s (if s (w 511) then 1 else 0)
    · rw [hg]
      simpa only [skywalkPoolB,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] using h.2.1.trans ht.2
    · rw [wireBlock_length]; split <;> norm_num

theorem arith_clear_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (w 511::w 512::w 770::(wireBlock w 513 257++wireBlock w 771 257)).Nodup := by
  have hsep : (List.range' 513 257).Disjoint (List.range' 771 257) := by
    apply List.disjoint_left.mpr
    intro j hj hk
    simp only [List.mem_range'_1] at hj hk
    omega
  have hd : (511::512::770::(List.range' 513 257++List.range' 771 257)).Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,List.mem_range'_1]
    refine ⟨by omega,by omega,by omega,List.nodup_append'.mpr
      ⟨List.nodup_range',List.nodup_range',hsep⟩⟩
  change ((511::512::770::(List.range' 513 257++List.range' 771 257)).map w).Nodup
  apply List.Nodup.map_on
  · intro i hi j hj he
    simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hi hj
    exact skywalkShared_index_inj w hn i j (by omega) (by omega) he
  · exact hd

theorem arith_clear_gates (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    [w 511,w 512,w 770].Nodup := by
  have hd := arith_clear_nodup w hn
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hd q
  simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
  omega

theorem arith_clear_words (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x : Nat) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s.basis) :
    regValue (wireBlock w 512 258) (run (skywalkArithmeticClear w) m s).basis=0 ∧
    regValue (wireBlock w 770 258) (run (skywalkArithmeticClear w) m s).basis=0 := by
  have ht := arith_terminal_words w x hx0 hx s.basis h
  have hA : wireBlock w 512 258=w 512::wireBlock w 513 257 := by
    have he := wireBlock_append w 512 1 257
    simpa only [show wireBlock w 512 1=[w 512] from rfl,List.singleton_append] using he.symm
  have hB : wireBlock w 770 258=w 770::wireBlock w 771 257 := by
    have he := wireBlock_append w 770 1 257
    simpa only [show wireBlock w 770 1=[w 770] from rfl,List.singleton_append] using he.symm
  rw [hA,hB] at ht ⊢
  have ho := skywalkTerminalClear_words _ _ _ _ _ (arith_clear_nodup w hn)
    (s.basis (w 511)) s m ⟨⟨rfl,ht.1⟩,ht.2⟩
  exact ⟨ho.2.1.2,ho.2.2⟩

end ECDSAAdd.Arithmetic.DirectSkywalk
