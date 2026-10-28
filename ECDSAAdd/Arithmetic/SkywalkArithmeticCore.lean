import ECDSAAdd.Arithmetic.SkywalkShared
import ECDSAAdd.Arithmetic.NarrowSkywalkRoutedLoop
import ECDSAAdd.Arithmetic.SkywalkTerminal
import ECDSAAdd.Arithmetic.SkywalkDialog
import ECDSAAdd.Arithmetic.FusedSharedRetainedSupport
import ECDSAAdd.Arithmetic.FusedSharedInverseSupport

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- The original public divisor and numerator ports, each exactly 256 bits. -/
def skywalkArithmeticDivisor (w : Nat → Wire) := wireBlock w 770 256
def skywalkArithmeticNumerator (w : Nat → Wire) := wireBlock w 2056 256

def SkywalkArithmeticInput (w : Nat → Wire) (x y : Nat) (s : BasisState) : Prop :=
  regValue (skywalkArithmeticDivisor w) s=x ∧
  regValue (skywalkArithmeticNumerator w) s=y ∧
  ∀ q∈skywalkSharedWires w,q∉skywalkArithmeticDivisor w →
    q∉skywalkArithmeticNumerator w → s q=false

def skywalkArithmeticClear (w : Nat → Wire) : Program :=
  skywalkTerminalClear (w 511) (w 512) (w 770)

/-- Executable seven-stage exact port. `divide=false` selects multiplication. -/
def skywalkArithmetic (divide : Bool) (w : Nat → Wire) : Program :=
  skywalkSeed (skywalkSharedSeed w) p ++
  (narrowSkywalkRoutedLoop w 0 512 ++
  (skywalkArithmeticClear w ++
  ((if divide then skywalkFieldDivisionRetained w
      else skywalkFieldMultiplicationRetained w) ++
  (skywalkArithmeticClear w ++
  (narrowSkywalkRoutedUnloop w 0 512 ++ skywalkUnseed (skywalkSharedSeed w) p)))))

attribute [local irreducible] skywalkSeed skywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop
attribute [local irreducible] skywalkFieldDivisionRetained skywalkFieldMultiplicationRetained run

def skywalkArithmeticResult (divide : Bool) (x : Nat) (Y : Fp) : Fp :=
  if divide then Y/(x : Fp) else Y*(x : Fp)

private theorem arith_coprime (x : Nat) (hx0 : 0 < x) (hx : x < p) : x.Coprime p := by
  apply Nat.Coprime.symm
  apply p_prime.coprime_iff_not_dvd.mpr
  intro hd
  exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)

private theorem arith_modulus_bound : p < 2^256 := by norm_num [p]

private theorem arith_mem (w : Nat → Wire) (start len j : Nat)
    (hlo : start ≤ j) (hhi : j < start+len) : w j∈wireBlock w start len := by
  apply List.mem_map.mpr
  exact ⟨j,by simp only [List.mem_range'_1]; omega,rfl⟩

private theorem arith_block_away (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i start len : Nat) (hi : i < 2314) (hb : start+len ≤ 2314)
    (ha : i < start ∨ start+len ≤ i) : w i∉wireBlock w start len := by
  intro hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  simp only [List.mem_range'_1] at hj
  have hh := skywalkShared_index_inj w hn j i (by omega) hi he
  omega

private theorem arith_input_bit (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s)
    (i : Nat) (hi : i < 2314) (hx : i < 770 ∨ 1026 ≤ i) (hy : i < 2056 ∨ 2312 ≤ i) :
    s (w i)=false :=
  h.2.2 _ (arith_mem w 0 2314 i (by omega) hi)
    (arith_block_away w hn i 770 256 hi (by omega) hx)
    (arith_block_away w hn i 2056 256 hi (by omega) hy)

private theorem arith_input_zero (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y start len : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s)
    (hb : start+len ≤ 2314) (hx : start+len ≤ 770 ∨ 1026 ≤ start)
    (hy : start+len ≤ 2056 ∨ 2312 ≤ start) : regValue (wireBlock w start len) s=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact arith_input_bit w hn x y s h i (by omega) (by omega) (by omega)

private theorem arith_seed_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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

private theorem arith_seed_input (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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
private theorem arith_seed_stage0 (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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

private theorem arith_trace_map (n : Nat) (r : SkywalkRails.State) :
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

private theorem arith_tape (w : Nat → Wire) (x : Nat) (s : BasisState)
    (h : SkywalkIntegerStage w (SkywalkRails.encode false false (x : Int) (p : Int)) 512 s) :
    skywalkTapeControls s (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) := by
  rw [arith_trace_map]
  simp only [skywalkTapeControls,skywalkSharedTape,List.map_map]
  apply List.map_congr_left
  intro i hi
  have hh := h.2.2.2.1 i (List.mem_range.mp hi)
  exact Prod.ext hh.1 hh.2

private theorem arith_terminal (x : Nat) (hx0 : 0 < x) (hx : x < p) :
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

private theorem arith_signed_read_nat (r : List Wire) (s : BasisState) (N : Nat)
    (hs : signedRegValue r s=(N : Int)) (hn : N < 2^r.length) : regValue r s=N := by
  have hh := congrArg (fun a : Int => a%(2^r.length:Nat)) hs
  change signedDecode r.length (regValue r s)%(2^r.length:Nat)=(N:Int)%(2^r.length:Nat) at hh
  rw [signedDecode_emod] at hh
  have hv := regValue_lt r s
  rw [Int.emod_eq_of_lt (by omega) (Int.ofNat_lt.mpr hv),
    Int.emod_eq_of_lt (by omega) (Int.ofNat_lt.mpr hn)] at hh
  omega

private theorem arith_terminal_words (w : Nat → Wire) (x : Nat) (hx0 : 0 < x) (hx : x < p)
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

private theorem arith_clear_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
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

private theorem arith_clear_gates (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    [w 511,w 512,w 770].Nodup := by
  have hd := arith_clear_nodup w hn
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hd q
  simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
  omega

private theorem arith_clear_words (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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

/-- PairFrame plus a source that starts and ends zero is a numerator-only frame. -/
private theorem arith_field_frame (L : ModInPlaceLayout) (base s : BasisState) (Z : Nat)
    (ha : regValue L.a base=0) (hf : PairFrame L.z L.a base Z 0 s) :
    ∀ q,q∉L.z → s q=base q := by
  have he := (regValue_eq_iff L.a s base).mp (hf.2.1.trans ha.symm)
  intro q hq
  by_cases hs : q∈L.a
  · exact he q hs
  · exact hf.2.2 q hq hs

private theorem arith_pool_away_z (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (q : Wire) (hq : q∈skywalkPoolWires w) : q∉(skywalkSharedField w).z := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  rw [skywalkShared_field_z]
  exact arith_block_away w hn i 2056 257 (by omega) (by omega) (by omega)

private theorem arith_loop_outside (back : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (if back then narrowSkywalkRoutedUnloop w 0 512 else narrowSkywalkRoutedLoop w 0 512) m s).basis q=s.basis q := by
  have hp := narrowSkywalkRoutedLoop_support w 0 512 (skywalkShared_integer_nodup w hn) (by omega)
  apply run_preserves_outside
  intro hm
  cases back
  · exact hq (List.mem_toFinset.mp (hp.1 hm))
  · exact hq (List.mem_toFinset.mp (hp.2 hm))

private theorem arith_record_outside (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (narrowSkywalkRoutedLoop w 0 512) m s).basis q=s.basis q := by
  simpa only [Bool.false_eq_true,if_false] using arith_loop_outside false w hn s m q hq

private theorem arith_unrecord_outside (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉skywalkPoolWires w) :
    (run (narrowSkywalkRoutedUnloop w 0 512) m s).basis q=s.basis q := by
  simpa only [if_true] using arith_loop_outside true w hn s m q hq

private theorem arith_clear_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire) (hq : q∉skywalkPoolWires w) :
    (run (skywalkArithmeticClear w) m s).basis q=s.basis q := by
  apply (skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s m).2.1
  · intro he; subst q; exact hq (arith_mem w 0 1798 512 (by omega) (by omega))
  · intro he; subst q; exact hq (arith_mem w 0 1798 770 (by omega) (by omega))

private theorem arith_stage_congr (w : Nat → Wire) (r : SkywalkRails.State)
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

private theorem arith_clear_transport (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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

private theorem arith_z_input (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (x y : Nat) (s : BasisState) (h : SkywalkArithmeticInput w x y s) :
    regValue (skywalkSharedField w).z s=y := by
  change regValue (wireBlock w 2056 256++[w 2312]) s=y
  rw [regValue_append]
  change regValue (skywalkArithmeticNumerator w) s+_=_
  rw [h.2.1]
  simp [regValue,arith_input_bit w hn x y s h 2312 (by omega) (by omega) (by omega)]

private theorem arith_preparation_frame (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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

private theorem arith_clean_preparation (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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

private theorem arith_tape_clear (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
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

private theorem arith_seed_components (L : SkywalkSeedLayout) :
    L.a⊆L.usedWires ∧ L.b⊆L.usedWires ∧ L.constant⊆L.usedWires ∧ L.carry⊆L.usedWires := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro q hq <;>
    simp only [SkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append] <;> tauto

private theorem arith_seed_away (L : SkywalkSeedLayout) (q : Wire)
    (hi : q≠L.cin) (ha : q∉L.a) (hb : q∉L.b) (hc : q∉L.constant) (hd : q∉L.carry) :
    q∉L.usedWires := by
  simp only [SkywalkSeedLayout.usedWires,List.mem_cons,List.mem_append]
  tauto

theorem skywalkArithmetic_states (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (active : Wire) (ha : active∉skywalkSharedWires w)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool)
    (hin : SkywalkArithmeticInput w x Y.val s.basis)
    (s1 s2 s3 s4 s5 s6 s7 : State)
    (hs1 : run (skywalkSeed (skywalkSharedSeed w) p) m1 s=s1)
    (hs2 : run (narrowSkywalkRoutedLoop w 0 512) m2 s1=s2)
    (hs3 : run (skywalkArithmeticClear w) m3 s2=s3)
    (hs4 : run (if divide then skywalkFieldDivisionRetained w
      else skywalkFieldMultiplicationRetained w) m4 s3=s4)
    (hs5 : run (skywalkArithmeticClear w) m5 s4=s5)
    (hs6 : run (narrowSkywalkRoutedUnloop w 0 512) m6 s5=s6)
    (hs7 : run (skywalkUnseed (skywalkSharedSeed w) p) m7 s6=s7) :
    s7.phase=s.phase ∧ regValue (skywalkArithmeticNumerator w) s7.basis=
      (skywalkArithmeticResult divide x Y).val ∧
      ∀ q,q∉skywalkArithmeticNumerator w → s7.basis q=s.basis q := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let L := skywalkSharedSeed w
  let F := skywalkSharedField w
  let Z := (skywalkArithmeticResult divide x Y).val
  have hw := skywalkShared_seed_widths w
  have hnseed := skywalkShared_seed_nodup w hn
  have hnpool := skywalkShared_integer_nodup w hn
  have hp : p < 2^256 := by norm_num [p]
  have hp0 : 0 < p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have h1 := skywalkSeed_spec L 258 p x hw hnseed (by omega) hp (hx.trans hp)
    s m1 (arith_seed_input w hn x Y.val s.basis hin)
  rw [hs1] at h1
  have hstage0 := arith_seed_stage0 w hn x Y.val hx s m1 hin
  rw [hs1] at hstage0
  have h2 := narrowSkywalkRouted512_spec w hnpool x p hp0 hx0 hpo hp hx (arith_coprime x hx0 hx) s1 m2 hstage0
  rw [hs2] at h2
  have h3 := skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s2 m3
  change (run (skywalkArithmeticClear w) m3 s2).phase=s2.phase ∧ _ at h3
  rw [hs3] at h3
  have hclean := arith_clean_preparation w hn x Y.val hx0 hx s m1 m2 m3 hin
  rw [hs1,hs2,hs3] at hclean
  have hwork := skywalkShared_clean_to_field w s3.basis hclean
  have hz3 : regValue F.z s3.basis=Y.val := by
    have hk := arith_preparation_frame w hn s m1 m2 m3
    rw [hs1,hs2,hs3] at hk
    exact (regValue_congr _ _ _ hk).trans (arith_z_input w hn x Y.val s.basis hin)
  have htape : skywalkTapeControls s3.basis (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)) :=
    by
      have hk := arith_tape_clear w hn s2 m3
      rw [hs3] at hk
      exact hk.trans (arith_tape w x s2.basis h2.2)
  have h4 : s4.phase=s3.phase ∧ PairFrame F.z F.a s3.basis Z 0 s4.basis := by
    have hbefore : PairFrame F.z F.a s3.basis Y.val 0 s3.basis := ⟨hz3,hwork.1,fun _ _ _ => rfl⟩
    cases divide
    · have hh := skywalkFieldMultiplicationRetained_spec active w hn ha
        s3.basis hwork.2.1 hwork.2.2 x Y hx0 hx htape s3 m4 hbefore
      change run (skywalkFieldMultiplicationRetained w) m4 s3=s4 at hs4
      rw [hs4] at hh
      exact hh
    · have hh := skywalkFieldDivisionRetained_spec active w hn ha
        s3.basis hwork.2.1 hwork.2.2 x Y hx0 hx htape s3 m4 hbefore
      change run (skywalkFieldDivisionRetained w) m4 s3=s4 at hs4
      rw [hs4] at hh
      exact hh
  have hframe4 := arith_field_frame F s3.basis s4.basis Z hwork.1 h4.2
  have h5 := skywalkTerminalClear_correct _ _ _ (arith_clear_gates w hn) s4 m5
  change (run (skywalkArithmeticClear w) m5 s4).phase=s4.phase ∧ _ at h5
  rw [hs5] at h5
  have hframe5 := arith_clear_transport w hn s2 s4 m3 m5 (by rw [hs3]; exact hframe4)
  rw [hs5] at hframe5
  have hstage5 := arith_stage_congr w _ s2.basis s5.basis h2.2
    (fun q hq => hframe5 q (arith_pool_away_z w hn q hq))
  have h6 := narrowSkywalkRoutedUnloop_restore_pool w hnpool x p hp0 hx0 hpo hp hx (arith_coprime x hx0 hx) s1 s5 m6 hstage0 hstage5
  rw [hs6] at h6
  have outsideZ (q : Wire) (hq : q∉F.z) : s6.basis q=s1.basis q := by
    by_cases hpool : q∈skywalkPoolWires w
    · exact h6.2 q hpool
    · have hb := arith_unrecord_outside w hn s5 m6 q hpool
      have hf := arith_record_outside w hn s1 m2 q hpool
      rw [hs6] at hb
      rw [hs2] at hf
      exact hb.trans ((hframe5 q hq).trans hf)
  have seedAway (q : Wire) (hq : q∈L.usedWires) : q∉F.z := by
    change q∈w 2313::(wireBlock w 0 258++wireBlock w 770 258++
      wireBlock w 1798 258++wireBlock w 1540 257) at hq
    rw [skywalkShared_field_z]
    rcases List.mem_cons.mp hq with rfl|hr
    · exact arith_block_away w hn 2313 2056 257 (by omega) (by omega) (by omega)
    · simp only [List.mem_append,or_assoc] at hr
      rcases hr with hq|hq|hq|hq
      all_goals
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
        simp only [List.mem_range'_1] at hj
        exact arith_block_away w hn j 2056 257 (by omega) (by omega) (by omega)
  have readSeed (r : List Wire) (hr : r⊆L.usedWires) : regValue r s6.basis=regValue r s1.basis :=
    regValue_congr _ _ _ (fun q hq => outsideZ q (seedAway q (hr hq)))
  have hin6 : SkywalkSeedValues L (p+x) x 0 s6.basis := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · exact (readSeed L.a (arith_seed_components L).1).trans h1.2.a
    · exact (readSeed L.b (arith_seed_components L).2.1).trans h1.2.b
    · exact (readSeed L.constant (arith_seed_components L).2.2.1).trans h1.2.constant
    · exact (readSeed L.carry (arith_seed_components L).2.2.2).trans h1.2.carry
    · exact (outsideZ _ (seedAway _ (by simp [SkywalkSeedLayout.usedWires]))).trans h1.2.cin
    · exact (h6.2 _ (arith_mem w 0 1798 1797 (by omega) (by omega))).trans h1.2.orientation
  have h7 := skywalkUnseed_spec L 258 p x hw hnseed (by omega) hp (hx.trans hp) s6 m7 hin6
  rw [hs7] at h7
  have frame7Z : ∀ q,q∉F.z → s7.basis q=s.basis q := by
    have hentry := arith_seed_input w hn x Y.val s.basis hin
    have readback (r : List Wire) (hb : regValue r s7.basis=regValue r s.basis) :
        ∀ q∈r,s7.basis q=s.basis q := (regValue_eq_iff r _ _).mp hb
    have hA := readback L.a (h7.2.a.trans hentry.a.symm)
    have hB := readback L.b (h7.2.b.trans hentry.b.symm)
    have hC := readback L.constant (h7.2.constant.trans hentry.constant.symm)
    have hD := readback L.carry (h7.2.carry.trans hentry.carry.symm)
    intro q hq
    by_cases hcin : q=L.cin
    · subst q; exact h7.2.cin.trans hentry.cin.symm
    by_cases hqa : q∈L.a
    · exact hA q hqa
    by_cases hqb : q∈L.b
    · exact hB q hqb
    by_cases hqc : q∈L.constant
    · exact hC q hqc
    by_cases hqd : q∈L.carry
    · exact hD q hqd
    have hout := arith_seed_away L q hcin hqa hqb hqc hqd
    have hb := skywalkSeed_frame L 258 p hw s6 m7 q hout
    have hf := skywalkSeed_frame L 258 p hw s m1 q hout
    rw [hs7] at hb
    rw [hs1] at hf
    exact hb.2.trans ((outsideZ q hq).trans hf.1)
  have hz7 : regValue F.z s7.basis=Z := by
    apply Eq.trans (regValue_congr _ _ _ ?_) h4.2.1
    intro q hq
    rw [skywalkShared_field_z] at hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    have hpaway := arith_block_away w hn j 0 1798 (by omega) (by omega) (by omega)
    have hsaway := arith_seed_outside w hn j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hseed := skywalkSeed_frame L 258 p hw s6 m7 (w j) hsaway
    have hloop := arith_unrecord_outside w hn s5 m6 (w j) hpaway
    have hclear := arith_clear_outside w hn s4 m5 (w j) hpaway
    rw [hs7] at hseed
    rw [hs6] at hloop
    rw [hs5] at hclear
    exact hseed.2.trans (hloop.trans hclear)
  have hZ : Z < 2^256 := (ZMod.val_lt (skywalkArithmeticResult divide x Y)).trans hp
  have hhigh := skywalkShared_numerator_high_zero w s7.basis Z hz7 hZ
  have hlow7 : regValue (skywalkArithmeticNumerator w) s7.basis=Z := by
    change regValue (wireBlock w 2056 256++[w 2312]) s7.basis=Z at hz7
    rw [regValue_append] at hz7
    simpa [regValue,hhigh,skywalkArithmeticNumerator] using hz7
  refine ⟨h7.1.trans (h6.1.trans (h5.1.trans (h4.1.trans (h3.1.trans (h2.1.trans h1.1))))),hlow7,?_⟩
  intro q hq
  by_cases hz : q∈F.z
  · change q∈wireBlock w 2056 256++[w 2312] at hz
    rcases List.mem_append.mp hz with hlow|hpad
    · exact False.elim (hq hlow)
    · have he : q=w 2312 := by simpa using hpad
      subst q
      exact hhigh.trans (arith_input_bit w hn x Y.val s.basis hin 2312 (by omega) (by omega) (by omega)).symm
  · exact frame7Z q hz

/-- Pure interpreter composition. The callback is discharged by the concrete
state theorem; this lemma introduces no circuit oracle or input assumption. -/
theorem skywalkRunSeven (p1 p2 p3 p4 p5 p6 p7 : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 s5 s6 s7 : State) (m1 m2 m3 m4 m5 m6 m7 : List Bool),
      run p1 m1 s=s1 → run p2 m2 s1=s2 → run p3 m3 s2=s3 →
      run p4 m4 s3=s4 → run p5 m5 s4=s5 → run p6 m6 s5=s6 →
      run p7 m7 s6=s7 → P s s7) (s : State) (m : List Bool) :
    P s (run (p1++(p2++(p3++(p4++(p5++(p6++p7)))))) m s) := by
  simp only [run_append]
  apply h s _ _ _ _ _ _ _ _ _ _ _ _ _ _ <;> rfl

end ECDSAAdd.Arithmetic
