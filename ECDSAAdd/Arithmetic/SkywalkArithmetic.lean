import ECDSAAdd.Arithmetic.SkywalkArithmeticCore

set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace ECDSAAdd.Arithmetic
open Secp256k1
def SkywalkArithmeticStrong (divide : Bool) (w : Nat → Wire) (x : Nat) (Y : Fp)
    (initial out : State) : Prop :=
  out.phase=initial.phase ∧ regValue (skywalkArithmeticNumerator w) out.basis=
    (skywalkArithmeticResult divide x Y).val ∧
    ∀ q,q∉skywalkArithmeticNumerator w → out.basis q=initial.basis q

attribute [local irreducible] run skywalkArithmetic SkywalkArithmeticStrong

/-- Complete executable circuit semantics, sealed behind generic interpreter
composition instead of repeated concrete measurement-count expansion. -/
theorem skywalkArithmetic_run (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (active : Wire) (ha : active∉skywalkSharedWires w)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x Y.val s.basis) :
    SkywalkArithmeticStrong divide w x Y s (run (skywalkArithmetic divide w) m s) := by
  let P : State → State → Prop := fun initial out =>
    SkywalkArithmeticInput w x Y.val initial.basis → SkywalkArithmeticStrong divide w x Y initial out
  have hh := skywalkRunSeven
    (skywalkSeed (skywalkSharedSeed w) p) (narrowSkywalkRoutedLoop w 0 512)
    (skywalkArithmeticClear w)
    (if divide then skywalkFieldDivisionRetained w
      else skywalkFieldMultiplicationRetained w)
    (skywalkArithmeticClear w) (narrowSkywalkRoutedUnloop w 0 512)
    (skywalkUnseed (skywalkSharedSeed w) p) P
    (by
      intro initial s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hinput
      unfold SkywalkArithmeticStrong
      exact skywalkArithmetic_states divide w hn active ha x Y hx0 hx initial
        m1 m2 m3 m4 m5 m6 m7 hinput s1 s2 s3 s4 s5 s6 s7 hs1 hs2 hs3 hs4 hs5 hs6 hs7)
    s m
  simpa only [skywalkArithmetic] using hh hin

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

/-- Universal exact divisor-preserving quotient/product, with arbitrary
measurement lists and an arbitrary incoming phase. Every other bit is restored. -/
theorem skywalkArithmetic_spec (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (active : Wire) (ha : active∉skywalkSharedWires w)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) :
    Triple (SkywalkArithmeticInput w x Y.val) (skywalkArithmetic divide w)
      (fun out => regValue (skywalkArithmeticNumerator w) out=(skywalkArithmeticResult divide x Y).val ∧
        SkywalkArithmeticInput w x (skywalkArithmeticResult divide x Y).val out) := by
  intro s m hin
  generalize hout : run (skywalkArithmetic divide w) m s=out
  have strong := skywalkArithmetic_run divide w hn active ha x Y hx0 hx s m hin
  rw [hout] at strong
  unfold SkywalkArithmeticStrong at strong
  refine ⟨strong.1,strong.2.1,?_,strong.2.1,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hin.1
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact strong.2.2 _ (arith_block_away w hn j 2056 256 (by omega) (by omega) (by omega))
  · intro q hq hd hy
    exact (strong.2.2 q hy).trans (hin.2.2 q hq hd hy)

/-- The concrete seven-stage circuit restores every caller bit outside Y,
including wires outside the shared pool. -/
theorem skywalkArithmetic_frame (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (active : Wire) (ha : active∉skywalkSharedWires w)
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s : State) (m : List Bool)
    (hin : SkywalkArithmeticInput w x Y.val s.basis) :
    ∀ q,q∉skywalkArithmeticNumerator w →
      (run (skywalkArithmetic divide w) m s).basis q=s.basis q := by
  generalize hout : run (skywalkArithmetic divide w) m s=out
  have hh := skywalkArithmetic_run divide w hn active ha x Y hx0 hx s m hin
  rw [hout] at hh
  unfold SkywalkArithmeticStrong at hh
  exact hh.2.2

/-- Counts of the actual composed programs, including both integer passes. -/
theorem skywalkArithmetic_counts (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (active : Wire) (ha : active∉skywalkSharedWires w) :
    toffoliCount (skywalkArithmetic true w)=1314817 ∧
    measurementCount (skywalkArithmetic true w)=986367 ∧
    toffoliCount (skywalkArithmetic false w)=1314818 ∧
    measurementCount (skywalkArithmetic false w)=986368 := by
  have hs := skywalkSeed_counts (skywalkSharedSeed w) 258 p (skywalkShared_seed_widths w)
  have hi := narrowSkywalkRouted512_counts w (skywalkShared_integer_nodup w hn)
  have hc := skywalkTerminalClear_counts (w 511) (w 512) (w 770)
  have hret := skywalkFieldDivisionRetained_counts active w hn ha
  have hmul := skywalkFieldMultiplicationRetained_counts active w hn ha
  simp only [skywalkArithmetic,skywalkArithmeticClear,if_true,Bool.false_eq_true,if_false,
    toffoliCount_append,measurementCount_append,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    hi.1,hi.2.1,hi.2.2.1,hi.2.2.2,hc.1,hc.2,hret.1,hret.2,hmul.1,hmul.2]
  norm_num

private theorem arith_block_subset_shared (w : Nat → Wire) (a n : Nat)
    (hb : a+n ≤ 2314) : wireBlock w a n ⊆ skywalkSharedWires w := by
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hj
  exact arith_mem w 0 2314 j (by omega) (by omega)

private theorem arith_seed_subset_shared (w : Nat → Wire) :
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

private theorem arith_field_subset_shared (w : Nat → Wire) :
    (skywalkSharedField w).wires ⊆ skywalkSharedWires w := by
  intro q hq
  unfold ModInPlaceLayout.wires at hq
  rw [skywalkShared_field_z] at hq
  change q∈wireBlock w 770 257++wireBlock w 2056 257++
    (wireBlock w 1540 257++wireBlock w 1798 256++[w 1797]++
      wireBlock w 512 257++[w 2313]) at hq
  simp only [List.mem_append,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq|hq|hq
  · exact arith_block_subset_shared w 770 257 (by omega) hq
  · exact arith_block_subset_shared w 2056 257 (by omega) hq
  · exact arith_block_subset_shared w 1540 257 (by omega) hq
  · exact arith_block_subset_shared w 1798 256 (by omega) hq
  · have he : q=w 1797 := List.mem_singleton.mp hq
    subst q
    exact arith_mem w 0 2314 1797 (by omega) (by omega)
  · exact arith_block_subset_shared w 512 257 (by omega) hq
  · have he : q=w 2313 := List.mem_singleton.mp hq
    subst q
    exact arith_mem w 0 2314 2313 (by omega) (by omega)

private theorem arith_tape_subset_shared (w : Nat → Wire) :
    ∀ r∈skywalkSharedTape w,r.1∈skywalkSharedWires w ∧ r.2∈skywalkSharedWires w := by
  intro r hr
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
  have hb := List.mem_range.mp hj
  exact ⟨arith_mem w 0 2314 j (by omega) (by omega),
    arith_mem w 0 2314 (1028+j) (by omega) (by omega)⟩

private theorem arith_field_legs_support (L : ModInPlaceLayout) (rs : List (Wire×Wire))
    (hw : L.Widths 256) (W : List Wire) (hl : L.wires⊆W)
    (ht : ∀ r∈rs,r.1∈W ∧ r.2∈W) :
    wires (skywalkFieldDivision L rs)⊆W.toFinset ∧
    wires (skywalkFieldMultiplication L rs)⊆W.toFinset := by
  have hReplay : wires (skywalkDialogReplay L rs)⊆W.toFinset ∧
      wires (skywalkDialogUnreplay L rs)⊆W.toFinset := by
    induction rs with
    | nil => simp [skywalkDialogReplay,skywalkDialogUnreplay,wires]
    | cons r rs ih =>
      have hc := skywalkField_wires_subset r.1 r.2 L 256 p hw (by omega)
      have own : (r.1::r.2::L.wires).toFinset⊆W.toFinset := by
        intro q hq
        apply List.mem_toFinset.mpr
        rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl|hq
        · exact (ht r (by simp)).1
        · rcases List.mem_cons.mp hq with rfl|hq
          · exact (ht r (by simp)).2
          · exact hl hq
      have htail := ih (fun r hr => ht r (List.mem_cons_of_mem _ hr))
      simp only [skywalkDialogReplay,skywalkDialogUnreplay,wires_append,Finset.union_subset_iff]
      exact ⟨⟨hc.1.trans own,htail.1⟩,⟨htail.2,hc.2.trans own⟩⟩
  have hUnary := modUnary_wires L.unary 256 p (L.unary_widths 256 hw) (by omega)
  have hHalf : wires (halfInPlace L.unary p)⊆W.toFinset := by
    rw [hUnary.2]
    intro q hq
    apply List.mem_toFinset.mpr
    apply hl
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,ModUnaryLayout.core,
      ModAddCoreLayout.z,ModAddCoreLayout.work,ModInPlaceLayout.z] at hq ⊢
    tauto
  have hDouble : wires (dblInPlace L.unary p)⊆W.toFinset := by
    rw [hUnary.1]
    intro q hq
    apply List.mem_toFinset.mpr
    apply hl
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,ModUnaryLayout.core,
      ModAddCoreLayout.z,ModAddCoreLayout.work,ModInPlaceLayout.z] at hq ⊢
    tauto
  have hlen : L.z.length=L.a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hCopy : wires (copyRegister none L.z L.a)⊆W.toFinset := by
    rw [copyRegister_wires none L.z L.a hlen]
    split
    · exact Finset.empty_subset _
    · intro q hq
      apply List.mem_toFinset.mpr
      apply hl
      have hh : q∈L.z++L.a := by simpa only [Option.toList_none,List.nil_append,List.mem_toFinset] using hq
      have hh' := List.mem_append.mp hh
      rcases hh' with hz|ha
      · exact List.mem_append_left _ (List.mem_append_right _ hz)
      · exact List.mem_append_left _ (List.mem_append_left _ ha)
  simp only [skywalkFieldDivision,skywalkFieldMultiplication,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨hDouble,hReplay.1⟩,hCopy⟩,⟨⟨hCopy,hReplay.2⟩,hHalf⟩⟩

/-- Physical support of the actual seven-stage arithmetic circuit. The proof-only
active wire is absent; every instruction uses one of the2314 shared sites. -/
theorem skywalkArithmetic_support (divide : Bool) (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    wires (skywalkArithmetic divide w)⊆(skywalkSharedWires w).toFinset := by
  have hs := skywalkSeed_wires (skywalkSharedSeed w) 258 p (skywalkShared_seed_widths w)
  have hseed : wires (skywalkSeed (skywalkSharedSeed w) p)⊆(skywalkSharedWires w).toFinset := by
    rw [hs.1]
    intro q hq
    exact List.mem_toFinset.mpr (arith_seed_subset_shared w (List.mem_toFinset.mp hq))
  have hunseed : wires (skywalkUnseed (skywalkSharedSeed w) p)⊆(skywalkSharedWires w).toFinset := by
    rw [hs.2]
    intro q hq
    exact List.mem_toFinset.mpr (arith_seed_subset_shared w (List.mem_toFinset.mp hq))
  have hi := narrowSkywalkRoutedLoop_support w 0 512 (skywalkShared_integer_nodup w hn) (by omega)
  have hpool : (skywalkPoolWires w).toFinset⊆(skywalkSharedWires w).toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (arith_block_subset_shared w 0 1798 (by omega) (List.mem_toFinset.mp hq))
  have hclear : wires (skywalkArithmeticClear w)⊆(skywalkSharedWires w).toFinset := by
    rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
    intro q hq
    have hh : q=w 511 ∨ q=w 512 ∨ q=w 770 := by
      simpa only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] using hq
    apply List.mem_toFinset.mpr
    rcases hh with rfl|rfl|rfl
    · exact arith_mem w 0 2314 511 (by omega) (by omega)
    · exact arith_mem w 0 2314 512 (by omega) (by omega)
    · exact arith_mem w 0 2314 770 (by omega) (by omega)
  have hf := arith_field_legs_support (skywalkSharedField w) (skywalkSharedTape w)
    (skywalkShared_field_widths w) (skywalkSharedWires w)
    (arith_field_subset_shared w) (arith_tape_subset_shared w)
  have hleg : wires (if divide then skywalkFieldDivisionRetained w
      else skywalkFieldMultiplicationRetained w)⊆(skywalkSharedWires w).toFinset := by
    cases divide
    · exact skywalkFieldMultiplicationRetained_support w
    · exact skywalkFieldDivisionRetained_support w
  simp only [skywalkArithmetic,wires_append,Finset.union_subset_iff]
  exact ⟨hseed,hi.1.trans hpool,hclear,hleg,hclear,hi.2.trans hpool,hunseed⟩

end ECDSAAdd.Arithmetic
