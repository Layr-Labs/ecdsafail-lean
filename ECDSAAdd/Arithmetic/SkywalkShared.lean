import ECDSAAdd.Arithmetic.SkywalkSeed
import ECDSAAdd.Arithmetic.SkywalkPool
import ECDSAAdd.Arithmetic.ModInPlaceWrappers
import ECDSAAdd.Arithmetic.ConditionalXor

namespace ECDSAAdd.Arithmetic

/-- Integer memory plus a 258-bit seed constant, 257-bit numerator and auxiliary flag. -/
def skywalkSharedWires (w : Nat → Wire) : List Wire := wireBlock w 0 2314

def skywalkSharedSeed (w : Nat → Wire) : SkywalkSeedLayout :=
  { a:=wireBlock w 0 258,b:=wireBlock w 770 258,constant:=wireBlock w 1798 258,
    carry:=wireBlock w 1540 257,cin:=w 2313,orientation:=w 1797 }

/-- Field arithmetic borrows cleared terminal rails and restored integer/seed scratch. -/
def skywalkSharedField (w : Nat → Wire) : ModInPlaceLayout :=
  { a:=wireBlock w 770 257,low:=wireBlock w 2056 256,high:=w 2312,
    constant:=wireBlock w 1540 257,carry:=wireBlock w 1798 256,cin:=w 1797,
    mask:=wireBlock w 512 257,flag:=w 2313 }

def skywalkSharedTape (w : Nat → Wire) : List (Wire × Wire) :=
  (List.range 512).map (fun i => (w i,w (1028+i)))

def skywalkSharedUnused (w : Nat → Wire) : List Wire := [w 769,w 1027,w 2054,w 2055]

private def sharedSeedIds : List Nat :=
  2313::1797::(List.range' 0 258++List.range' 770 258++
    List.range' 1798 258++List.range' 1540 257)

private def sharedFieldIds : List Nat :=
  List.range' 770 257++List.range' 2056 257++List.range' 1540 257++
    List.range' 1798 256++[1797]++List.range' 512 257++[2313]

private theorem shared_block_one (w : Nat → Wire) (s : Nat) : wireBlock w s 1=[w s] := by
  simp [wireBlock,List.range']

private theorem shared_append_region (ls : List Nat) (hd : ls.Nodup) (s n : Nat)
    (hsep : ∀ j∈ls,j<s ∨ s+n≤j) : (ls++List.range' s n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hd,List.nodup_range',?_⟩
  apply List.disjoint_left.mpr
  intro j hj hk
  have hh := hsep j hj
  simp only [List.mem_range'_1] at hk
  omega

private theorem shared_seedIds_nodup : sharedSeedIds.Nodup := by
  have h1 := shared_append_region (List.range' 0 258) List.nodup_range' 770 258 (by
    intro j hj; simp only [List.mem_range'_1] at hj; omega)
  have h2 := shared_append_region _ h1 1798 258 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h3 := shared_append_region _ h2 1540 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h4 : (1797::(List.range' 0 258++List.range' 770 258++
      List.range' 1798 258++List.range' 1540 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,h3⟩
    intro hm
    simp only [List.mem_append,List.mem_range'_1] at hm
    omega
  apply List.nodup_cons.mpr
  refine ⟨?_,h4⟩
  intro hm
  simp only [List.mem_cons,List.mem_append,List.mem_range'_1] at hm
  omega

private theorem shared_fieldIds_nodup : sharedFieldIds.Nodup := by
  have h1 := shared_append_region (List.range' 770 257) List.nodup_range' 2056 257 (by
    intro j hj; simp only [List.mem_range'_1] at hj; omega)
  have h2 := shared_append_region _ h1 1540 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h3 := shared_append_region _ h2 1798 256 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h4 := shared_append_region _ h3 1797 1 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h5 := shared_append_region _ h4 512 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have h6 := shared_append_region _ h5 2313 1 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  simpa only [show List.range' 1797 1=[1797] from rfl,
    show List.range' 2313 1=[2313] from rfl] using h6

private theorem shared_seedIds_bound (j : Nat) (hj : j∈sharedSeedIds) : j<2314 := by
  simp only [sharedSeedIds,List.mem_cons,List.mem_append,List.mem_range'_1] at hj
  omega

private theorem shared_fieldIds_bound (j : Nat) (hj : j∈sharedFieldIds) : j<2314 := by
  simp only [sharedFieldIds,List.mem_cons,List.mem_append,List.mem_range'_1,List.not_mem_nil,or_false] at hj
  omega

theorem skywalkShared_index_inj (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i j : Nat) (hi : i<2314) (hj : j<2314) (he : w i=w j) : i=j := by
  change ((List.range' 0 2314).map w).Nodup at hn
  exact List.inj_on_of_nodup_map hn
    (by simp only [List.mem_range'_1]; omega)
    (by simp only [List.mem_range'_1]; omega) he

private theorem shared_map_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (ls : List Nat) (hd : ls.Nodup) (hb : ∀ j∈ls,j<2314) : (ls.map w).Nodup := by
  apply List.Nodup.map_on
  · intro j hj k hk he
    exact skywalkShared_index_inj w hn j k (hb j hj) (hb k hk) he
  · exact hd

private theorem shared_not_mem_map (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (i : Nat) (hi : i<2314) (ls : List Nat) (hb : ∀ j∈ls,j<2314) (he : i∉ls) : w i∉ls.map w := by
  intro hm
  obtain ⟨j,hj,hji⟩ := List.mem_map.mp hm
  have hh := skywalkShared_index_inj w hn j i (hb j hj) hi hji
  subst j
  exact he hj

theorem skywalkShared_integer_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (skywalkPoolWires w).Nodup := by
  have he := wireBlock_append w 0 1798 516
  change (wireBlock w 0 1798).Nodup
  apply (List.sublist_append_left (wireBlock w 0 1798) (wireBlock w 1798 516)).nodup
  simpa only [he,Nat.zero_add,Nat.reduceAdd,skywalkSharedWires] using hn

theorem skywalkShared_seed_widths (w : Nat → Wire) : (skywalkSharedSeed w).Widths 258 := by
  constructor <;> simp [skywalkSharedSeed,wireBlock_length]

theorem skywalkShared_seed_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (skywalkSharedSeed w).wires.Nodup := by
  have he : (skywalkSharedSeed w).wires=sharedSeedIds.map w := by
    simp only [skywalkSharedSeed,SkywalkSeedLayout.wires,sharedSeedIds,
      wireBlock,List.map_cons,List.map_append]
  rw [he]
  exact shared_map_nodup w hn _ shared_seedIds_nodup shared_seedIds_bound

theorem skywalkShared_field_z (w : Nat → Wire) :
    (skywalkSharedField w).z=wireBlock w 2056 257 := by
  change wireBlock w 2056 256++[w 2312]=_
  have he := wireBlock_append w 2056 256 1
  simp only [shared_block_one,Nat.reduceAdd] at he
  exact he

theorem skywalkShared_field_widths (w : Nat → Wire) : (skywalkSharedField w).Widths 256 := by
  constructor
  · constructor <;> simp [skywalkSharedField,wireBlock_length]
  · simp [skywalkSharedField,wireBlock_length]

private theorem shared_field_wires (w : Nat → Wire) :
    (skywalkSharedField w).wires=sharedFieldIds.map w := by
  unfold ModInPlaceLayout.wires
  rw [skywalkShared_field_z]
  simp only [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,
    sharedFieldIds,wireBlock,List.map_append,List.map_cons,List.map_nil]
  simp only [List.append_assoc]

theorem skywalkShared_field_nodup (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup) :
    (skywalkSharedField w).wires.Nodup := by
  rw [shared_field_wires]
  exact shared_map_nodup w hn _ shared_fieldIds_nodup shared_fieldIds_bound

theorem skywalkShared_tape_length (w : Nat → Wire) : (skywalkSharedTape w).length=512 := by
  simp [skywalkSharedTape]

/-- Every real record pair is disjoint from all field data/scratch. An existing
caller control outside the universe may serve as the proof-only active wire. -/
theorem skywalkShared_tape_layout (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (active : Wire) (ha : active∉skywalkSharedWires w) :
    ∀ r∈skywalkSharedTape w,(active::r.2::r.1::(skywalkSharedField w).wires).Nodup := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  have hib : i<512 := List.mem_range.mp hi
  have hfield := skywalkShared_field_nodup w hn
  have hgi : w i∉(skywalkSharedField w).wires := by
    rw [shared_field_wires]
    apply shared_not_mem_map w hn i (by omega) _ shared_fieldIds_bound
    simp only [sharedFieldIds,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false]
    omega
  have hsi : w (1028+i)∉(skywalkSharedField w).wires := by
    rw [shared_field_wires]
    apply shared_not_mem_map w hn (1028+i) (by omega) _ shared_fieldIds_bound
    simp only [sharedFieldIds,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false]
    omega
  have hsg : w (1028+i)≠w i := by
    intro he
    have hh := skywalkShared_index_inj w hn (1028+i) i (by omega) (by omega) he
    omega
  have hbase : (w i::(skywalkSharedField w).wires).Nodup := List.nodup_cons.mpr ⟨hgi,hfield⟩
  have hpair : (w (1028+i)::w i::(skywalkSharedField w).wires).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hbase⟩
    intro hm
    rcases List.mem_cons.mp hm with hm|hm
    · exact hsg hm
    · exact hsi hm
  apply List.nodup_cons.mpr
  refine ⟨?_,hpair⟩
  intro hm
  have hpool : ∀ j<2314,w j∈skywalkSharedWires w := by
    intro j hj
    apply List.mem_map.mpr
    refine ⟨j,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  simp only [List.mem_cons] at hm
  rcases hm with rfl|rfl|hm
  · exact ha (hpool _ (by omega))
  · exact ha (hpool _ (by omega))
  · rw [shared_field_wires] at hm
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
    exact ha (hpool _ (shared_fieldIds_bound j hj))

/-- Full integer/seed scratch after terminal clear, before any field borrowing. -/
def SkywalkSharedClean (w : Nat → Wire) (s : BasisState) : Prop :=
  regValue (wireBlock w 512 258) s=0 ∧ regValue (wireBlock w 770 258) s=0 ∧
  regValue (wireBlock w 1540 257) s=0 ∧ regValue (wireBlock w 1798 258) s=0 ∧
  s (w 1797)=false ∧ s (w 2313)=false

private theorem shared_block_prefix (w : Nat → Wire) (start n m : Nat) (h : n≤m) :
    (wireBlock w start n).Sublist (wireBlock w start m) := by
  have he := wireBlock_append w start n (m-n)
  rw [Nat.add_sub_of_le h] at he
  rw [← he]
  exact List.sublist_append_left _ _

private theorem shared_zero_sublist (a b : List Wire) (s : BasisState)
    (hab : a.Sublist b) (h : regValue b s=0) : regValue a s=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  exact (regValue_zero _ _).mp h q (hab.subset hq)

/-- Exact transfer of clean integer rails/seed constant to source and all field work.
The four omitted padding sites are retained explicitly, rather than discarded. -/
theorem skywalkShared_clean_to_field (w : Nat → Wire) (s : BasisState)
    (h : SkywalkSharedClean w s) :
    regValue (skywalkSharedField w).a s=0 ∧ regValue (skywalkSharedField w).work s=0 ∧
      regValue (skywalkSharedUnused w) s=0 := by
  have ha := shared_zero_sublist _ _ s (shared_block_prefix w 770 257 258 (by decide)) h.2.1
  have hm := shared_zero_sublist _ _ s (shared_block_prefix w 512 257 258 (by decide)) h.1
  have hc := shared_zero_sublist _ _ s (shared_block_prefix w 1798 256 258 (by decide)) h.2.2.2.1
  refine ⟨ha,?_,?_⟩
  · change regValue (wireBlock w 1540 257++wireBlock w 1798 256++[w 1797]++
      wireBlock w 512 257++[w 2313]) s=0
    rw [regValue_append,regValue_append,regValue_append,regValue_append,
      h.2.2.1,hc,hm]
    simp [regValue,h.2.2.2.2.1,h.2.2.2.2.2]
  · apply (regValue_zero _ _).mpr
    intro q hq
    have memA : w 769∈wireBlock w 512 258 := by
      apply List.mem_map.mpr; refine ⟨769,?_,rfl⟩; simp only [List.mem_range'_1]; omega
    have memB : w 1027∈wireBlock w 770 258 := by
      apply List.mem_map.mpr; refine ⟨1027,?_,rfl⟩; simp only [List.mem_range'_1]; omega
    have memC (j : Nat) (hj : j=2054 ∨ j=2055) : w j∈wireBlock w 1798 258 := by
      apply List.mem_map.mpr; refine ⟨j,?_,rfl⟩; simp only [List.mem_range'_1]; omega
    simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact (regValue_zero _ _).mp h.1 _ memA
    · exact (regValue_zero _ _).mp h.2.1 _ memB
    · exact (regValue_zero _ _).mp h.2.2.2.1 _ (memC 2054 (Or.inl rfl))
    · exact (regValue_zero _ _).mp h.2.2.2.1 _ (memC 2055 (Or.inr rfl))

/-- Return all borrowed word sites, not only the shortened field views. -/
theorem skywalkShared_field_to_clean (w : Nat → Wire) (s : BasisState)
    (ha : regValue (skywalkSharedField w).a s=0)
    (hw : regValue (skywalkSharedField w).work s=0)
    (hu : regValue (skywalkSharedUnused w) s=0) : SkywalkSharedClean w s := by
  have clean := (regValue_zero _ _).mp hw
  have unused := (regValue_zero _ _).mp hu
  have h769 : s (w 769)=false := unused _ (by simp [skywalkSharedUnused])
  have h1027 : s (w 1027)=false := unused _ (by simp [skywalkSharedUnused])
  have h2054 : s (w 2054)=false := unused _ (by simp [skywalkSharedUnused])
  have h2055 : s (w 2055)=false := unused _ (by simp [skywalkSharedUnused])
  change regValue (wireBlock w 770 257) s=0 at ha
  have hm : regValue (wireBlock w 512 257) s=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact clean q (by simp [skywalkSharedField,ModInPlaceLayout.work,hq])
  have hc : regValue (wireBlock w 1798 256) s=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact clean q (by simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,hq])
  have hd : regValue (wireBlock w 1540 257) s=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact clean q (by simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work,hq])
  have hb1797 : s (w 1797)=false := clean _ (by
    simp [skywalkSharedField,ModInPlaceLayout.work,ModAddCoreLayout.work])
  have hb2313 : s (w 2313)=false := clean _ (by simp [skywalkSharedField,ModInPlaceLayout.work])
  have hA := wireBlock_append w 512 257 1
  have hB := wireBlock_append w 770 257 1
  have hC := wireBlock_append w 1798 256 2
  simp only [shared_block_one,Nat.reduceAdd] at hA hB
  have htwo : wireBlock w 2054 2=[w 2054,w 2055] := by simp [wireBlock,List.range']
  rw [show 1798+256=2054 from rfl,htwo] at hC
  refine ⟨?_,?_,hd,?_,hb1797,hb2313⟩
  · rw [← hA,regValue_append,hm]
    simp [regValue,h769]
  · rw [← hB,regValue_append,ha]
    simp [regValue,h1027]
  · rw [← hC,regValue_append,hc]
    simp [regValue,h2054,h2055]

theorem skywalkShared_unused_outside (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (q : Wire) (hq : q∈skywalkSharedUnused w) : q∉(skywalkSharedField w).wires := by
  rw [shared_field_wires]
  have notField (i : Nat) (hi : i=769 ∨ i=1027 ∨ i=2054 ∨ i=2055) : w i∉sharedFieldIds.map w := by
    apply shared_not_mem_map w hn i (by omega) _ shared_fieldIds_bound
    simp only [sharedFieldIds,List.mem_append,List.mem_cons,List.mem_range'_1,List.not_mem_nil,or_false]
    omega
  simp only [skywalkSharedUnused,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl
  · exact notField 769 (Or.inl rfl)
  · exact notField 1027 (Or.inr (Or.inl rfl))
  · exact notField 2054 (Or.inr (Or.inr (Or.inl rfl)))
  · exact notField 2055 (Or.inr (Or.inr (Or.inr rfl)))

/-- The actual field leg's target/source frame returns the integer workspace,
including every omitted padding bit, while allowing the numerator to change. -/
theorem skywalkShared_return_pairFrame (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (base s : BasisState) (Z : Nat) (hb : SkywalkSharedClean w base)
    (hf : PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base Z 0 s) :
    SkywalkSharedClean w s := by
  have hbefore := skywalkShared_clean_to_field w base hb
  have hnd := skywalkShared_field_nodup w hn
  have work_away (q : Wire) (hq : q∈(skywalkSharedField w).work) :
      q∉(skywalkSharedField w).z ∧ q∉(skywalkSharedField w).a := by
    have hd := (List.nodup_append'.mp hnd).2.2
    constructor
    · intro hz
      exact List.disjoint_left.mp hd (List.mem_append_right _ hz) hq
    · intro ha
      exact List.disjoint_left.mp hd (List.mem_append_left _ ha) hq
  have hwork : regValue (skywalkSharedField w).work s=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hbefore.2.1
    intro q hq
    exact hf.2.2 q (work_away q hq).1 (work_away q hq).2
  have hUnused : regValue (skywalkSharedUnused w) s=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hbefore.2.2
    intro q hq
    have ho := skywalkShared_unused_outside w hn q hq
    apply hf.2.2 q
    · intro hz
      exact ho (by simp [ModInPlaceLayout.wires,hz])
    · intro ha
      exact ho (by simp [ModInPlaceLayout.wires,ha])
  exact skywalkShared_field_to_clean w s hf.2.1 hwork hUnused

/-- The numerator's used high padding bit is also zero for every canonical
256-bit field result; unlike the four unused sites it is part of the target. -/
theorem skywalkShared_numerator_high_zero (w : Nat → Wire) (s : BasisState) (Z : Nat)
    (hz : regValue (skywalkSharedField w).z s=Z) (hZ : Z<2^256) : s (w 2312)=false := by
  have hp := regValue_highBit (wireBlock w 2056 256) (w 2312) s
  have hl : (wireBlock w 2056 256).length=256 := wireBlock_length _ _ _
  rw [hl] at hp
  change regValue (wireBlock w 2056 256++[w 2312]) s=Z at hz
  rw [hz] at hp
  cases hs : s (w 2312) with
  | false => rfl
  | true => have hh := hp.mp hs; omega

end ECDSAAdd.Arithmetic
