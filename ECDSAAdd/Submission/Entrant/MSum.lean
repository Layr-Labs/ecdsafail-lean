import ECDSAAdd.Submission.Entrant.AccFold
import ECDSAAdd.Baselines.SlotBalanced

/-! Measured sum preparation for the streamed square's third branch.

The branch squares `A + B`, the sum of the two 128-bit input halves, held in
the 129-bit register `sum = high ++ [sumCarry]`.  The sum used to be prepared
with a 129-bit Cuccaro adder and cleared by its exact reverse (256 Toffolis
each way, no measurements).  Here it is prepared by one measured `mappedAdd`
of `low ++ [0]` into `sum` (128 Toffolis, 128 measurements) and cleared by one
fresh-record `mappedSub` (complement, add, complement; 128 Toffolis, 128
measurements).  The carry bank is the first 128 wires of the square's clean
`work` register; no new wires are used. -/

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def msumBits (L : CuccaroStreamedSquareWideLayout) : List MappedBit :=
  mappedRead L.core.low false++[({wire:=none,flip:=false} : MappedBit)]
def msumBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 128
def msumPrepare (L : CuccaroStreamedSquareWideLayout) : Program :=
  mappedAdd (msumBits L) L.core.sum (msumBank L) L.core.cin
def msumClear (L : CuccaroStreamedSquareWideLayout) : Program :=
  mappedSub (msumBits L) L.core.sum (msumBank L) L.core.cin

theorem mappedValue_append' (a b : List MappedBit) (s : BasisState) :
    mappedValue (a++b) s=mappedValue a s+2^a.length*mappedValue b s := by
  induction a with
  | nil => simp [mappedValue]
  | cons x xs ih =>
    simp only [List.cons_append,mappedValue,ih,List.length_cons,pow_succ]
    ring

theorem msumBits_value (L : CuccaroStreamedSquareWideLayout) (s : BasisState) :
    mappedValue (msumBits L) s=regValue L.core.low s := by
  rw [msumBits,mappedValue_append',mappedRead_value]
  simp [mappedValue,MappedBit.value]

theorem msumBits_wires (L : CuccaroStreamedSquareWideLayout) (q : Wire)
    (hq : q∈mappedWires (msumBits L)) : q∈L.core.low := by
  simp only [msumBits,mappedWires,mappedRead,List.flatMap_append,List.mem_append,List.flatMap_map,
    List.mem_flatMap,Option.toList_some,List.mem_singleton,List.flatMap_cons,List.flatMap_nil,
    Option.toList_none,List.append_nil,List.not_mem_nil,or_false] at hq
  obtain ⟨w,hw',rfl⟩ := hq
  exact hw'

theorem msum_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (msumBits L).length=L.core.sum.length ∧ (msumBank L).length+1=L.core.sum.length := by
  have lo := L.core.low_length hw.core
  have su := L.core.sum_length hw.core
  constructor
  · simp [msumBits,mappedRead_length,lo,su]
  · simp [msumBank,hw.core.work,su]

theorem msum_nodup (L : CuccaroStreamedSquareWideLayout) (hnd : L.wires.Nodup) :
    (L.core.cin::(L.core.sum++msumBank L)).Nodup ∧
      ∀q∈L.core.low,q∉L.core.cin::(L.core.sum++msumBank L) := by
  have cnt (q : Wire) := List.nodup_iff_count.mp hnd q
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    have h := cnt q
    have hlo := (List.take_sublist 128 L.core.y).count_le q
    have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
    have hsplit := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
    have hbank := (List.take_sublist 128 L.core.work).count_le q
    simp only [List.count_append] at hsplit
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,msumBank,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append,
      List.count_cons,List.count_nil] at h ⊢
    omega
  · intro q hq hm
    have h := cnt q
    have pos := List.count_pos_iff.mpr hq
    have pos2 := List.count_pos_iff.mpr hm
    have hlo := (List.take_sublist 128 L.core.y).count_le q
    have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
    have hsplit := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
    have hbank := (List.take_sublist 128 L.core.work).count_le q
    simp only [List.count_append] at hsplit
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,msumBank,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,CuccaroStreamedSquareLayout.low,
      List.count_append,List.count_cons,List.count_nil] at h pos pos2 ⊢
    omega

theorem msum_sep (L : CuccaroStreamedSquareWideLayout) (hnd : L.wires.Nodup) :
    ∀q∈mappedWires (msumBits L),q∉L.core.cin::(L.core.sum++msumBank L) :=
  fun q hq => (msum_nodup L hnd).2 q (msumBits_wires L q hq)

theorem msum_bank_away (L : CuccaroStreamedSquareWideLayout) (hnd : L.wires.Nodup)
    (q : Wire) (hq : q∈msumBank L) : q∉L.core.sum ∧ q≠L.core.cin := by
  have nd := (msum_nodup L hnd).1
  have h := List.nodup_iff_count.mp nd q
  have pos := List.count_pos_iff.mpr hq
  constructor
  · intro bad
    have p2 := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h
    omega
  · intro bad
    subst bad
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
    omega

theorem msum_cin_away (L : CuccaroStreamedSquareWideLayout) (hnd : L.wires.Nodup) :
    L.core.cin∉L.core.sum :=
  fun h => (List.nodup_cons.mp (msum_nodup L hnd).1).1 (List.mem_append_left _ h)

theorem msumPrepare_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A)
    (hbound : A+B<2^129) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame L.core.sum base B) (msumPrepare L)
      (SquareFrame L.core.sum base (A+B)) := by
  obtain ⟨nd,sep⟩ := msum_nodup L hnd
  have lens := msum_lengths L hw
  intro s m ⟨hv,hfr⟩
  have clean : ∀q∈msumBank L,s.basis q=false := fun q hq =>
    (hfr q (msum_bank_away L hnd q hq).1).trans
      ((regValue_zero _ _).mp hwork q (List.mem_of_mem_take hq))
  have cinS : s.basis L.core.cin=false := (hfr _ (msum_cin_away L hnd)).trans hcin
  have lowS : regValue L.core.low s.basis=A :=
    (regValue_congr _ _ _ (fun q hq => hfr q (fun h => sep q hq
      (List.mem_cons_of_mem _ (List.mem_append_left _ h))))).trans hA
  have r := mappedAdd_correct (msumBits L) L.core.sum (msumBank L) L.core.cin nd
    (msum_sep L hnd) lens.1 lens.2 s m clean
  unfold msumPrepare
  refine ⟨r.1,?_,?_⟩
  · rw [r.2.2,msumBits_value,lowS,hv,cinS,L.core.sum_length hw.core]
    simp only [Bool.toNat_false,Nat.add_zero]
    exact Nat.mod_eq_of_lt hbound
  · intro w hw'
    rw [r.2.1 w hw']
    exact hfr w hw'

theorem msumClear_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hB : regValue L.core.sum base=B)
    (hbound : A+B<2^129) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame L.core.sum base (A+B)) (msumClear L)
      (SquareFrame L.core.sum base B) := by
  obtain ⟨nd,sep⟩ := msum_nodup L hnd
  have lens := msum_lengths L hw
  intro s m ⟨hv,hfr⟩
  have clean : ∀q∈msumBank L,s.basis q=false := fun q hq =>
    (hfr q (msum_bank_away L hnd q hq).1).trans
      ((regValue_zero _ _).mp hwork q (List.mem_of_mem_take hq))
  have cinS : s.basis L.core.cin=false := (hfr _ (msum_cin_away L hnd)).trans hcin
  have lowS : regValue L.core.low s.basis=A :=
    (regValue_congr _ _ _ (fun q hq => hfr q (fun h => sep q hq
      (List.mem_cons_of_mem _ (List.mem_append_left _ h))))).trans hA
  have r := mappedSub_correct (msumBits L) L.core.sum (msumBank L) L.core.cin nd
    (msum_sep L hnd) lens.1 lens.2 s m clean cinS
  unfold msumClear
  refine ⟨r.1,?_,?_⟩
  · rw [r.2.2,msumBits_value,lowS,hv,L.core.sum_length hw.core]
    rw [show A+B+2^129-A=B+2^129 by omega,Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  · intro w hw'
    rw [r.2.1 w hw']
    exact hfr w hw'

theorem msum_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (toffoliCount (msumPrepare L)=128 ∧ measurementCount (msumPrepare L)=128) ∧
    (toffoliCount (msumClear L)=128 ∧ measurementCount (msumClear L)=128) := by
  have lens := msum_lengths L hw
  have su := L.core.sum_length hw.core
  have a := mappedAdd_counts (msumBits L) L.core.sum (msumBank L) L.core.cin lens.1 lens.2
  have b := mappedSub_counts (msumBits L) L.core.sum (msumBank L) L.core.cin lens.1 lens.2
  rw [su] at a b
  exact ⟨a,b⟩

theorem msum_sites (L : CuccaroStreamedSquareWideLayout) (q : Wire)
    (hq : q∈mappedWires (msumBits L)++L.core.sum++msumBank L++[L.core.cin]) :
    q∈L.wires := by
  simp only [List.mem_append,List.mem_singleton] at hq
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  rcases hq with ((h|h)|h)|h
  · have := msumBits_wires L q h
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_of_mem_take this))))))
  · simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.mem_append,
      List.mem_singleton] at h
    rcases h with h|rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (List.mem_of_mem_drop (List.mem_of_mem_take h)))))))
    · simp
  · exact Or.inl (Or.inl (Or.inr (List.mem_of_mem_take h)))
  · subst h; simp

theorem msum_support (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    ECDSAAdd.wires (msumPrepare L)⊆(control::L.wires).toFinset ∧
    ECDSAAdd.wires (msumClear L)⊆(control::L.wires).toFinset := by
  have lift (P : Program)
      (h : ECDSAAdd.wires P⊆(mappedWires (msumBits L)++L.core.sum++msumBank L++[L.core.cin]).toFinset) :
      ECDSAAdd.wires P⊆(control::L.wires).toFinset := by
    intro q hq
    have m := List.mem_toFinset.mp (h hq)
    exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (msum_sites L q m))
  exact ⟨lift _ (mappedAdd_wires_subset _ _ _ _),lift _ (mappedSub_wires_subset _ _ _ _)⟩

theorem msum_physical (L : CuccaroStreamedSquareWideLayout) (hnd : L.wires.Nodup) :
    GatePhysical (msumPrepare L) ∧ GatePhysical (msumClear L) := by
  have nd := (msum_nodup L hnd).1
  have ha : ∀b∈msumBits L,∀q∈b.wire,q∉L.core.cin::L.core.sum++msumBank L := by
    intro b hb q hq
    apply msum_sep L hnd q
    simp only [mappedWires,List.mem_flatMap]
    exact ⟨b,hb,by simpa using hq⟩
  have add := mappedAdd_physical (msumBits L) L.core.sum (msumBank L) L.core.cin nd ha
  have nots : GatePhysical (notRegister L.core.sum) := by
    intro i hi
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hi
    trivial
  refine ⟨add,?_⟩
  simp only [msumClear,mappedSub,gatePhysical_append]
  exact ⟨⟨nots,add⟩,nots⟩

theorem msum_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (msumPrepare L)≤2193 ∧ Challenge.gateSlots (msumClear L)≤2451 := by
  have lens := msum_lengths L hw
  have su := L.core.sum_length hw.core
  have a := Baselines.mappedAdd_gateSlots_le (msumBits L) L.core.sum (msumBank L) L.core.cin
  have b := Baselines.mappedSub_gateSlots_le (msumBits L) L.core.sum (msumBank L) L.core.cin
  rw [lens.1,su] at a b
  simp only [msumPrepare,msumClear]
  exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant
