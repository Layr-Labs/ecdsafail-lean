import ECDSAAdd.Arithmetic.PointMeasuredSquareCandidate
import ECDSAAdd.Framework.WireRenameComposition
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.CompressedPointSquare
open ControlledPointLayout
attribute [local irreducible] run wires pointMeasuredSquareCandidate

def indexFn (i : Nat) : Nat :=
  if 515 ≤ i ∧ i < 684 then i+261 else if 776 ≤ i ∧ i < 945 then i-261 else i

private theorem index_twice : Function.Involutive indexFn := by
  intro i
  unfold indexFn
  split_ifs <;> omega

def indexPermutation : Equiv.Perm Nat :=
  {toFun:=indexFn,invFun:=indexFn,left_inv:=index_twice,right_inv:=index_twice}

theorem index_bounded (i : Nat) (hi : i < 945) : indexPermutation i < 945 := by
  change indexFn i < 945
  unfold indexFn
  split_ifs <;> omega

theorem prefix_allowed (i : Nat) (hi : i < 776) :
    indexPermutation i < 515 ∨ (684 ≤ indexPermutation i ∧ indexPermutation i < 945) := by
  change indexFn i < 515 ∨ (684 ≤ indexFn i ∧ indexFn i < 945)
  unfold indexFn
  split_ifs <;> omega

def BoundedInjective (w : Nat → Wire) : Prop :=
  ∀i j,i < 945 → j < 945 → w i=w j → i=j

def LeftSite (w : Nat → Wire) (q : Wire) : Prop := ∃i,515 ≤ i ∧ i < 684 ∧ q=w i
def RightSite (w : Nat → Wire) (q : Wire) : Prop := ∃i,776 ≤ i ∧ i < 945 ∧ q=w i

/-- Only the338 declared pool sites are moved; fallback labels outside
that allocation are never assumed injective. -/
noncomputable def wireFn (w : Nat → Wire) (q : Wire) : Wire := by
  classical
  exact if h : LeftSite w q then w (Classical.choose h+261)
    else if h : RightSite w q then w (Classical.choose h-261) else q

theorem wire_apply (w : Nat → Wire) (hn : BoundedInjective w)
    (i : Nat) (hi : i < 945) : wireFn w (w i)=w (indexPermutation i) := by
  classical
  change wireFn w (w i)=w (indexFn i)
  by_cases a : 515 ≤ i ∧ i < 684
  · have yes : LeftSite w (w i) := ⟨i,a.1,a.2,rfl⟩
    have spec := Classical.choose_spec yes
    have pick : Classical.choose yes=i := hn _ i (by omega) hi spec.2.2.symm
    simp only [wireFn,dif_pos yes,pick,indexFn,if_pos a]
  · have no : ¬LeftSite w (w i) := by
      rintro ⟨j,hj,hk,e⟩
      have eq := hn i j hi (by omega) e
      exact a (by omega)
    by_cases b : 776 ≤ i ∧ i < 945
    · have yes : RightSite w (w i) := ⟨i,b.1,b.2,rfl⟩
      have spec := Classical.choose_spec yes
      have pick : Classical.choose yes=i := hn _ i spec.2.1 hi spec.2.2.symm
      simp only [wireFn,dif_neg no,dif_pos yes,pick,indexFn,if_neg a,if_pos b]
    · have no' : ¬RightSite w (w i) := by
        rintro ⟨j,hj,hk,e⟩
        have eq := hn i j hi hk e
        exact b (by omega)
      simp only [wireFn,dif_neg no,dif_neg no',indexFn,if_neg a,if_neg b]

private theorem wire_twice (w : Nat → Wire) (hn : BoundedInjective w) :
    Function.Involutive (wireFn w) := by
  classical
  intro q
  by_cases a : LeftSite w q
  · obtain ⟨i,lo,hi,rfl⟩ := a
    rw [wire_apply w hn i (by omega),wire_apply w hn _ (index_bounded i (by omega))]
    exact congrArg w (indexPermutation.symm_apply_apply i)
  · by_cases b : RightSite w q
    · obtain ⟨i,lo,hi,rfl⟩ := b
      rw [wire_apply w hn i hi,wire_apply w hn _ (index_bounded i hi)]
      exact congrArg w (indexPermutation.symm_apply_apply i)
    · simp only [wireFn,dif_neg a,dif_neg b]

noncomputable def poolPermutation (w : Nat → Wire) (hn : BoundedInjective w) : Equiv.Perm Wire :=
  {toFun:=wireFn w,invFun:=wireFn w,left_inv:=wire_twice w hn,right_inv:=wire_twice w hn}

theorem outside_fixed (w : Nat → Wire) (hn : BoundedInjective w) (q : Wire)
    (ha : ¬LeftSite w q) (hb : ¬RightSite w q) : poolPermutation w hn q=q := by
  classical
  change wireFn w q=q
  simp only [wireFn,dif_neg ha,dif_neg hb]

private theorem getD_member {α : Type} (xs : List α) (i : Nat) (d : α) (hi : i < xs.length) :
    xs.getD i d∈xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => exact List.mem_cons_of_mem a (ih i (by simpa using hi))

private theorem getD_injective (xs : List Wire) (nd : xs.Nodup) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) (eq : xs.getD i 0=xs.getD j 0) : i=j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a xs ih =>
    have tail := (List.nodup_cons.mp nd)
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getD_cons_zero,List.getD_cons_succ] at eq
        exact (tail.1 (eq.symm ▸ getD_member xs j 0 (by simpa using hj))).elim
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getD_cons_zero,List.getD_cons_succ] at eq
        exact (tail.1 (eq ▸ getD_member xs i 0 (by simpa using hi))).elim
      | succ j =>
        exact congrArg Nat.succ (ih tail.2 i j (by simpa using hi) (by simpa using hj) eq)

theorem layout_bounded_injective (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    BoundedInjective L.core.poolWire := by
  have nd : L.core.pool.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have full := List.nodup_iff_count.mp (L.core_nodup hn) q
    simp only [PointAddLayout.wires,PointAddLayout.work,List.count_append] at full
    omega
  intro i j hi hj eq
  exact getD_injective L.core.pool nd i j (by rw [hw.pool]; omega) (by rw [hw.pool]; omega) eq

def residents (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags

theorem resident_fixed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈residents L) : poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) q=q := by
  have dis := (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  have away : q∉L.dialogPool := List.disjoint_left.mp dis hq
  have bit (i : Nat) (hi : i < 945) : L.core.poolWire i∈L.dialogPool := by
    have small : L.core.poolWire i∈L.core.pool.take 2613 := by
      rw [←L.core.pool_prefix hw 2613 (by omega)]
      exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1]; omega,rfl⟩
    exact small
  apply outside_fixed
  · rintro ⟨i,lo,hi,e⟩
    exact away (e ▸ bit i (by omega))
  · rintro ⟨i,lo,hi,e⟩
    exact away (e ▸ bit i hi)

/-- Explicit common work inventory; square image uses its existing first
and second intervals, and does not reintroduce515..683. -/
def sharedPool (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 0 515++wireBlock L.core.poolWire 684 858++wireBlock L.core.poolWire 1800 5

noncomputable def program (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (pointMeasuredSquareCandidate L)

theorem measured_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L hw hn)⊆(residents L++sharedPool L).toFinset := by
  intro q hq
  rw [program,renameProgram_support] at hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  have supp := pointMeasuredSquareCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at supp
  have res : old∈residents L ∨ old∈L.dialogPool.take 776 := by
    simp only [residents,PointAddLayout.pointWires,inPlaceFlags,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false]
    tauto
  rcases res with res|mem
  · rw [resident_fixed L hw hn old res]
    exact List.mem_toFinset.mpr (List.mem_append_left _ res)
  · have prefixView : L.dialogPool.take 776=wireBlock L.core.poolWire 0 776 := by
      simp only [dialogPool,List.take_take,Nat.min_eq_left (show 776 ≤ 2613 by omega)]
      exact (L.core.pool_prefix hw 776 (by omega)).symm
    rw [prefixView] at mem
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) (L.core.poolWire i)=
      L.core.poolWire (indexPermutation i) from
        wire_apply L.core.poolWire (layout_bounded_injective L hw hn) i (by omega)]
    apply List.mem_toFinset.mpr
    apply List.mem_append_right
    rcases prefix_allowed i bound with lo|hi
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))

theorem sharedPool_length (L : ControlledPointLayout) : (sharedPool L).length=1378 := by
  simp only [sharedPool,List.length_append,wireBlock_length]

/-- Computable finite lookup, with length as the not-found sentinel. -/
def searchIndex (q : Wire) : List Wire → Nat
  | [] => 0
  | a::as => if q=a then 0 else searchIndex q as+1

private theorem search_spec (xs : List Wire) (q : Wire) (h : searchIndex q xs < xs.length) :
    xs.getD (searchIndex q xs) 0=q := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases e : q=a
    · simp [searchIndex,e]
    · have bound : searchIndex q xs < xs.length := by simpa [searchIndex,e] using h
      simpa only [searchIndex,if_neg e,List.getD_cons_succ] using ih bound

private theorem search_hits (xs : List Wire) (nd : xs.Nodup) (i : Nat) (hi : i < xs.length) :
    searchIndex (xs.getD i 0) xs=i := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    have tail := List.nodup_cons.mp nd
    cases i with
    | zero => simp [searchIndex]
    | succ i =>
      have bound : i < xs.length := by simpa using hi
      have away : xs.getD i 0≠a := fun e => tail.1 (e ▸ getD_member xs i 0 bound)
      simp only [List.getD_cons_succ,searchIndex,if_neg away]
      exact congrArg Nat.succ (ih tail.2 i bound)

private theorem prefix_getD (w : Nat → Wire) (i : Nat) (hi : i < 945) :
    (wireBlock w 0 945).getD i 0=w i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [wireBlock_length] using hi)]
  simp [wireBlock]

private theorem found_index (w : Nat → Wire) (hn : BoundedInjective w) (i : Nat) (hi : i < 945) :
    searchIndex (w i) (wireBlock w 0 945)=i := by
  have nd : (wireBlock w 0 945).Nodup := by
    apply List.Nodup.map_on
    · intro a ha b hb eq
      simp only [List.mem_range'_1] at ha hb
      exact hn a b (by omega) (by omega) eq
    · exact List.nodup_range'
  have hit := search_hits (wireBlock w 0 945) nd i (by simpa only [wireBlock_length] using hi)
  rw [prefix_getD w i hi] at hit
  exact hit

/-- Production relabeling reads only945 declared pool labels and is fully
computable; no Classical.choose value occurs in the emitted program. -/
def labelFn (w : Nat → Wire) (q : Wire) : Wire :=
  let i := searchIndex q (wireBlock w 0 945)
  if i < 945 then w (indexPermutation i) else q

theorem label_matches (w : Nat → Wire) (hn : BoundedInjective w) (q : Wire) :
    labelFn w q=poolPermutation w hn q := by
  let i := searchIndex q (wireBlock w 0 945)
  by_cases found : i < 945
  · have qeq : q=w i := (search_spec (wireBlock w 0 945) q
        (by simpa only [wireBlock_length] using found)).symm.trans (prefix_getD w i found)
    change (if i < 945 then w (indexPermutation i) else q)=wireFn w q
    rw [if_pos found,qeq,wire_apply w hn i found]
  · have noA : ¬LeftSite w q := by
      rintro ⟨j,lo,hi,e⟩
      have hit : i=j := by change searchIndex q (wireBlock w 0 945)=j; rw [e]; exact found_index w hn j (by omega)
      omega
    have noB : ¬RightSite w q := by
      rintro ⟨j,lo,hi,e⟩
      have hit : i=j := by change searchIndex q (wireBlock w 0 945)=j; rw [e]; exact found_index w hn j hi
      omega
    change (if i < 945 then w (indexPermutation i) else q)=poolPermutation w hn q
    rw [if_neg found,outside_fixed w hn q noA noB]

def computableProgram (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (pointMeasuredSquareCandidate L)

theorem computableProgram_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    computableProgram L=program L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

theorem computable_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (computableProgram L)⊆(residents L++sharedPool L).toFinset := by
  rw [computableProgram_eq L hw hn]
  exact measured_support L hw hn

end ECDSAAdd.Arithmetic.CompressedPointSquare
#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.indexPermutation
#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.poolPermutation
#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.measured_support

#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.computable_support
