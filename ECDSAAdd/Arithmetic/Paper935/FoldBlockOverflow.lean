import ECDSAAdd.Arithmetic.Paper935.FoldBlockRun
import ECDSAAdd.Arithmetic.Paper935.FoldKeeperMath

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

private theorem block_geometry (control : Wire) (b : FoldCell) (rest : List FoldCell)
    (cin : Option Wire) (hn : (control::cin.toList++(b::rest).flatMap FoldCell.wires).Nodup) :
    ([control,b.data,b.carry]++cin.toList).Nodup ∧
    (control::(b.next cin).toList++rest.flatMap FoldCell.wires).Nodup ∧
    List.Disjoint ([control,b.data,b.carry]++cin.toList) (rest.flatMap FoldCell.wires) := by
  have localNd : ([control,b.data,b.carry]++cin.toList).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have nextCount (q : Wire) : (b.next cin).toList.count q ≤ cin.toList.count q+[b.carry].count q := by
    cases cin <;> cases hb : b.literal <;> simp [FoldCell.next,hb]
  have tailNd : (control::(b.next cin).toList++rest.flatMap FoldCell.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    have hnext := nextCount q
    simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h hnext ⊢
    omega
  refine ⟨localNd,tailNd,?_⟩
  apply List.disjoint_left.mpr
  intro q hq hr
  have h := List.nodup_iff_count.mp hn q
  have hc := List.count_pos_iff.mpr hq
  have ht := List.count_pos_iff.mpr hr
  simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h hc
  omega


/-- The terminal Boolean carry computed from the original data word. -/
def foldBlockOverflow : List FoldCell → Bool → Bool → BasisState → Bool
  | [],_,input,_ => input
  | b::rest,enabled,input,s =>
      foldBlockOverflow rest enabled (carryBit (s b.data) (b.literal && enabled) input) s

private theorem data_cons (b : FoldCell) (rest : List FoldCell) (s : BasisState) :
    regValue ((b::rest).map FoldCell.data) s=(s b.data).toNat+2*regValue (rest.map FoldCell.data) s := by
  simp only [List.map_cons,regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite]

/-- Carry conservation for the exact sum word, without execution assumptions. -/
theorem foldBlockOverflow_value (cells : List FoldCell) (enabled input : Bool) (s : BasisState) :
    (regValue (cells.map FoldCell.data) s+foldBlockLiteral cells enabled+input.toNat)%2^cells.length+
      2^cells.length*(foldBlockOverflow cells enabled input s).toNat=
      regValue (cells.map FoldCell.data) s+foldBlockLiteral cells enabled+input.toNat := by
  induction cells generalizing input with
  | nil => simp [foldBlockOverflow,foldBlockLiteral,regValue,Nat.mod_one]
  | cons b rest ih =>
    have tailEq := ih (carryBit (s b.data) (b.literal && enabled) input)
    have bitEq := fullAdder_bit_value (s b.data) (b.literal && enabled) input
    have lowEq := sum_value_step (s b.data) (b.literal && enabled) input
      (regValue (rest.map FoldCell.data) s) (foldBlockLiteral rest enabled) rest.length
    simp only [data_cons,foldBlockLiteral,List.length_cons,foldBlockOverflow]
    rw [←lowEq,Nat.pow_succ]
    nlinarith

/-- The model's terminal carry detects overflow of the controlled word sum. -/
theorem foldBlockOverflow_iff (cells : List FoldCell) (enabled input : Bool) (s : BasisState) :
    foldBlockOverflow cells enabled input s=true ↔
      2^cells.length≤regValue (cells.map FoldCell.data) s+foldBlockLiteral cells enabled+input.toNat := by
  have h := foldBlockOverflow_value cells enabled input s
  have bound := Nat.mod_lt (regValue (cells.map FoldCell.data) s+foldBlockLiteral cells enabled+input.toNat)
    (show 0<2^cells.length by positivity)
  cases he : foldBlockOverflow cells enabled input s with
  | false =>
    simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    rw [h] at bound
    simp only [Bool.false_eq_true,false_iff]
    exact Nat.not_le.mpr bound
  | true =>
    simp only [he,Bool.toNat_true,Nat.mul_one] at h
    simp only [true_iff]
    rw [←h]
    exact Nat.le_add_left _ _

theorem foldBlockOverflow_congr (cells : List FoldCell) (enabled input : Bool) (s t : BasisState)
    (h : ∀ b∈cells,s b.data=t b.data) :
    foldBlockOverflow cells enabled input s=foldBlockOverflow cells enabled input t := by
  induction cells generalizing input with
  | nil => rfl
  | cons b rest ih =>
    simp only [foldBlockOverflow,h b (by simp)]
    exact ih _ (by intro c hc; exact h c (by simp [hc]))

private theorem top_mem (b : FoldCell) (rest : List FoldCell) (cin : Option Wire) (q : Wire)
    (h : foldBlockTop (b::rest) cin=some q) : q∈(b::rest).flatMap FoldCell.wires := by
  induction rest generalizing b cin with
  | nil =>
    cases hi : cin <;> cases hb : b.literal <;>
      simp [foldBlockTop,FoldCell.next,hi,hb] at h <;> simp [←h,FoldCell.wires]
  | cons c rest ih =>
    have mem := ih c (b.next cin) (by simpa only [foldBlockTop] using h)
    simp only [List.flatMap_cons,List.mem_append]
    exact Or.inr (by simpa only [List.flatMap_cons,List.mem_append] using mem)

/-- When retained, the final physical carry line holds exactly the terminal
carry of the original integer addition. Absence of that line denotes zero. -/
theorem foldBlockModel_top (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup) (s : BasisState) :
    ((foldBlockTop cells cin).map (foldBlockModel control cells cin true true s)).getD false=
      foldBlockOverflow cells (s control) ((cin.map s).getD false) s := by
  induction cells generalizing cin s with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨localNd,tailNd,apart⟩ := block_geometry control b rest cin hn
    let input := (cin.map s).getD false
    let outCarry := carryBit (s b.data) (b.literal && s control) input
    let prepared := writeBit (writeBit s b.carry outCarry) b.data (s b.data ^^ (b.literal && input))
    have nd : [control,b.data,b.carry].Nodup := (List.nodup_append.mp localNd).1
    have hcd : control≠b.data := by
      have h := (List.nodup_cons.mp nd).1
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.1
    have hct : control≠b.carry := by
      have h := (List.nodup_cons.mp nd).1
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
      exact h.2
    have hdt : b.data≠b.carry := by
      simpa using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    have ctrl : prepared control=s control := by simp [prepared,writeBit,hcd,hct]
    have next : ((b.next cin).map prepared).getD false=outCarry := by
      cases hi : cin <;> cases hb : b.literal <;>
        simp [FoldCell.next,hb,prepared,writeBit,Ne.symm hdt,outCarry,input,hi,carryBit]
    have away (q : Wire) (hq : q∈rest.flatMap FoldCell.wires) : q≠b.data ∧ q≠b.carry := by
      constructor
      · intro e; subst q
        exact List.disjoint_left.mp apart (show b.data∈[control,b.data,b.carry]++cin.toList by simp) hq
      · intro e; subst q
        exact List.disjoint_left.mp apart (show b.carry∈[control,b.data,b.carry]++cin.toList by simp) hq
    have same : foldBlockOverflow rest (s control) outCarry prepared=foldBlockOverflow rest (s control) outCarry s := by
      apply foldBlockOverflow_congr
      intro c hc
      obtain ⟨hd,ht⟩ := away c.data (List.mem_flatMap.mpr ⟨c,hc,by simp [FoldCell.wires]⟩)
      simp [prepared,writeBit,hd,ht]
    have tailEq := ih (b.next cin) tailNd prepared
    rw [ctrl,next,same] at tailEq
    cases rest with
    | nil =>
      cases hi : cin <;> cases hb : b.literal <;>
        simp [foldBlockTop,foldBlockModel,FoldCell.next,hb,foldBlockOverflow,writeBit,
          Ne.symm hdt,carryBit]
    | cons c cs =>
      have topAway : ∀ q,foldBlockTop (c::cs) (b.next cin)=some q → q≠b.data ∧ q≠b.carry := by
        intro q hq
        exact away q (top_mem c cs (b.next cin) q hq)
      rw [foldBlockTop]
      change ((foldBlockTop (c::cs) (b.next cin)).map _).getD false=_
      change ((foldBlockTop (c::cs) (b.next cin)).map _).getD false=
        foldBlockOverflow (c::cs) (s control) outCarry s
      rw [←tailEq]
      cases ht : foldBlockTop (c::cs) (b.next cin) with
      | none => rfl
      | some q =>
        obtain ⟨hd,hc⟩ := topAway q ht
        simp [foldBlockModel,prepared,outCarry,input,writeBit,hd,hc]

/-- Every nonretained carry is cleared, including an omitted final carry. -/
theorem foldBlockModel_carry_clean (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (sums keep : Bool) (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : BasisState) (cell : FoldCell) (hc : cell∈cells)
    (notKept : keep=false ∨ foldBlockTop cells cin≠some cell.carry) :
    foldBlockModel control cells cin sums keep s cell.carry=false := by
  induction cells generalizing cin s with
  | nil => simp at hc
  | cons b rest ih =>
    obtain ⟨localNd,tailNd,apart⟩ := block_geometry control b rest cin hn
    have nd : [control,b.data,b.carry].Nodup := (List.nodup_append.mp localNd).1
    have hdt : b.data≠b.carry := by
      simpa using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    rcases List.mem_cons.mp hc with rfl | hc
    · cases rest with
      | nil =>
        cases hi : cin <;> cases hb : cell.literal <;> cases keep <;>
          simp_all [foldBlockModel,foldBlockTop,FoldCell.next,writeBit,Ne.symm hdt,carryBit]
      | cons c cs => simp [foldBlockModel,writeBit,Ne.symm hdt]
    · have mem : cell.carry∈rest.flatMap FoldCell.wires := List.mem_flatMap.mpr ⟨cell,hc,by simp [FoldCell.wires]⟩
      have hd : cell.carry≠b.data := by
        intro e
        exact List.disjoint_left.mp apart (show b.data∈[control,b.data,b.carry]++cin.toList by simp) (e ▸ mem)
      have ht : cell.carry≠b.carry := by
        intro e
        exact List.disjoint_left.mp apart (show b.carry∈[control,b.data,b.carry]++cin.toList by simp) (e ▸ mem)
      simp only [foldBlockModel,writeBit,Function.update_of_ne hd,Function.update_of_ne ht]
      apply ih (b.next cin) tailNd _ hc
      simpa only [foldBlockTop] using notKept

theorem foldBlockLiteral_disabled (cells : List FoldCell) : foldBlockLiteral cells false=0 := by
  induction cells with
  | nil => rfl
  | cons b rest ih => simp [foldBlockLiteral,ih]

theorem foldBlockLiteral_bound (cells : List FoldCell) (enabled : Bool) :
    foldBlockLiteral cells enabled<2^cells.length := by
  induction cells with
  | nil => simp [foldBlockLiteral]
  | cons b rest ih =>
    have bitBound : (b.literal && enabled).toNat≤1 := by cases b.literal && enabled <;> decide
    simp only [foldBlockLiteral,List.length_cons,Nat.pow_succ]
    omega

/-- The actual retained keeper is recoverable by the controlled borrow
predicate on the actual written sum. This states the predicate to uncompute;
it does not yet execute the comparator/erasure gates. -/
theorem foldBlock_keeper_predicate (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup)
    (s : State) (m : List Bool) (clean : ∀ b∈cells,s.basis b.carry=false)
    (inactive : s.basis control=false → (cin.map s.basis).getD false=false) :
    let out := run (foldBlock control cells cin true true) m s
    ((foldBlockTop cells cin).map out.basis).getD false=
      (s.basis control && decide (regValue (cells.map FoldCell.data) out.basis<
        foldBlockLiteral cells true+((cin.map s.basis).getD false).toNat)) := by
  dsimp only
  rw [foldBlock_run control cells cin true true hn s m clean]
  change ((foldBlockTop cells cin).map (foldBlockModel control cells cin true true s.basis)).getD false=_
  rw [foldBlockModel_top control cells cin hn s.basis,
    foldBlockModel_value control cells cin true hn s.basis]
  have overflow : foldBlockOverflow cells (s.basis control) ((cin.map s.basis).getD false) s.basis=
      decide (2^cells.length≤regValue (cells.map FoldCell.data) s.basis+
        foldBlockLiteral cells (s.basis control)+((cin.map s.basis).getD false).toNat) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using foldBlockOverflow_iff cells (s.basis control) ((cin.map s.basis).getD false) s.basis
  rw [overflow]
  have lit : foldBlockLiteral cells (s.basis control)=
      (if s.basis control then foldBlockLiteral cells true else 0) := by
    cases s.basis control <;> simp [foldBlockLiteral_disabled]
  rw [lit]
  exact foldKeeper_controlled cells.length (regValue (cells.map FoldCell.data) s.basis)
    (foldBlockLiteral cells true) (s.basis control) ((cin.map s.basis).getD false)
    (by simpa only [List.length_map] using regValue_lt (cells.map FoldCell.data) s.basis)
    (foldBlockLiteral_bound cells true) inactive

end ECDSAAdd.Arithmetic.Paper935
