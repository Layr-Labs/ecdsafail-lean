import ECDSAAdd.Arithmetic.Paper935.HornerCarryValue

namespace ECDSAAdd.Arithmetic.Paper935

private theorem top_mem (bs : List HornerCarryCell) (cin : Option Wire) (q : Wire)
    (h : q ∈ (hornerCarryTop bs cin).toList) : q ∈ cin.toList ++ hornerCarryPorts bs := by
  induction bs generalizing cin with
  | nil => simpa [hornerCarryTop,hornerCarryPorts] using h
  | cons b bs ih =>
    have hh := ih (some b.carry) h
    simp only [Option.toList_some,List.cons_append,List.nil_append,List.mem_cons] at hh
    rcases hh with rfl|hh
    · simp [hornerCarryPorts]
    · exact List.mem_append_right _ (List.mem_append_right _ hh)

private theorem carry_congr (bs : List HornerCarryCell) (cin : Bool) (s t : BasisState)
    (h : ∀q∈hornerCarryPorts bs,s q=t q) : hornerWordCarry bs cin s=hornerWordCarry bs cin t := by
  induction bs generalizing cin with
  | nil => rfl
  | cons b bs ih =>
    simp only [hornerWordCarry]
    rw [h b.target (by simp [hornerCarryPorts]),h b.addend (by simp [hornerCarryPorts])]
    exact ih _ (fun q hq => h q (List.mem_append_right _ hq))

/-- The physical carry produced by the forward sweep is the mathematical
carry of the original two words. -/
theorem hornerCarryAdvance_top (bs : List HornerCarryCell) (cin : Option Wire) (s : BasisState)
    (distinct : (cin.toList++hornerCarryPorts bs).Nodup) :
    ((hornerCarryTop bs cin).map (hornerCarryAdvance bs cin s)).getD false=
      hornerWordCarry bs ((cin.map s).getD false) s := by
  induction bs generalizing cin s with
  | nil => rfl
  | cons b bs ih =>
    have body : ([b.target,b.addend,b.carry]++hornerCarryPorts bs).Nodup :=
      (List.nodup_append.mp distinct).2.1
    have tail : ((some b.carry).toList++hornerCarryPorts bs).Nodup :=
      (List.nodup_cons.mp (List.nodup_cons.mp body).2).2
    have hat : b.target≠b.carry := fun h => (List.nodup_cons.mp body).1 (by simp [h])
    have het : b.addend≠b.carry := fun h => (List.nodup_cons.mp (List.nodup_cons.mp body).2).1 (by simp [h])
    have bit : b.advance cin s b.carry=carryBit (s b.target) (s b.addend) ((cin.map s).getD false) := by
      simp [HornerCarryCell.advance,writeBit,Ne.symm hat,Ne.symm het]
    change ((hornerCarryTop bs (some b.carry)).map (hornerCarryAdvance bs (some b.carry) (b.advance cin s))).getD false=_
    rw [ih _ _ tail]
    simp only [Option.map_some,Option.getD_some,bit,hornerWordCarry]
    apply carry_congr
    intro q hq
    have dis := (List.nodup_append.mp body).2.2
    exact hornerCarryAdvance_frame b cin s q
      (Ne.symm (dis _ (by simp) q hq)) (Ne.symm (dis _ (by simp) q hq)) (Ne.symm (dis _ (by simp) q hq))

/-- Keeping the highest carry preserves its physical wire through the
entire descending sweep, including writes of controlled sums. -/
theorem hornerCarryFinishSweep_top (ctrl : Wire) (sums : Bool) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : BasisState)
    (distinct : (cin.toList++hornerCarryPorts bs).Nodup) :
    ((hornerCarryTop bs cin).map (hornerCarryFinishSweep ctrl sums true bs cin s)).getD false=
      ((hornerCarryTop bs cin).map s).getD false := by
  induction bs generalizing cin with
  | nil => rfl
  | cons b bs ih =>
    have body : ([b.target,b.addend,b.carry]++hornerCarryPorts bs).Nodup :=
      (List.nodup_append.mp distinct).2.1
    have tail : ((some b.carry).toList++hornerCarryPorts bs).Nodup :=
      (List.nodup_cons.mp (List.nodup_cons.mp body).2).2
    cases bs with
    | nil =>
      have hat : b.target≠b.carry := fun h => (List.nodup_cons.mp body).1 (by simp [h])
      have het : b.addend≠b.carry := fun h => (List.nodup_cons.mp (List.nodup_cons.mp body).2).1 (by simp [h])
      simp [hornerCarryTop,hornerCarryFinishSweep,hornerCarryFinish,writeBit,Ne.symm hat,Ne.symm het]
    | cons d ds =>
      have frame : ∀q∈(hornerCarryTop (d::ds) (some b.carry)).toList,
          hornerCarryFinish ctrl b.target b.addend b.carry cin sums (true && (d::ds).isEmpty)
            (hornerCarryFinishSweep ctrl sums true (d::ds) (some b.carry) s) q=
          hornerCarryFinishSweep ctrl sums true (d::ds) (some b.carry) s q := by
        intro q hq
        have hp : q∈hornerCarryPorts (d::ds) := by
          have hh := top_mem ds (some d.carry) q hq
          simp only [Option.toList_some,List.cons_append,List.nil_append,List.mem_cons] at hh
          rcases hh with rfl|hh
          · simp [hornerCarryPorts]
          · exact List.mem_append_right _ hh
        have dis := (List.nodup_append.mp body).2.2
        exact hornerCarryFinish_frame _ _ _ _ _ _ _ _ q
          (Ne.symm (dis _ (by simp) q hp)) (Ne.symm (dis _ (by simp) q hp)) (Ne.symm (dis _ (by simp) q hp))
      change ((hornerCarryTop (d::ds) (some b.carry)).map _).getD false=
        ((hornerCarryTop (d::ds) (some b.carry)).map s).getD false
      rw [← ih (some b.carry) tail]
      cases ht : hornerCarryTop (d::ds) (some b.carry) with
      | none => rfl
      | some q => exact frame q (by simp [ht])

/-- Physical retained carry of the complete block. -/
theorem hornerCarryResult_top (ctrl : Wire) (sums : Bool) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : BasisState)
    (distinct : (ctrl::(cin.toList++hornerCarryPorts bs)).Nodup) :
    ((hornerCarryTop bs cin).map (hornerCarryResult ctrl sums true bs cin s)).getD false=
      hornerWordCarry bs ((cin.map s).getD false) s := by
  rw [hornerCarryResult,hornerCarryFinishSweep_top _ _ _ _ _ (List.nodup_cons.mp distinct).2]
  exact hornerCarryAdvance_top _ _ _ (List.nodup_cons.mp distinct).2

/-- The actual retained physical carry and actual low output together
encode the full integer sum when controlled addition is enabled. -/
theorem hornerCarryBlock_fullValue (ctrl : Wire) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : State) (m n : List Bool)
    (distinct : (ctrl::(cin.toList++hornerCarryPorts bs)).Nodup)
    (clean : ∀b∈bs,s.basis b.carry=false) (enabled : s.basis ctrl=true) :
    let out := (run (hornerCarryUnsweep ctrl true true bs cin) n
      (run (hornerCarrySweep bs cin) m s)).basis
    regValue (bs.map HornerCarryCell.target) out+
      2^bs.length*(((hornerCarryTop bs cin).map out).getD false).toNat=
      regValue (bs.map HornerCarryCell.target) s.basis+
      regValue (bs.map HornerCarryCell.addend) s.basis+((cin.map s.basis).getD false).toNat := by
  dsimp only
  rw [hornerCarryBlock_run ctrl true true bs cin s m n distinct clean]
  change regValue (bs.map HornerCarryCell.target) (hornerCarryResult ctrl true true bs cin s.basis)+
    2^bs.length*(((hornerCarryTop bs cin).map (hornerCarryResult ctrl true true bs cin s.basis)).getD false).toNat=_
  rw [hornerCarryResult_value _ _ _ _ _ _ distinct,hornerCarryResult_top _ _ _ _ _ distinct]
  simp only [enabled,Bool.and_self,ite_true]
  rw [← hornerWordSum_value]
  exact hornerWordSum_carry bs ((cin.map s.basis).getD false) s.basis

end ECDSAAdd.Arithmetic.Paper935
