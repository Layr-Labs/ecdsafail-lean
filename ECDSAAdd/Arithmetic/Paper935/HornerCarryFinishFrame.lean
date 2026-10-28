import ECDSAAdd.Arithmetic.Paper935.HornerCarryFinishSweep
import ECDSAAdd.Arithmetic.Paper935.HornerCarryGeometry

namespace ECDSAAdd.Arithmetic.Paper935

theorem hornerCarryFinish_frame (ctrl a e t : Wire) (cin : Option Wire) (sums keep : Bool)
    (s : BasisState) (q : Wire) (ha : q≠a) (he : q≠e) (ht : q≠t) :
    hornerCarryFinish ctrl a e t cin sums keep s q=s q := by
  simp [hornerCarryFinish,writeBit,ha,he,ht]

/-- Both modes of the descending pure recurrence preserve every wire
outside the explicit block ports, including the incoming carry. -/
theorem hornerCarryFinishSweep_frame (ctrl : Wire) (sums keep : Bool)
    (bs : List HornerCarryCell) (cin : Option Wire) (s : BasisState)
    (q : Wire) (away : q∉hornerCarryPorts bs) :
    hornerCarryFinishSweep ctrl sums keep bs cin s q=s q := by
  induction bs generalizing cin with
  | nil => rfl
  | cons b bs ih =>
    have h : q≠b.target ∧ q≠b.addend ∧ q≠b.carry ∧ q∉hornerCarryPorts bs := by
      simpa [hornerCarryPorts,List.mem_flatMap] using away
    rw [hornerCarryFinishSweep,hornerCarryFinish_frame _ _ _ _ _ _ _ _ _ h.1 h.2.1 h.2.2.1]
    exact ih _ h.2.2.2

/-- Forward dressing establishes precisely the carry relation consumed
by a later measured backward cell. This is an algebraic invariant. -/
theorem hornerCarryAdvance_valid (b : HornerCarryCell) (cin : Option Wire) (s : BasisState)
    (distinct : ([b.target,b.addend,b.carry]++cin.toList).Nodup) :
    let u := b.advance cin s
    u b.carry=carryBit (u b.target ^^ (cin.map u).getD false)
      (u b.addend ^^ (cin.map u).getD false) ((cin.map u).getD false) := by
  cases cin with
  | none =>
    simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
    obtain ⟨⟨hae,hat⟩,het⟩ := distinct
    simp [HornerCarryCell.advance,writeBit,hae,Ne.symm hat,Ne.symm het]
  | some d =>
    simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      List.nodup_nil,not_or,not_false_eq_true,and_true] at distinct
    obtain ⟨⟨hae,hat,had⟩,⟨het,hed⟩,htd⟩ := distinct
    simp [HornerCarryCell.advance,writeBit,hae,
      Ne.symm hat,Ne.symm had,Ne.symm het,Ne.symm hed,Ne.symm htd]

end ECDSAAdd.Arithmetic.Paper935
