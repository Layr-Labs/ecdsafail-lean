import ECDSAAdd.Arithmetic.Paper935.HornerCarryValid
import ECDSAAdd.Arithmetic.Paper935.HornerCarryMath

namespace ECDSAAdd.Arithmetic.Paper935

/-- Pure full-block state already identified with actual sweep execution. -/
def hornerCarryResult (ctrl : Wire) (sums keep : Bool) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : BasisState) : BasisState :=
  hornerCarryFinishSweep ctrl sums keep bs cin (hornerCarryAdvance bs cin s)

private theorem word_cons (q : Wire) (r : List Wire) (s : BasisState) :
    regValue (q::r) s=(s q).toNat+2*regValue r s := by
  cases h : s q <;> simp [regValue,h]

/-- The actual pure block state writes the controlled low integer sum;
retaining the highest carry does not alter this low-word formula. -/
theorem hornerCarryResult_value (ctrl : Wire) (sums keep : Bool) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : BasisState)
    (distinct : (ctrl::(cin.toList++hornerCarryPorts bs)).Nodup) :
    regValue (bs.map HornerCarryCell.target) (hornerCarryResult ctrl sums keep bs cin s)=
      if sums && s ctrl then
        (regValue (bs.map HornerCarryCell.target) s+regValue (bs.map HornerCarryCell.addend) s+
          ((cin.map s).getD false).toNat)%2^bs.length
      else regValue (bs.map HornerCarryCell.target) s := by
  induction bs generalizing cin s with
  | nil => simp [hornerCarryResult,hornerCarryAdvance,hornerCarryFinishSweep,regValue,Nat.mod_one]
  | cons b bs ih =>
    have nd : (ctrl::(cin.toList++([b.target,b.addend,b.carry]++hornerCarryPorts bs))).Nodup := distinct
    have body := (List.nodup_append.mp (List.nodup_cons.mp nd).2).2.1
    have next : (ctrl::((some b.carry).toList++hornerCarryPorts bs)).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · intro h
        apply (List.nodup_cons.mp nd).1
        apply List.mem_append_right
        change ctrl∈b.carry::hornerCarryPorts bs at h
        rcases List.mem_cons.mp h with h|h
        · simp [h]
        · exact List.mem_append_right _ h
      · exact (List.nodup_cons.mp (List.nodup_cons.mp body).2).2
    have splitND : ((ctrl::(cin.toList++[b.target,b.addend,b.carry]))++hornerCarryPorts bs).Nodup := by
      simpa only [List.cons_append,List.append_assoc] using nd
    let t := b.advance cin s
    let u := hornerCarryResult ctrl sums keep bs (some b.carry) t
    have unchanged (q : Wire) (hq : q∈ctrl::(cin.toList++[b.target,b.addend,b.carry])) : u q=t q := by
      have away : q∉hornerCarryPorts bs := fun h => (List.nodup_append.mp splitND).2.2 q hq q h rfl
      exact (hornerCarryFinishSweep_frame ctrl sums keep bs (some b.carry) _ q away).trans
        (hornerCarryAdvance_block_frame bs (some b.carry) t q away)
    have tailAway (q : Wire) (hq : q∈hornerCarryPorts bs) :
        q≠b.target ∧ q≠b.addend ∧ q≠b.carry := by
      have a := (List.nodup_append.mp body).2.2
      exact ⟨Ne.symm (a _ (by simp) q hq),Ne.symm (a _ (by simp) q hq),Ne.symm (a _ (by simp) q hq)⟩
    have tailSource : regValue (bs.map HornerCarryCell.target) t=regValue (bs.map HornerCarryCell.target) s ∧
        regValue (bs.map HornerCarryCell.addend) t=regValue (bs.map HornerCarryCell.addend) s := by
      constructor
      · apply regValue_congr
        intro q hq
        obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hq
        have h := tailAway d.target (List.mem_flatMap.mpr ⟨d,hd,by simp⟩)
        exact hornerCarryAdvance_frame b cin s _ h.1 h.2.1 h.2.2
      · apply regValue_congr
        intro q hq
        obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hq
        have h := tailAway d.addend (List.mem_flatMap.mpr ⟨d,hd,by simp⟩)
        exact hornerCarryAdvance_frame b cin s _ h.1 h.2.1 h.2.2
    have localND := (hornerCarryGeometry_of_nodup ctrl (b::bs) cin distinct).1
    have ctrlSame : t ctrl=s ctrl := by
      have away := (List.nodup_cons.mp localND).1
      exact hornerCarryAdvance_frame b cin s ctrl
        (fun h => away (by simp [h])) (fun h => away (by simp [h])) (fun h => away (by simp [h]))
    have cinSame : (cin.map u).getD false=(cin.map t).getD false := by
      cases cin with
      | none => rfl
      | some d => exact unchanged d (by simp)
    have bits :
        hornerCarryResult ctrl sums keep (b::bs) cin s b.target=
          (if sums && s ctrl then sumBit (s b.target) (s b.addend) ((cin.map s).getD false) else s b.target) ∧
        t b.carry=carryBit (s b.target) (s b.addend) ((cin.map s).getD false) := by
      change hornerCarryFinish ctrl b.target b.addend b.carry cin sums (keep && bs.isEmpty) u b.target=_ ∧ _
      cases cin with
      | none =>
        simp only [Option.toList_none,List.append_nil,List.nodup_cons,List.mem_cons,List.not_mem_nil,
          List.nodup_nil,not_or,not_false_eq_true,and_true] at localND
        obtain ⟨⟨hca,hce,hct⟩,⟨hae,hat⟩,het⟩ := localND
        simp [hornerCarryFinish,writeBit,hae,unchanged b.target (by simp),unchanged b.addend (by simp),
          unchanged ctrl (by simp),hca,hce,hct,t,HornerCarryCell.advance,Ne.symm hat,Ne.symm het]
      | some d =>
        simp only [Option.toList_some,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,List.not_mem_nil,
          List.nodup_nil,not_or,not_false_eq_true,and_true] at localND
        obtain ⟨⟨hca,hce,hct,hcd⟩,⟨hae,hat,had⟩,⟨het,hed⟩,htd⟩ := localND
        simp [hornerCarryFinish,writeBit,hae,unchanged b.target (by simp),unchanged b.addend (by simp),
          unchanged ctrl (by simp),unchanged d (by simp),hca,hce,hct,t,HornerCarryCell.advance,
          Ne.symm hat,Ne.symm had,Ne.symm het,Ne.symm hed,Ne.symm htd]
    have tailResult : regValue (bs.map HornerCarryCell.target)
        (hornerCarryResult ctrl sums keep (b::bs) cin s)=regValue (bs.map HornerCarryCell.target) u := by
      apply regValue_congr
      intro q hq
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hq
      have h := tailAway d.target (List.mem_flatMap.mpr ⟨d,hd,by simp⟩)
      exact hornerCarryFinish_frame ctrl b.target b.addend b.carry cin sums (keep && bs.isEmpty) u d.target h.1 h.2.1 h.2.2
    have high := ih (some b.carry) t next
    rw [tailSource.1,tailSource.2,ctrlSame] at high
    simp only [Option.map_some,Option.getD_some] at high
    rw [bits.2] at high
    simp only [List.map_cons,word_cons,List.length_cons]
    rw [bits.1,tailResult,high]
    cases h : sums && s ctrl
    · simp
    · simp only [if_true]
      exact sum_value_step (s b.target) (s b.addend) ((cin.map s).getD false)
        (regValue (bs.map HornerCarryCell.target) s) (regValue (bs.map HornerCarryCell.addend) s) bs.length

/-- Integer specification of the actual two sweeps. This is the full-width
controlled addition stage required before the lazy carry correction. -/
theorem hornerCarryBlock_value (ctrl : Wire) (sums keep : Bool) (bs : List HornerCarryCell)
    (cin : Option Wire) (s : State) (m n : List Bool)
    (distinct : (ctrl::(cin.toList++hornerCarryPorts bs)).Nodup)
    (clean : ∀b∈bs,s.basis b.carry=false) :
    regValue (bs.map HornerCarryCell.target)
      (run (hornerCarryUnsweep ctrl sums keep bs cin) n (run (hornerCarrySweep bs cin) m s)).basis=
      if sums && s.basis ctrl then
        (regValue (bs.map HornerCarryCell.target) s.basis+
          regValue (bs.map HornerCarryCell.addend) s.basis+((cin.map s.basis).getD false).toNat)%2^bs.length
      else regValue (bs.map HornerCarryCell.target) s.basis := by
  rw [hornerCarryBlock_run ctrl sums keep bs cin s m n distinct clean]
  exact hornerCarryResult_value ctrl sums keep bs cin s.basis distinct

end ECDSAAdd.Arithmetic.Paper935
