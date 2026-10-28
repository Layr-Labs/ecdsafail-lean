import ECDSAAdd.Arithmetic.Paper935.FoldCarryResources

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic

/-- The backward sweep only needs the actual local dressed-data/carry
relations. Other data bits may already have been updated by later cells. -/
theorem foldCarryBackward_run (bit : Bool) (control data target : Wire) (cin : Option Wire)
    (sums keep : Bool) (hn : ([control,data,target]++cin.toList).Nodup)
    (s : State) (m : List Bool) (oldData : Bool)
    (dressed : s.basis data=(oldData ^^ (bit && (cin.map s.basis).getD false)))
    (carry : s.basis target=carryBit oldData (bit && s.basis control) ((cin.map s.basis).getD false)) :
    run (foldCarryBackward bit control data target cin sums keep) m s=
      ⟨s.phase,writeBit (writeBit s.basis target (if keep then s.basis target else false)) data
        (if sums then sumBit oldData (bit && s.basis control) ((cin.map s.basis).getD false) else oldData)⟩ := by
  have nd : [control,data,target].Nodup := (List.nodup_append.mp hn).1
  have hcd : control≠data := by
    intro e
    exact (List.nodup_cons.mp nd).1 (by simp [e])
  have hct : control≠target := by
    have h := (List.nodup_cons.mp nd).1
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.2
  have hdt : data≠target := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
  let origin : State := ⟨s.phase,writeBit (writeBit s.basis target false) data oldData⟩
  have ctrl : origin.basis control=s.basis control := by simp [origin,writeBit,hcd,hct]
  have inp : (cin.map origin.basis).getD false=(cin.map s.basis).getD false := by
    cases hc : cin with
    | none => rfl
    | some d =>
      have apart := (List.nodup_append'.mp hn).2.2
      have dd : d≠data := by
        intro e; subst d
        exact List.disjoint_left.mp apart (show data∈[control,data,target] by simp) (by simp [hc])
      have dt : d≠target := by
        intro e; subst d
        exact List.disjoint_left.mp apart (show target∈[control,data,target] by simp) (by simp [hc])
      simp [origin,writeBit,dd,dt]
  have original : origin.basis data=oldData := by simp [origin,writeBit]
  have clean : origin.basis target=false := by simp [origin,writeBit,Ne.symm hdt]
  have forward : run (foldCarryForward bit control data target cin) m origin=s := by
    rw [foldCarryForward_run bit control data target cin hn origin m clean,ctrl,inp,original,←carry,←dressed]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hd : q=data <;> by_cases ht : q=target <;>
      simp_all [origin,writeBit,Function.update]
  have result := foldCarryCell_run bit control data target cin sums keep hn origin m clean
  rw [run_append,run_take,forward,(foldCarryForward_counts bit control data target cin).2,List.drop_zero] at result
  rw [ctrl,inp,original,←carry] at result
  rw [result]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hd : q=data <;> by_cases ht : q=target <;>
    simp_all [origin,writeBit,Function.update]

end ECDSAAdd.Arithmetic.Paper935
