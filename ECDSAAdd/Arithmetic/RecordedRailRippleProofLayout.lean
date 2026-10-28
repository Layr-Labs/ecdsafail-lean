import ECDSAAdd.Arithmetic.RecordedRailRippleProofFrame

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailRipple

/-- Layout extraction is purely structural, with no circuit hypothesis. -/
theorem step_layout (a b c : Wire) (A B work : List Wire) (prev : Option Wire)
    (nd : (prev.toList++(a::A)++(b::B)++(c::work)).Nodup) :
    (prev.toList++[a,b,c]).Nodup ∧
    ([c]++A++B++work).Nodup ∧
    a∉B ∧ b∉B ∧ c∉B ∧
    (∀q∈A++B++work,q≠a ∧ q≠b ∧ q≠c) ∧
    (∀p∈prev.toList,p∉B) := by
  have rearranged : ((prev.toList++[a,b,c])++(A++B++work)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have split := List.nodup_append'.mp rearranged
  have away : ∀q∈A++B++work,∀r∈prev.toList++[a,b,c],q≠r := by
    intro q hq r hr e
    exact List.disjoint_left.mp split.2.2 hr (e ▸ hq)
  refine ⟨split.1,?_,?_,?_,?_,?_,?_⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  · intro h; exact away a (by simp [h]) a (by simp) rfl
  · intro h; exact away b (by simp [h]) b (by simp) rfl
  · intro h; exact away c (by simp [h]) c (by simp) rfl
  · intro q hq
    exact ⟨away q hq a (by simp),away q hq b (by simp),away q hq c (by simp)⟩
  · intro p hp h
    exact away p (by simp [h]) p (by simp [hp]) rfl

/-- Exact values at the three changed sites and unchanged incoming carry. -/
theorem computed_head (a b c : Wire) (prev : Option Wire) (bits : BasisState)
    (nd : (prev.toList++[a,b,c]).Nodup) :
    computedBits a b c prev bits a=(bits a ^^ incomingValue prev bits) ∧
    computedBits a b c prev bits b=(bits b ^^ incomingValue prev bits) ∧
    computedBits a b c prev bits c=carryFn (bits a) (bits b) (incomingValue prev bits) ∧
    incomingValue prev (computedBits a b c prev bits)=incomingValue prev bits := by
  cases prev with
  | none =>
    simp_all [List.nodup_cons,List.mem_cons,not_or,computedBits,
      incomingValue,writeBit,Function.update,eq_comm]
  | some p =>
    simp only [Option.toList_some,List.singleton_append,List.nodup_cons,
      List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
      not_false_eq_true,and_true] at nd
    obtain ⟨⟨hpa,hpb,hpc⟩,⟨hab,hac⟩,hbc⟩ := nd
    have hap := Ne.symm hpa
    have hbp := Ne.symm hpb
    have hcp := Ne.symm hpc
    have hba := Ne.symm hab
    have hca := Ne.symm hac
    have hcb := Ne.symm hbc
    simp [computedBits,incomingValue,writeBit,Function.update,
      hpa,hpb,hpc,hap,hbp,hcp,hab,hac,hbc,hba,hca,hcb]

/-- Unwind undresses the head and writes its ordinary low sum bit. -/
theorem unwound_head (a b c : Wire) (prev : Option Wire)
    (original bits : BasisState) (nd : (prev.toList++[a,b,c]).Nodup)
    (ha : bits a=(original a ^^ incomingValue prev original))
    (hb : bits b=(original b ^^ incomingValue prev original))
    (hp : incomingValue prev bits=incomingValue prev original) :
    let out := writeBit (writeBit (writeBit bits c false)
      a (bits a ^^ incomingValue prev bits))
      b (bits b ^^ (bits a ^^ incomingValue prev bits))
    out a=original a ∧
    out b=((original b ^^ original a) ^^ incomingValue prev original) ∧ out c=false := by
  cases prev with
  | none =>
    simp only [Option.toList_none,List.nil_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
    obtain ⟨⟨hab,hac⟩,hbc⟩ := nd
    have hba := Ne.symm hab
    have hca := Ne.symm hac
    have hcb := Ne.symm hbc
    cases hA : original a <;> cases hB : original b <;>
      simp_all [writeBit,Function.update,incomingValue]
  | some p =>
    simp only [Option.toList_some,List.singleton_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
    obtain ⟨⟨hpa,hpb,hpc⟩,⟨hab,hac⟩,hbc⟩ := nd
    have hap := Ne.symm hpa
    have hbp := Ne.symm hpb
    have hcp := Ne.symm hpc
    have hba := Ne.symm hab
    have hca := Ne.symm hac
    have hcb := Ne.symm hbc
    simp only [incomingValue] at ha hb hp ⊢
    cases hA : original a <;> cases hB : original b <;> cases hP : original p <;>
      simp_all [writeBit,Function.update]


end ECDSAAdd.Arithmetic.RecordedRailRipple
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.step_layout
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.computed_head
#print axioms ECDSAAdd.Arithmetic.RecordedRailRipple.unwound_head
