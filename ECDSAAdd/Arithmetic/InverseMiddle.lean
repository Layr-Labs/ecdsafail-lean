import ECDSAAdd.Arithmetic.InverseLoopState

namespace ECDSAAdd.Arithmetic
namespace InverseLoopLayout

theorem a_mem_phase (L : InverseLoopLayout) {w : Wire} (hw : w∈L.a) : w∈L.phaseWires := by
  simp [phaseWires,extra,hw]

theorem negative_nodup (L : InverseLoopLayout) (hnd : L.wires.Nodup) :
    (L.middle.r++L.temp++L.a++L.arithmetic.wires).Nodup := by
  have ht : (L.temp++L.a++L.arithmetic.wires).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp (L.phase_nodup hnd) w
    simp only [phaseWires,extra,List.count_append] at hh ⊢
    omega
  have hs := (List.nodup_append'.mp (L.middle_nodup hnd)).2.1
  have hd := (List.nodup_append'.mp (List.nodup_append'.mp hs).1).2.1
  have hr : L.middle.r.Nodup := L.middle.data.reg_nodup hd .r
  have hdis : L.middle.r.Disjoint (L.temp++L.a++L.arithmetic.wires) := by
    apply List.disjoint_left.mpr
    intro w hR hT
    apply List.disjoint_left.mp (L.rest_phase_disjoint hnd)
    · exact List.mem_append_right _ (L.middle.data.reg_mem .r hR)
    · simp only [List.mem_append] at hT
      simp only [phaseWires,extra,List.mem_append]
      tauto
  simpa only [List.append_assoc] using List.nodup_append'.mpr ⟨hr,ht,hdis⟩

end InverseLoopLayout

theorem InverseMiddle.update_a (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (z : KState) (cs : List (Bool×Bool)) (A Z : Nat) (s t : BasisState)
    (h : InverseMiddle L z cs A s) (he : ∀ w, w∉L.a → t w=s w) (hz : regValue L.a t=Z) :
    InverseMiddle L z cs Z t := by
  have hn := List.nodup_iff_count.mp (L.phase_nodup hnd)
  have hout (w : Wire) (hw : w∈L.temp++L.arithmetic.wires++[L.middle.compareCin]++L.middle.counter.wires) : w∉L.a := by
    intro hm
    have h1 := hn w
    have h2 := List.count_pos_iff.mpr hw
    have h3 := List.count_pos_iff.mpr hm
    simp only [InverseLoopLayout.phaseWires,InverseLoopLayout.extra,List.count_append] at h1 h2
    omega
  refine ⟨InverseRest.congr L z cs s t h.1 ?_,⟨hz,?_,?_⟩,HalvingCounter.congr _ _ _ _ h.2.2 ?_⟩
  · intro w hw
    exact he w (fun hh => List.disjoint_left.mp (L.rest_phase_disjoint hnd) hw (L.a_mem_phase hh))
  · apply (he _ (hout _ ?_)).trans h.2.1.2.1
    simp [KaliskiRoundLayout.counter,AdderLayout.wires]
  · exact (regValue_congr _ _ _ (fun w hw => he w (hout w (by simp only [List.mem_append] at hw ⊢; tauto)))).trans h.2.1.2.2
  · intro w hw
    apply he w (hout w ?_)
    simp only [InverseLoopLayout.halving,HalvingLayout.counter,AdderLayout.wires,List.mem_cons] at hw
    simp only [List.mem_append,KaliskiRoundLayout.counter,AdderLayout.wires,List.mem_cons]
    tauto

theorem inverseNegative_values (L : InverseLoopLayout) (hnd : L.wires.Nodup)
    (hw : L.first.data.width=L.arithmetic.width+1)
    (ha : L.a.length=L.arithmetic.width+1) (ht : L.temp.length=L.arithmetic.width+1)
    (q : Nat) (z : KState) (cs : List (Bool×Bool)) (A : Nat)
    (hq0 : 0<q) (hq : q<2^L.arithmetic.width) (hr : z.r<2*q) :
    Triple (InverseMiddle L z cs A)
      (negativeInit L.arithmetic q L.middle.r L.temp L.a)
      (InverseMiddle L z cs (A ^^^ (-(z.r : ZMod q)).val)) := by
  intro s m h
  have hlen : L.middle.r.length=L.arithmetic.width+1 := by
    change (L.middle.data.reg .r).length = _
    rw [L.middle.data.reg_length,InverseLoopLayout.middle,loopEnd_data,hw]
  have hR : regValue L.middle.r s.basis=z.r := h.1.1.1 .r
  have he := (InverseMiddle.iff L z cs A s.basis).mp h
  obtain ⟨hp,hkeep,hval⟩ := negativeInit_correct L.arithmetic q L.middle.r L.temp L.a
    (L.negative_nodup hnd) hlen ht ha hq0 hq s m (by simpa [hR] using hr) he.2.2.2.1 he.2.2.2.2
  exact ⟨hp,InverseMiddle.update_a L hnd z cs A _ s.basis _ h hkeep
    (by simpa [hR,he.2.2.1,negativeInit_value q z.r hq0] using hval)⟩

theorem InversePhase.congr (L : InverseLoopLayout) (K A : Nat)
    (s t : BasisState) (h : InversePhase L K A s) (he : ∀ w∈L.phaseWires,t w=s w) :
    InversePhase L K A t := by
  have keep (r : List Wire) (hr : r ⊆ L.phaseWires) : regValue r t=regValue r s :=
    regValue_congr _ _ _ (fun w hw => he w (hr hw))
  refine ⟨⟨(keep L.a (fun _ hw => L.a_mem_phase hw)).trans h.1.1,?_,?_⟩,
    HalvingCounter.congr _ _ _ _ h.2 ?_⟩
  · apply (he _ ?_).trans h.1.2.1
    simp [InverseLoopLayout.phaseWires,KaliskiRoundLayout.counter,AdderLayout.wires]
  · apply (keep (L.temp++L.arithmetic.wires) ?_).trans h.1.2.2
    intro w hw
    simp only [InverseLoopLayout.phaseWires,InverseLoopLayout.extra,List.mem_append] at hw ⊢
    tauto
  · intro w hw
    apply he w
    simp only [InverseLoopLayout.halving,HalvingLayout.counter,AdderLayout.wires,List.mem_cons] at hw
    simp only [InverseLoopLayout.phaseWires,List.mem_append,List.mem_cons,
      KaliskiRoundLayout.counter,AdderLayout.wires]
    tauto

end ECDSAAdd.Arithmetic
