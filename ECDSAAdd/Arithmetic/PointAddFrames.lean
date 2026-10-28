import ECDSAAdd.Arithmetic.PointAddState

namespace ECDSAAdd.Arithmetic

theorem PointAddLayout.reg_external_nodup (L : PointAddLayout) (hn : L.wires.Nodup)
    (f : CandidateField) : (L.reg f++L.flags++PointAddLayout.pointWires L.output).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  cases f <;>
    simp only [PointAddLayout.reg,PointAddLayout.extendedX,PointAddLayout.extendedY,
      PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.words,
      PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,
      List.count_append,List.count_cons,List.count_nil] at hh ⊢ <;> omega

theorem PointAddLayout.pool_external_nodup (L : PointAddLayout) (hn : L.wires.Nodup) :
    (L.pool++L.flags++PointAddLayout.pointWires L.output).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have hh := List.nodup_iff_count.mp hn w
  simp only [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,
    List.count_append,List.count_cons] at hh ⊢
  omega

theorem CandidateValues.pointFlags {L : PointAddLayout} (hn : L.wires.Nodup)
    {v : CandidateField → Nat} {G : Bool} {s : BasisState} (hv : CandidateValues L v G s)
    (EX EY G' D : Bool) : CandidateValues L v G' (pointFlagState L s EX EY G' D) := by
  constructor
  · intro f
    have hd := (List.nodup_append'.mp (List.nodup_append'.mp (L.reg_external_nodup hn f)).1).2.2
    exact (regValue_congr _ _ _ (fun w hw => pointFlagState_outside L _ _ _ _ _ _
      (List.disjoint_left.mp hd hw))).trans (hv.1 f)
  constructor
  · have hd := (List.nodup_append'.mp (List.nodup_append'.mp (L.pool_external_nodup hn)).1).2.2
    exact (regValue_congr _ _ _ (fun w hw => pointFlagState_outside L _ _ _ _ _ _
      (List.disjoint_left.mp hd hw))).trans hv.2.1
  · exact (pointFlagState_flags L (L.flags_disjoint hn).1 s EX EY G' D).2.2.1

theorem CandidateValues.pointOutput {L : PointAddLayout} (hn : L.wires.Nodup)
    {v : CandidateField → Nat} {G F : Bool} {X Y : Nat} {s t : State}
    (hv : CandidateValues L v G s.basis) (he : PointEffect L.output F X Y s t) :
    CandidateValues L v G t.basis := by
  constructor
  · intro f
    have hd := (List.nodup_append'.mp (L.reg_external_nodup hn f)).2.2
    exact (he.reg _ (List.disjoint_left.mpr (fun w hw => List.disjoint_left.mp hd
      (List.mem_append_left _ hw)))).trans (hv.1 f)
  constructor
  · have hd := (List.nodup_append'.mp (L.pool_external_nodup hn)).2.2
    exact (he.reg _ (List.disjoint_left.mpr (fun w hw => List.disjoint_left.mp hd
      (List.mem_append_left _ hw)))).trans hv.2.1
  · have hd := (List.nodup_append'.mp (L.pool_external_nodup hn)).2.2
    exact (he.outside _ (List.disjoint_left.mp hd (List.mem_append_right _ (by simp [PointAddLayout.flags])))).trans hv.2.2

theorem PointBoundary.pointOutput {L : PointAddLayout} (hn : L.wires.Nodup)
    {F EX EY D OF A : Bool} {OX OY X Y : Nat} {s t : State}
    (hb : PointBoundary L F EX EY D OF OX OY s.basis) (he : PointEffect L.output A X Y s t) :
    PointBoundary L F EX EY D (OF^^A) (OX^^^X) (OY^^^Y) t.basis := by
  have hfd := (L.output_interfaces hn).2.2
  have hf : L.input.finite∉PointAddLayout.pointWires L.output :=
    fun hm => (List.nodup_cons.mp hfd).1 (List.mem_cons_of_mem _ hm)
  have hd : L.double∉PointAddLayout.pointWires L.output := (List.nodup_cons.mp (List.nodup_cons.mp hfd).2).1
  have hh := (List.nodup_append'.mp (L.pool_external_nodup hn)).2.2
  have hx : L.equalX∉PointAddLayout.pointWires L.output :=
    List.disjoint_left.mp hh (List.mem_append_right _ (by simp [PointAddLayout.flags]))
  have hy : L.equalNegY∉PointAddLayout.pointWires L.output :=
    List.disjoint_left.mp hh (List.mem_append_right _ (by simp [PointAddLayout.flags]))
  exact ⟨(he.outside _ hf).trans hb.finite,(he.outside _ hx).trans hb.equalX,
    (he.outside _ hy).trans hb.equalNegY,(he.outside _ hd).trans hb.double,
    by rw [he.finite,hb.outFinite],by rw [he.x,hb.outX],by rw [he.y,hb.outY]⟩

end ECDSAAdd.Arithmetic
