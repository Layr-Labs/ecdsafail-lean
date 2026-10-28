import ECDSAAdd.Arithmetic.PointConstantProof

namespace ECDSAAdd.Arithmetic

/-- 两个坐标复制模块的统一组合；有限位由前一段的具体门写入。 -/
theorem pointCoordinates_effect (r : PointReg) (control : Option Wire) (xs ys : List Wire)
    (hn : (PointAddLayout.pointWires r).Nodup)
    (nx : (xs++r.x).Nodup) (ny : (ys++r.y).Nodup)
    (dx : xs.Disjoint (PointAddLayout.pointWires r))
    (dy : ys.Disjoint (PointAddLayout.pointWires r))
    (hc : ∀ c∈control,c∉PointAddLayout.pointWires r)
    (hx : xs.length=r.x.length) (hy : ys.length=r.y.length)
    (F : Bool) (s u : State) (e0 : PointEffect r F 0 0 s u) (m : List Bool) :
    PointEffect r F (copyValue control s.basis (regValue xs s.basis))
      (copyValue control s.basis (regValue ys s.basis)) s
      (run (copyRegister control ys r.y) m (run (copyRegister control xs r.x) m u)) := by
  have cx : ∀ c∈control,c∉r.x := fun c hm hw => hc c hm (by simp [PointAddLayout.pointWires,hw])
  have cy : ∀ c∈control,c∉r.y := fun c hm hw => hc c hm (by simp [PointAddLayout.pointWires,hw])
  obtain ⟨px,ex,vx⟩ := copyRegister_correct control xs r.x hx nx cx u m
  have e1 := PointEffect.of_x r hn _ u _ px ex vx
  let v := run (copyRegister control xs r.x) m u
  obtain ⟨py,ey,vy⟩ := copyRegister_correct control ys r.y hy ny cy v m
  have e2 := PointEffect.of_y r hn _ v _ py ey vy
  have ux := e0.reg xs dx
  have vy' := (e0.trans e1).reg ys dy
  have hcv (a : List Wire) (v : State) (he : ∀ c∈control,v.basis c=s.basis c)
      (hr : regValue a v.basis=regValue a s.basis) :
      copyValue control v.basis (regValue a v.basis)=copyValue control s.basis (regValue a s.basis) := by
    rw [hr]
    cases control with
    | none => rfl
    | some c => simp only [copyValue,he c (by simp)]
  have hu := hcv xs u (fun c hm => e0.outside c (hc c hm)) ux
  have hv := hcv ys v (fun c hm => (e0.trans e1).outside c (hc c hm)) vy'
  have hh := e0.trans (e1.trans e2)
  simpa only [hu,hv,Bool.xor_false,Nat.zero_xor,Nat.xor_zero] using hh

theorem PointAddLayout.output_interfaces (L : PointAddLayout) (hn : L.wires.Nodup) :
    (L.generic::L.candidateX.take 256++L.candidateY.take 256++
      PointAddLayout.pointWires L.output).Nodup ∧
    (PointAddLayout.pointWires L.input++PointAddLayout.pointWires L.output).Nodup ∧
    (L.input.finite::L.double::PointAddLayout.pointWires L.output).Nodup := by
  constructor
  · apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    have hx := (List.take_sublist 256 L.candidateX).count_le w
    have hy := (List.take_sublist 256 L.candidateY).count_le w
    simp only [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,PointAddLayout.flags,
      List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at hh ⊢
    omega
  constructor
  · exact (List.nodup_append'.mp hn).1
  · apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [PointAddLayout.wires,PointAddLayout.pointWires,PointAddLayout.work,PointAddLayout.flags,
      List.count_append,List.count_cons,List.count_nil] at hh ⊢
    omega

theorem pointGenericOutput_correct (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) :
    PointEffect L.output (s.basis L.generic)
      (if s.basis L.generic then regValue (L.candidateX.take 256) s.basis else 0)
      (if s.basis L.generic then regValue (L.candidateY.take 256) s.basis else 0) s
      (run (pointGenericOutput L) m s) := by
  have ha := (L.output_interfaces hn).1
  have hr := List.nodup_append'.mp (List.nodup_cons.mp ha).2
  have nr := hr.2.1
  have cx : (L.candidateX.take 256++L.output.x).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp (List.nodup_cons.mp ha).2 w
    change ((L.candidateX.take 256++L.candidateY.take 256)++
      (L.output.finite::(L.output.x++L.output.y))).count w≤1 at hh
    simp only [List.count_append,List.count_cons] at hh ⊢
    omega
  have cy : (L.candidateY.take 256++L.output.y).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp (List.nodup_cons.mp ha).2 w
    change ((L.candidateX.take 256++L.candidateY.take 256)++
      (L.output.finite::(L.output.x++L.output.y))).count w≤1 at hh
    simp only [List.count_append,List.count_cons] at hh ⊢
    omega
  have dx := List.disjoint_left.mpr (fun w hw => List.disjoint_left.mp hr.2.2 (List.mem_append_left _ hw))
  have dy := List.disjoint_left.mpr (fun w hw => List.disjoint_left.mp hr.2.2 (List.mem_append_right _ hw))
  have hc : ∀ c∈some L.generic,c∉PointAddLayout.pointWires L.output := by
    intro c hm hw
    have he : c=L.generic := by simpa [eq_comm] using hm
    subst c
    exact (List.nodup_cons.mp ha).1 (List.mem_append_right _ hw)
  have hx : (L.candidateX.take 256).length=L.output.x.length := by
    have hh := h.words L.candidateX (by simp [PointAddLayout.words]); simp [hh,h.outputX]
  have hy : (L.candidateY.take 256).length=L.output.y.length := by
    have hh := h.words L.candidateY (by simp [PointAddLayout.words]); simp [hh,h.outputY]
  have ef := pointFinite_effect L.generic L.output true nr s m
  have ee : PointEffect L.output (s.basis L.generic) 0 0 s (run [.CX L.generic L.output.finite] m s) := by
    simpa [maskedConstant] using ef
  have hh := pointCoordinates_effect L.output (some L.generic) _ _ nr cx cy dx dy hc hx hy _ s _ ee m
  rw [pointGenericOutput,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(copyRegister_counts _ _ _ hx).2,measurementCount,Nat.zero_add,List.drop_zero]
  exact hh


theorem pointCopy_correct (a b : PointReg) (hn : (PointAddLayout.pointWires a++PointAddLayout.pointWires b).Nodup)
    (hx : a.x.length=b.x.length) (hy : a.y.length=b.y.length) (s : State) (m : List Bool) :
    PointEffect b (s.basis a.finite) (regValue a.x s.basis) (regValue a.y s.basis) s
      (run (pointCopy a b) m s) := by
  have ha := List.nodup_append'.mp hn
  have nx : (a.x++b.x).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [PointAddLayout.pointWires,List.count_append,List.count_cons] at hh ⊢
    omega
  have ny : (a.y++b.y).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [PointAddLayout.pointWires,List.count_append,List.count_cons] at hh ⊢
    omega
  have dx : a.x.Disjoint (PointAddLayout.pointWires b) := List.disjoint_left.mpr
    (fun w hw => List.disjoint_left.mp ha.2.2 (by simp [PointAddLayout.pointWires,hw]))
  have dy : a.y.Disjoint (PointAddLayout.pointWires b) := List.disjoint_left.mpr
    (fun w hw => List.disjoint_left.mp ha.2.2 (by simp [PointAddLayout.pointWires,hw]))
  have ef := pointFinite_effect a.finite b true ha.2.1 s m
  have ee : PointEffect b (s.basis a.finite) 0 0 s (run [.CX a.finite b.finite] m s) := by
    simpa [maskedConstant] using ef
  have hh := pointCoordinates_effect b none a.x a.y ha.2.1 nx ny dx dy (by simp) hx hy _ s _ ee m
  rw [pointCopy,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(copyRegister_counts _ _ _ hx).2,measurementCount,Nat.zero_add,List.drop_zero]
  exact hh

end ECDSAAdd.Arithmetic
