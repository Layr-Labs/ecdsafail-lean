import ECDSAAdd.Arithmetic.SelectedPointOutput

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem ControlledPointLayout.core_not_selectors (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (w : Wire) (hw : w∈L.core.wires) : w∉L.selectors := by
  intro hs
  exact L.extra_not_core hn w (List.mem_cons_of_mem _ hs) hw

theorem controlledPointOutput_correct (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool)
    (hz : s.basis L.genericSelect=false ∧ s.basis L.doubleSelect=false ∧ s.basis L.infinitySelect=false) :
    PointEffect L.core.output
      (s.basis L.control && (s.basis L.core.generic ^^ (s.basis L.core.double && pointFinite (C+C)) ^^ (!s.basis L.core.input.finite && pointFinite C)))
      (if s.basis L.control then
        (if s.basis L.core.generic then regValue (L.core.candidateX.take 256) s.basis else 0) ^^^
        (if s.basis L.core.double then pointX (C+C) else 0) ^^^ (if !s.basis L.core.input.finite then pointX C else 0) else 0)
      (if s.basis L.control then
        (if s.basis L.core.generic then regValue (L.core.candidateY.take 256) s.basis else 0) ^^^
        (if s.basis L.core.double then pointY (C+C) else 0) ^^^ (if !s.basis L.core.input.finite then pointY C else 0) else 0) s
      (run (controlledPointOutput L C) m s) := by
  let G := s.basis L.control && s.basis L.core.generic
  let D := s.basis L.control && s.basis L.core.double
  let O := s.basis L.control && !s.basis L.core.input.finite
  let u : State := ⟨s.phase,selectorState L s.basis G D O⟩
  have hu : run (pointSelectors L) m s=u := by
    rw [pointSelectors_correct L hn]; simp only [hz.1,hz.2.1,hz.2.2,Bool.false_xor]; rfl
  have uc (w : Wire) (hw : w∈L.core.wires) : u.basis w=s.basis w :=
    selectorState_outside L _ _ _ _ w (L.core_not_selectors hn w hw)
  have us := selectorState_values L hn s.basis G D O
  have ub : u.basis L.control=s.basis L.control := by
    apply selectorState_outside
    exact (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
  let v := run (selectedPointOutput L C) m u
  have he := selectedPointOutput_correct L h hn C u m
  have vs (w : Wire) (hw : w∈L.extras) : v.basis w=u.basis w :=
    he.outside w (L.extra_not_output hn w hw)
  have vd := vs L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have vg := vs L.genericSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have vo := vs L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have vb := vs L.control (by simp [ControlledPointLayout.extras])
  have hd := (L.core.output_interfaces (L.core_nodup hn)).2.2
  have vf : v.basis L.core.input.finite=s.basis L.core.input.finite := by
    rw [he.outside _ (fun hw => (List.nodup_cons.mp hd).1 (List.mem_cons_of_mem _ hw))]
    exact uc _ (by simp [PointAddLayout.wires,PointAddLayout.pointWires])
  have vD : v.basis L.core.double=s.basis L.core.double := by
    rw [he.outside _ (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1]
    exact uc _ (by simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.flags])
  have vG : v.basis L.core.generic=s.basis L.core.generic := by
    have hh := (List.nodup_append'.mp (L.core.pool_external_nodup (L.core_nodup hn))).2.2
    rw [he.outside _ (List.disjoint_left.mp hh (List.mem_append_right _ (by simp [PointAddLayout.flags])))]
    exact uc _ (by simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.flags])
  have ht : run (pointSelectors L) m v=⟨s.phase,selectorState L v.basis false false false⟩ := by
    rw [pointSelectors_correct L hn]
    have hp : v.phase=s.phase := he.phase
    simp only [hp,vg,vd,vo,vb,vG,vD,vf,ub,show u.basis L.genericSelect=G from us.1,
      show u.basis L.doubleSelect=D from us.2.1,show u.basis L.infinitySelect=O from us.2.2,G,D,O,Bool.xor_self]
  have eo (w : Wire) (hw : w∈PointAddLayout.pointWires L.core.output) : w∉L.selectors :=
    L.core_not_selectors hn w (by simp [PointAddLayout.wires,hw])
  have ux : regValue (L.core.candidateX.take 256) u.basis=regValue (L.core.candidateX.take 256) s.basis := by
    apply regValue_congr; intro w hw
    exact uc w (by have hm := List.mem_of_mem_take hw; simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,hm])
  have uy : regValue (L.core.candidateY.take 256) u.basis=regValue (L.core.candidateY.take 256) s.basis := by
    apply regValue_congr; intro w hw
    exact uc w (by have hm := List.mem_of_mem_take hw; simp [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,hm])
  have huf : u.basis L.core.output.finite=s.basis L.core.output.finite := uc _ (by simp [PointAddLayout.wires,PointAddLayout.pointWires])
  have hur (r : List Wire) (hr : ∀ w∈r,w∈PointAddLayout.pointWires L.core.output) :
      regValue r u.basis=regValue r s.basis := regValue_congr _ _ _ (fun w hw => uc w (by simp [PointAddLayout.wires,hr w hw]))
  have htr (r : List Wire) (hr : ∀ w∈r,w∈PointAddLayout.pointWires L.core.output) :
      regValue r (selectorState L v.basis false false false)=regValue r v.basis :=
    regValue_congr _ _ _ (fun w hw => selectorState_outside L _ _ _ _ w (eo w (hr w hw)))
  rw [controlledPointOutput,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(pointSelectors_counts L).2,(selectedPointOutput_counts L h C).2,
    Nat.zero_add,List.drop_zero,hu]
  change PointEffect _ _ _ _ s (run (pointSelectors L) m v)
  rw [ht]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · intro w hw
    by_cases hs : w∈L.selectors
    · simp only [ControlledPointLayout.selectors,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl|rfl|rfl
      · exact (selectorState_values L hn v.basis false false false).1.trans hz.1.symm
      · exact (selectorState_values L hn v.basis false false false).2.1.trans hz.2.1.symm
      · exact (selectorState_values L hn v.basis false false false).2.2.trans hz.2.2.symm
    · dsimp only
      rw [selectorState_outside L _ _ _ _ w hs,he.outside w hw]
      exact selectorState_outside L _ _ _ _ w hs
  · dsimp only
    rw [selectorState_outside L v.basis false false false L.core.output.finite (eo L.core.output.finite (by simp [PointAddLayout.pointWires])),he.finite,
      huf,show u.basis L.genericSelect=G from us.1,show u.basis L.doubleSelect=D from us.2.1,
      show u.basis L.infinitySelect=O from us.2.2]
    cases hb : s.basis L.control <;> simp [G,D,O,hb]
  · rw [htr _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),he.x,
      hur _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),ux,
      show u.basis L.genericSelect=G from us.1,show u.basis L.doubleSelect=D from us.2.1,
      show u.basis L.infinitySelect=O from us.2.2]
    cases hb : s.basis L.control <;> simp [G,D,O,hb]
  · rw [htr _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),he.y,
      hur _ (by intro w hw; simp [PointAddLayout.pointWires,hw]),uy,
      show u.basis L.genericSelect=G from us.1,show u.basis L.doubleSelect=D from us.2.1,
      show u.basis L.infinitySelect=O from us.2.2]
    cases hb : s.basis L.control <;> simp [G,D,O,hb]

end ECDSAAdd.Arithmetic
