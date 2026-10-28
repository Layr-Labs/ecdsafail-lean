import ECDSAAdd.Arithmetic.PointSelectors

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem ControlledPointLayout.output_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup) :
    (PointAddLayout.pointWires L.core.output).Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp (L.core_nodup hn)).1).2.1

theorem ControlledPointLayout.extra_not_output (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (w : Wire) (hw : w∈L.extras) : w∉PointAddLayout.pointWires L.core.output := by
  intro ho
  exact L.extra_not_core hn w hw (by simp [PointAddLayout.wires,ho])

theorem selectedPointOutput_counts (L : ControlledPointLayout) (h : L.Widths) (C : Point) :
    toffoliCount (selectedPointOutput L C)=512 ∧ measurementCount (selectedPointOutput L C)=0 := by
  simp [selectedPointOutput,toffoliCount_append,measurementCount_append,
    (pointGenericOutput_counts L.selected (L.selected_widths h)).1,
    (pointGenericOutput_counts L.selected (L.selected_widths h)).2,maskedPointConstant_counts]

theorem selectedPointOutput_correct (L : ControlledPointLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.core.output
      (s.basis L.genericSelect ^^ (s.basis L.doubleSelect && pointFinite (C+C)) ^^ (s.basis L.infinitySelect && pointFinite C))
      ((if s.basis L.genericSelect then regValue (L.core.candidateX.take 256) s.basis else 0) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0) ^^^ (if s.basis L.infinitySelect then pointX C else 0))
      ((if s.basis L.genericSelect then regValue (L.core.candidateY.take 256) s.basis else 0) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0) ^^^ (if s.basis L.infinitySelect then pointY C else 0)) s
      (run (selectedPointOutput L C) m s) := by
  have hd := L.extra_not_output hn L.doubleSelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  have ho := L.extra_not_output hn L.infinitySelect (by simp [ControlledPointLayout.extras,ControlledPointLayout.selectors])
  let u := run (pointGenericOutput L.selected) m s
  have e0 := pointGenericOutput_correct L.selected (L.selected_widths h) (L.selected_nodup hn) s m
  have ud : u.basis L.doubleSelect=s.basis L.doubleSelect := e0.outside _ hd
  let v := run (maskedPointConstant L.doubleSelect L.core.output (C+C)) m u
  have e1 := maskedPointConstant_correct L.doubleSelect L.core.output (C+C) (L.output_nodup hn) hd h.outputX h.outputY u m
  have vo : v.basis L.infinitySelect=s.basis L.infinitySelect := (e0.trans e1).outside _ ho
  have e2 := maskedPointConstant_correct L.infinitySelect L.core.output C (L.output_nodup hn) ho h.outputX h.outputY v m
  have hh := (e0.trans e1).trans e2
  rw [selectedPointOutput,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(pointGenericOutput_counts L.selected (L.selected_widths h)).2,
    (maskedPointConstant_counts L.doubleSelect L.core.output (C+C)).2,Nat.zero_add,List.drop_zero]
  simpa only [ControlledPointLayout.selected,ud,vo] using hh

end ECDSAAdd.Arithmetic
