import ECDSAAdd.Baselines.Layout
import ECDSAAdd.Submissions.Skywalk
import ECDSAAdd.Submissions.ValueWalk

namespace ECDSAAdd.Baselines
open Arithmetic Secp256k1

theorem point_wire_lt (w : Wire) (h : w ∈ PointAddLayout.pointWires Challenge.point) :
    w < 514 := by
  simp only [PointAddLayout.pointWires, Challenge.point, List.mem_append,
    List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with (rfl | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · decide
  · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hi 2) (by decide)
  · exact Nat.add_lt_add_right hi 258

theorem dialog_support_partition (L : ControlledPointLayout) (w : Wire)
    (hw : w ∈ L.dialogUsedWires) :
    w = L.control ∨ w ∈ PointAddLayout.pointWires L.point ∨ w ∈ L.work := by
  simp only [ControlledPointLayout.dialogUsedWires, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ((hp | hc) | hf) | hb
  · exact Or.inr (Or.inl hp)
  · exact Or.inl hc
  · right; right
    simp only [ControlledPointLayout.inPlaceFlags, List.mem_cons, List.not_mem_nil] at hf
    simp only [ControlledPointLayout.work, ControlledPointLayout.outWork,
      ControlledPointLayout.selectors, PointAddLayout.work, PointAddLayout.flags,
      List.mem_append, List.mem_cons, List.not_mem_nil]
    tauto
  · right; right
    have hb' : w ∈ L.core.pool := List.mem_of_mem_take hb
    simp only [ControlledPointLayout.work, ControlledPointLayout.outWork,
      PointAddLayout.work, List.mem_append]
    tauto

/-- Upgrade the old named-work Triple using actual support, never an entrant
claim that unlisted wires are irrelevant. -/
theorem fixed_correct (p : Program) (b : Bool) (R S : Point)
    (spec : {{ layout.control=b,layout.point=R,layout.work=0 }} p
      {{ layout.control=b,layout.point=S,layout.work=0 }})
    (support : wires p ⊆ layout.dialogUsedWires.toFinset) :
    Triple (Challenge.encodes b R) p (Challenge.encodes b S) := by
  intro st tape hs
  have hz : regValue layout.work st.basis = 0 :=
    (regValue_zero _ _).mpr (fun w hw => hs.2.2 w (work_lower w hw))
  obtain ⟨phase, ⟨hctrl, hpoint⟩, hwork⟩ := spec st tape ⟨⟨hs.1,hs.2.1⟩,hz⟩
  refine ⟨phase, hctrl, hpoint, ?_⟩
  intro w hw
  by_cases hm : w ∈ layout.work
  · exact (regValue_zero _ _).mp hwork w hm
  · have outside : w ∉ wires p := by
      intro h
      have hparts := dialog_support_partition layout w (List.mem_toFinset.mp (support h))
      rcases hparts with hc | hp | hwork
      · have hc' : w = 0 := hc
        subst w
        exact (by decide : ¬ (514 ≤ (0:Nat))) hw
      · exact (Nat.not_lt_of_ge hw) (point_wire_lt w hp)
      · exact hm hwork
    exact (run_preserves_outside p tape st w outside).trans (hs.2.2 w hw)

end ECDSAAdd.Baselines
