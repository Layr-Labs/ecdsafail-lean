import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Arithmetic.ControlledPointPorts

namespace ECDSAAdd.Baselines
open Arithmetic

/-- A fixed instance of the legacy allocation. Only actual program support is
charged by the challenge; unused legacy fields remain zero by framing. -/
def layout : ControlledPointLayout where
  control := Challenge.control
  genericSelect := 9814
  doubleSelect := 9815
  infinitySelect := 9816
  core := {
    input := Challenge.point
    output := ⟨514, List.range' 515 256, List.range' 771 256⟩
    dx := List.range' 1027 257
    dy := List.range' 1284 257
    slope := List.range' 1541 257
    square := List.range' 1798 257
    offset := List.range' 2055 257
    candidateX := List.range' 2312 257
    delta := List.range' 2569 257
    product := List.range' 2826 257
    candidateY := List.range' 3083 257
    constant := List.range' 3340 257
    divisor := List.range' 3597 256
    inverse := List.range' 3853 256
    inputXHigh := 4109
    inputYHigh := 4110
    equalX := 4111
    equalNegY := 4112
    generic := 4113
    double := 4114
    pool := List.range' 4115 5699
  }

theorem layout_control : layout.control = Challenge.control := rfl
theorem layout_point : layout.point = Challenge.point := rfl

theorem layout_widths : layout.Widths := by
  constructor <;>
    simp [layout, Challenge.point, PointAddLayout.words]

theorem core_wires : layout.core.wires = List.range' 1 9813 := by
  have mr (a n : Nat) : (List.range n).map (· + a) = List.range' a n := by
    simpa only [Nat.add_comm] using (List.range'_eq_map_range (s := a) (n := n)).symm
  have consr (s n : Nat) : s :: List.range' (s+1) n = List.range' s (n+1) := rfl
  simp only [PointAddLayout.wires, PointAddLayout.work,
    PointAddLayout.words, PointAddLayout.flags, PointAddLayout.pointWires, layout,
    Challenge.point, List.flatten_cons, List.flatten_nil, List.append_nil, mr]
  rw [show [4109,4110] = List.range' 4109 2 from rfl,
    show [4111,4112,4113,4114] = List.range' 4111 4 from rfl]
  simp only [consr, ← List.append_assoc]
  rw [show List.range' 1 257 ++ List.range' 258 256 = List.range' 1 513
    from List.range'_append_1]
  rw [show List.range' 1 513 ++ List.range' 514 257 = List.range' 1 770
    from List.range'_append_1]
  rw [show List.range' 1 770 ++ List.range' 771 256 = List.range' 1 1026
    from List.range'_append_1]
  rw [show List.range' 1 1026 ++ List.range' 1027 257 = List.range' 1 1283
    from List.range'_append_1]
  rw [show List.range' 1 1283 ++ List.range' 1284 257 = List.range' 1 1540
    from List.range'_append_1]
  rw [show List.range' 1 1540 ++ List.range' 1541 257 = List.range' 1 1797
    from List.range'_append_1]
  rw [show List.range' 1 1797 ++ List.range' 1798 257 = List.range' 1 2054
    from List.range'_append_1]
  rw [show List.range' 1 2054 ++ List.range' 2055 257 = List.range' 1 2311
    from List.range'_append_1]
  rw [show List.range' 1 2311 ++ List.range' 2312 257 = List.range' 1 2568
    from List.range'_append_1]
  rw [show List.range' 1 2568 ++ List.range' 2569 257 = List.range' 1 2825
    from List.range'_append_1]
  rw [show List.range' 1 2825 ++ List.range' 2826 257 = List.range' 1 3082
    from List.range'_append_1]
  rw [show List.range' 1 3082 ++ List.range' 3083 257 = List.range' 1 3339
    from List.range'_append_1]
  rw [show List.range' 1 3339 ++ List.range' 3340 257 = List.range' 1 3596
    from List.range'_append_1]
  rw [show List.range' 1 3596 ++ List.range' 3597 256 = List.range' 1 3852
    from List.range'_append_1]
  rw [show List.range' 1 3852 ++ List.range' 3853 256 = List.range' 1 4108
    from List.range'_append_1]
  rw [show List.range' 1 4108 ++ List.range' 4109 2 = List.range' 1 4110
    from List.range'_append_1]
  rw [show List.range' 1 4110 ++ List.range' 4111 4 = List.range' 1 4114
    from List.range'_append_1]
  rw [show List.range' 1 4114 ++ List.range' 4115 5699 = List.range' 1 9813
    from List.range'_append_1]

theorem layout_nodup : layout.wires.Nodup := by
  change (layout.core.wires ++ [0,9814,9815,9816]).Nodup
  rw [core_wires, List.nodup_append']
  refine ⟨List.nodup_range', by decide, ?_⟩
  intro a ha hb
  simp only [List.mem_range'_1] at ha
  simp only [List.mem_cons, List.not_mem_nil] at hb
  rcases hb with rfl | rfl | rfl | rfl | h
  all_goals omega

theorem work_lower (w : Wire) (hw : w ∈ layout.work) : 514 ≤ w := by
  simp only [ControlledPointLayout.work, ControlledPointLayout.temporary,
    ControlledPointLayout.outWork, ControlledPointLayout.selectors,
    PointAddLayout.work, PointAddLayout.words, PointAddLayout.flags,
    PointAddLayout.pointWires, layout, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_cons, List.mem_range'_1,
    List.not_mem_nil, or_false, or_assoc] at hw
  rcases hw with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first | (subst w; decide) | exact Nat.le_trans (by decide) h.1

end ECDSAAdd.Baselines
