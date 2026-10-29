import ECDSAAdd.Submission.Entrant.CompressedMath
import ECDSAAdd.Submission.Entrant.ZeroFlag
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof

namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout

def compressedPorts (L : ControlledPointLayout) : List ZeroBit :=
  zeroPorts (L.point.x ++ L.point.y.take 1) (L.dialogPool.take 257)

def compressedEqual (L : ControlledPointLayout) (c t : Wire) (C : Point) : Program :=
  equalConstant c t (compressedPorts L) (compressedCode C)

theorem compressed_lengths (L : ControlledPointLayout) (hw : L.Widths) :
    (L.point.x ++ L.point.y.take 1).length = 257 ∧
    (L.dialogPool.take 257).length = 257 ∧
    (compressedPorts L).length = 257 := by
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hs : (L.point.x ++ L.point.y.take 1).length = 257 := by simp [hx, hy]
  have hp : (L.dialogPool.take 257).length = 257 := by simp [L.dialogPool_length hw]
  have hm := (zeroPorts_maps _ _ (hs.trans hp.symm)).1
  exact ⟨hs, hp, by simpa only [List.length_map, compressedPorts, hs] using congrArg List.length hm⟩

theorem compressed_nodup (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (c t : Wire) (hct : c ≠ t) (hc : c = L.control ∨ c ∈ L.inPlaceFlags)
    (ht : t ∈ L.inPlaceFlags) :
    (c :: t :: (L.point.x ++ L.point.y.take 1) ++ L.dialogPool.take 257).Nodup := by
  have h := L.dialogPointZero_nodup hn c t hct hc ht
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp h q
  have hp := (List.take_sublist_take_left (l := L.dialogPool) (show 257 ≤ 513 by omega)).count_le q
  have hy := (List.take_sublist 1 L.point.y).count_le q
  simp only [PointAddLayout.pointWires, List.count_append, List.count_cons] at hh ⊢
  omega

theorem compressed_equal_boundary (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (R C : Point) (b : Bool) (f : BasisState) (c t : Wire)
    (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags) (hct : c≠t) (B : Bool)
    (hb : (if c=L.control then b else f c)=B) :
    Triple (PointDialogBoundary L R b f) (compressedEqual L c t C)
      (PointDialogBoundary L R b (writeBit f t (f t ^^ (B && pointEqual R C)))) := by
  have hl := compressed_lengths L hw
  have hnd := compressed_nodup L hn c t hct hc ht
  intro s m v
  have hclean : regValue (L.dialogPool.take 257) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp v.clean q (List.take_subset _ _ hq))
  have hh := equalPorts_correct c t (L.point.x ++ L.point.y.take 1) (L.dialogPool.take 257)
    (compressedCode C) (hl.1.trans hl.2.1.symm) hnd
    (by rw [hl.1]; exact compressedCode_lt C) s m hclean
  have hv := (point_holds _ _ _).mp v.point
  have hr : regValue (L.point.x ++ L.point.y.take 1) s.basis = compressedCode R := by
    rw [regValue_append, show L.point.x.length = 256 from hw.inputX, hv.2.1,
      CuccaroStreamedSquareWideLayout.regValue_take_mod L.point.y 1
        (by rw [show L.point.y.length = 256 from hw.inputY]; decide), hv.2.2]
    rfl
  have he : decide (compressedCode R = compressedCode C) = pointEqual R C := by
    apply Bool.eq_iff_iff.mpr
    simp only [pointEqual, decide_eq_true_eq,
      compressedCode_injective.eq_iff, pointCode_injective.eq_iff]
  rw [hr, he] at hh
  have hcval : s.basis c=B := by
    rw [← hb]
    split_ifs with h
    · subst c; exact v.control
    · exact v.flags c (hc.resolve_left h)
  change run (compressedEqual L c t C) m s = _ at hh
  refine ⟨by rw [hh], v.withFlags hn ?_ ?_⟩
  · intro q hq
    rw [hh]
    by_cases he : q=t
    · subst q; simp [writeBit,hcval,v.flags t ht]
    · simp [writeBit,he,v.flags q hq]
  · intro q hq
    rw [hh]
    have hqt : q≠t := fun he => hq (he ▸ ht)
    simp [writeBit,hqt]

theorem compressed_counts (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    toffoliCount (compressedEqual L c t C) = 257 ∧
    measurementCount (compressedEqual L c t C) = 257 := by
  simpa only [compressedEqual, (compressed_lengths L hw).2.2] using
    equalConstant_counts c t (compressedPorts L) (compressedCode C)

theorem compressed_wires (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    wires (compressedEqual L c t C) =
      (c :: t :: (L.point.x ++ L.point.y.take 1) ++ L.dialogPool.take 257).toFinset := by
  rw [compressedEqual, equalConstant_wires]
  have hl := compressed_lengths L hw
  exact List.toFinset_eq_of_perm _ _
    ((zeroPorts_perm _ _ (hl.1.trans hl.2.1.symm)).cons t |>.cons c)

theorem compressed_support (L : ControlledPointLayout) (hw : L.Widths)
    (c t : Wire) (C : Point) (k : Nat) :
    wires (compressedEqual L c t C) ⊆ wires (equalConstant c t L.dialogPointZero k) := by
  rw [compressed_wires L hw]
  rw [equalConstant_wires]
  have hl : (PointAddLayout.pointWires L.point).length = (L.dialogPool.take 513).length := by
    simp [PointAddLayout.pointWires, show L.point.x.length = 256 from hw.inputX,
      show L.point.y.length = 256 from hw.inputY, L.dialogPool_length hw]
  rw [show (c::t::L.dialogPointZero.flatMap ZeroBit.wires).toFinset =
      (c::t::PointAddLayout.pointWires L.point ++ L.dialogPool.take 513).toFinset from
    List.toFinset_eq_of_perm _ _ ((zeroPorts_perm _ _ hl).cons t |>.cons c)]
  intro q hq
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢
  have hp : q ∈ L.dialogPool.take 257 → q ∈ L.dialogPool.take 513 :=
    fun h => (List.take_sublist_take_left (l := L.dialogPool) (show 257 ≤ 513 by omega)).subset h
  have hy : q ∈ L.point.y.take 1 → q ∈ L.point.y := fun h => List.take_subset _ _ h
  simp only [PointAddLayout.pointWires, List.mem_cons, List.mem_append]
  tauto

theorem compressed_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c t : Wire) (hc : c=L.control ∨ c∈L.inPlaceFlags) (ht : t∈L.inPlaceFlags)
    (hct : c≠t) (C : Point) : GatePhysical (compressedEqual L c t C) := by
  apply equalConstant_physical
  have hl := compressed_lengths L hw
  exact ((zeroPorts_perm _ _ (hl.1.trans hl.2.1.symm)).cons t |>.cons c).nodup_iff.mpr
    (compressed_nodup L hn c t hct hc ht)

theorem compressed_slots (L : ControlledPointLayout) (hw : L.Widths) (c t : Wire) (C : Point) :
    Challenge.gateSlots (compressedEqual L c t C) ≤ 2314 := by
  have h := Baselines.equalConstant_gateSlots_le c t (compressedPorts L) (compressedCode C)
  rw [(compressed_lengths L hw).2.2] at h
  exact h.trans (by decide)

end ECDSAAdd.Entrant
