import ECDSAAdd.Arithmetic.FieldRenameOffsetSlim
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
open BalancedCleanupOffset
attribute [local irreducible] BalancedCleanupOffsetSlim.chain majority eraseCarry

private theorem mapped_tail {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).tail=xs.tail.map f := by cases xs <;> rfl

/-- A default wire is never read on the proven production-width input. -/
private theorem mapped_head (f : Wire → Wire) (xs : List Wire) (h : xs≠[]) :
    (xs.map f).headD 0=f (xs.headD 0) := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => rfl

/-- Rename the actual first-bit omission and the unchanged slim tail. -/
theorem zero_head_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (a y cinC cinB d target : Wire)
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    renameProgram f (BalancedCleanupOffsetZeroHead.program bits xs ys cs ds a y cinC cinB d target)=
      BalancedCleanupOffsetZeroHead.program (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f a) (f y) (f cinC) (f cinB) (f d) (f target) := by
  have tail := slim_offset_chain_natural f bits xs ys cs ds cinC d target hb hx hc hd
  simp only [BalancedCleanupOffsetZeroHead.program,rename_append,majority_natural,
    eraseCarry_natural,tail]
  rfl

/-- The actual mapped lists have256 entries, so headD defaults cannot cause
an invalid assumption that the relabeling fixes physical wire0. -/
theorem zero_offset_core_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (BalancedCleanupOffsetZero.core L)=
      BalancedCleanupOffsetZero.core (mapOffset f L) := by
  have widths := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  have co : L.offsetCarry.length=256 := hw.2
  have hy : L.y≠[] := by intro h; simp [h] at widths
  have hr : L.r≠[] := by intro h; simp [h] at widths
  have hc : L.carry≠[] := by intro h; simp [h] at cy
  have bitlen : (offsetBits L).tail.length=255 := by rw [List.length_tail,offsetBits_length]
  have ylen : L.y.tail.length=255 := by rw [List.length_tail,widths.2.2.1]
  have rlen : L.r.tail.length=255 := by rw [List.length_tail,widths.2.1]
  have clen : L.offsetCarry.tail.length=255 := by rw [List.length_tail,co]
  have dlen : L.carry.tail.length=255 := by rw [List.length_tail,cy]
  have ym : (mapOffset f L).y=L.y.map f := y_map f L.toCircuit.toLayout
  have rm : (mapOffset f L).r=L.r.map f := r_map f L.toCircuit.toLayout
  have cm : (mapOffset f L).offsetCarry=L.offsetCarry.map f := rfl
  have dm : (mapOffset f L).carry=L.carry.map f := rfl
  have natural := zero_head_natural f (offsetBits L).tail L.y.tail L.r.tail
    L.offsetCarry.tail L.carry.tail (L.y.headD 0) (L.r.headD 0) L.one L.cout
    (L.carry.headD 0) L.parity (by omega) (by omega) (by omega) (by omega)
  simp only [BalancedCleanupOffsetZero.core,natural,ym,rm,cm,dm,←offsetBits_map,
    mapped_tail,mapped_head f L.y hy,mapped_head f L.r hr,mapped_head f L.carry hc]
  rfl

private theorem zero_front_natural (f : Wire → Wire) (L : Layout) :
    renameProgram f (front L)=front (mapOffset f L) := by
  simp only [front,rename_append,prepareSign_natural,offset_view_natural]
  rfl

/-- Exact instruction-list equality for the actual510-T/M cleanup.
No injectivity or phase premise is needed for structural relabeling. -/
theorem zero_offset_program_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (BalancedCleanupOffsetZero.program L)=
      BalancedCleanupOffsetZero.program (mapOffset f L) := by
  simp only [BalancedCleanupOffsetZero.program,rename_append,rename_reverse,
    zero_front_natural,zero_offset_core_natural f L hw]
end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.zero_head_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.zero_offset_core_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.zero_offset_program_natural
