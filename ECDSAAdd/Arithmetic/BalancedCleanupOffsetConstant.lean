import ECDSAAdd.Arithmetic.BalancedCleanupOffsetProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

/-- J's bit 1 is absent, so the selector contributes exactly two. -/
theorem offset_bit1 : offset.testBit 1=false := by decide

private def virtualOffset (b : Bool) : Nat :=
  (List.range 256).foldr (fun i n =>
    (if i=1 then b else offset.testBit i).toNat+2*n) 0

private theorem virtualOffset_value (b : Bool) :
    virtualOffset b=offset+2*b.toNat := by cases b <;> decide

private theorem offset_list (is : List Nat) (L : Layout) (s : BasisState) :
    mappedValue (is.map (fun i =>
      if i=1 then ({wire:=some L.lower,flip:=false} : MappedBit)
      else {wire:=none,flip:=offset.testBit i})) s=
    is.foldr (fun i n => (if i=1 then s L.lower else offset.testBit i).toNat+2*n) 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons,ih]
    by_cases hi : i=1 <;> simp [MappedBit.value,hi]

/-- Value of the concrete emitted bits on every layout and basis state.
Only the single selector at bit 1 is read from the state. -/
theorem offsetBits_value (L : Layout) (s : BasisState) :
    mappedValue (offsetBits L) s=offset+2*(s L.lower).toNat := by
  rw [offsetBits,offset_list]
  exact virtualOffset_value _

theorem offsetBits_length (L : Layout) : (offsetBits L).length=256 := by
  simp [offsetBits]

theorem offsetBits_sources (L : Layout) (w : Wire)
    (hw : w∈mappedWires (offsetBits L)) : w=L.lower := by
  obtain ⟨b,hb,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  by_cases he : i=1
  · simpa [he] using hw
  · simp [he] at hw

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.offset_bit1
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.offsetBits_value
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.offsetBits_length
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.offsetBits_sources
