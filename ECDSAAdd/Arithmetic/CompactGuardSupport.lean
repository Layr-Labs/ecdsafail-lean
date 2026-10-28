import ECDSAAdd.Arithmetic.FusedHalfSupportCommon

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

private theorem compact_source_mem (L : FusedHalfPorts) {q : Wire} (h : q∈L.compactSource) : q∈L.wires := by
  have hs := L.compactSource_sublist.subset h
  simp [FusedHalfPorts.wires,hs]
private theorem compact_target_mem (L : FusedHalfPorts) {q : Wire} (h : q∈L.compactTarget) : q∈L.wires := by
  have hs := L.compactTarget_sublist.subset h
  simp [FusedHalfPorts.wires,hs]
private theorem compact_constant_mem (L : FusedHalfPorts) {q : Wire} (h : q∈L.compactConstant) : q∈L.wires := by
  have hs := L.compactConstant_sublist.subset h
  simp [FusedHalfPorts.wires,hs]
private theorem compact_carry_mem (L : FusedHalfPorts) {q : Wire} (h : q∈L.compactCarry) : q∈L.wires := by
  have hs := L.compactCarry_sublist.subset h
  simp [FusedHalfPorts.wires,hs]

private theorem compact_masked_word (L : FusedHalfPorts) (c : Wire) (hc : c∈L.wires) (K : Nat) :
    ECDSAAdd.wires (maskedConstant c L.compactConstant K)⊆L.wires.toFinset :=
  (maskedConstant_wires_subset c L.compactConstant K).trans (listed_subset L (by
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact hc
    · exact compact_constant_mem L hq))

private theorem compact_loader_support (L : FusedHalfPorts) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedCorrectionWordLoad L.a L.j L.l L.m L.compactConstant
      p (2*p) (2^L.compactTarget.length-p))⊆L.wires.toFinset := by
  have ha := compact_masked_word L L.a (early_mem L he (by simp [early])) p
  have hj := compact_masked_word L L.j (early_mem L he (by simp [early])) (2*p)
  have hlp := compact_masked_word L L.l (early_mem L he (by simp [early])) p
  have hln := compact_masked_word L L.l (early_mem L he (by simp [early])) (2^L.compactTarget.length-p)
  have hmp := compact_masked_word L L.m (early_mem L he (by simp [early])) p
  have hmd := compact_masked_word L L.m (early_mem L he (by simp [early])) (2*p)
  have hmn := compact_masked_word L L.m (early_mem L he (by simp [early])) (2^L.compactTarget.length-p)
  simp only [fusedCorrectionWordLoad,wires_append,Finset.union_subset_iff]
  aesop

private theorem compact_arith_subset (L : FusedHalfPorts) :
    (L.cin::(L.compactConstant++L.compactTarget++
      L.compactCarry.take (L.compactTarget.length-1))).toFinset⊆L.wires.toFinset :=
  listed_subset L (by
    intro q hq
    simp only [List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hct|hk
    · simp [FusedHalfPorts.wires]
    · rcases hct with hc|ht
      · exact compact_constant_mem L hc
      · exact compact_target_mem L ht
    · exact compact_carry_mem L (List.mem_of_mem_take hk))

private theorem compact_correction_support (inverse : Bool) (L : FusedHalfPorts)
    (hw : L.Widths) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (if inverse then fusedCorrectionUndo L.a L.j L.l L.m L.compactConstant
        L.compactTarget (L.compactCarry.take (L.compactTarget.length-1)) L.cin
        p (2*p) (2^L.compactTarget.length-p)
      else fusedCorrectionApply L.a L.j L.l L.m L.compactConstant
        L.compactTarget (L.compactCarry.take (L.compactTarget.length-1)) L.cin
        p (2*p) (2^L.compactTarget.length-p))⊆L.wires.toFinset := by
  have hv := L.compact_widths hw
  have hCR := hv.2.2.1.trans hv.2.1.symm
  have hk : (L.compactCarry.take (L.compactTarget.length-1)).length+1=L.compactTarget.length := by
    simp [hv.2.2.2,hv.2.1]
  have hl := compact_loader_support L he
  have ha : ECDSAAdd.wires (addInPlace L.compactConstant L.compactTarget
      (L.compactCarry.take (L.compactTarget.length-1)) L.cin)⊆L.wires.toFinset := by
    rw [addInPlace_wires _ _ _ _ hCR hk]; exact compact_arith_subset L
  have hs : ECDSAAdd.wires (subInPlace L.compactConstant L.compactTarget
      (L.compactCarry.take (L.compactTarget.length-1)) L.cin)⊆L.wires.toFinset := by
    rw [subInPlace_wires _ _ _ _ hCR hk]; exact compact_arith_subset L
  cases inverse <;> simp only [Bool.false_eq_true,if_false,if_true,fusedCorrectionUndo,
    fusedCorrectionApply,wires_append,Finset.union_subset_iff] <;> aesop

private theorem compact_signed_support (inverse : Bool) (L : FusedHalfPorts) (hw : L.Widths) :
    ECDSAAdd.wires (if inverse then signedSub L.b L.compactSource L.compactTarget
        (L.compactCarry.take (L.compactTarget.length-1))
      else signedAdd L.b L.compactSource L.compactTarget
        (L.compactCarry.take (L.compactTarget.length-1)))⊆L.wires.toFinset := by
  have hv := L.compact_widths hw
  have hk : (L.compactCarry.take (L.compactTarget.length-1)).length+1=L.compactTarget.length := by
    simp [hv.2.2.2,hv.2.1]
  have hs := signedWord_wires L.b L.compactSource L.compactTarget
    (L.compactCarry.take (L.compactTarget.length-1)) (hv.1.trans hv.2.1.symm) hk
  have bound : (L.b::(L.compactSource++L.compactTarget++
      L.compactCarry.take (L.compactTarget.length-1))).toFinset⊆L.wires.toFinset :=
    listed_subset L (by
      intro q hq
      simp only [List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|hst|hk
      · simp [FusedHalfPorts.wires]
      · rcases hst with hs|ht
        · exact compact_source_mem L hs
        · exact compact_target_mem L ht
      · exact compact_carry_mem L (List.mem_of_mem_take hk))
  cases inverse <;> simp only [Bool.false_eq_true,if_false,if_true]
  · rw [hs.1]; exact bound
  · rw [hs.2]; exact bound

private theorem compact_compare_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedInverseRawFlagClear L.compactTarget L.compactConstant
      L.compactCarry L.cin L.h p)⊆L.wires.toFinset := by
  have hv := L.compact_widths hw
  have hc0 := (compareLt_wires none L.compactTarget L.compactConstant L.compactCarry L.cin L.h
    (hv.2.1.trans hv.2.2.1.symm) (hv.2.2.2.trans hv.2.2.1.symm)).2 p
  have hc : ECDSAAdd.wires (compareLtConst none L.compactTarget L.compactConstant
      L.compactCarry L.cin L.h p)⊆L.wires.toFinset := by
    rw [hc0]
    exact listed_subset L (by
      intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|rfl|htc|hk
      · exact early_mem L he (by simp [early])
      · simp [FusedHalfPorts.wires]
      · rcases htc with ht|hc
        · exact compact_target_mem L ht
        · exact compact_constant_mem L hc
      · exact compact_carry_mem L hk)
  have hx : ECDSAAdd.wires [.X L.h]⊆L.wires.toFinset := by
    intro q hq
    have hq' : q=L.h := by simpa [ECDSAAdd.wires,Instr.wires] using hq
    subst q; exact List.mem_toFinset.mpr (early_mem L he (by simp [early]))
  simp only [fusedInverseRawFlagClear,wires_append,Finset.union_subset_iff]
  exact ⟨hc,hx⟩

private theorem compact_seed_support (L : FusedHalfPorts) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedInverseCorrectionFlagsSeed L.b L.a L.h L.j L.l L.m)⊆L.wires.toFinset := by
  intro q hq
  simp only [fusedInverseCorrectionFlagsSeed,ECDSAAdd.wires,Instr.wires,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq
  have hb : L.b∈L.wires := by simp [FusedHalfPorts.wires]
  have ha : L.a∈L.wires := early_mem L he (by simp [early])
  have hh : L.h∈L.wires := early_mem L he (by simp [early])
  have hj : L.j∈L.wires := early_mem L he (by simp [early])
  have hl : L.l∈L.wires := early_mem L he (by simp [early])
  have hm : L.m∈L.wires := early_mem L he (by simp [early])
  simp only [List.mem_toFinset]
  aesop

private theorem compact_xor_support (L : FusedHalfPorts) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires [.CX L.low L.a]⊆L.wires.toFinset := by
  intro q hq
  have hq' : q=L.low∨q=L.a := by simpa [ECDSAAdd.wires,Instr.wires] using hq
  rcases hq' with rfl|rfl
  · simp [FusedHalfPorts.wires,target,targetLow]
  · exact List.mem_toFinset.mpr (early_mem L he (by simp [early]))

private theorem compact_rotate_support (left : Bool) (L : FusedHalfPorts) :
    ECDSAAdd.wires (if left then rotateLeft L.compactTarget else rotateRight L.compactTarget)⊆
      L.wires.toFinset := by
  have hr := rotate_wires L.compactTarget
  cases left <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals first | rw [hr.1] | rw [hr.2]
  all_goals split
  all_goals first | exact Finset.empty_subset _ | exact listed_subset L (by intro q hq; exact compact_target_mem L hq)

theorem compact_forward_support (L : FusedHalfPorts) (hw : L.Widths) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires L.compactForwardProgram⊆L.wires.toFinset := by
  have had := compact_signed_support false L hw
  have hcmp := compact_compare_support L hw he
  have hcor := compact_correction_support false L hw he
  have hrot := compact_rotate_support false L
  have hflags := correctionFlagsErase_support L he
  have hseed := compact_seed_support L he
  have hxor := compact_xor_support L he
  have hmove := move_support L he
  have hback := retainedBack_support L hw
  simp only [Bool.false_eq_true,if_false] at had hcor hrot
  have hraw : ECDSAAdd.wires (fusedRawNormalize L.b L.h L.compactSource L.compactTarget
      L.compactConstant (L.compactCarry.take (L.compactTarget.length-1)) L.compactCarry L.cin p)⊆
      L.wires.toFinset := by
    have heq : fusedRawNormalize L.b L.h L.compactSource L.compactTarget L.compactConstant
        (L.compactCarry.take (L.compactTarget.length-1)) L.compactCarry L.cin p=
        signedAdd L.b L.compactSource L.compactTarget (L.compactCarry.take (L.compactTarget.length-1)) ++
          fusedInverseRawFlagClear L.compactTarget L.compactConstant L.compactCarry L.cin L.h p := by
      simp only [fusedRawNormalize,fusedInverseRawFlagClear,List.append_assoc]
    rw [heq,wires_append]; exact Finset.union_subset_iff.mpr ⟨had,hcmp⟩
  have heven : ECDSAAdd.wires (fusedEvenHalf L.b L.a L.h L.j L.l L.m L.compactConstant
      L.compactTarget (L.compactCarry.take (L.compactTarget.length-1)) L.cin p)⊆L.wires.toFinset := by
    simp only [fusedEvenHalf,wires_append,Finset.union_subset_iff]
    aesop
  simp only [compactForwardProgram,compactSignedHalfFront,wires_append,Finset.union_subset_iff]
  aesop

theorem compact_inverse_support (L : FusedHalfPorts) (hw : L.Widths) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires L.compactInverseProgram⊆L.wires.toFinset := by
  have hsig := compact_signed_support true L hw
  have hcmp := compact_compare_support L hw he
  have hcor := compact_correction_support true L hw he
  have hrot := compact_rotate_support true L
  have hflags := correctionFlagsErase_support L he
  have hseed := compact_seed_support L he
  have hxor := compact_xor_support L he
  simp only [if_true] at hsig hcor hrot
  have hb := retainedBack_support L hw
  have hinit : ECDSAAdd.wires (fusedInverseFlagSeed L.b L.cin L.qOut L.hOut L.t L.d L.e
      L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length))⊆L.wires.toFinset := by
    have heq : fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf
        L.targetLow L.A L.C (L.carry.take L.A.length)=
        fusedRetainedFlagToggle L.b L.cin L.qOut L.hOut L.t L.d L.e L.sourceHalf L.targetLow
          L.A L.C (L.carry.take L.A.length) ++ fusedHalfParityClear L.targetLow L.C
            (L.carry.take L.A.length) L.cin L.qOut := by
      simp only [fusedSignedHalfRetainedBack,fusedRetainedFlagToggle,List.append_assoc]
    have heqw : ECDSAAdd.wires (fusedInverseFlagSeed L.b L.cin L.qOut L.hOut L.t L.d L.e
        L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length))=
        ECDSAAdd.wires (fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e
          L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)) := by
      rw [heq,fusedInverseFlagSeed,wires_append,wires_append,Finset.union_comm]
    rw [heqw]; exact hb
  have hmove : ECDSAAdd.wires (fusedInverseFlagsMove L.a L.h L.qOut L.hOut)⊆L.wires.toFinset := by
    have heqw : ECDSAAdd.wires (fusedInverseFlagsMove L.a L.h L.qOut L.hOut)=
        ECDSAAdd.wires (fusedFlagsMove L.a L.h L.qOut L.hOut) := by
      simp only [fusedInverseFlagsMove,fusedFlagsMove,wires_append]; ac_rfl
    rw [heqw]; exact move_support L he
  simp only [compactInverseProgram,fusedSignedHalfUnfront,wires_append,Finset.union_subset_iff]
  aesop

end FusedHalfPorts
end ECDSAAdd.Arithmetic
