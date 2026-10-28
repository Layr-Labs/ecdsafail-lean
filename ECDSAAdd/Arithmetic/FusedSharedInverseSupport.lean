import ECDSAAdd.Arithmetic.FusedSharedInverseMultiplication
import ECDSAAdd.Arithmetic.FusedSharedRetainedSupport

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic
namespace FusedHalfPorts

attribute [local irreducible] fusedThresholdFlagsSeed fusedThresholdPrepare
attribute [local irreducible] fusedRetainedThresholdRecover fusedThresholdUnprepare
attribute [local irreducible] fusedThresholdFlagsErase fusedHalfParityClear swapBits

private theorem inverse_word_subset (L : FusedHalfPorts) :
    (L.cin::L.constant++L.target++L.carry.take (L.target.length-1)).toFinset⊆L.wires.toFinset :=
  listed_subset L (by
    intro q hq
    simp only [List.mem_cons,List.mem_append] at hq
    rcases hq with ((rfl|hc)|ht)|hk
    · simp [FusedHalfPorts.wires]
    · simp [FusedHalfPorts.wires,hc]
    · simp [FusedHalfPorts.wires,ht]
    · have hk' : q∈L.carry := List.mem_of_mem_take hk
      simp [FusedHalfPorts.wires,hk'])

private theorem inverse_undo_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedCorrectionUndo L.a L.j L.l L.m L.constant L.target
      (L.carry.take (L.target.length-1)) L.cin p (2*p) (2^L.target.length-p))⊆L.wires.toFinset := by
  have hv := L.widths hw
  have hCR : L.constant.length=L.target.length := hv.2.2.1.trans hv.2.1.symm
  have hcarry : (L.carry.take (L.target.length-1)).length+1=L.target.length := by
    simp [hw.carry,hv.2.1]
  have hl := correctionWordLoad_constant_support L he p (2*p) (2^L.target.length-p)
  have hs : ECDSAAdd.wires (subInPlace L.constant L.target
      (L.carry.take (L.target.length-1)) L.cin)⊆L.wires.toFinset := by
    rw [subInPlace_wires L.constant L.target (L.carry.take (L.target.length-1)) L.cin hCR hcarry]
    exact inverse_word_subset L
  simp only [fusedCorrectionUndo,wires_append,Finset.union_subset_iff]
  aesop

private theorem inverse_signed_support (L : FusedHalfPorts) (hw : L.Widths) :
    ECDSAAdd.wires (signedSub L.b L.source L.target (L.carry.take (L.target.length-1)))⊆
      L.wires.toFinset := by
  have hv := L.widths hw
  have hs := (signedWord_wires L.b L.source L.target (L.carry.take (L.target.length-1))
    (hv.1.trans hv.2.1.symm) (by simp [hw.carry,hv.2.1])).2
  rw [hs]
  exact listed_subset L (by
    intro q hq
    simp only [List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hst|hk
    · simp [FusedHalfPorts.wires]
    · rcases hst with hs|ht
      · simp [FusedHalfPorts.wires,hs]
      · simp [FusedHalfPorts.wires,ht]
    · have hk' : q∈L.carry := List.mem_of_mem_take hk
      simp [FusedHalfPorts.wires,hk'])

private theorem inverse_raw_flag_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedInverseRawFlagClear L.target L.constant L.carry L.cin L.h p)⊆
      L.wires.toFinset := by
  have hv := L.widths hw
  have hc0 := (compareLt_wires none L.target L.constant L.carry L.cin L.h
    (hv.2.1.trans hv.2.2.1.symm) (hw.carry.trans hv.2.2.1.symm)).2 p
  have hc : ECDSAAdd.wires (compareLtConst none L.target L.constant L.carry L.cin L.h p)⊆
      L.wires.toFinset := by
    rw [hc0]
    exact listed_subset L (by
      intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|rfl|htc|hk
      · exact early_mem L he (by simp [early])
      · simp [FusedHalfPorts.wires]
      · rcases htc with ht|hc
        · simp [FusedHalfPorts.wires,ht]
        · simp [FusedHalfPorts.wires,hc]
      · simp [FusedHalfPorts.wires,hk])
  have hx : ECDSAAdd.wires [.X L.h]⊆L.wires.toFinset := by
    intro q hq
    have hq' : q=L.h := by simpa [ECDSAAdd.wires,Instr.wires] using hq
    subst q
    exact List.mem_toFinset.mpr (early_mem L he (by simp [early]))
  simp only [fusedInverseRawFlagClear,wires_append,Finset.union_subset_iff]
  exact ⟨hc,hx⟩

private theorem inverse_front_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedSignedHalfUnfront L.b L.cin L.low L.a L.h L.j L.l L.m
      L.source L.target L.constant L.carry p)⊆L.wires.toFinset := by
  have hu := inverse_undo_support L hw he
  have hs := inverse_signed_support L hw
  have hh := inverse_raw_flag_support L hw he
  have hf := correctionFlagsErase_support L he
  have hrot : ECDSAAdd.wires (rotateLeft L.target)⊆L.wires.toFinset := by
    rw [(rotate_wires L.target).2]
    split
    · exact Finset.empty_subset _
    · exact listed_subset L (by intro q hq; simp [FusedHalfPorts.wires,hq])
  have hseed : ECDSAAdd.wires (fusedInverseCorrectionFlagsSeed L.b L.a L.h L.j L.l L.m)⊆
      L.wires.toFinset := by
    intro q hq
    simp only [fusedInverseCorrectionFlagsSeed,ECDSAAdd.wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq
    have hb : L.b∈L.wires := by simp [FusedHalfPorts.wires]
    have ha : L.a∈L.wires := early_mem L he (by simp [early])
    have hh' : L.h∈L.wires := early_mem L he (by simp [early])
    have hj : L.j∈L.wires := early_mem L he (by simp [early])
    have hl : L.l∈L.wires := early_mem L he (by simp [early])
    have hm : L.m∈L.wires := early_mem L he (by simp [early])
    simp only [List.mem_toFinset]
    aesop
  have hcx : ECDSAAdd.wires [.CX L.low L.a]⊆L.wires.toFinset := by
    intro q hq
    have hh' : q=L.low∨q=L.a := by simpa [ECDSAAdd.wires,Instr.wires] using hq
    rcases hh' with rfl|rfl
    · simp [FusedHalfPorts.wires,target,targetLow]
    · exact List.mem_toFinset.mpr (early_mem L he (by simp [early]))
  simp only [fusedSignedHalfUnfront,wires_append,Finset.union_subset_iff]
  aesop

theorem inverse_support (L : FusedHalfPorts) (hw : L.Widths) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires L.inverseProgram⊆L.wires.toFinset := by
  have hb := retainedBack_support L hw
  have hs : ECDSAAdd.wires (fusedInverseFlagSeed L.b L.cin L.qOut L.hOut L.t L.d L.e
      L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length))⊆L.wires.toFinset := by
    have eqw : ECDSAAdd.wires (fusedInverseFlagSeed L.b L.cin L.qOut L.hOut L.t L.d L.e
        L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length))=
        ECDSAAdd.wires (fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e
          L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)) := by
      have hProgram : fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut L.t L.d L.e
          L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length)=
          fusedRetainedFlagToggle L.b L.cin L.qOut L.hOut L.t L.d L.e
            L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length) ++
            fusedHalfParityClear L.targetLow L.C (L.carry.take L.A.length) L.cin L.qOut := by
        simp only [fusedSignedHalfRetainedBack,fusedRetainedFlagToggle,List.append_assoc]
      rw [hProgram,fusedInverseFlagSeed,wires_append,wires_append,Finset.union_comm]
    rw [eqw]
    exact hb
  have hm : ECDSAAdd.wires (fusedInverseFlagsMove L.a L.h L.qOut L.hOut)⊆L.wires.toFinset := by
    have eqw : ECDSAAdd.wires (fusedInverseFlagsMove L.a L.h L.qOut L.hOut)=
        ECDSAAdd.wires (fusedFlagsMove L.a L.h L.qOut L.hOut) := by
      simp only [fusedInverseFlagsMove,fusedFlagsMove,wires_append]
      ac_rfl
    rw [eqw]
    exact move_support L he
  have hf := inverse_front_support L hw he
  simp only [inverseProgram,wires_append,Finset.union_subset_iff]
  aesop

end FusedHalfPorts

attribute [local irreducible] wireBlock swapRegisters copyRegister halfInPlace

theorem fusedSharedInverseKernel_support (w : Nat → Wire) (g : Wire)
    (hg : g∈skywalkSharedWires w) :
    wires (fusedSharedPorts w g).compactInverseProgram⊆(skywalkSharedWires w).toFinset := by
  have hs := (fusedSharedPorts w g).compact_inverse_support
    (fusedSharedPorts_widths w g) (fusedSharedPorts_early w g)
  exact hs.trans (by
    intro q hq
    rw [fusedSharedPorts_wires] at hq
    apply List.mem_toFinset.mpr
    rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl|hq
    · exact hg
    · exact fusedSharedSites_subset w hq)

theorem fusedSharedInverseSigned_support (w : Nat → Wire) (g : Wire)
    (hg : g∈skywalkSharedWires w) :
    wires (fusedSharedInverseSigned w g)⊆(skywalkSharedWires w).toFinset := by
  have hk := fusedSharedInverseKernel_support w g hg
  have hx : wires [.X g]⊆(skywalkSharedWires w).toFinset := by
    intro q hq
    have hq' : q=g := by simpa [wires,Instr.wires] using hq
    subst q
    exact List.mem_toFinset.mpr hg
  simp only [fusedSharedInverseSigned,fusedFieldSignedHalf,wires_append,Finset.union_subset_iff]
  aesop

theorem fusedSharedInverseCell_support (w : Nat → Wire) (g swap : Wire)
    (hg : g∈skywalkSharedWires w) (hswap : swap∈skywalkSharedWires w) :
    wires (fusedSharedInverseCell w g swap)⊆(skywalkSharedWires w).toFinset := by
  have hk := fusedSharedInverseSigned_support w g hg
  have hw := skywalkShared_field_widths w
  have hlen : ((skywalkSharedField w).z.take (skywalkSharedField w).low.length).length=
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length).length := by
    simp [List.length_take,ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hs := swapRegisters_wires swap
    ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length) hlen
  have hs' : wires (swapRegisters swap
      ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length))⊆
      (skywalkSharedWires w).toFinset := by
    intro q hq
    have hh := List.mem_toFinset.mp (hs hq)
    apply List.mem_toFinset.mpr
    simp only [List.mem_cons,List.mem_append] at hh
    rcases hh with rfl|hz|ha
    · exact hswap
    · exact retained_field_subset_shared w
        (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take hz])
    · exact retained_field_subset_shared w
        (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take ha])
  simp only [fusedSharedInverseCell,wires_append,Finset.union_subset_iff]
  exact ⟨hs',hk⟩

theorem fusedSharedInverseReplay_support (w : Nat → Wire) (rs : List (Wire×Wire))
    (ht : ∀ r∈rs,r.1∈skywalkSharedWires w ∧ r.2∈skywalkSharedWires w) :
    wires (fusedSharedInverseReplay w rs)⊆(skywalkSharedWires w).toFinset := by
  induction rs with
  | nil => simp [fusedSharedInverseReplay,wires]
  | cons r rs ih =>
    have hr := ht r (by simp)
    have ht' : ∀ q∈rs,q.1∈skywalkSharedWires w ∧ q.2∈skywalkSharedWires w :=
      fun q hq => ht q (by simp [hq])
    have hc := fusedSharedInverseCell_support w r.1 r.2 hr.1 hr.2
    have hi := ih ht'
    simp only [fusedSharedInverseReplay,wires_append,Finset.union_subset_iff]
    exact ⟨hi,hc⟩

theorem skywalkFieldMultiplicationRetained_support (w : Nat → Wire) :
    wires (skywalkFieldMultiplicationRetained w)⊆(skywalkSharedWires w).toFinset := by
  have hw := skywalkShared_field_widths w
  have hu := modUnary_wires (skywalkSharedField w).unary 256 p
    ((skywalkSharedField w).unary_widths 256 hw) (by omega)
  have hh : wires (halfInPlace (skywalkSharedField w).unary p)⊆(skywalkSharedWires w).toFinset := by
    rw [hu.2]
    intro q hq
    apply List.mem_toFinset.mpr
    apply retained_field_subset_shared w
    simp only [List.mem_toFinset,List.mem_append,ModInPlaceLayout.wires,
      ModInPlaceLayout.work,ModInPlaceLayout.unary,ModUnaryLayout.z,ModUnaryLayout.core,
      ModAddCoreLayout.z,ModAddCoreLayout.work,ModInPlaceLayout.z] at hq ⊢
    tauto
  have hr := fusedSharedInverseReplay_support w (skywalkSharedTape w) (retained_tape_subset_shared w)
  have hlen : (skywalkSharedField w).z.length=(skywalkSharedField w).a.length := by
    simp [ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have hc0 := copyRegister_wires none (skywalkSharedField w).z (skywalkSharedField w).a hlen
  have hc : wires (copyRegister none (skywalkSharedField w).z (skywalkSharedField w).a)⊆
      (skywalkSharedWires w).toFinset := by
    rw [hc0]
    split
    · exact Finset.empty_subset _
    · intro q hq
      apply List.mem_toFinset.mpr
      apply retained_field_subset_shared w
      simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
      rcases hq with hz|ha
      · simp [ModInPlaceLayout.wires,hz]
      · simp [ModInPlaceLayout.wires,ha]
  simp only [skywalkFieldMultiplicationRetained,wires_append,Finset.union_subset_iff]
  aesop

end ECDSAAdd.Arithmetic
