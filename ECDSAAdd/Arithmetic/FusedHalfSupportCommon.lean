import ECDSAAdd.Arithmetic.CompactGuardLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ECDSAAdd.Arithmetic

namespace FusedHalfPorts

theorem listed_subset (L : FusedHalfPorts) {xs : List Wire}
    (h : ∀ q ∈ xs, q ∈ L.wires) : xs.toFinset ⊆ L.wires.toFinset := by
  intro q hq
  exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem early_mem (L : FusedHalfPorts) (he : L.early.Sublist L.A)
    {q : Wire} (hq : q∈L.early) : q∈L.wires := by
  simp [FusedHalfPorts.wires,he.subset hq]

theorem constant_mem (L : FusedHalfPorts) {q : Wire} (hq : q∈L.C) :
    q∈L.wires := by
  simp [FusedHalfPorts.wires,FusedHalfPorts.constant,hq]

theorem sourceHalf_mem (L : FusedHalfPorts) {q : Wire} (hq : q∈L.sourceHalf) :
    q∈L.wires := by
  have hs : q∈L.source := by
    simp [FusedHalfPorts.source,FusedHalfPorts.sourceHalf] at hq ⊢
    tauto
  simp [FusedHalfPorts.wires,hs]

private theorem correctionWordLoad_support (L : FusedHalfPorts)
    (he : L.early.Sublist L.A) (P D N : Nat) :
    ECDSAAdd.wires (fusedCorrectionWordLoad L.a L.j L.l L.m L.C P D N) ⊆ L.wires.toFinset := by
  have ha : (L.a::L.C).toFinset⊆L.wires.toFinset := listed_subset L (by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact early_mem L he (by simp [FusedHalfPorts.early])
    · exact constant_mem L hq)
  have hj : (L.j::L.C).toFinset⊆L.wires.toFinset := listed_subset L (by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact early_mem L he (by simp [FusedHalfPorts.early])
    · exact constant_mem L hq)
  have hl : (L.l::L.C).toFinset⊆L.wires.toFinset := listed_subset L (by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact early_mem L he (by simp [FusedHalfPorts.early])
    · exact constant_mem L hq)
  have hm : (L.m::L.C).toFinset⊆L.wires.toFinset := listed_subset L (by
    intro q hq; rcases List.mem_cons.mp hq with rfl|hq
    · exact early_mem L he (by simp [FusedHalfPorts.early])
    · exact constant_mem L hq)
  have hpa := (maskedConstant_wires_subset L.a L.C P).trans ha
  have hpl := (maskedConstant_wires_subset L.l L.C P).trans hl
  have hpm := (maskedConstant_wires_subset L.m L.C P).trans hm
  have hdj := (maskedConstant_wires_subset L.j L.C D).trans hj
  have hdm := (maskedConstant_wires_subset L.m L.C D).trans hm
  have hnl := (maskedConstant_wires_subset L.l L.C N).trans hl
  have hnm := (maskedConstant_wires_subset L.m L.C N).trans hm
  simp only [fusedCorrectionWordLoad, wires_append, Finset.union_subset_iff]
  aesop

private theorem thresholdWordLoad_support (L : FusedHalfPorts) (K P : Nat) :
    ECDSAAdd.wires (fusedThresholdWordLoad L.b L.qOut L.t L.d L.C K P) ⊆ L.wires.toFinset := by
  have hb := (maskedConstant_wires_subset L.b L.C K).trans
    (listed_subset L (by
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · simp [FusedHalfPorts.wires]
      · exact constant_mem L hq))
  have hq := (maskedConstant_wires_subset L.qOut L.C K).trans
    (listed_subset L (by
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · simp [FusedHalfPorts.wires,FusedHalfPorts.target]
      · exact constant_mem L hq))
  have ht := (maskedConstant_wires_subset L.t L.C P).trans
    (listed_subset L (by
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · simp [FusedHalfPorts.wires,FusedHalfPorts.constant]
      · exact constant_mem L hq))
  have hd := (maskedConstant_wires_subset L.d L.C 1).trans
    (listed_subset L (by
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · simp [FusedHalfPorts.wires,FusedHalfPorts.constant]
      · exact constant_mem L hq))
  simp only [fusedThresholdWordLoad, wires_append, Finset.union_subset_iff]
  aesop

private theorem prepare_support (L : FusedHalfPorts) (hw : L.Widths) :
    ECDSAAdd.wires (fusedThresholdPrepare L.b L.sourceHalf L.A) ⊆ L.wires.toFinset ∧
    ECDSAAdd.wires (fusedThresholdUnprepare L.b L.sourceHalf L.A) ⊆ L.wires.toFinset := by
  have hv := L.widths hw
  have hc := copyRegister_wires none L.sourceHalf L.A
    hv.2.2.2.1
  have hn := signComplement_wires_subset L.b L.A
  have hcopy : ECDSAAdd.wires (copyRegister none L.sourceHalf L.A) ⊆ L.wires.toFinset := by
    rw [hc]
    split
    · exact Finset.empty_subset _
    · exact listed_subset L (by
        intro q hq
        simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
        rcases hq with hs|ha
        · exact sourceHalf_mem L hs
        · simp [FusedHalfPorts.wires,ha])
  have hsign : ECDSAAdd.wires (signComplement L.b L.A) ⊆ L.wires.toFinset :=
    hn.trans (listed_subset L (by intro q hq; simp [FusedHalfPorts.wires] at hq ⊢; tauto))
  simp only [fusedThresholdPrepare, fusedThresholdUnprepare, wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨hcopy,hsign⟩,⟨hsign,hcopy⟩⟩

private theorem retainedAdd_support_ports (L : FusedHalfPorts) :
    ECDSAAdd.wires (retainedAddStart L.C L.A ((L.carry.take L.A.length).take
      (L.targetLow.length-1)) L.cin) ⊆ L.wires.toFinset ∧
    ECDSAAdd.wires (retainedAddFinish L.C L.A ((L.carry.take L.A.length).take
      (L.targetLow.length-1)) L.cin) ⊆ L.wires.toFinset := by
  have hs := retainedAdd_support L.C L.A
    ((L.carry.take L.A.length).take (L.targetLow.length-1)) L.cin
  constructor
  · exact hs.1.trans (listed_subset L (by
      intro q hq
      simp only [List.mem_cons,List.mem_append] at hq
      rcases hq with ((rfl|hC)|hA)|hc
      · simp [FusedHalfPorts.wires]
      · simp [FusedHalfPorts.wires,FusedHalfPorts.constant,hC]
      · simp [FusedHalfPorts.wires,hA]
      · have hc' : q∈L.carry := List.mem_of_mem_take (List.mem_of_mem_take hc)
        simp [FusedHalfPorts.wires,hc']))
  · exact hs.2.trans (listed_subset L (by
      intro q hq
      simp only [List.mem_cons,List.mem_append] at hq
      rcases hq with ((rfl|hC)|hA)|hc
      · simp [FusedHalfPorts.wires]
      · simp [FusedHalfPorts.wires,FusedHalfPorts.constant,hC]
      · simp [FusedHalfPorts.wires,hA]
      · have hc' : q∈L.carry := List.mem_of_mem_take (List.mem_of_mem_take hc)
        simp [FusedHalfPorts.wires,hc']))

theorem correctionWordLoad_constant_support (L : FusedHalfPorts)
    (he : L.early.Sublist L.A) (P D N : Nat) :
    ECDSAAdd.wires (fusedCorrectionWordLoad L.a L.j L.l L.m L.constant P D N) ⊆
      L.wires.toFinset := by
  have hconst (c : Wire) (hc : c∈L.early) (k : Nat) :
      ECDSAAdd.wires (maskedConstant c L.constant k)⊆L.wires.toFinset :=
    (maskedConstant_wires_subset c L.constant k).trans (listed_subset L (by
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact early_mem L he hc
      · simp [FusedHalfPorts.wires,hq]))
  have ha := hconst L.a (by simp [FusedHalfPorts.early]) P
  have hj := hconst L.j (by simp [FusedHalfPorts.early]) D
  have hlp := hconst L.l (by simp [FusedHalfPorts.early]) P
  have hln := hconst L.l (by simp [FusedHalfPorts.early]) N
  have hmp := hconst L.m (by simp [FusedHalfPorts.early]) P
  have hmd := hconst L.m (by simp [FusedHalfPorts.early]) D
  have hmn := hconst L.m (by simp [FusedHalfPorts.early]) N
  simp only [fusedCorrectionWordLoad,wires_append,Finset.union_subset_iff]
  aesop

private theorem correctionApply_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) (P D N : Nat) :
    ECDSAAdd.wires (fusedCorrectionApply L.a L.j L.l L.m L.constant L.target
      (L.carry.take (L.target.length-1)) L.cin P D N)⊆L.wires.toFinset := by
  have hv := L.widths hw
  have hCR : L.constant.length=L.target.length := hv.2.2.1.trans hv.2.1.symm
  have hcarry : (L.carry.take (L.target.length-1)).length+1=L.target.length := by
    simp [hw.carry,hv.2.1]
  have hl := correctionWordLoad_constant_support L he P D N
  have ha := addInPlace_wires L.constant L.target
    (L.carry.take (L.target.length-1)) L.cin hCR hcarry
  have ha' : ECDSAAdd.wires (addInPlace L.constant L.target
      (L.carry.take (L.target.length-1)) L.cin)⊆L.wires.toFinset := by
    rw [ha]
    exact listed_subset L (by
      intro q hq
      simp only [List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|hq
      · simp [FusedHalfPorts.wires]
      rcases hq with hct|hk
      rcases hct with hc|ht
      · simp [FusedHalfPorts.wires,hc]
      · simp [FusedHalfPorts.wires,ht]
      · have hk' : q∈L.carry := List.mem_of_mem_take hk
        simp [FusedHalfPorts.wires,hk'])
  simp only [fusedCorrectionApply,wires_append,Finset.union_subset_iff]
  aesop

private theorem rawNormalize_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) (P : Nat) :
    ECDSAAdd.wires (fusedRawNormalize L.b L.h L.source L.target L.constant
      (L.carry.take (L.target.length-1)) L.carry L.cin P)⊆L.wires.toFinset := by
  have hv := L.widths hw
  have hST : L.source.length=L.target.length := hv.1.trans hv.2.1.symm
  have hCT : L.constant.length=L.target.length := hv.2.2.1.trans hv.2.1.symm
  have htaken : (L.carry.take (L.target.length-1)).length+1=L.target.length := by
    simp [hw.carry,hv.2.1]
  have hs := (signedWord_wires L.b L.source L.target
    (L.carry.take (L.target.length-1)) hST htaken).1
  have hcmp := (compareLt_wires none L.target L.constant L.carry L.cin L.h
    hCT.symm (hw.carry.trans hv.2.2.1.symm)).2 P
  have hs' : ECDSAAdd.wires (signedAdd L.b L.source L.target
      (L.carry.take (L.target.length-1)))⊆L.wires.toFinset := by
    rw [hs]
    exact listed_subset L (by
      intro q hq
      simp only [List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|hq
      · simp [FusedHalfPorts.wires]
      rcases hq with hst|hc
      rcases hst with hs|ht
      · simp [FusedHalfPorts.wires,hs]
      · simp [FusedHalfPorts.wires,ht]
      · have hc' : q∈L.carry := List.mem_of_mem_take hc
        simp [FusedHalfPorts.wires,hc'])
  have hcmp' : ECDSAAdd.wires (compareLtConst none L.target L.constant L.carry
      L.cin L.h P)⊆L.wires.toFinset := by
    rw [hcmp]
    exact listed_subset L (by
      intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|hq
      · exact early_mem L he (by simp [FusedHalfPorts.early])
      rcases hq with rfl|hq
      · simp [FusedHalfPorts.wires]
      rcases hq with htc|hk
      rcases htc with ht|hc
      · simp [FusedHalfPorts.wires,ht]
      · simp [FusedHalfPorts.wires,hc]
      · simp [FusedHalfPorts.wires,hk])
  have hx : ECDSAAdd.wires [.X L.h]⊆L.wires.toFinset := by
    intro q hq
    have heq : q=L.h := by simpa [ECDSAAdd.wires,Instr.wires] using hq
    subst q
    exact List.mem_toFinset.mpr (early_mem L he (by simp [FusedHalfPorts.early]))
  simp only [fusedRawNormalize,wires_append,Finset.union_subset_iff]
  aesop

theorem correctionFlagsErase_support (L : FusedHalfPorts)
    (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedCorrectionFlagsErase L.b L.a L.h L.j L.l L.m)⊆
      L.wires.toFinset := by
  intro q hq
  simp only [fusedCorrectionFlagsErase,wires_append,Finset.mem_union] at hq
  rcases hq with (h1|h2)|h3
  · have hh := eraseMask_wires_subset L.a [L.j] [L.m] h1
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl
    all_goals exact List.mem_toFinset.mpr (early_mem L he (by simp [FusedHalfPorts.early]))
  · have hh := eraseMask_wires_subset L.a [L.h] [L.l] h2
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl
    all_goals exact List.mem_toFinset.mpr (early_mem L he (by simp [FusedHalfPorts.early]))
  · have hh := eraseMask_wires_subset L.b [L.h] [L.j] h3
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl
    · simp [FusedHalfPorts.wires]
    all_goals exact List.mem_toFinset.mpr (early_mem L he (by simp [FusedHalfPorts.early]))

private theorem evenHalf_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) (P : Nat) :
    ECDSAAdd.wires (fusedEvenHalf L.b L.a L.h L.j L.l L.m L.constant L.target
      (L.carry.take (L.target.length-1)) L.cin P)⊆L.wires.toFinset := by
  have ha := correctionApply_support L hw he P (2*P) (2^L.target.length-P)
  have hf := correctionFlagsErase_support L he
  have hr := (rotate_wires L.target).1
  have hr' : ECDSAAdd.wires (rotateRight L.target)⊆L.wires.toFinset := by
    rw [hr]
    split
    · exact Finset.empty_subset _
    · exact listed_subset L (by intro q hq; simp [FusedHalfPorts.wires,hq])
  simp only [fusedEvenHalf,wires_append,Finset.union_subset_iff]
  aesop

private theorem front_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) (P : Nat) :
    ECDSAAdd.wires (fusedSignedHalfFront L.b L.cin L.low L.hOut
      L.a L.h L.j L.l L.m L.source L.target L.constant L.carry P)⊆
      L.wires.toFinset := by
  have hr := rawNormalize_support L hw he P
  have hh := evenHalf_support L hw he P
  have hlow : L.low∈L.target := by simp [FusedHalfPorts.target,FusedHalfPorts.targetLow]
  have hcx : ECDSAAdd.wires [.CX L.low L.a]⊆L.wires.toFinset := by
    intro q hq
    simp only [ECDSAAdd.wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with (rfl|rfl)|hfalse
    · exact List.mem_toFinset.mpr (by simp [FusedHalfPorts.wires,hlow])
    · exact List.mem_toFinset.mpr (early_mem L he (by simp [FusedHalfPorts.early]))
    · simp at hfalse
  have hseed : ECDSAAdd.wires (fusedCorrectionFlagsSeed L.hOut L.a L.h
      L.j L.l L.m)⊆L.wires.toFinset := by
    intro q hq
    simp only [fusedCorrectionFlagsSeed,ECDSAAdd.wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq
    have hout : L.hOut∈L.wires := by simp [FusedHalfPorts.wires,FusedHalfPorts.target]
    have ha : L.a∈L.wires := early_mem L he (by simp [FusedHalfPorts.early])
    have hh' : L.h∈L.wires := early_mem L he (by simp [FusedHalfPorts.early])
    have hj : L.j∈L.wires := early_mem L he (by simp [FusedHalfPorts.early])
    have hl : L.l∈L.wires := early_mem L he (by simp [FusedHalfPorts.early])
    have hm : L.m∈L.wires := early_mem L he (by simp [FusedHalfPorts.early])
    simp only [List.mem_toFinset]
    aesop
  simp only [fusedSignedHalfFront,wires_append,Finset.union_subset_iff]
  aesop

theorem move_support (L : FusedHalfPorts) (he : L.early.Sublist L.A) :
    ECDSAAdd.wires (fusedFlagsMove L.a L.h L.qOut L.hOut)⊆L.wires.toFinset := by
  intro q hq
  simp only [fusedFlagsMove,swapBits,ECDSAAdd.wires,Instr.wires,wires_append,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq
  have ha : L.a∈L.wires := early_mem L he (by simp [FusedHalfPorts.early])
  have hh : L.h∈L.wires := early_mem L he (by simp [FusedHalfPorts.early])
  have hq' : L.qOut∈L.wires := by simp [FusedHalfPorts.wires,FusedHalfPorts.target]
  have ho : L.hOut∈L.wires := by simp [FusedHalfPorts.wires,FusedHalfPorts.target]
  simp only [List.mem_toFinset]
  aesop

private theorem thresholdFlags_support (L : FusedHalfPorts) :
    ECDSAAdd.wires (fusedThresholdFlagsSeed L.b L.qOut L.e L.t L.d)⊆L.wires.toFinset ∧
    ECDSAAdd.wires (fusedThresholdFlagsErase L.b L.qOut L.e L.t L.d)⊆L.wires.toFinset := by
  have all (q : Wire) (hq : q∈[L.b,L.qOut,L.e,L.t,L.d]) : q∈L.wires := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl
    · simp [FusedHalfPorts.wires]
    · simp [FusedHalfPorts.wires,FusedHalfPorts.target]
    · simp [FusedHalfPorts.wires,FusedHalfPorts.source]
    all_goals simp [FusedHalfPorts.wires,FusedHalfPorts.constant]
  constructor
  · intro q hq
    simp only [fusedThresholdFlagsSeed,fusedThresholdToggle,ECDSAAdd.wires,
      Instr.wires,wires_append,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq
    apply List.mem_toFinset.mpr
    apply all q
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    aesop
  · intro q hq
    simp only [fusedThresholdFlagsErase,wires_append,Finset.mem_union] at hq
    rcases hq with ((h1|ht1)|h2)|ht2
    · have hh := eraseMask_wires_subset L.b [L.qOut] [L.t] h1
      apply List.mem_toFinset.mpr
      apply all q
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh ⊢
      rcases hh with rfl|rfl|rfl <;> simp
    · simp [fusedThresholdToggle,ECDSAAdd.wires,Instr.wires] at ht1
      apply List.mem_toFinset.mpr
      exact all q (by simp only [List.mem_cons,List.not_mem_nil,or_false]; aesop)
    · have hh := eraseMask_wires_subset L.qOut [L.e] [L.d] h2
      apply List.mem_toFinset.mpr
      apply all q
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh ⊢
      rcases hh with rfl|rfl|rfl <;> simp
    · simp [fusedThresholdToggle,ECDSAAdd.wires,Instr.wires] at ht2
      apply List.mem_toFinset.mpr
      exact all q (by simp only [List.mem_cons,List.not_mem_nil,or_false]; aesop)

private theorem thresholdRecover_support (L : FusedHalfPorts) (hw : L.Widths) :
    ECDSAAdd.wires (fusedRetainedThresholdRecover L.b L.qOut L.t L.d L.hOut
      L.targetLow L.A L.C ((L.carry.take L.A.length).take (L.targetLow.length-1))
      L.cin (FusedSignedHalf.halfThreshold p) (p+1))⊆L.wires.toFinset := by
  have hv := L.widths hw
  have hload := thresholdWordLoad_support L (FusedSignedHalf.halfThreshold p) (p+1)
  have hadd := retainedAdd_support_ports L
  have hcmp0 := (compareLt_wires none L.targetLow L.A L.C L.cin L.hOut
    hv.2.2.2.2 hw.constant).1
  have hcmp : ECDSAAdd.wires (compareLt none L.targetLow L.A L.C L.cin L.hOut)⊆
      L.wires.toFinset := by
    rw [hcmp0]
    exact listed_subset L (by
      intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|hq
      · simp [FusedHalfPorts.wires,FusedHalfPorts.target]
      rcases hq with rfl|hq
      · simp [FusedHalfPorts.wires]
      rcases hq with hta|hc
      rcases hta with ht|ha
      · have ht' : q∈L.target := by simp [FusedHalfPorts.target,ht]
        simp [FusedHalfPorts.wires,ht']
      · simp [FusedHalfPorts.wires,ha]
      · exact constant_mem L hc)
  have hcx : ECDSAAdd.wires [.CX L.b L.hOut]⊆L.wires.toFinset := by
    intro q hq
    have hm : q=L.b∨q=L.hOut := by simpa [ECDSAAdd.wires,Instr.wires] using hq
    rcases hm with rfl|rfl
    · simp [FusedHalfPorts.wires]
    · simp [FusedHalfPorts.wires,FusedHalfPorts.target]
  simp only [fusedRetainedThresholdRecover,fusedRetainedThresholdCore,wires_append,
    Finset.union_subset_iff]
  aesop

private theorem parityClear_support (L : FusedHalfPorts) (hw : L.Widths) :
    ECDSAAdd.wires (fusedHalfParityClear L.targetLow L.C
      (L.carry.take L.A.length) L.cin L.qOut)⊆L.wires.toFinset := by
  have hv := L.widths hw
  have hxt : (L.targetLow.drop 3).length=
      (L.C.take (L.targetLow.length-3)).length := by simp [hv.2.2.2.2,hw.constant]
  have hct : ((L.carry.take L.A.length).take (L.targetLow.length-3)).length=
      (L.C.take (L.targetLow.length-3)).length := by
    simp [hv.2.2.2.2,hw.constant,hw.carry]
  have hcmp0 := (compareLt_wires none (L.targetLow.drop 3)
    (L.C.take (L.targetLow.length-3))
    ((L.carry.take L.A.length).take (L.targetLow.length-3))
    L.cin L.qOut hxt hct).2 (FusedSignedHalf.halfThreshold p/8)
  have hcmp : ECDSAAdd.wires (compareLtMultipleEight L.targetLow L.C
      (L.carry.take L.A.length) L.cin L.qOut (FusedSignedHalf.halfThreshold p))⊆
      L.wires.toFinset := by
    rw [compareLtMultipleEight,hcmp0]
    exact listed_subset L (by
      intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
      rcases hq with rfl|hq
      · simp [FusedHalfPorts.wires,FusedHalfPorts.target]
      rcases hq with rfl|hq
      · simp [FusedHalfPorts.wires]
      rcases hq with hxy|hk
      rcases hxy with hx|hy
      · have hx' : q∈L.targetLow := List.mem_of_mem_drop hx
        have hx'' : q∈L.target := by simp [FusedHalfPorts.target,hx']
        simp [FusedHalfPorts.wires,hx'']
      · exact constant_mem L (List.mem_of_mem_take hy)
      · have hk' : q∈L.carry :=
          List.mem_of_mem_take (List.mem_of_mem_take hk)
        simp [FusedHalfPorts.wires,hk'])
  have hx : ECDSAAdd.wires [.X L.qOut]⊆L.wires.toFinset := by
    intro q hq
    have heq : q=L.qOut := by simpa [ECDSAAdd.wires,Instr.wires] using hq
    subst q
    simp [FusedHalfPorts.wires,FusedHalfPorts.target]
  simp only [fusedHalfParityClear,wires_append,Finset.union_subset_iff]
  exact ⟨hcmp,hx⟩

theorem retainedBack_support (L : FusedHalfPorts) (hw : L.Widths) :
    ECDSAAdd.wires (fusedSignedHalfRetainedBack L.b L.cin L.qOut L.hOut
      L.t L.d L.e L.sourceHalf L.targetLow L.A L.C (L.carry.take L.A.length))⊆
      L.wires.toFinset := by
  have hf := thresholdFlags_support L
  have hp := prepare_support L hw
  have hr := thresholdRecover_support L hw
  have hq := parityClear_support L hw
  simp only [fusedSignedHalfRetainedBack,wires_append,Finset.union_subset_iff]
  aesop

theorem retained_support (L : FusedHalfPorts) (hw : L.Widths)
    (he : L.early.Sublist L.A) :
    ECDSAAdd.wires L.retainedProgram⊆L.wires.toFinset := by
  have hf := front_support L hw he p
  have hm := move_support L he
  have hb := retainedBack_support L hw
  simp only [retainedProgram,wires_append,Finset.union_subset_iff]
  aesop

end FusedHalfPorts

end ECDSAAdd.Arithmetic
