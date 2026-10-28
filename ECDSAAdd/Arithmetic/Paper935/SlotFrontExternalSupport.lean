import ECDSAAdd.Arithmetic.Paper935.SlotFrontLocality
import ECDSAAdd.Arithmetic.Paper935.WindowPaddingSupport

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps

/-- The emitted front and its actual inverse never address a pre-owned external wire. -/
theorem SlotFront.Compiled.external_support (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (compiled : P.Compiled A b addWidth exitWidth F)
    (counterNonempty : F.counter≠[]) (coefficientNonempty : P.exitBank.fv.payload≠[])
    (q : Wire) (owned : q∈A.live) (noMeta : q∉F.wires) (noRows : q∉b.rows.flatMap WindowRow.wires) :
    q∈P.exitArena.live ∧ q∉P.exitBank.rows.flatMap WindowRow.wires ∧
      q∉wires (P.program F) ∧ q∉wires (P.inverse F) := by
  have pad := compileBankResize_external A P.addArena b P.addBank addWidth P.padding compiled.padding
    ⟨false,fun _ => false⟩ [] q owned noRows
  have route := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout compiled.routed
  have beforeEq := route.2.1
  obtain ⟨qeq,beq,ueq,keq,aeq⟩ := route.2.2
  have noBefore : q∉P.layout.before.rows.flatMap WindowRow.wires := by rw [beforeEq]; exact pad.2.1
  have noAfter : q∉P.layout.after.rows.flatMap WindowRow.wires := by simpa only [P.layout.rows_membership] using noBefore
  have resized := compileBankResize_external P.addArena P.exitArena P.layout.after P.exitBank exitWidth
    P.resizing compiled.resizing ⟨false,fun _ => false⟩ [] q pad.1 noAfter
  have hz : 1≤F.counter.length := by cases he : F.counter <;> simp_all
  have scratch := planCounterScratch_contract P.exitArena P.counterArena F.counter.length P.zero P.carry hz compiled.counter
  have reserve := (P.exitArena.reserve_success (P.zero++P.carry).toFinset).mp ⟨P.counterArena,scratch.2.2.2⟩
  have noWork : q∉P.zero++P.carry := fun hq => Finset.disjoint_left.mp reserve.2 resized.1 (List.mem_toFinset.mpr hq)
  have noCounter : q∉F.counter := fun hq => noMeta (by simp [SlotRegisters.wires,hq])
  have signMem : F.counter.getLastD 0∈F.counter := by
    have hc := List.dropLast_concat_getLast counterNonempty
    have last : F.counter.getLastD 0=F.counter.getLast counterNonempty := by
      conv_lhs => rw [←hc]
      exact List.getLastD_concat
    rw [last]
    exact List.getLast_mem counterNonempty
  have noSign : q≠F.counter.getLastD 0 := fun he => noCounter (he ▸ signMem)
  have metaAway : q≠F.active ∧ q≠F.swap ∧ q≠F.parity ∧ q≠F.work0 ∧ q≠F.work1 ∧ q≠F.frozen := by
    simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at noMeta
    clear * - noMeta
    tauto
  have noGlow : q≠P.layout.glow := by
    intro he
    apply noBefore
    simp [RoutedBankLayout.before,WindowBank.rows,WindowRow.wires,he]
  have noSecond : q≠P.exitBank.fv.second := by
    intro he
    apply resized.2.1
    have hs := WindowRow.second_mem P.exitBank.fv coefficientNonempty
    simp only [WindowBank.rows,List.flatMap_cons,List.flatMap_nil,List.mem_append,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr (Or.inl (he ▸ hs)))
  have noMint : q∉wires (P.layout.mintControls F.frozen (F.counter.getLastD 0)) := by
    intro hq
    have hm := P.layout.mintControls_support F.frozen (F.counter.getLastD 0) hq
    rw [aeq,beq,qeq] at hm
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hm
    clear * - hm metaAway noSign noGlow
    tauto
  have noRouted : q∉wires P.layout.program := by
    intro hq
    have hm := P.layout.program_support route.1 hq
    rw [qeq,beq,ueq,keq,aeq] at hm
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    clear * - hm metaAway noBefore
    tauto
  have noUpdate : q∉wires (counterUpdate P.layout.active P.layout.q P.zero F.counter P.carry) := by
    intro hq
    have hm := counterUpdate_wires_subset P.layout.active P.layout.q P.zero F.counter P.carry scratch.1 scratch.2.1 hq
    rw [aeq,qeq] at hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hm
    simp only [List.mem_append,not_or] at noWork
    clear * - hm metaAway noWork noCounter
    tauto
  have noErase : q∉wires (eraseAnd P.layout.active P.exitBank.fv.second P.layout.q) := by
    rw [aeq,qeq]
    simp [eraseAnd,wires,Instr.wires,correctionWires,metaAway.1,metaAway.2.1,noSecond]
  have noUnupdate : q∉wires (counterUpdateInverse P.layout.active P.layout.q P.zero F.counter P.carry) := by
    intro hq
    have hm := counterUpdateInverse_wires_subset P.layout.active P.layout.q P.zero F.counter P.carry scratch.1 scratch.2.1 hq
    rw [aeq,qeq] at hm
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hm
    simp only [List.mem_append,not_or] at noWork
    clear * - hm metaAway noWork noCounter
    tauto
  have noUnmint : q∉wires [.CCX P.layout.active P.exitBank.fv.second P.layout.q] := by
    rw [aeq,qeq]
    simp [wires,Instr.wires,metaAway.1,metaAway.2.1,noSecond]
  have noPad := b.padding_support_away P.addBank addWidth A P.addArena P.padding
    (compileBankResize_contract _ _ _ _ _ _ compiled.padding) q owned noRows
  have noResize := P.layout.after.padding_support_away P.exitBank exitWidth P.addArena P.exitArena P.resizing
    (compileBankResize_contract _ _ _ _ _ _ compiled.resizing) q pad.1 noAfter
  refine ⟨resized.1,resized.2.1,?_,?_⟩
  · simpa only [SlotFront.program,RoutedBankLayout.retiredWindow,RoutedBankLayout.taggedWindow,
      RoutedBankLayout.windowStep,wires_append,Finset.mem_union,not_or] using
      And.intro noPad (And.intro (And.intro noMint (And.intro noRouted (And.intro noResize noUpdate))) noErase)
  · simpa only [SlotFront.inverse,RoutedBankLayout.retiredWindowInverse,RoutedBankLayout.taggedWindowInverse,
      RoutedBankLayout.windowStepInverse,wires_append,wires_reverse,P.layout.inverse_wires,Finset.mem_union,not_or] using
      And.intro (And.intro noUnmint (And.intro (And.intro (And.intro noUnupdate noResize) noRouted) noMint)) noPad

end ECDSAAdd.Arithmetic.Paper935
