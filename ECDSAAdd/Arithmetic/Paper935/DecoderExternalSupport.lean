import ECDSAAdd.Arithmetic.Paper935.SlotDecoderResources
import ECDSAAdd.Arithmetic.Paper935.WindowPaddingSupport
import ECDSAAdd.Arithmetic.Paper935.WindowRowsLocality

namespace ECDSAAdd.Arithmetic.Paper935

private theorem zip_away (xs ws : List Wire) (q : Wire) (hx : q∉xs) (hw : q∉ws) :
    q∉(List.zipWith ZeroBit.mk xs ws).flatMap ZeroBit.wires := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    cases ws with
    | nil => simp
    | cons w ws =>
      simp only [List.mem_cons,not_or] at hx hw
      simpa only [List.zipWith_cons_cons,List.flatMap_cons,ZeroBit.wires,List.cons_append,List.nil_append,
        List.mem_cons,not_or] using And.intro hx.1 (And.intro hw.1 (ih ws hx.2 hw.2))

/-- All depth stages use only their supplied input and shared scratch lists. -/
theorem compileBorrowedDepths_external_support (A D : Arena) (one frozen output : Wire)
    (z f v work : List Wire) (layouts : List DepthLayout)
    (h : compileBorrowedDepths A one frozen output z f v=some (D,work,layouts))
    (p : Int) (q : Wire) (owned : q∈A.live)
    (away : q∉one::frozen::output::(z++f++v)) :
    q∉wires (finiteDepthProgram layouts p) := by
  have pair := compileBorrowedDepths_contract A D one frozen output z f v work layouts h
  have hv := (A.reserve_success work.toFinset).mp ⟨D,(A.borrowMany_contract D _ work pair.1).2.2⟩
  have noWork : q∉work := fun hq => Finset.disjoint_left.mp hv.2 owned (List.mem_toFinset.mpr hq)
  have each : ∀ L∈layouts,q∉wires (L.program p) := by
    intro L hl hq
    obtain ⟨d,_,hc⟩ := compileBorrowedDepths_member A D one frozen output z f v work layouts h L hl
    have hd := (compileBorrowedDepth_contract A D one frozen output z f v work d L hc).2
    have hm := compileDepth_program_support one frozen output z f v work d L hd p hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hm away
    clear * - hm away noWork
    tauto
  clear h pair hv
  induction layouts with
  | nil => simp [finiteDepthProgram,wires]
  | cons L ls ih =>
    change q∉wires (L.program p++finiteDepthProgram ls p)
    simpa only [wires_append,Finset.mem_union,not_or] using
      And.intro (each L (by simp)) (ih (by intro K hk; exact each K (by simp [hk])))

/-- The actual decoder cannot borrow or address a pre-owned external wire. -/
theorem compileSlotDecoder_external_support (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D) (port : Q.history.port=F.parity)
    (p : Int) (index : Nat) (q : Wire) (owned : q∈Q.historyArena.live)
    (noMeta : q∉F.wires) (noRows : q∉Q.slot.front.exitBank.rows.flatMap WindowRow.wires) :
    q∉wires (D.program F Q p index) := by
  have hc := compileSlotDecoder_contract F Q D compiled
  have pad := compileBankResize_external _ _ _ _ _ _ hc.1 ⟨false,fun _ => false⟩ [] q owned noRows
  have noPad := Q.slot.front.exitBank.padding_support_away _ _ _ _ _
    (compileBankResize_contract _ _ _ _ _ _ hc.1) q owned noRows
  have borrow := (compileBorrowedDepths_contract _ _ _ _ _ _ _ _ _ _ hc.2).1
  have hv := (D.paddedArena.reserve_success D.work.toFinset).mp
    ⟨D.borrowedArena,(D.paddedArena.borrowMany_contract _ _ _ borrow).2.2⟩
  have noWork : q∉D.work := fun hq => Finset.disjoint_left.mp hv.2 pad.1 (List.mem_toFinset.mpr hq)
  have noF : q∉D.bank.f.wires := fun hq => pad.2.1 (by simp [WindowBank.rows,hq])
  have noV : q∉D.bank.fv.wires := fun hq => pad.2.1 (by simp [WindowBank.rows,hq])
  have noDepth := compileBorrowedDepths_external_support _ _ _ _ _ _ _ _ _ _ hc.2 p q pad.1 (by
    simp only [port,SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at noMeta ⊢
    clear * - noMeta noF noV
    tauto)
  have widths := compileBankResize_widths _ _ _ _ _ _ hc.1
  have len : 1<D.bank.fv.wires.length := by
    have h := widths.2.2.1
    simp only [WindowBank.decoderWidth] at h
    simp only [WindowRow.wires,List.length_append,List.length_singleton]
    omega
  have secondMem : D.bank.fv.wires.getD 1 0∈D.bank.fv.wires := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem len,Option.getD_some]
    exact List.getElem_mem len
  have noSecond : q≠D.bank.fv.wires.getD 1 0 := fun he => noV (he ▸ secondMem)
  have noOffset : q∉F.offset := fun hq => noMeta (by simp [SlotRegisters.wires,hq])
  have noZip := zip_away F.offset D.work q noOffset noWork
  let controls := (F.frozen::F.work0::F.work1::D.bank.fv.wires.getD 1 0::F.swap::Q.history.port::
    (List.zipWith ZeroBit.mk F.offset D.work).flatMap ZeroBit.wires).toFinset
  have noControls : q∉controls := by
    simp only [controls,List.mem_toFinset,List.mem_cons,port]
    simp only [SlotRegisters.wires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at noMeta
    clear * - noMeta noSecond noZip
    tauto
  have support := paddedCleanBranch_support D.padding D.layouts p F.frozen F.work0 F.work1
    (D.bank.fv.wires.getD 1 0) F.swap Q.history.port (List.zipWith ZeroBit.mk F.offset D.work)
    (decoderOffset index) (wires D.padding ∪ wires (finiteDepthProgram D.layouts p) ∪ controls)
    (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h))
    (fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h))
    (fun _ h => Finset.mem_union_right _ h)
  intro hq
  have hm := support hq
  simp only [Finset.mem_union] at hm
  exact hm.elim (fun hh => hh.elim noPad noDepth) noControls

theorem actualHistoryDecoder_external_support (F : SlotRegisters) (Q : HistoricalSlot)
    (port : Q.history.port=F.parity) (p : Int) (index : Nat) (q : Wire)
    (owned : q∈Q.historyArena.live) (noMeta : q∉F.wires)
    (noRows : q∉Q.slot.front.exitBank.rows.flatMap WindowRow.wires) :
    q∉wires (actualHistoryDecoder F p index Q) := by
  cases h : compileSlotDecoder F Q with
  | none => simp [actualHistoryDecoder,h,wires]
  | some D =>
    rw [actualHistoryDecoder_of_compiled F Q D h]
    exact compileSlotDecoder_external_support F Q D h port p index q owned noMeta noRows

end ECDSAAdd.Arithmetic.Paper935
