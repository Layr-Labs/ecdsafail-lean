import ECDSAAdd.Arithmetic.BalancedCleanupOffsetLayout
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

theorem view_support (L : Layout) (hw : L.Widths) :
    wires (view L) ⊆ ([L.sign,L.lower]++L.r++L.y).toFinset := by
  have w := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have rr := (rotate_wires L.r).2
  have cs := signComplement_wires_subset L.sign L.y
  have cl := signComplement_wires_subset L.lower L.y
  intro q hq
  simp only [view,wires_append,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq
  · rw [rr,if_neg (by omega)] at hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.mem_toFinset,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · have h := cs hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · have h := cl hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    simp only [BalancedCleanup.Layout.y,List.mem_toFinset,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false]
    tauto

theorem view_parity_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.parity∉wires (view L) := by
  have flags := List.nodup_cons.mp (L.flagsND hn)
  have away := L.flagAway hn L.parity (by simp)
  intro h
  have m := view_support L hw h
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  have ns : L.parity≠L.sign := fun e => flags.1 (by simp [e])
  have nl : L.parity≠L.lower := fun e => flags.1 (by simp [e])
  have nr : L.parity∉L.r := fun h => away (by simp [h])
  have ny : L.parity∉L.y := fun h => away (by simp [h])
  tauto

/-- Actual offset heads and both measured carry corrections remain in a
declared finite pool. This generic proof imports no caller field program. -/
theorem chain_pool_support (bits : List MappedBit) (xs ys cs ds : List Wire)
    (ci cb t : Wire) (W : Finset Wire)
    (hbits : ∀q∈mappedWires bits,q∈W) (hx : ∀q∈xs,q∈W) (hy : ∀q∈ys,q∈W)
    (hc : ∀q∈cs,q∈W) (hd : ∀q∈ds,q∈W) (hci : ci∈W) (hcb : cb∈W) (ht : t∈W) :
    wires (chain bits xs ys cs ds ci cb t)⊆W := by
  induction bits generalizing xs ys cs ds ci cb with
  | nil =>
    cases xs <;> cases ys <;> cases cs <;> cases ds <;>
      simp [chain,flipBelow_wires,wires,Finset.subset_iff,hcb,ht]
  | cons b bits ih =>
    cases xs with
    | nil => simp [chain,wires]
    | cons a xs =>
      cases ys with
      | nil => simp [chain,wires]
      | cons y ys =>
        cases cs with
        | nil => simp [chain,wires]
        | cons c cs =>
          cases ds with
          | nil => simp [chain,wires]
          | cons d ds =>
            have ha := hx a (by simp)
            have hyy := hy y (by simp)
            have hcc := hc c (by simp)
            have hdd := hd d (by simp)
            have source (q : Wire) (hq : q∈b.wire.toList) : q∈W :=
              hbits q (List.mem_append_left _ hq)
            have headPool : (b.wire.toList++[y,ci,c]).toFinset⊆W := by
              intro q hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
              rcases hq with hq|rfl|rfl|rfl
              · exact source q hq
              · exact hyy
              · exact hci
              · exact hcc
            have sum : (b.wire.toList++[y,ci]).toFinset⊆W := by
              intro q hq
              apply headPool
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
              tauto
            have recurse := ih xs ys cs ds c d
              (fun q hq => hbits q (List.mem_append_right _ hq))
              (fun q hq => hx q (List.mem_cons_of_mem _ hq))
              (fun q hq => hy q (List.mem_cons_of_mem _ hq))
              (fun q hq => hc q (List.mem_cons_of_mem _ hq))
              (fun q hq => hd q (List.mem_cons_of_mem _ hq)) hcc hdd
            have small : wires (majority a y cb d)⊆W ∧ wires (eraseCarry a y cb d)⊆W ∧
                wires [.X y]⊆W := by
              simp [majority,eraseCarry,wires,Instr.wires,correctionWires,Finset.subset_iff,
                ha,hyy,hcb,hdd]
            have bit := mappedBit_wires b y ci c
            simp only [chain,wires_append,Finset.union_subset_iff,and_assoc]
            exact ⟨bit.1.trans headPool,bit.2.2.trans sum,small.2.2,small.1,recurse,
              small.2.1,small.2.2,bit.2.2.trans sum,bit.2.1.trans headPool⟩

/-- Static support of the original generic cleanup emission. This theorem
is independent of forward/inverse caller kernels and relabeling modules. -/
theorem program_support (L : Layout) (hw : L.Widths) : wires (program L)⊆L.wires.toFinset := by
  let W := L.wires.toFinset
  have member (q : Wire) : q∈W ↔
      q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry ∨ q∈L.offsetCarry := by
    simp [W,Layout.wires,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,or_assoc]
  have data (q : Wire) (h : q∈L.y++L.r++L.carry++L.offsetCarry) : q∈W := by
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rw [member]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have sg : wires (BalancedCleanup.prepareSign L.toCircuit.toLayout)⊆W := by
    have sc := signComplement_wires_subset L.lower L.r
    simp only [BalancedCleanup.prepareSign,wires_append,Finset.union_subset_iff]
    constructor
    · simp [wires,Instr.wires,Finset.subset_iff,member]
    · intro q hq
      have h := sc hq
      simp only [List.mem_toFinset,List.mem_cons] at h
      rcases h with rfl|h
      · simp [member]
      · exact data q (by simp [h])
  have vw : wires (view L)⊆W := by
    intro q hq
    have h := view_support L hw hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
    rcases h with rfl|rfl|h|h
    · simp [member]
    · simp [member]
    · exact data q (by simp [h])
    · exact data q (by simp [h])
  have ch := chain_pool_support (offsetBits L) L.y L.r L.offsetCarry L.carry L.one L.cout L.parity W
    (fun q hq => by rw [offsetSources L q hq]; simp [member])
    (fun q hq => data q (by simp [hq])) (fun q hq => data q (by simp [hq]))
    (fun q hq => data q (by simp [hq])) (fun q hq => data q (by simp [hq]))
    (by simp [member]) (by simp [member]) (by simp [member])
  have cout : wires [.X L.cout]⊆W := by simp [wires,Instr.wires,Finset.subset_iff,member]
  simp only [program,wires_append,wires_reverse,Finset.union_subset_iff,and_assoc]
  exact ⟨sg,vw,cout,ch,cout,vw,sg⟩

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.view_support
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.view_parity_away
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.program_support
