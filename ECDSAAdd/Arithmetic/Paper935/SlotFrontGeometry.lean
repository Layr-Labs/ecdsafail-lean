import ECDSAAdd.Arithmetic.Paper935.SlotFrontTotal

namespace ECDSAAdd.Arithmetic.Paper935

private theorem last_mem (xs : List Wire) (nonempty : xs≠[]) : xs.getLastD 0∈xs := by
  have hc := List.dropLast_concat_getLast nonempty
  have last : xs.getLastD 0=xs.getLast nonempty := by
    conv_lhs => rw [←hc]
    exact List.getLastD_concat
  rw [last]
  exact List.getLast_mem nonempty

/-- The front's public gate/address checks follow from ordinary register and
row ownership at its two allocation boundaries and the real counter borrow. -/
theorem SlotFront.Compiled.checks_of_geometry (P : SlotFront) (A : Arena) (b : WindowBank)
    (addWidth exitWidth : RowWindow) (F : SlotRegisters) (compiled : P.Compiled A b addWidth exitWidth F)
    (counterNonempty : F.counter≠[])
    (addDistinct : (F.wires++P.addBank.rows.flatMap WindowRow.wires).Nodup)
    (addOwned : (F.wires++P.addBank.rows.flatMap WindowRow.wires).toFinset⊆P.addArena.live)
    (exitDistinct : (F.wires++P.exitBank.rows.flatMap WindowRow.wires).Nodup)
    (exitOwned : (F.wires++P.exitBank.rows.flatMap WindowRow.wires).toFinset⊆P.exitArena.live)
    (coefficientNonempty : P.exitBank.fv.payload≠[]) : P.PhysicalChecks F := by
  have route := compileRoutedBank_contract F.swap F.parity F.work0 F.work1 F.active P.addBank P.layout compiled.routed
  have beforeEq := route.2.1
  have ids := route.2.2
  have hz : 1≤F.counter.length := by cases hc : F.counter <;> simp_all
  have signMem := last_mem F.counter counterNonempty
  have addGeometry : (F.wires++P.layout.before.rows.flatMap WindowRow.wires).Nodup := by rw [beforeEq]; exact addDistinct
  have addBound : (F.wires++P.layout.before.rows.flatMap WindowRow.wires).toFinset⊆arenaWires := by
    rw [beforeEq]
    exact addOwned.trans P.addArena.bounded
  have exitBound := exitOwned.trans P.exitArena.bounded
  have counterDistinct : (F.active::F.swap::F.counter).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp exitDistinct q
    simp only [SlotRegisters.wires,List.count_append,List.count_cons,List.count_nil] at hc ⊢
    omega
  have counterOwned : (F.active::F.swap::F.counter).toFinset⊆P.exitArena.live := by
    intro q hq
    apply exitOwned
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SlotRegisters.wires,List.not_mem_nil,or_false] at hq ⊢
    clear route compiled addDistinct addOwned exitDistinct addGeometry addBound exitBound counterDistinct
    tauto
  have counterLayout := planCounterScratch_nodup P.exitArena P.counterArena F.active F.swap F.counter P.zero P.carry
    hz counterDistinct counterOwned compiled.counter
  have counterContract := planCounterScratch_contract P.exitArena P.counterArena F.counter.length P.zero P.carry hz compiled.counter
  have reserved := (P.exitArena.reserve_success (P.zero++P.carry).toFinset).mp ⟨P.counterArena,counterContract.2.2.2⟩
  have counterBound : (F.active::F.swap::(P.zero++F.counter++P.carry)).toFinset⊆arenaWires := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|((hq|hq)|hq)
    · exact P.exitArena.bounded (counterOwned (by simp))
    · exact P.exitArena.bounded (counterOwned (by simp))
    · exact reserved.1 (by simp [hq])
    · exact P.exitArena.bounded (counterOwned (by simp [hq]))
    · exact reserved.1 (by simp [hq])
  have tag : [F.counter.getLastD 0,P.layout.glow,F.parity,F.swap].Nodup := by
    have key : (F.parity::F.swap::P.layout.glow::F.counter).Nodup := by
      apply List.nodup_iff_count.mpr
      intro q
      have hc := List.nodup_iff_count.mp addGeometry q
      simp only [SlotRegisters.wires,RoutedBankLayout.before,WindowBank.rows,WindowRow.wires,
        List.flatMap_cons,List.flatMap_nil,List.count_append,List.count_cons,List.count_nil] at hc ⊢
      omega
    have selected : [F.parity,F.swap,P.layout.glow,F.counter.getLastD 0].Nodup :=
      List.Pairwise.sublist (by simp only [List.cons_sublist_cons]; exact List.singleton_sublist.mpr signMem) key
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp selected q
    simp only [List.count_cons,List.count_nil] at hc ⊢
    omega
  have frozenActive : F.frozen≠F.active := by
    clear route compiled addGeometry
    simp_all [SlotRegisters.wires,List.nodup_append',List.disjoint_append_right]
  have secondMem : P.exitBank.fv.second∈P.exitBank.fv.wires := P.exitBank.fv.second_mem coefficientNonempty
  have secondSwap : P.exitBank.fv.second≠F.swap := by
    have separated : F.swap∉P.exitBank.fv.wires := by
      clear route compiled addGeometry tag
      simp_all [SlotRegisters.wires,WindowBank.rows,List.nodup_append',List.disjoint_append_right]
    exact fun he => separated (he ▸ secondMem)
  have metadataBound (q : Wire) (hq : q∈F.wires) : q∈arenaWires :=
    addBound (List.mem_toFinset.mpr (List.mem_append_left _ hq))
  have glowBound : P.layout.glow∈arenaWires := by
    apply addBound
    simp [RoutedBankLayout.before,WindowBank.rows,WindowRow.wires]
  have secondBound : P.exitBank.fv.second∈arenaWires := by
    apply exitBound
    simp [WindowBank.rows,secondMem]
  unfold SlotFront.PhysicalChecks
  dsimp only
  rw [ids.1,ids.2.1,ids.2.2.1,ids.2.2.2.1,ids.2.2.2.2]
  refine ⟨hz,counterLayout,tag,frozenActive,secondSwap,?_,?_,?_,counterBound,?_⟩
  all_goals intro q hq
  all_goals simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,WindowRow.wires] at hq
  · apply addBound
    simp only [SlotRegisters.wires,RoutedBankLayout.before,WindowBank.rows,WindowRow.wires,
      List.flatMap_cons,List.flatMap_nil,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    clear route compiled addDistinct addOwned exitDistinct exitOwned addGeometry counterLayout counterContract reserved tag
    clear beforeEq ids hz signMem counterDistinct counterOwned counterBound frozenActive secondMem secondSwap exitBound counterNonempty coefficientNonempty addBound metadataBound glowBound secondBound
    tauto
  · apply addBound
    simp only [SlotRegisters.wires,RoutedBankLayout.before,WindowBank.rows,WindowRow.wires,
      List.flatMap_cons,List.flatMap_nil,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    clear route compiled addDistinct addOwned exitDistinct exitOwned addGeometry counterLayout counterContract reserved tag
    clear beforeEq ids hz signMem counterDistinct counterOwned counterBound frozenActive secondMem secondSwap exitBound counterNonempty coefficientNonempty addBound metadataBound glowBound secondBound
    tauto
  · apply addBound
    simp only [SlotRegisters.wires,RoutedBankLayout.before,WindowBank.rows,WindowRow.wires,
      List.flatMap_cons,List.flatMap_nil,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    clear route compiled addDistinct addOwned exitDistinct exitOwned addGeometry counterLayout counterContract reserved tag
    clear beforeEq ids hz signMem counterDistinct counterOwned counterBound frozenActive secondMem secondSwap exitBound counterNonempty coefficientNonempty addBound metadataBound glowBound secondBound
    tauto
  · rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact metadataBound _ (by simp [SlotRegisters.wires])
    · exact metadataBound _ (by simp [SlotRegisters.wires])
    · exact metadataBound _ (List.mem_append_left _ (List.mem_append_right _ signMem))
    · exact glowBound
    · exact metadataBound _ (by simp [SlotRegisters.wires])
    · exact metadataBound _ (by simp [SlotRegisters.wires])
    · exact secondBound

end ECDSAAdd.Arithmetic.Paper935
