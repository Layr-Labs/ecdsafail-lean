import ECDSAAdd.Arithmetic.LiteralConstPhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum
theorem balancedConverters_physical (L : BalancedConvert.Layout) (hn : L.wires.Nodup) :
    GatePhysical (BalancedConvert.center L) ∧ GatePhysical (BalancedConvert.canonical L) := by
  have nd : (L.cin::L.word++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [BalancedConvert.Layout.wires,BalancedConvert.Layout.word,
      List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have src : ∀ b∈BalancedConvert.correction L,∀q∈b.wire,q∉L.cin::L.word++L.carry := by
    intro b hb q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    dsimp only at hq
    split at hq
    · have eq : q=L.flag := by simpa [eq_comm] using hq
      subst q
      intro hm
      have h := List.nodup_iff_count.mp hn L.flag
      have hp := List.count_pos_iff.mpr hm
      simp only [BalancedConvert.Layout.wires,BalancedConvert.Layout.word,
        List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h hp
      omega
    · simp at hq
  have mf : L.msb≠L.flag := by
    intro eq
    have h := List.nodup_iff_count.mp hn L.flag
    simp only [BalancedConvert.Layout.wires,eq,List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have cx : GatePhysical [.CX L.msb L.flag] := by simp [GatePhysical,PhysicalInstr,ProperGate,mf]
  have a := literalAdd_physical L.word L.carry L.cin L.one BalancedConvert.bias nd
  have b := literalAdd_physical L.word L.carry L.cin L.one BalancedConvert.inverseBias nd
  have ma := mappedAdd_physical _ _ _ _ nd src
  have nt := notRegister_physical L.word
  have ms : GatePhysical (mappedSub (BalancedConvert.correction L) L.word L.carry L.cin) := by
    simpa only [mappedSub,gatePhysical_append] using And.intro (And.intro nt ma) nt
  have pred : GatePhysical (BalancedConvert.predicate L) := by
    simpa only [BalancedConvert.predicate,gatePhysical_append] using And.intro (And.intro a cx) b
  simp only [BalancedConvert.center,BalancedConvert.canonical,gatePhysical_append]
  exact ⟨⟨⟨pred,ma⟩,cx⟩,⟨⟨cx,ms⟩,pred⟩⟩
end ECDSAAdd.Arithmetic
