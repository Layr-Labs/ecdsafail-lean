import ECDSAAdd.Arithmetic.BalancedCleanupOffsetProgram

set_option maxHeartbeats 600000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

theorem Layout.baseND (L : Layout) (hn : L.wires.Nodup) : L.toCircuit.wires.Nodup :=
  (List.nodup_append'.mp hn).1

theorem Layout.cleanupND (L : Layout) (hn : L.wires.Nodup) : L.toCircuit.toLayout.wires.Nodup :=
  (List.nodup_append'.mp (L.baseND hn)).2.1

theorem Layout.allND (L : Layout) (hn : L.wires.Nodup) :
    ([L.parity,L.sign,L.lower,L.one,L.sourceGuard,L.cout,L.minus,L.plus] ++
      (L.r++L.y++L.carry++L.offsetCarry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem Layout.flagsND (L : Layout) (hn : L.wires.Nodup) :
    [L.parity,L.sign,L.lower,L.one,L.sourceGuard,L.cout,L.minus,L.plus].Nodup :=
  (List.nodup_append'.mp (L.allND hn)).1

theorem Layout.flagAway (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.parity,L.sign,L.lower,L.one,L.sourceGuard,L.cout,L.minus,L.plus]) :
    q∉L.r++L.y++L.carry++L.offsetCarry :=
  fun h => List.disjoint_left.mp (List.nodup_append'.mp (L.allND hn)).2.2 hq h

theorem Layout.chainND (L : Layout) (hn : L.wires.Nodup) :
    (L.parity::L.one::L.cout::(L.y++L.r++L.offsetCarry++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.allND hn) q
  simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

/-- The only data-dependent offset bit is the already retained lower sign. -/
theorem offsetSources (L : Layout) (q : Wire) (hq : q∈mappedWires (offsetBits L)) :
    q=L.lower := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  by_cases h : i=1
  · simp only [if_pos h] at hq
    simpa using hq
  · simp only [if_neg h] at hq
    simp at hq

theorem offsetSources_away (L : Layout) (hn : L.wires.Nodup) :
    ∀q∈mappedWires (offsetBits L),q∉L.parity::L.one::L.cout::
      (L.y++L.r++L.offsetCarry++L.carry) := by
  intro q hq
  have eq := offsetSources L q hq
  subst q
  have flags := L.flagsND hn
  have away := L.flagAway hn L.lower (by simp)
  have f := List.nodup_iff_count.mp flags L.lower
  simp only [List.count_cons,List.count_nil] at f
  have np : L.lower≠L.parity := by intro e; simp [e] at f
  have no : L.lower≠L.one := by intro e; simp [e] at f; omega
  have nc : L.lower≠L.cout := by intro e; simp [e] at f; omega
  intro h
  simp only [List.mem_cons,List.mem_append,np,no,nc,false_or] at h
  exact away (by simpa only [List.mem_append,or_assoc,or_left_comm,or_comm] using h)

theorem view_proper (L : Layout) (hn : L.wires.Nodup) : ProperProgram (view L) := by
  have nd := L.cleanupND hn
  have full := BalancedCleanup.Layout.dataND L.toCircuit.toLayout nd
  have nr := (List.nodup_append'.mp full).1
  have sR : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lR : L.lower∉L.r := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  have sY : L.sign∉L.y := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have lY : L.lower∉L.y := fun h => L.flagAway hn L.lower (by simp) (by simp [h])
  simp only [view,properProgram_append]
  refine ⟨⟨⟨⟨BalancedCleanup.rotateLeft_proper _ nr,?_⟩,
    BalancedCleanup.complement_proper _ _ sY⟩,
    BalancedCleanup.complement_proper _ _ lY⟩,by simp [ProperProgram,ProperGate]⟩
  simp only [ProperProgram,ProperGate,List.mem_cons,List.not_mem_nil,or_false]
  have sr : L.sign≠L.r0 := fun e => sR (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  have lr : L.lower≠L.r0 := fun e => lR (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  intro i hi
  rcases hi with rfl|rfl|rfl
  · trivial
  · exact sr
  · exact lr

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.Layout.chainND
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.offsetSources_away
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.view_proper
