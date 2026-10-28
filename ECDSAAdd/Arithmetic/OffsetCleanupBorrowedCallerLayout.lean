import ECDSAAdd.Arithmetic.BalancedCleanupOffsetLayout
import ECDSAAdd.Arithmetic.BalancedSharedPorts

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller

/-- The current source guard at 765 remains live. The clean old Cout at
768 replaces that single site in the borrowed mask bank. -/
def carry (w : Nat → Wire) : List Wire := wireBlock w 512 253++[w 766,w 767,w 768]

/-- Cleanup does not emit any instruction on the inherited Minus/Plus
roles. Distinct existing history sites supply those descriptor-only roles.
The active Cout borrows the preserved canonical source extension at 1026. -/
def layout (w : Nat → Wire) (sign : Wire) : BalancedCleanupOffset.Layout :=
  { toCircuit := { balancedSharedPorts w sign with cout:=w 1026,minus:=w 0,plus:=w 1 },
    offsetCarry := carry w }

private def ids : List Nat :=
  [765,1026,0,1,1796,1797,1027,2311,1025,2056]++List.range' 2057 254++
    List.range' 770 255++List.range' 1540 256++List.range' 512 253++[766,767,768]

private theorem idsND : ids.Nodup := by decide

private theorem idsBound (i : Nat) (hi : i∈ids) : i < 2314 := by
  simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
  omega

theorem widths (w : Nat → Wire) (sign : Wire) : (layout w sign).Widths := by
  simp [BalancedCleanupOffset.Layout.Widths,BalancedCircuit.Layout.Widths,
    BalancedCleanup.Layout.Widths,layout,carry,balancedSharedPorts,wireBlock]

theorem cleanupLayout (w : Nat → Wire) (sign : Wire) :
    (layout w sign).toCircuit.toLayout=(balancedSharedPorts w sign).toLayout := rfl

theorem nodup (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (hs : sign∉skywalkSharedWires w) : (layout w sign).wires.Nodup := by
  have mapped : (ids.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (idsBound i hi) (idsBound j hj) he
    · exact idsND
  have outside : sign∉ids.map w := by
    intro hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    apply hs
    simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by have bound := idsBound i hi; omega,rfl⟩
  have all := List.nodup_cons.mpr ⟨outside,mapped⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp all q
  simp only [BalancedCleanupOffset.Layout.wires,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,layout,carry,balancedSharedPorts,ids,wireBlock,
    List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem declared_shared (w : Nat → Wire) (sign : Wire) :
    (layout w sign).wires ⊆ sign::skywalkSharedWires w := by
  intro q hq
  have view : q∈(layout w sign).wires ↔ q=sign ∨ q∈ids.map w := by
    simp only [BalancedCleanupOffset.Layout.wires,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,layout,carry,balancedSharedPorts,ids,wireBlock,
      List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  rcases view.mp hq with rfl|hm
  · simp
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    apply List.mem_cons_of_mem
    simp only [skywalkSharedWires,wireBlock,List.mem_map,List.mem_range'_1]
    exact ⟨i,by have bound := idsBound i hi; omega,rfl⟩

end ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller
#print axioms ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller.nodup
#print axioms ECDSAAdd.Arithmetic.OffsetCleanupBorrowedCaller.declared_shared
