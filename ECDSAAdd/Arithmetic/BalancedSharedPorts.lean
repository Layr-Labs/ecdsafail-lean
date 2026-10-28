import ECDSAAdd.Arithmetic.BalancedFieldSupport
import ECDSAAdd.Arithmetic.BalancedCoreLayoutProof
import ECDSAAdd.Arithmetic.SkywalkShared

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- The balanced field port borrows terminal-zero mask and padding sites,
and the restored integer carry bank. It does not touch the seed bank. -/
def balancedSharedPorts (w : Nat → Wire) (sign : Wire) : BalancedCircuit.Layout :=
  { r0:=w 2056,rtail:=wireBlock w 2057 254,rmsb:=w 2311,
    ylow:=wireBlock w 770 255,ymsb:=w 1025,carry:=wireBlock w 1540 256,
    sign:=sign,parity:=w 1796,lower:=w 1797,one:=w 1027,
    sourceGuard:=w 765,cout:=w 768,minus:=w 767,plus:=w 766 }

def balancedSharedIds : List Nat :=
  [765,768,767,766,1796,1797,1027,2311,1025,2056]++
    List.range' 2057 254++List.range' 770 255++List.range' 1540 256

theorem balancedSharedIds_nodup : balancedSharedIds.Nodup := by decide

theorem balancedSharedIds_bound (j : Nat) (hj : j∈balancedSharedIds) : j<2314 := by
  simp only [balancedSharedIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega

theorem balancedSharedPorts_widths (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).Widths := by
  simp [BalancedCircuit.Layout.Widths,BalancedCleanup.Layout.Widths,
    balancedSharedPorts,wireBlock]

theorem balancedSharedPorts_nodup (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hs : sign∉balancedSharedIds.map w) :
    (balancedSharedPorts w sign).wires.Nodup := by
  have mapped : (balancedSharedIds.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (balancedSharedIds_bound i hi)
        (balancedSharedIds_bound j hj) he
    · exact balancedSharedIds_nodup
  have all : (sign::balancedSharedIds.map w).Nodup := List.nodup_cons.mpr ⟨hs,mapped⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp all q
  simp only [balancedSharedPorts,balancedSharedIds,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem balancedSharedPorts_y (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).y=wireBlock w 770 256 := by
  have a := wireBlock_append w 770 255 1
  have one : wireBlock w 1025 1=[w 1025] := by simp [wireBlock,List.range']
  change wireBlock w 770 255++[w 1025]=wireBlock w 770 256
  simpa only [Nat.reduceAdd,one] using a

theorem balancedSharedPorts_r (w : Nat → Wire) (sign : Wire) :
    (balancedSharedPorts w sign).r=wireBlock w 2056 256 := by
  have a := wireBlock_append w 2056 1 254
  have b := wireBlock_append w 2056 255 1
  have one (s : Nat) : wireBlock w s 1=[w s] := by simp [wireBlock,List.range']
  rw [one] at a b
  have a0 : [w 2056]++wireBlock w 2057 254=wireBlock w 2056 255 := by simpa using a
  change (w 2056::wireBlock w 2057 254)++[w 2311]=_
  rw [show w 2056::wireBlock w 2057 254=[w 2056]++wireBlock w 2057 254 from rfl,a0]
  simpa using b

theorem balancedSharedPorts_support (w : Nat → Wire) (sign : Wire) :
    wires (BalancedCircuit.program (balancedSharedPorts w sign)) ⊆
      (balancedSharedPorts w sign).wires.toFinset :=
  BalancedCircuit.support _ (balancedSharedPorts_widths w sign)

private def balancedWorkIds : List Nat :=
  [765,768,767,766,1796,1797,1027]++List.range' 1540 256

private def availableWorkIds : List Nat :=
  List.range' 1540 257++List.range' 1798 256++[1797]++List.range' 512 257++
    [2313,769,1027,2054,2055]

private theorem balancedWorkIds_subset : balancedWorkIds⊆availableWorkIds := by decide

/-- All temporary balanced sites were proved zero by the existing terminal
clear/field-work interface, including the explicitly borrowed padding bit. -/
theorem balancedSharedPorts_work_subset (w : Nat → Wire) (sign : Wire) :
    BalancedCircuit.work (balancedSharedPorts w sign) ⊆
      (skywalkSharedField w).work++skywalkSharedUnused w := by
  have used : BalancedCircuit.work (balancedSharedPorts w sign)=balancedWorkIds.map w := by
    simp [BalancedCircuit.work,balancedSharedPorts,balancedWorkIds,wireBlock]
  have available : (skywalkSharedField w).work++skywalkSharedUnused w=availableWorkIds.map w := by
    simp [skywalkSharedField,skywalkSharedUnused,ModInPlaceLayout.work,
      ModAddCoreLayout.work,availableWorkIds,wireBlock,List.map_append,List.append_assoc]
  rw [used,available]
  intro q hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  exact List.mem_map.mpr ⟨j,balancedWorkIds_subset hj,rfl⟩

theorem balancedSharedPorts_clean (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (hw : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) :
    ∀q∈BalancedCircuit.work (balancedSharedPorts w sign),base q=false := by
  intro q hq
  have h := balancedSharedPorts_work_subset w sign hq
  rcases List.mem_append.mp h with h|h
  · exact (regValue_zero _ _).mp hw q h
  · exact (regValue_zero _ _).mp hu q h

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.balancedSharedPorts_nodup
#print axioms ECDSAAdd.Arithmetic.balancedSharedPorts_r
#print axioms ECDSAAdd.Arithmetic.balancedSharedPorts_y
#print axioms ECDSAAdd.Arithmetic.balancedSharedPorts_clean
