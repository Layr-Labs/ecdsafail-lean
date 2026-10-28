import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryLayout

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic
attribute [local irreducible] dblInPlace halfInPlace

/-- Actual gate support includes the original Y guard and borrowed clean
banks, but excludes the declared ghost mask and old auxiliary Cin. -/
def borrowedSkywalkUnary_sites (w : Nat → Wire) : Finset Wire :=
  (wireBlock w 2056 257++wireBlock w 512 257++wireBlock w 1540 256++[w 1797,w 769]).toFinset

private def unarySiteIds : List Nat :=
  List.range' 2056 257++List.range' 512 257++List.range' 1540 256++[1797,769]
private theorem sites_map (w : Nat → Wire) :
    borrowedSkywalkUnary_sites w=(unarySiteIds.map w).toFinset := by
  simp [borrowedSkywalkUnary_sites,unarySiteIds,wireBlock,List.map_append]

/-- modUnary_wires proves that the untouched mask is absent from execution. -/
theorem borrowedSkywalkUnary_support (w : Nat → Wire) (p : Nat) :
    wires (dblInPlace (borrowedSkywalkUnary w) p) ⊆ borrowedSkywalkUnary_sites w ∧
    wires (halfInPlace (borrowedSkywalkUnary w) p) ⊆ borrowedSkywalkUnary_sites w := by
  have hs := modUnary_wires (borrowedSkywalkUnary w) 256 p
    (borrowedSkywalkUnary_widths w) (by decide)
  constructor <;> intro q hq
  · rw [hs.1] at hq
    simp only [borrowedSkywalkUnary_z_block] at hq
    simp only [ModUnaryLayout.core,ModAddCoreLayout.work,
      borrowedSkywalkUnary,List.mem_toFinset,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hq
    simp only [borrowedSkywalkUnary_sites,List.mem_toFinset,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false]
    tauto
  · rw [hs.2] at hq
    simp only [borrowedSkywalkUnary_z_block] at hq
    simp only [ModUnaryLayout.core,ModAddCoreLayout.work,
      borrowedSkywalkUnary,List.mem_toFinset,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hq
    simp only [borrowedSkywalkUnary_sites,List.mem_toFinset,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false]
    tauto

private theorem unarySiteIdsBound (j : Nat) (hj : j∈unarySiteIds) : j<2314 := by
  simp only [unarySiteIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega

/-- No actual seed-constant-bank site 1798..2055 or old Cin2313 is used. -/
theorem borrowedSkywalkUnary_sites_avoid (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (j : Nat)
    (hj : (1798≤j ∧ j<2056) ∨ j=2313) : w j∉borrowedSkywalkUnary_sites w := by
  intro hm
  rw [sites_map] at hm
  obtain ⟨i,hi,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  have hb : j<2314 := by omega
  have eqij := skywalkShared_index_inj w hn i j (unarySiteIdsBound i hi) hb he
  subst i
  simp only [unarySiteIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hi
  omega

theorem borrowedSkywalkUnary_no_old_bank (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (p j : Nat)
    (hj : (1798≤j ∧ j<2056) ∨ j=2313) :
    w j∉wires (dblInPlace (borrowedSkywalkUnary w) p) ∧
    w j∉wires (halfInPlace (borrowedSkywalkUnary w) p) := by
  have hs := borrowedSkywalkUnary_support w p
  have ha := borrowedSkywalkUnary_sites_avoid w hn j hj
  exact ⟨fun h => ha (hs.1 h),fun h => ha (hs.2 h)⟩

/-- Standalone unary resources only; this is not a whole-stage width bound. -/
theorem borrowedSkywalkUnary_resources (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (p : Nat) :
    toffoliCount (dblInPlace (borrowedSkywalkUnary w) p)=511 ∧
    measurementCount (dblInPlace (borrowedSkywalkUnary w) p)=511 ∧
    qubitCount (dblInPlace (borrowedSkywalkUnary w) p)=771 ∧
    toffoliCount (halfInPlace (borrowedSkywalkUnary w) p)=512 ∧
    measurementCount (halfInPlace (borrowedSkywalkUnary w) p)=512 ∧
    qubitCount (halfInPlace (borrowedSkywalkUnary w) p)=772 :=
  modUnary_resources (borrowedSkywalkUnary w) 256 p (borrowedSkywalkUnary_widths w)
    (borrowedSkywalkUnary_nodup w hn) (by decide)

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_support
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_no_old_bank
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_resources
