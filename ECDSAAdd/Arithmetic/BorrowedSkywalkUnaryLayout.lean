import ECDSAAdd.Arithmetic.ModUnaryResources
import ECDSAAdd.Arithmetic.SkywalkShared

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Unary arithmetic borrows the cleared mask and integer carry. The mask
field is a ghost of the old clean bank; actual unary gates never touch it. -/
def borrowedSkywalkUnary (w : Nat → Wire) : ModUnaryLayout :=
  { low:=wireBlock w 2056 256,high:=w 2312,constant:=wireBlock w 512 257,
    carry:=wireBlock w 1540 256,cin:=w 1797,mask:=wireBlock w 1798 257,flag:=w 769 }

theorem borrowedSkywalkUnary_widths (w : Nat → Wire) :
    (borrowedSkywalkUnary w).Widths 256 := by
  constructor <;> simp [borrowedSkywalkUnary,wireBlock]

theorem borrowedSkywalkUnary_z (w : Nat → Wire) :
    (borrowedSkywalkUnary w).z=(skywalkSharedField w).z := rfl

theorem borrowedSkywalkUnary_z_block (w : Nat → Wire) :
    (borrowedSkywalkUnary w).z=wireBlock w 2056 257 := by
  rw [borrowedSkywalkUnary_z,skywalkShared_field_z]

private def borrowedUnaryJointIds : List Nat :=
  [769,1797]++List.range' 512 257++List.range' 1540 256++List.range' 1798 257++
    List.range' 2056 257++List.range' 770 257

private theorem appendRegion (ls : List Nat) (hd : ls.Nodup) (s n : Nat)
    (ha : ∀j∈ls,j<s ∨ s+n≤j) : (ls++List.range' s n).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hd,List.nodup_range',?_⟩
  apply List.disjoint_left.mpr
  intro j hj hk
  have h := ha j hj
  simp only [List.mem_range'_1] at hk
  omega

private theorem borrowedUnaryJointIdsND : borrowedUnaryJointIds.Nodup := by
  have a := appendRegion (List.range' 512 257) List.nodup_range' 1540 256 (by
    intro j hj; simp only [List.mem_range'_1] at hj; omega)
  have b := appendRegion _ a 1798 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have c := appendRegion _ b 2056 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have d := appendRegion _ c 770 257 (by
    intro j hj; simp only [List.mem_append,List.mem_range'_1] at hj; omega)
  have e : (769::1797::(List.range' 512 257++List.range' 1540 256++
      List.range' 1798 257++List.range' 2056 257++List.range' 770 257)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_cons.mpr ⟨?_,d⟩⟩
    · simp only [List.mem_cons,List.mem_append,List.mem_range'_1]
      omega
    · simp only [List.mem_append,List.mem_range'_1]
      omega
  simpa only [borrowedUnaryJointIds,List.cons_append,List.nil_append] using e

private theorem borrowedUnaryJointIdsBound (j : Nat) (hj : j∈borrowedUnaryJointIds) :
    j<2314 := by
  simp only [borrowedUnaryJointIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj
  omega

/-- Full unary validity includes the untouched ghost mask and the preserved X port. -/
theorem borrowedSkywalkUnary_jointND (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    ((borrowedSkywalkUnary w).wires++(skywalkSharedField w).a).Nodup := by
  have mapped : (borrowedUnaryJointIds.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (borrowedUnaryJointIdsBound i hi)
        (borrowedUnaryJointIdsBound j hj) he
    · exact borrowedUnaryJointIdsND
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp mapped q
  simp only [ModUnaryLayout.wires,borrowedSkywalkUnary_z_block]
  simp only [ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
    borrowedSkywalkUnary,skywalkSharedField,
    borrowedUnaryJointIds,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_append,List.count_cons,List.count_nil] at h ⊢
  omega

theorem borrowedSkywalkUnary_nodup (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) : (borrowedSkywalkUnary w).wires.Nodup :=
  (List.nodup_append'.mp (borrowedSkywalkUnary_jointND w hn)).1

theorem borrowedSkywalkUnary_workAway (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) (q : Wire)
    (hq : q∈(borrowedSkywalkUnary w).work) :
    q∉(skywalkSharedField w).z ∧ q∉(skywalkSharedField w).a := by
  have h := List.nodup_iff_count.mp (borrowedSkywalkUnary_jointND w hn) q
  have hw := List.count_pos_iff.mpr hq
  simp only [ModUnaryLayout.wires,borrowedSkywalkUnary_z,List.count_append] at h
  constructor <;> intro hp <;> have hd := List.count_pos_iff.mpr hp <;> omega

theorem borrowedSkywalkUnary_pairDisjoint (w : Nat → Wire)
    (hn : (skywalkSharedWires w).Nodup) :
    (skywalkSharedField w).z.Disjoint (skywalkSharedField w).a := by
  apply List.disjoint_left.mpr
  intro q hz ha
  have h := List.nodup_iff_count.mp (borrowedSkywalkUnary_jointND w hn) q
  have hr := List.count_pos_iff.mpr hz
  have hs := List.count_pos_iff.mpr ha
  simp only [ModUnaryLayout.wires,borrowedSkywalkUnary_z,List.count_append] at h
  omega

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_jointND
#print axioms ECDSAAdd.Arithmetic.borrowedSkywalkUnary_workAway
