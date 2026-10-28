import ECDSAAdd.Arithmetic.Paper935.FoldCarryBackward

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum

structure FoldCell where
  literal : Bool
  data : Wire
  carry : Wire
  deriving DecidableEq,Repr

def FoldCell.wires (b : FoldCell) : List Wire := [b.data,b.carry]

def FoldCell.next (b : FoldCell) (cin : Option Wire) : Option Wire :=
  if b.literal || cin.isSome then some b.carry else none

/-- One author carry block: forward sweep then backward sweep. The last
carry may be retained for the next block; all earlier carries are erased. -/
def foldBlock (control : Wire) : List FoldCell → Option Wire → Bool → Bool → Program
  | [],_,_,_ => []
  | b::rest,cin,sums,keep =>
      foldCarryForward b.literal control b.data b.carry cin ++
      foldBlock control rest (b.next cin) sums keep ++
      foldCarryBackward b.literal control b.data b.carry cin sums (keep && rest.isEmpty)

def foldBlockCarries : List FoldCell → Bool → Nat
  | [],_ => 0
  | b::rest,present => (if b.literal || present then 1 else 0)+foldBlockCarries rest (b.literal || present)

def foldBlockTop : List FoldCell → Option Wire → Option Wire
  | [],cin => cin
  | b::rest,cin => foldBlockTop rest (b.next cin)

theorem foldBlock_forward_count (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (sums keep : Bool) : toffoliCount (foldBlock control cells cin sums keep)=foldBlockCarries cells cin.isSome := by
  induction cells generalizing cin with
  | nil => rfl
  | cons b rest ih =>
    simp only [foldBlock,toffoliCount_append,(foldCarryForward_counts _ _ _ _ _).1,
      (foldCarryBackward_counts _ _ _ _ _ _ _).1,Nat.add_zero,ih,foldBlockCarries]
    cases cin <;> cases hb : b.literal <;> simp [FoldCell.next,hb]

theorem foldBlock_support (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (sums keep : Bool) :
    wires (foldBlock control cells cin sums keep) ⊆ (control::cin.toList++cells.flatMap FoldCell.wires).toFinset := by
  induction cells generalizing cin with
  | nil => simp [foldBlock,wires]
  | cons b rest ih =>
    have cell := foldCarry_support b.literal control b.data b.carry cin sums (keep && rest.isEmpty)
    rw [wires_append,Finset.union_subset_iff] at cell
    have localSubset : ([control,b.data,b.carry]++cin.toList).toFinset ⊆
        (control::cin.toList++(b::rest).flatMap FoldCell.wires).toFinset := by
      intro q h
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.flatMap_cons,FoldCell.wires,
        List.not_mem_nil,or_false] at h ⊢
      tauto
    have tailSubset : (control::(b.next cin).toList++rest.flatMap FoldCell.wires).toFinset ⊆
        (control::cin.toList++(b::rest).flatMap FoldCell.wires).toFinset := by
      intro q h
      cases hc : cin <;> cases hb : b.literal <;>
        simp only [FoldCell.next,hc,hb,Bool.false_or,Bool.true_or,Option.isSome_none,Option.isSome_some,
          Bool.false_eq_true,if_false,if_true,Option.toList_none,Option.toList_some,
          List.mem_toFinset,List.mem_append,List.mem_cons,List.flatMap_cons,FoldCell.wires,
          List.not_mem_nil,or_false] at h ⊢ <;> tauto
    rw [foldBlock,wires_append,wires_append,Finset.union_subset_iff,Finset.union_subset_iff]
    exact ⟨⟨Finset.Subset.trans cell.1 localSubset,Finset.Subset.trans (ih (b.next cin)) tailSubset⟩,
      Finset.Subset.trans cell.2 localSubset⟩

theorem foldBlock_physical (control : Wire) (cells : List FoldCell) (cin : Option Wire)
    (sums keep : Bool) (hn : (control::cin.toList++cells.flatMap FoldCell.wires).Nodup) :
    GatePhysical (foldBlock control cells cin sums keep) := by
  induction cells generalizing cin with
  | nil => simp [foldBlock,GatePhysical]
  | cons b rest ih =>
    have localNd : ([control,b.data,b.carry]++cin.toList).Nodup := by
      apply List.nodup_iff_count.mpr
      intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
      omega
    have nextCount (q : Wire) : (b.next cin).toList.count q≤cin.toList.count q+[b.carry].count q := by
      cases cin <;> cases hb : b.literal <;> simp [FoldCell.next,hb]
    have tailNd : (control::(b.next cin).toList++rest.flatMap FoldCell.wires).Nodup := by
      apply List.nodup_iff_count.mpr
      intro q
      have h := List.nodup_iff_count.mp hn q
      have hnext := nextCount q
      simp only [List.flatMap_cons,FoldCell.wires,List.count_append,List.count_cons,List.count_nil] at h hnext ⊢
      omega
    have localPhysical := foldCarry_physical b.literal control b.data b.carry cin sums (keep && rest.isEmpty) localNd
    rw [gatePhysical_append] at localPhysical
    rw [foldBlock,gatePhysical_append,gatePhysical_append]
    exact ⟨⟨localPhysical.1,ih (b.next cin) tailNd⟩,localPhysical.2⟩

end ECDSAAdd.Arithmetic.Paper935
