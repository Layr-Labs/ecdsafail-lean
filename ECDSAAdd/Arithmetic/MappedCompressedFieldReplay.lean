import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryLayout
import ECDSAAdd.Arithmetic.BalancedSharedLayoutBoundary

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.MappedCompressed
open CompressedAllocation Secp256k1
attribute [local irreducible] wires OffsetBorrowedCanonical.cell OffsetBorrowedInverseCanonical.cell
attribute [local irreducible] compressedHistoryEncode compressedHistoryDecode
attribute [local irreducible] dblInPlace halfInPlace copyRegister
attribute [local irreducible] addInPlace subInPlace compareLt

def logicalCell (divide : Bool) (i : Nat) : Program :=
  let unit := mixedTranscriptUnitTrace.getD i (false,false)
  if divide then OffsetBorrowedCanonical.cell id 2400 i (1028+i) 2409 2410 unit.1 unit.2
  else OffsetBorrowedInverseCanonical.cell id 2400 i (1028+i) 2409 2410 unit.1 unit.2

private theorem shared_live (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : live q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold live
  omega

private theorem shared_site (q : Nat) (h : q∈CompressedFieldSupport.sharedSites id 2409) : fieldSite q := by
  simp only [CompressedFieldSupport.sharedSites,balancedSharedPorts,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,OffsetCleanupBorrowedCaller.carry,wireBlock,List.map_id,
    List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  dsimp only [id] at h
  unfold fieldSite
  omega

private theorem inventory_live (j q : Nat) (hj : j < 170) (h : q∈groupInventory j) : live q := by
  simp only [groupInventory,List.mem_append] at h
  rcases h with (h|h)|h
  · exact shared_live q h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    unfold live
    omega
  · exact packet_live j q hj h

theorem mappedCell_support (divide : Bool) (j i : Nat) (hj : j < 170)
    (hi0 : 3*j ≤ i) (hi : i < 3*j+3) :
    wires (renameProgram (placed j) (logicalCell divide i))⊆slots.toFinset := by
  have g : i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    omega
  have s : 1028+i∈packetSites j := by
    simp only [packetSites,List.mem_cons,List.not_mem_nil,or_false]
    unfold H
    omega
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 (groupInventory j).toFinset
    (by intro q hq; simp only [groupInventory,List.mem_toFinset,List.mem_append];
        exact Or.inl (Or.inl (List.mem_toFinset.mp hq)))
    (by simp [groupInventory]) (by simp [groupInventory,g])
    (by simp [groupInventory,s]) (by simp [groupInventory])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈groupInventory j := by
    cases divide
    · exact List.mem_toFinset.mp (body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw))
    · exact List.mem_toFinset.mp (body.1 (by simpa only [logicalCell,if_true] using hraw))
  exact slot_mem _ (pi_live j old hj (inventory_live j old hj belongs)) (inventory_safe j old hj belongs)

def mappedGroup (divide : Bool) (j : Nat) : Program :=
  compressedHistoryDecode (placed j) (3*j) ++
  (if divide then renameProgram (placed j) (logicalCell divide (3*j)) ++
      renameProgram (placed j) (logicalCell divide (3*j+1)) ++
      renameProgram (placed j) (logicalCell divide (3*j+2))
   else renameProgram (placed j) (logicalCell divide (3*j+2)) ++
      renameProgram (placed j) (logicalCell divide (3*j+1)) ++
      renameProgram (placed j) (logicalCell divide (3*j))) ++
  compressedHistoryEncode (placed j) (3*j)

theorem mappedGroup_support (divide : Bool) (j : Nat) (hj : j < 170) :
    wires (mappedGroup divide j)⊆slots.toFinset := by
  have codec := codec_support j hj
  have a := mappedCell_support divide j (3*j) hj (by omega) (by omega)
  have b := mappedCell_support divide j (3*j+1) hj (by omega) (by omega)
  have c := mappedCell_support divide j (3*j+2) hj (by omega) (by omega)
  cases divide <;> simp only [mappedGroup,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc]
  · exact ⟨codec.2,c,b,a,codec.1⟩
  · exact ⟨codec.2,a,b,c,codec.1⟩

def mappedGroups (divide : Bool) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if divide then mappedGroup divide j++mappedGroups divide (j+1) n
    else mappedGroups divide (j+1) n++mappedGroup divide j

theorem mappedGroups_support (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    wires (mappedGroups divide j n)⊆slots.toFinset := by
  induction n generalizing j with
  | zero => simp [mappedGroups,wires]
  | succ n ih =>
    have current := mappedGroup_support divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [mappedGroups,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.union_subset_iff]
    · exact ⟨rest,current⟩
    · exact ⟨current,rest⟩

private theorem tail_support (divide : Bool) (i : Nat) (hi : i=510 ∨ i=511) :
    wires (renameProgram allPlaced (logicalCell divide i))⊆slots.toFinset := by
  let W := (CompressedFieldSupport.sharedSites id 2409++[2400,2410,i,1028+i]).toFinset
  have body := CompressedFieldSupport.cells_active id 2400 i (1028+i) 2409 2410
    (mixedTranscriptUnitTrace.getD i (false,false)).1
    (mixedTranscriptUnitTrace.getD i (false,false)).2 W
    (by intro q hq; simp only [W,List.mem_toFinset,List.mem_append]; exact Or.inl (List.mem_toFinset.mp hq))
    (by simp [W]) (by simp [W]) (by simp [W]) (by simp [W])
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have belongs : old∈W := by
    cases divide
    · exact body.2 (by simpa only [logicalCell,Bool.false_eq_true,if_false] using hraw)
    · exact body.1 (by simpa only [logicalCell,if_true] using hraw)
  have bounds : 510 ≤ i ∧ i ≤ 511 := by omega
  simp only [W,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,or_assoc] at belongs
  have hl : live old := by
    rcases belongs with h|rfl|rfl|rfl|rfl
    · exact shared_live old h
    all_goals unfold live; omega
  have nh : ¬holeRegion old := by
    rcases belongs with h|rfl|rfl|rfl|rfl
    · exact field_not_hole old (shared_site old h)
    all_goals unfold holeRegion; omega
  exact slot_mem _ (pi0_live old hl) (nonhole_pi0_safe old nh)

def mappedReplay (divide : Bool) : Program :=
  if divide then mappedGroups divide 0 170++renameProgram allPlaced (logicalCell divide 510)++
      renameProgram allPlaced (logicalCell divide 511)
  else renameProgram allPlaced (logicalCell divide 511)++
      renameProgram allPlaced (logicalCell divide 510)++mappedGroups divide 0 170

theorem mappedReplay_support (divide : Bool) : wires (mappedReplay divide)⊆slots.toFinset := by
  have groups := mappedGroups_support divide 0 170 (by omega)
  have a := tail_support divide 510 (by omega)
  have b := tail_support divide 511 (by omega)
  cases divide <;> simp only [mappedReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc]
  · exact ⟨b,a,groups⟩
  · exact ⟨groups,a,b⟩

private theorem convert_site (target : Bool) (q : Nat)
    (h : q∈(if target then balancedSharedTargetConvert id else balancedSharedSourceConvert id).wires) :
    fieldSite q := by
  cases target <;> simp only [Bool.false_eq_true,if_false,if_true,
    balancedSharedTargetConvert,balancedSharedSourceConvert,BalancedConvert.Layout.wires,
    wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at h
  all_goals dsimp only [id] at h; unfold fieldSite; omega

def converterPair (canonical : Bool) : Program :=
  if canonical then BalancedConvert.canonical (balancedSharedTargetConvert id)++
    BalancedConvert.canonical (balancedSharedSourceConvert id)
  else BalancedConvert.center (balancedSharedTargetConvert id)++
    BalancedConvert.center (balancedSharedSourceConvert id)

theorem converters_support (canonical : Bool) :
    wires (renameProgram allPlaced (converterPair canonical))⊆slots.toFinset := by
  have target := BalancedConvert.support (balancedSharedTargetConvert id)
  have source := BalancedConvert.support (balancedSharedSourceConvert id)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have site : fieldSite old := by
    cases canonical <;> simp only [converterPair,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at hraw
    · rcases hraw with h|h
      · exact convert_site true old (List.mem_toFinset.mp (target.1 h))
      · exact convert_site false old (List.mem_toFinset.mp (source.1 h))
    · rcases hraw with h|h
      · exact convert_site true old (List.mem_toFinset.mp (target.2 h))
      · exact convert_site false old (List.mem_toFinset.mp (source.2 h))
  exact allPlaced_field_mem old site

theorem unary_support (divide : Bool) :
    wires (renameProgram allPlaced (if divide then dblInPlace (borrowedSkywalkUnary id) p
      else halfInPlace (borrowedSkywalkUnary id) p))⊆slots.toFinset := by
  have u := modUnary_wires (borrowedSkywalkUnary id) 256 p (borrowedSkywalkUnary_widths id) (by omega)
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member : old∈((borrowedSkywalkUnary id).z++(borrowedSkywalkUnary id).core.work++
      [(borrowedSkywalkUnary id).flag]).toFinset := by
    cases divide
    · simp only [Bool.false_eq_true,if_false] at hraw
      rw [u.2] at hraw
      exact hraw
    · simp only [if_true] at hraw
      rw [u.1] at hraw
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hraw))
  have site : fieldSite old := by
    change old∈((wireBlock id 2056 256++[id 2312])++
      (wireBlock id 512 257++wireBlock id 1540 256++[id 1797])++[id 769]).toFinset at member
    simp only [List.mem_toFinset,wireBlock,List.map_id,List.mem_append,List.mem_cons,List.not_mem_nil,
      List.mem_range'_1,or_false] at member
    dsimp only [id] at member
    simp only [or_assoc] at member
    rcases member with h|rfl|h|h|rfl|rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · norm_num [fieldSite]
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · norm_num [fieldSite]
    · norm_num [fieldSite]
  exact allPlaced_field_mem old site

theorem copy_support : wires (renameProgram allPlaced
    (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))⊆slots.toFinset := by
  have zword : (skywalkSharedField id).z=wireBlock id 2056 257 := skywalkShared_field_z id
  have aword : (skywalkSharedField id).a=wireBlock id 770 257 := rfl
  have cp := copyRegister_wires_subset none (skywalkSharedField id).z (skywalkSharedField id).a
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨old,hraw,rfl⟩ := Finset.mem_image.mp hq
  have member := cp hraw
  rw [zword,aword] at member
  have site : fieldSite old := by
    simp only [List.mem_toFinset,Option.toList_none,List.nil_append,wireBlock,List.map_id,
      List.mem_append,List.mem_range'_1] at member
    unfold fieldSite
    omega
  exact allPlaced_field_mem old site

def fieldSegment (divide : Bool) : Program :=
  (if divide then renameProgram allPlaced (dblInPlace (borrowedSkywalkUnary id) p)
   else renameProgram allPlaced (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a))++
  renameProgram allPlaced (converterPair false)++mappedReplay divide++
  renameProgram allPlaced (converterPair true)++
  (if divide then renameProgram allPlaced (copyRegister none (skywalkSharedField id).z (skywalkSharedField id).a)
   else renameProgram allPlaced (halfInPlace (borrowedSkywalkUnary id) p))

theorem fieldSegment_support (divide : Bool) : wires (fieldSegment divide)⊆slots.toFinset := by
  have unary := unary_support divide
  have a := converters_support false
  have b := converters_support true
  have r := mappedReplay_support divide
  cases divide <;> simp only [fieldSegment,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff,and_assoc]
  · exact ⟨copy_support,a,r,b,unary⟩
  · exact ⟨unary,a,r,b,copy_support⟩

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.mappedReplay_support
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.fieldSegment_support
