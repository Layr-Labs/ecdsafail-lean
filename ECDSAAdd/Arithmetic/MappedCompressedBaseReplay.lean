import ECDSAAdd.Arithmetic.MappedCompressedPacketTransport
import ECDSAAdd.Arithmetic.MappedCompressedReplayCounts

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.MappedCompressed
attribute [local irreducible] toffoliCount measurementCount logicalCell
private theorem baseRenameT (P : Program) :
    toffoliCount (renameProgram base P)=toffoliCount P := (renameProgram_counts base P).1
private theorem baseRenameM (P : Program) :
    measurementCount (renameProgram base P)=measurementCount P := (renameProgram_counts base P).2

def baseGroups (divide : Bool) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if divide then baseGroup divide j++baseGroups divide (j+1) n
    else baseGroups divide (j+1) n++baseGroup divide j

def baseTail (divide : Bool) : Program :=
  if divide then renameProgram base (logicalCell divide 510)++renameProgram base (logicalCell divide 511)
  else renameProgram base (logicalCell divide 511)++renameProgram base (logicalCell divide 510)

theorem baseGroup_counts (divide : Bool) (j : Nat) :
    toffoliCount (baseGroup divide j)=(if divide then 3847 else 3850) ∧ measurementCount (baseGroup divide j)=3076 := by
  have codec := compressedHistory_counts base (3*j)
  have a := logicalCell_counts divide (3*j)
  have b := logicalCell_counts divide (3*j+1)
  have c := logicalCell_counts divide (3*j+2)
  cases divide <;> simp only [baseGroup,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append,baseRenameT,baseRenameM,
    a.1,a.2,b.1,b.2,c.1,c.2,codec.1,codec.2.1,codec.2.2.1,codec.2.2.2]
  all_goals norm_num

theorem baseGroups_counts (divide : Bool) (j n : Nat) :
    toffoliCount (baseGroups divide j n)=(if divide then 3847 else 3850)*n ∧
    measurementCount (baseGroups divide j n)=3076*n := by
  induction n generalizing j with
  | zero => simp [baseGroups,toffoliCount,measurementCount]
  | succ n ih =>
    have head := baseGroup_counts divide j
    have rest := ih (j+1)
    cases divide <;> simp only [baseGroups,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,head.1,head.2,rest.1,rest.2]
    all_goals constructor <;> omega

theorem baseGroup_counts_eq (divide : Bool) (j : Nat) (hj : j < 170) :
    toffoliCount (baseGroup divide j)=toffoliCount (mappedGroup divide j) ∧
    measurementCount (baseGroup divide j)=measurementCount (mappedGroup divide j) := by
  rw [mappedGroup_eq_rename divide j hj]
  have counts := renameProgram_counts (shifted (CompressedAllocation.pi j)) (baseGroup divide j)
  exact ⟨counts.1.symm,counts.2.symm⟩

theorem baseGroups_counts_eq (divide : Bool) (j n : Nat) (h : j+n ≤ 170) :
    toffoliCount (baseGroups divide j n)=toffoliCount (mappedGroups divide j n) ∧
    measurementCount (baseGroups divide j n)=measurementCount (mappedGroups divide j n) := by
  induction n generalizing j with
  | zero => simp only [baseGroups,mappedGroups]
            constructor <;> trivial
  | succ n ih =>
    have head := baseGroup_counts_eq divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide <;> simp only [baseGroups,mappedGroups,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,head.1,head.2,rest.1,rest.2]
    all_goals constructor <;> trivial

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.baseGroups_counts_eq
