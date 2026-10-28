import ECDSAAdd.Arithmetic.MappedCompressedConversionNaturality
import ECDSAAdd.Arithmetic.BorrowedSkywalkUnaryLayout

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] addInPlace subInPlace compareLt compareLtConst
attribute [local irreducible] maskedConstant xorConstant maskedAddConst maskedSubConst

def mapModUnary (f : Wire → Wire) (U : ModUnaryLayout) : ModUnaryLayout :=
  {low:=U.low.map f,high:=f U.high,constant:=U.constant.map f,
   carry:=U.carry.map f,cin:=f U.cin,mask:=U.mask.map f,flag:=f U.flag}

theorem modUnary_z_map (f : Wire → Wire) (U : ModUnaryLayout) :
    (mapModUnary f U).z=U.z.map f := by
  simp [mapModUnary,ModUnaryLayout.z]

/-- Both the nonempty head and the fallback high wire are relabeled. -/
theorem modUnary_bit_map (f : Wire → Wire) (U : ModUnaryLayout) :
    (mapModUnary f U).bit=f U.bit := by
  cases h : U.low <;> simp [ModUnaryLayout.bit,mapModUnary,h]

theorem take_natural (f : Wire → Wire) (r : List Wire) (n : Nat) :
    (r.take n).map f=(r.map f).take n := by
  induction n generalizing r with
  | zero => simp
  | succ n ih => cases r <;> simp [ih]

theorem maskedConstant_natural (f : Wire → Wire) (control : Wire) (r : List Wire) (k : Nat) :
    renameProgram f (maskedConstant control r k)=maskedConstant (f control) (r.map f) k := by
  induction r generalizing k with
  | nil => simp [maskedConstant,renameProgram]
  | cons x xs ih =>
    by_cases h : k%2=1
    · simp only [maskedConstant,if_pos h,List.map_cons,rename_append,ih]
      rfl
    · simp only [maskedConstant,if_neg h,List.map_cons,rename_append,ih]
      rfl

theorem maskedAddConst_natural (f : Wire → Wire) (control : Wire)
    (constant target carry : List Wire) (cin : Wire) (k : Nat) :
    renameProgram f (maskedAddConst control constant target carry cin k)=
      maskedAddConst (f control) (constant.map f) (target.map f) (carry.map f) (f cin) k := by
  simp only [maskedAddConst,rename_append,maskedConstant_natural,addInPlace_natural]

theorem maskedSubConst_natural (f : Wire → Wire) (control : Wire)
    (constant target carry : List Wire) (cin : Wire) (k : Nat) :
    renameProgram f (maskedSubConst control constant target carry cin k)=
      maskedSubConst (f control) (constant.map f) (target.map f) (carry.map f) (f cin) k := by
  simp only [maskedSubConst,rename_append,maskedConstant_natural,subInPlace_natural]

theorem dblInPlace_natural (f : Wire → Wire) (U : ModUnaryLayout) (p : Nat) :
    renameProgram f (dblInPlace U p)=dblInPlace (mapModUnary f U) p := by
  simp only [dblInPlace,rename_append,rotateLeft_natural,xorConstant_natural,
    subInPlace_natural,maskedAddConst_natural,modUnary_z_map,modUnary_bit_map]
  simp only [mapModUnary,List.length_map,take_natural]
  rfl

theorem halfInPlace_natural (f : Wire → Wire) (U : ModUnaryLayout) (p : Nat) :
    renameProgram f (halfInPlace U p)=halfInPlace (mapModUnary f U) p := by
  simp only [halfInPlace,rename_append,maskedAddConst_natural,rotateRight_natural,
    compareLtConst_natural,modUnary_z_map,modUnary_bit_map,Option.map_none]
  simp only [mapModUnary,List.length_map,take_natural]
  rfl

theorem borrowedUnary_map (f w : Wire → Wire) :
    mapModUnary f (borrowedSkywalkUnary w)=borrowedSkywalkUnary (f ∘ w) := by
  simp only [mapModUnary,borrowedSkywalkUnary,wireBlock_map,Function.comp_def]

theorem borrowed_dbl_natural (f : Wire → Wire) (p : Nat) :
    renameProgram f (dblInPlace (borrowedSkywalkUnary id) p)=dblInPlace (borrowedSkywalkUnary f) p := by
  rw [dblInPlace_natural,borrowedUnary_map,Function.comp_id]

theorem borrowed_half_natural (f : Wire → Wire) (p : Nat) :
    renameProgram f (halfInPlace (borrowedSkywalkUnary id) p)=halfInPlace (borrowedSkywalkUnary f) p := by
  rw [halfInPlace_natural,borrowedUnary_map,Function.comp_id]

end ECDSAAdd.Arithmetic.FieldRename

namespace ECDSAAdd.Arithmetic.MappedCompressed
open FieldRename Secp256k1

/-- Public all-packed placement maps every gate and correction of each
endpoint, with the modulus and all classical constant bits preserved. -/
theorem allPlaced_dbl_natural :
    renameProgram allPlaced (dblInPlace (borrowedSkywalkUnary id) p)=
      renameProgram (shifted CompressedAllocation.pi0) (dblInPlace (borrowedSkywalkUnary base) p) := by
  rw [←borrowed_dbl_natural base,renameProgram_comp]
  have placement : shifted CompressedAllocation.pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base _ _
  rw [placement]

theorem allPlaced_half_natural :
    renameProgram allPlaced (halfInPlace (borrowedSkywalkUnary id) p)=
      renameProgram (shifted CompressedAllocation.pi0) (halfInPlace (borrowedSkywalkUnary base) p) := by
  rw [←borrowed_half_natural base,renameProgram_comp]
  have placement : shifted CompressedAllocation.pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base _ _
  rw [placement]

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.FieldRename.borrowed_dbl_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.borrowed_half_natural
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.allPlaced_dbl_natural
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.allPlaced_half_natural
