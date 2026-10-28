import ECDSAAdd.Arithmetic.FieldRenameRegisters
import ECDSAAdd.Arithmetic.MappedCompressedFieldReplay
import ECDSAAdd.Arithmetic.CompressedPlacementTransport

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.FieldRename
attribute [local irreducible] majority eraseCarry mappedAdd mappedSub

def mapConvert (f : Wire → Wire) (L : BalancedConvert.Layout) : BalancedConvert.Layout :=
  {low:=L.low.map f,msb:=f L.msb,carry:=L.carry.map f,
   cin:=f L.cin,one:=f L.one,flag:=f L.flag}

theorem convert_word_map (f : Wire → Wire) (L : BalancedConvert.Layout) :
    (mapConvert f L).word=L.word.map f := by
  simp [mapConvert,BalancedConvert.Layout.word]

theorem convert_correction_map (f : Wire → Wire) (L : BalancedConvert.Layout) :
    (BalancedConvert.correction L).map (mapBit f)=BalancedConvert.correction (mapConvert f L) := by
  simp only [BalancedConvert.correction,List.map_map]
  apply List.map_congr_left
  intro i _
  by_cases h : BalancedCircuit.sparseF.testBit i <;> simp [mapBit,mapConvert,h]

theorem literalConstSum_natural (f : Wire → Wire) (bit : Bool) (x cin : Wire) :
    renameProgram f (literalConstSum bit x cin)=literalConstSum bit (f x) (f cin) := by
  cases bit <;> rfl

theorem literalConstStep_natural (f : Wire → Wire) (bit : Bool) (x cin cout : Wire) :
    renameProgram f (literalConstStep bit x cin cout)=literalConstStep bit (f x) (f cin) (f cout) := by
  cases bit <;> rfl

theorem literalConstErase_natural (f : Wire → Wire) (bit : Bool) (x cin cout one : Wire) :
    renameProgram f (literalConstErase bit x cin cout one)=
      literalConstErase bit (f x) (f cin) (f cout) (f one) := by
  cases bit <;> rfl

theorem literalConstAdd_natural (f : Wire → Wire) (xs cs : List Wire) (cin one : Wire) (k : Nat) :
    renameProgram f (literalConstAdd xs cs cin one k)=
      literalConstAdd (xs.map f) (cs.map f) (f cin) (f one) k := by
  induction xs generalizing cs cin k with
  | nil => simp [literalConstAdd,renameProgram]
  | cons x xs ih =>
    cases xs with
    | nil => simpa only [literalConstAdd,List.map_cons,List.map_nil] using
        literalConstSum_natural f (decide (k%2=1)) x cin
    | cons y ys =>
      cases cs with
      | nil => simp [literalConstAdd,renameProgram]
      | cons c cs =>
        simp only [literalConstAdd,List.map_cons,rename_append,literalConstStep_natural,
          literalConstErase_natural,ih]

theorem xorConstant_natural (f : Wire → Wire) (xs : List Wire) (k : Nat) :
    renameProgram f (xorConstant xs k)=xorConstant (xs.map f) k := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : k%2=1
    · simp only [xorConstant,if_pos h,List.map_cons,rename_append,ih]
      rfl
    · simp only [xorConstant,if_neg h,List.map_cons,rename_append,ih]
      rfl

theorem compareChain_natural (f : Wire → Wire) (control : Option Wire)
    (xs ys cs : List Wire) (cin target : Wire) :
    renameProgram f (compareChain control xs ys cs cin target)=
      compareChain (control.map f) (xs.map f) (ys.map f) (cs.map f) (f cin) (f target) := by
  induction xs generalizing ys cs cin with
  | nil =>
    cases ys <;> cases cs <;> simp only [compareChain,List.map_nil,List.map_cons,renameProgram,List.map_nil]
    exact flipBelow_natural f control cin target
  | cons x xs ih =>
    cases ys with
    | nil => simp [compareChain,renameProgram]
    | cons y ys =>
      cases cs with
      | nil => simp [compareChain,renameProgram]
      | cons c cs => simp only [compareChain,List.map_cons,rename_append,majority_natural,eraseCarry_natural,ih]

theorem compareLt_natural (f : Wire → Wire) (control : Option Wire)
    (xs ys cs : List Wire) (cin target : Wire) :
    renameProgram f (compareLt control xs ys cs cin target)=
      compareLt (control.map f) (xs.map f) (ys.map f) (cs.map f) (f cin) (f target) := by
  simp only [compareLt,rename_append,notRegister_natural,compareChain_natural,List.map_cons]

theorem compareLtConst_natural (f : Wire → Wire) (control : Option Wire)
    (xs constant cs : List Wire) (cin target : Wire) (k : Nat) :
    renameProgram f (compareLtConst control xs constant cs cin target k)=
      compareLtConst (control.map f) (xs.map f) (constant.map f) (cs.map f) (f cin) (f target) k := by
  simp only [compareLtConst,rename_append,xorConstant_natural,compareLt_natural]

theorem convert_predicate_natural (f : Wire → Wire) (L : BalancedConvert.Layout) :
    renameProgram f (BalancedConvert.predicate L)=BalancedConvert.predicate (mapConvert f L) := by
  simp only [BalancedConvert.predicate,rename_append,literalConstAdd_natural,convert_word_map]
  rfl

theorem convert_center_natural (f : Wire → Wire) (L : BalancedConvert.Layout) :
    renameProgram f (BalancedConvert.center L)=BalancedConvert.center (mapConvert f L) := by
  simp only [BalancedConvert.center,rename_append,convert_predicate_natural,mappedAdd_natural,
    convert_word_map,convert_correction_map]
  rfl

theorem convert_canonical_natural (f : Wire → Wire) (L : BalancedConvert.Layout) :
    renameProgram f (BalancedConvert.canonical L)=BalancedConvert.canonical (mapConvert f L) := by
  simp only [BalancedConvert.canonical,rename_append,convert_predicate_natural,mappedSub_natural,
    convert_word_map,convert_correction_map]
  rfl

theorem sharedTargetConvert_map (f w : Wire → Wire) :
    mapConvert f (balancedSharedTargetConvert w)=balancedSharedTargetConvert (f ∘ w) := by
  simp only [mapConvert,balancedSharedTargetConvert,wireBlock_map,Function.comp_def]

theorem sharedSourceConvert_map (f w : Wire → Wire) :
    mapConvert f (balancedSharedSourceConvert w)=balancedSharedSourceConvert (f ∘ w) := by
  simp only [mapConvert,balancedSharedSourceConvert,wireBlock_map,Function.comp_def]

end ECDSAAdd.Arithmetic.FieldRename

namespace ECDSAAdd.Arithmetic.MappedCompressed
open FieldRename

def converterPairAt (w : Nat → Wire) (canonical : Bool) : Program :=
  if canonical then BalancedConvert.canonical (balancedSharedTargetConvert w)++
    BalancedConvert.canonical (balancedSharedSourceConvert w)
  else BalancedConvert.center (balancedSharedTargetConvert w)++
    BalancedConvert.center (balancedSharedSourceConvert w)

theorem converterPair_natural (f : Wire → Wire) (canonical : Bool) :
    renameProgram f (converterPair canonical)=converterPairAt f canonical := by
  cases canonical <;> simp only [converterPair,converterPairAt,Bool.false_eq_true,if_false,if_true,
    rename_append,convert_center_natural,convert_canonical_natural,
    sharedTargetConvert_map,sharedSourceConvert_map,Function.comp_id]

theorem base_converterPair_natural (canonical : Bool) :
    renameProgram base (converterPair canonical)=converterPairAt base canonical :=
  converterPair_natural base canonical

/-- The all-packed converter uses the same injective public pi0 placement
as the rest of the field boundary. This is exact program syntax, including
every measurement correction; a zero-boundary state bridge is separate. -/
theorem allPlaced_converterPair_natural (canonical : Bool) :
    renameProgram allPlaced (converterPair canonical)=
      renameProgram (shifted CompressedAllocation.pi0) (converterPairAt base canonical) := by
  rw [←base_converterPair_natural,renameProgram_comp]
  have placement : shifted CompressedAllocation.pi0 ∘ base=allPlaced := by
    funext q
    exact shifted_base _ _
  rw [placement]

end ECDSAAdd.Arithmetic.MappedCompressed
#print axioms ECDSAAdd.Arithmetic.FieldRename.literalConstAdd_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.compareLtConst_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.convert_center_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.convert_canonical_natural
#print axioms ECDSAAdd.Arithmetic.MappedCompressed.allPlaced_converterPair_natural
