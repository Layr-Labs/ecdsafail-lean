import ECDSAAdd.Arithmetic.FieldRenameLayouts
import ECDSAAdd.Arithmetic.TranscriptSelectFlag
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.MappedSubtract
import ECDSAAdd.Arithmetic.Rotate
import ECDSAAdd.Framework.WireRenameComposition

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename

theorem rename_append (f : Wire → Wire) (p q : Program) :
    renameProgram f (p++q)=renameProgram f p++renameProgram f q := by
  simp only [renameProgram,List.map_append]

theorem rename_reverse (f : Wire → Wire) (p : Program) :
    renameProgram f p.reverse=(renameProgram f p).reverse := by
  simp only [renameProgram,List.map_reverse]

theorem majority_natural (f : Wire → Wire) (a b c d : Wire) :
    renameProgram f (majority a b c d)=majority (f a) (f b) (f c) (f d) := rfl
theorem eraseCarry_natural (f : Wire → Wire) (a b c d : Wire) :
    renameProgram f (eraseCarry a b c d)=eraseCarry (f a) (f b) (f c) (f d) := rfl

theorem mappedMajority_natural (f : Wire → Wire) (b : MappedBit) (y c d : Wire) :
    renameProgram f (mappedMajority b y c d)=mappedMajority (mapBit f b) (f y) (f c) (f d) := by
  cases b with
  | mk a flip =>
    cases a <;> cases flip <;>
      simp [mappedMajority,mapBit,borrowMajority,majority,
        renameProgram,renameInstr]

theorem mappedEraseCarry_natural (f : Wire → Wire) (b : MappedBit) (y c d : Wire) :
    renameProgram f (mappedEraseCarry b y c d)=mappedEraseCarry (mapBit f b) (f y) (f c) (f d) := by
  cases b with
  | mk a flip =>
    cases a <;> cases flip <;>
      simp [mappedEraseCarry,mapBit,eraseBorrow,eraseCarry,
        renameProgram,renameInstr,renameCorrection]

theorem mappedSum_natural (f : Wire → Wire) (b : MappedBit) (y c : Wire) :
    renameProgram f (mappedSum b y c)=mappedSum (mapBit f b) (f y) (f c) := by
  cases b with
  | mk a flip =>
    cases a <;> cases flip <;> simp [mappedSum,mapBit,renameProgram,renameInstr]

theorem flipBelow_natural (f : Wire → Wire) (c : Option Wire) (top t : Wire) :
    renameProgram f (flipBelow c top t)=flipBelow (c.map f) (f top) (f t) := by
  cases c <;> rfl

theorem notRegister_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (notRegister r)=notRegister (r.map f) := by
  simp only [notRegister,renameProgram,List.map_map,Function.comp_def,renameInstr]

theorem signComplement_natural (f : Wire → Wire) (q : Wire) (r : List Wire) :
    renameProgram f (signComplement q r)=signComplement (f q) (r.map f) := by
  simp only [signComplement,renameProgram,List.map_map,Function.comp_def,renameInstr]

theorem swapBits_natural (f : Wire → Wire) (a b : Wire) :
    renameProgram f (swapBits a b)=swapBits (f a) (f b) := rfl

theorem selectWindow_natural (f : Wire → Wire) (b src flag : Wire)
    (constant : Bool) (body : Program) :
    renameProgram f (transcriptSelectWindow b src flag constant body)=
      transcriptSelectWindow (f b) (f src) (f flag) constant (renameProgram f body) := by
  cases constant <;>
    simp [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,renameProgram,renameInstr,renameCorrection]

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.mappedEraseCarry_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.selectWindow_natural
