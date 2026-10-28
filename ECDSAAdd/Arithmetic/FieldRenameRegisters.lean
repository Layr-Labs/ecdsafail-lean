import ECDSAAdd.Arithmetic.FieldRenamePrimitives

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename

theorem copyRegister_natural (f : Wire → Wire) (c : Option Wire) (a b : List Wire) :
    renameProgram f (copyRegister c a b)=copyRegister (c.map f) (a.map f) (b.map f) := by
  induction a generalizing b with
  | nil => simp [copyRegister,renameProgram]
  | cons a as ih =>
    cases b with
    | nil => simp [copyRegister,renameProgram]
    | cons b bs =>
      simp only [copyRegister,List.map_cons,rename_append,ih]
      cases c <;> rfl

theorem swapRegisters_natural (f : Wire → Wire) (c : Wire) (a b : List Wire) :
    renameProgram f (swapRegisters c a b)=swapRegisters (f c) (a.map f) (b.map f) := by
  simp only [swapRegisters,rename_append,copyRegister_natural,Option.map_none,Option.map_some]

theorem addInPlace_natural (f : Wire → Wire) (a b carry : List Wire) (cin : Wire) :
    renameProgram f (addInPlace a b carry cin)=addInPlace (a.map f) (b.map f) (carry.map f) (f cin) := by
  induction a generalizing b carry cin with
  | nil => simp [addInPlace,renameProgram]
  | cons a as ih =>
    cases as with
    | nil =>
      cases b with
      | nil => simp [addInPlace,renameProgram]
      | cons b bs => cases bs <;> simp [addInPlace,renameProgram,renameInstr]
    | cons a' as =>
      cases b with
      | nil => simp [addInPlace,renameProgram]
      | cons b bs =>
        cases bs with
        | nil => simp [addInPlace,renameProgram]
        | cons b' bs =>
          cases carry with
          | nil => simp [addInPlace,renameProgram]
          | cons c cs =>
            simp only [addInPlace,List.map_cons,rename_append,majority_natural,
              eraseCarry_natural,ih]
            rfl

theorem subInPlace_natural (f : Wire → Wire) (a b carry : List Wire) (cin : Wire) :
    renameProgram f (subInPlace a b carry cin)=subInPlace (a.map f) (b.map f) (carry.map f) (f cin) := by
  simp only [subInPlace,rename_append,notRegister_natural,addInPlace_natural]

theorem mappedAdd_natural (f : Wire → Wire) (a : List MappedBit) (b carry : List Wire) (cin : Wire) :
    renameProgram f (mappedAdd a b carry cin)=
      mappedAdd (a.map (mapBit f)) (b.map f) (carry.map f) (f cin) := by
  induction a generalizing b carry cin with
  | nil => simp [mappedAdd,renameProgram]
  | cons a as ih =>
    cases as with
    | nil =>
      cases b with
      | nil => simp [mappedAdd,renameProgram]
      | cons b bs =>
        cases bs with
        | nil => simpa only [mappedAdd,List.map_cons,List.map_nil] using mappedSum_natural f a b cin
        | cons b' bs => simp [mappedAdd,renameProgram]
    | cons a' as =>
      cases b with
      | nil => simp [mappedAdd,renameProgram]
      | cons b bs =>
        cases bs with
        | nil => simp [mappedAdd,renameProgram]
        | cons b' bs =>
          cases carry with
          | nil => simp [mappedAdd,renameProgram]
          | cons c cs =>
            simp only [mappedAdd,List.map_cons,rename_append,mappedMajority_natural,
              mappedEraseCarry_natural,mappedSum_natural,ih]

theorem mappedSub_natural (f : Wire → Wire) (a : List MappedBit) (b carry : List Wire) (cin : Wire) :
    renameProgram f (mappedSub a b carry cin)=
      mappedSub (a.map (mapBit f)) (b.map f) (carry.map f) (f cin) := by
  simp only [mappedSub,rename_append,notRegister_natural,mappedAdd_natural]

theorem rotate_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (rotateRight r)=rotateRight (r.map f) ∧
    renameProgram f (rotateLeft r)=rotateLeft (r.map f) := by
  induction r with
  | nil => simp [rotateRight,rotateLeft,renameProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,rotateLeft,renameProgram]
    | cons b bs =>
      simp only [rotateRight,rotateLeft,List.map_cons,rename_append,swapBits_natural,ih.1,ih.2]
      constructor <;> trivial

theorem rotateRight_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (rotateRight r)=rotateRight (r.map f) := (rotate_natural f r).1
theorem rotateLeft_natural (f : Wire → Wire) (r : List Wire) :
    renameProgram f (rotateLeft r)=rotateLeft (r.map f) := (rotate_natural f r).2

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.addInPlace_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.mappedAdd_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.rotate_natural
