import ECDSAAdd.Arithmetic.FieldRenameOffset
import ECDSAAdd.Arithmetic.TerminalParityChain

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
open BalancedCleanupOffset

attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry majority eraseCarry

private theorem measured_prepareHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (prepareHead b a y cinC cinB c d) =
      prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [prepareHead,rename_append,mappedMajority_natural,mappedSum_natural,
    majority_natural]
  rfl

private theorem measured_releaseHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (releaseHead b a y cinC cinB c d) =
      releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [releaseHead,rename_append,eraseCarry_natural,mappedSum_natural,
    mappedEraseCarry_natural]
  rfl

private theorem measured_terminal_natural (f : Wire → Wire) (a y cin target : Wire) :
    renameProgram f (TerminalParityMeasure.program a y cin target)=
      TerminalParityMeasure.program (f a) (f y) (f cin) (f target) := by
  simp only [TerminalParityMeasure.program,rename_append,eraseCarry_natural]
  rfl

/-- Relabel the actual shortened final branch as well as all ordinary heads.
Aligned lengths are sufficient for every production-width call. -/
theorem measured_offset_chain_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    renameProgram f (TerminalParityMeasure.chain bits xs ys cs ds cinC cinB target) =
      TerminalParityMeasure.chain (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f cinC) (f cinB) (f target) := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simpa only [TerminalParityMeasure.chain,List.map_nil,Option.map_none] using
      (flipBelow_natural f none cinB target)
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            cases ys with
            | nil =>
              have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
              have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
              have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
              have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
              subst bits xs cs ds
              simp only [TerminalParityMeasure.chain,TerminalParityMeasure.leaf,List.map_cons,List.map_nil,
                rename_append,mappedSum_natural,measured_terminal_natural]
              rfl
            | cons y' ys =>
              cases bits with
              | nil => simp at hb
              | cons b' bits =>
                have tail := ih (b'::bits) xs cs ds c d
                  (by simpa using hb) (by simpa using hx)
                  (by simpa using hc) (by simpa using hd)
                change renameProgram f
                    (prepareHead b a y cinC cinB c d ++
                      TerminalParityMeasure.chain (b'::bits) xs (y'::ys) cs ds c d target ++
                      releaseHead b a y cinC cinB c d) =
                  prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) ++
                    TerminalParityMeasure.chain ((b'::bits).map (mapBit f))
                      (xs.map f) ((y'::ys).map f) (cs.map f) (ds.map f)
                      (f c) (f d) (f target) ++
                    releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d)
                simp only [rename_append,measured_prepareHead_natural,measured_releaseHead_natural,tail]

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.measured_offset_chain_natural
