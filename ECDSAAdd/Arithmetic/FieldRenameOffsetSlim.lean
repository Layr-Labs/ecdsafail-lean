import ECDSAAdd.Arithmetic.FieldRenameOffset
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlimProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.FieldRename
open BalancedCleanupOffset

attribute [local irreducible] mappedMajority mappedSum mappedEraseCarry majority eraseCarry

private theorem slim_prepareHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (prepareHead b a y cinC cinB c d) =
      prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [prepareHead,rename_append,mappedMajority_natural,mappedSum_natural,
    majority_natural]
  rfl

private theorem slim_releaseHead_natural (f : Wire → Wire) (b : MappedBit)
    (a y cinC cinB c d : Wire) :
    renameProgram f (releaseHead b a y cinC cinB c d) =
      releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) := by
  simp only [releaseHead,rename_append,eraseCarry_natural,mappedSum_natural,
    mappedEraseCarry_natural]
  rfl

private theorem slim_compare_singleton_natural (f : Wire → Wire)
    (a y d cin target : Wire) :
    renameProgram f (compareChain none [a] [y] [d] cin target) =
      compareChain none [f a] [f y] [f d] (f cin) (f target) := by
  simp only [compareChain,rename_append,majority_natural,eraseCarry_natural,
    flipBelow_natural,Option.map_none]

/-- Relabel the actual shortened final branch as well as all ordinary heads.
Aligned lengths are sufficient for every production-width call. -/
theorem slim_offset_chain_natural (f : Wire → Wire) (bits : List MappedBit)
    (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    renameProgram f (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC cinB target) =
      BalancedCleanupOffsetSlim.chain (bits.map (mapBit f)) (xs.map f) (ys.map f)
        (cs.map f) (ds.map f) (f cinC) (f cinB) (f target) := by
  induction ys generalizing bits xs cs ds cinC cinB with
  | nil =>
    have be := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have xe := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have ce := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have de := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    simpa only [BalancedCleanupOffsetSlim.chain,List.map_nil,Option.map_none] using
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
              simp only [BalancedCleanupOffsetSlim.chain,List.map_cons,List.map_nil,
                rename_append,mappedSum_natural,slim_compare_singleton_natural]
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
                      BalancedCleanupOffsetSlim.chain (b'::bits) xs (y'::ys) cs ds c d target ++
                      releaseHead b a y cinC cinB c d) =
                  prepareHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d) ++
                    BalancedCleanupOffsetSlim.chain ((b'::bits).map (mapBit f))
                      (xs.map f) ((y'::ys).map f) (cs.map f) (ds.map f)
                      (f c) (f d) (f target) ++
                    releaseHead (mapBit f b) (f a) (f y) (f cinC) (f cinB) (f c) (f d)
                simp only [rename_append,slim_prepareHead_natural,slim_releaseHead_natural,tail]

private theorem slim_front_natural (f : Wire → Wire) (L : Layout) :
    renameProgram f (front L)=front (mapOffset f L) := by
  simp only [front,rename_append,prepareSign_natural,offset_view_natural]
  rfl

attribute [local irreducible] BalancedCleanupOffsetSlim.chain

/-- Naturality of the actual 511-T/M cleanup, including the singleton leaf.
No injectivity premise is needed for this syntactic relabeling identity. -/
theorem slim_offset_program_natural (f : Wire → Wire) (L : Layout) (hw : L.Widths) :
    renameProgram f (BalancedCleanupOffsetSlim.program L) =
      BalancedCleanupOffsetSlim.program (mapOffset f L) := by
  have widths := BalancedCleanup.widths L.toCircuit.toLayout hw.1
  have cy : L.carry.length=256 := hw.1.2.2
  have co : L.offsetCarry.length=256 := hw.2
  have cn := slim_offset_chain_natural f (offsetBits L) L.y L.r L.offsetCarry L.carry
    L.one L.cout L.parity (by simp [offsetBits,widths.2.1]) (by omega)
    (by omega) (by omega)
  simp only [BalancedCleanupOffsetSlim.program,rename_append,rename_reverse,
    slim_front_natural,cn,offsetBits_map]
  simp only [mapOffset,mapCircuit,mapCleanup,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.map_cons,List.map_append]
  rfl

end ECDSAAdd.Arithmetic.FieldRename
#print axioms ECDSAAdd.Arithmetic.FieldRename.slim_offset_chain_natural
#print axioms ECDSAAdd.Arithmetic.FieldRename.slim_offset_program_natural
