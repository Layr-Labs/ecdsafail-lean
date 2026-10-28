import ECDSAAdd.Arithmetic.CuccaroStreamedSquareSupport
import ECDSAAdd.Arithmetic.ControlledNormalizedMod

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

def controlledAddSource (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  controlledNormalizedModAdd c scratch (L.source src) SquareReduction.c SquareReduction.p

def controlledSubSource (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  controlledNormalizedModSub c scratch (L.source src) SquareReduction.c SquareReduction.p

def controlledAddCMinusOne (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  L.controlledAddSource c scratch (L.shifted src 4)++
  L.controlledSubSource c scratch (L.shifted src 6)++
  L.controlledAddSource c scratch (L.shifted src 10)++
  L.controlledAddSource c scratch (L.shifted src 32)

def controlledSubCMinusOne (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (src : List Wire) : Program :=
  L.controlledSubSource c scratch (L.shifted src 4)++
  L.controlledAddSource c scratch (L.shifted src 6)++
  L.controlledSubSource c scratch (L.shifted src 10)++
  L.controlledSubSource c scratch (L.shifted src 32)

def controlledAddRotate128 (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (overhang : Bool) : Program :=
  L.controlledAddSource c scratch L.rotated128++
  L.controlledAddCMinusOne c scratch (L.core.product.drop 128)++
  if overhang then L.controlledAddSource c scratch
    (L.shifted (L.core.product.drop 256) 128) else []

def controlledSubRotate128 (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (overhang : Bool) : Program :=
  L.controlledSubSource c scratch L.rotated128++
  L.controlledSubCMinusOne c scratch (L.core.product.drop 128)++
  if overhang then L.controlledSubSource c scratch
    (L.shifted (L.core.product.drop 256) 128) else []

def controlledAddShiftFull (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (j : Nat) : Program :=
  if j=0 then L.controlledAddSource c scratch (L.core.product.take 256)
  else L.controlledAddSource c scratch (rotateFull (L.core.product.take 256) j)++
    L.controlledAddCMinusOne c scratch ((L.core.product.take 256).drop (256-j))

def controlledSubShiftFull (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire)
    (j : Nat) : Program :=
  if j=0 then L.controlledSubSource c scratch (L.core.product.take 256)
  else L.controlledSubSource c scratch (rotateFull (L.core.product.take 256) j)++
    L.controlledSubCMinusOne c scratch ((L.core.product.take 256).drop (256-j))

def controlledTimesC (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.controlledSubShiftFull c scratch 0++L.controlledSubShiftFull c scratch 4++
  L.controlledAddShiftFull c scratch 6++L.controlledSubShiftFull c scratch 10++
  L.controlledSubShiftFull c scratch 32

def controlledBranchA (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.core.square128 L.core.low++
    (L.controlledSubSource c scratch (L.core.product.take 256)++
      L.controlledAddRotate128 c scratch false)++L.core.square128Clear L.core.low

def controlledBranchB (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.core.square128 L.core.high++
    (L.controlledAddRotate128 c scratch false++L.controlledTimesC c scratch)++
    L.core.square128Clear L.core.high

def controlledBranchC (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  (L.core.prepareSum++L.core.square129)++L.controlledSubRotate128 c scratch true++
    (L.core.square129Clear++L.core.clearSum)

/-- Compute and uncompute each square unconditionally.  Normalize each source
unconditionally too; only its canonical modular output update is controlled. -/
def controlledProgram (L : CuccaroStreamedSquareWideLayout) (c scratch : Wire) : Program :=
  L.controlledBranchA c scratch++L.controlledBranchB c scratch++L.controlledBranchC c scratch

theorem source_layout_subset (L : CuccaroStreamedSquareWideLayout)
    (src : List Wire) (hv : L.SourceView src) : (L.source src).wires⊆L.wires := by
  intro q hq
  have srcMem (hq : q∈src) : q∈L.core.product ∨ q∈L.foldPad := by
    by_contra h
    simp only [not_or] at h
    have hs := hv.count_le q
    have hc := List.count_pos_iff.mpr hq
    rw [List.count_eq_zero.mpr h.1,List.count_eq_zero.mpr h.2] at hs
    omega
  simp only [source,CuccaroNormalizedModLayout.wires,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [wires,CuccaroStreamedSquareLayout.wires,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  have hs : q∈src → q∈L.core.product ∨ q∈L.core.pad ∨ q∈L.overflowPad := by
    intro h
    simpa only [foldPad,List.mem_append,or_assoc] using srcMem h
  tauto

variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c scratch : Wire) (hc : c∉L.wires) (ht : scratch∉L.wires) (hct : c≠scratch)
include hw hn hc ht hct

theorem controlledSource_exact (src : List Wire) (hv : L.SourceView src) :
    ExactControl c scratch (L.addSource src) (L.controlledAddSource c scratch src) ∧
    ExactControl c scratch (L.subSource src) (L.controlledSubSource c scratch src) := by
  have embed := L.source_layout_subset src hv
  exact controlledNormalizedMod_exact c scratch (L.source src) 256
    SquareReduction.c SquareReduction.p (L.source_widths hw src hv.length)
    (L.source_nodup hn src hv) (fun h => hc (embed h)) (fun h => ht (embed h)) hct

theorem controlledCMinusOne_exact (src : List Wire)
    (hsrc : ∀q,src.count q≤L.core.product.count q)
    (hs2 : 2≤src.length) (hs : src.length+32≤256) :
    ExactControl c scratch (L.addCMinusOne src) (L.controlledAddCMinusOne c scratch src) ∧
    ExactControl c scratch (L.subCMinusOne src) (L.controlledSubCMinusOne c scratch src) := by
  have s4 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 4 hs2 (by omega))
  have s6 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 6 hs2 (by omega))
  have s10 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 10 hs2 (by omega))
  have s32 := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shifted_view hw src hsrc 32 hs2 hs)
  exact ⟨((s4.1.append s6.2).append s10.1).append s32.1,
    ((s4.2.append s6.1).append s10.2).append s32.2⟩

theorem controlledRotate128_exact (overhang : Bool) :
    ExactControl c scratch (L.addRotate128 overhang) (L.controlledAddRotate128 c scratch overhang) ∧
    ExactControl c scratch (L.subRotate128 overhang) (L.controlledSubRotate128 c scratch overhang) := by
  have rot := L.controlledSource_exact hw hn c scratch hc ht hct _ (L.rotated128_view hw)
  have terms := L.controlledCMinusOne_exact hw hn c scratch hc ht hct
    (L.core.product.drop 128) (L.productDrop_count 128)
    (by simp [hw.core.product]) (by simp [hw.core.product])
  have tail := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.shiftedProductDrop_view hw 256 128 (by simp [hw.core.product])
      (by simp [hw.core.product]))
  cases overhang
  · exact ⟨(rot.1.append terms.1).append (ExactControl.nil c scratch),
      (rot.2.append terms.2).append (ExactControl.nil c scratch)⟩
  · exact ⟨(rot.1.append terms.1).append tail.1,
      (rot.2.append terms.2).append tail.2⟩

theorem controlledShiftFull_exact (j : Nat) (hj2 : 2≤j) (hj : j≤224) :
    ExactControl c scratch (L.addShiftFull (L.core.product.take 256) j)
      (L.controlledAddShiftFull c scratch j) ∧
    ExactControl c scratch (L.subShiftFull (L.core.product.take 256) j)
      (L.controlledSubShiftFull c scratch j) := by
  have rot := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.rotateFull_view hw j (by omega))
  have len : ((L.core.product.take 256).drop (256-j)).length=j := by
    simp [hw.core.product]
    omega
  have terms := L.controlledCMinusOne_exact hw hn c scratch hc ht hct
    ((L.core.product.take 256).drop (256-j)) (L.productTakeDrop_count (256-j))
    (by rw [len]; exact hj2) (by rw [len]; omega)
  have jnz : j≠0 := by omega
  simpa only [addShiftFull,subShiftFull,controlledAddShiftFull,controlledSubShiftFull,
    jnz,if_false] using And.intro (rot.1.append terms.1) (rot.2.append terms.2)

theorem controlledTimesC_exact :
    ExactControl c scratch (L.subTimesC (L.core.product.take 256))
      (L.controlledTimesC c scratch) := by
  have base := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.productTake256_view hw)
  have s4 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 4 (by omega) (by omega)
  have s6 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 6 (by omega) (by omega)
  have s10 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 10 (by omega) (by omega)
  have s32 := L.controlledShiftFull_exact hw hn c scratch hc ht hct 32 (by omega) (by omega)
  simpa only [subTimesC,controlledTimesC,subShiftFull,controlledSubShiftFull,if_true] using
    (((base.2.append s4.2).append s6.1).append s10.2).append s32.2

private theorem certified_away (p : Program) (hp : L.Certified p) :
    c∉ECDSAAdd.wires p ∧ scratch∉ECDSAAdd.wires p := by
  exact ⟨fun h => hc (List.mem_toFinset.mp (hp.2 h)),
    fun h => ht (List.mem_toFinset.mp (hp.2 h))⟩

theorem controlledBranchA_exact :
    ExactControl c scratch L.branchA (L.controlledBranchA c scratch) := by
  have prod := L.square128_certified hw hn L.core.low (L.core.low_length hw.core)
    (by intro q; exact (List.take_sublist 128 L.core.y).count_le q)
  have away := L.certified_away hw hn c scratch hc ht hct _ prod.1
  have sub := L.controlledSource_exact hw hn c scratch hc ht hct _
    (L.productTake256_view hw)
  have rot := L.controlledRotate128_exact hw hn c scratch hc ht hct false
  have inner := sub.2.append rot.1
  have result := ExactControl.sandwich prod.1.1 away.1 away.2 inner
  have clearEq : L.core.square128Clear L.core.low=
      (L.core.square128 L.core.low).reverse := rfl
  simpa only [branchA,controlledBranchA,clearEq,List.append_assoc] using result

theorem controlledBranchB_exact :
    ExactControl c scratch L.branchB (L.controlledBranchB c scratch) := by
  have prod := L.square128_certified hw hn L.core.high (L.core.high_length hw.core)
    (by
      intro q
      exact ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
        ((List.drop_sublist 128 L.core.y).count_le q))
  have away := L.certified_away hw hn c scratch hc ht hct _ prod.1
  have rot := L.controlledRotate128_exact hw hn c scratch hc ht hct false
  have times := L.controlledTimesC_exact hw hn c scratch hc ht hct
  have result := ExactControl.sandwich prod.1.1 away.1 away.2 (rot.1.append times)
  have clearEq : L.core.square128Clear L.core.high=
      (L.core.square128 L.core.high).reverse := rfl
  simpa only [branchB,controlledBranchB,clearEq,List.append_assoc] using result

theorem controlledBranchC_exact :
    ExactControl c scratch L.branchC (L.controlledBranchC c scratch) := by
  have prep := L.sum_certified hw hn
  have sq := L.square129_certified hw hn
  have producer := prep.1.append sq.1
  have away := L.certified_away hw hn c scratch hc ht hct _ producer
  have rot := L.controlledRotate128_exact hw hn c scratch hc ht hct true
  have result := ExactControl.sandwich producer.1 away.1 away.2 rot.2
  have clearEq : L.core.square129Clear=(L.core.square129).reverse := rfl
  simpa only [branchC,controlledBranchC,clearEq,CuccaroStreamedSquareLayout.clearSum,
    List.reverse_append,List.append_assoc] using result

/-- Whole-state equality with the previous all-gates-controlled square, using
the same reusable scratch wire and no additional qubit sites. -/
theorem controlledProgram_exact :
    ExactControl c scratch L.program (L.controlledProgram c scratch) := by
  have a := L.controlledBranchA_exact hw hn c scratch hc ht hct
  have b := L.controlledBranchB_exact hw hn c scratch hc ht hct
  have z := L.controlledBranchC_exact hw hn c scratch hc ht hct
  exact (a.append b).append z

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
