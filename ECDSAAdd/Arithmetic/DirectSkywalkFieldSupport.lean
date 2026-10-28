import ECDSAAdd.Arithmetic.DirectSkywalkControlledPort

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

namespace ECDSAAdd.Arithmetic.DirectSupport
attribute [local irreducible] wireBlock swapRegisters fusedSharedRetainedCell fusedSharedInverseCell
attribute [local irreducible] mixedTranscriptFieldCell mixedTranscriptInverseFieldCell
attribute [local irreducible] FusedHalfPorts.compactForwardProgram FusedHalfPorts.compactInverseProgram

/-- The effective sign flag may be outside the shared arithmetic universe.
Compact-kernel support lists that flag explicitly, alongside borrowed sites. -/
theorem externalKernel (w : Nat → Wire) (g : Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) (hg : g∈W) :
    wires (fusedSharedPorts w g).compactForwardProgram⊆W ∧
    wires (fusedSharedPorts w g).compactInverseProgram⊆W := by
  have own : (fusedSharedPorts w g).wires.toFinset⊆W := by
    rw [fusedSharedPorts_wires]
    intro q hq
    rcases List.mem_cons.mp (List.mem_toFinset.mp hq) with rfl|hq
    · exact hg
    · exact hW (List.mem_toFinset.mpr (fusedSharedSites_subset w hq))
  exact ⟨((fusedSharedPorts w g).compact_forward_support
    (fusedSharedPorts_widths w g) (fusedSharedPorts_early w g)).trans own,
    ((fusedSharedPorts w g).compact_inverse_support
    (fusedSharedPorts_widths w g) (fusedSharedPorts_early w g)).trans own⟩

theorem externalSigned (w : Nat → Wire) (g : Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) (hg : g∈W) :
    wires (fusedSharedRetainedSignedHalf w g)⊆W ∧ wires (fusedSharedInverseSigned w g)⊆W := by
  have hk := externalKernel w g W hW hg
  have hx : wires [.X g]⊆W := by simpa [wires,Instr.wires] using hg
  simp only [fusedSharedRetainedSignedHalf,fusedSharedInverseSigned,fusedFieldSignedHalf,
    wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨hx,hk.1⟩,hx⟩,⟨⟨hx,hk.2⟩,hx⟩⟩

theorem externalCells (w : Nat → Wire) (g swap : Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) (hg : g∈W) (hs : swap∈W) :
    wires (fusedSharedRetainedCell w g swap)⊆W ∧ wires (fusedSharedInverseCell w g swap)⊆W := by
  have hk := externalSigned w g W hW hg
  have hw := skywalkShared_field_widths w
  have hlen : ((skywalkSharedField w).z.take (skywalkSharedField w).low.length).length=
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length).length := by
    simp [List.length_take,ModInPlaceLayout.z,ModAddCoreLayout.z,hw.core.low,hw.core.a]
  have sw := swapRegisters_wires swap
    ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
    ((skywalkSharedField w).a.take (skywalkSharedField w).low.length) hlen
  have hswap : wires (swapRegisters swap
      ((skywalkSharedField w).z.take (skywalkSharedField w).low.length)
      ((skywalkSharedField w).a.take (skywalkSharedField w).low.length))⊆W := by
    intro q hq
    have hh := sw hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh
    rcases hh with rfl|hz|ha
    · exact hs
    · exact hW (List.mem_toFinset.mpr (retained_field_subset_shared w
        (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take hz])))
    · exact hW (List.mem_toFinset.mpr (retained_field_subset_shared w
        (by simp [ModInPlaceLayout.wires,List.mem_of_mem_take ha])))
  simp only [fusedSharedRetainedCell,fusedSharedInverseCell,wires_append,Finset.union_subset_iff]
  exact ⟨⟨hk.1,hswap⟩,⟨hswap,hk.2⟩⟩

theorem selectWindow (b source flag : Wire) (constant : Bool) (body : Program) (W : Finset Wire)
    (hb : b∈W) (hs : source∈W) (hf : flag∈W) (hbody : wires body⊆W) :
    wires (transcriptSelectWindow b source flag constant body)⊆W := by
  have sides : wires (transcriptSelectCompute b source flag constant)⊆W ∧
      wires (transcriptSelectExpose flag constant)⊆W ∧
      wires (transcriptSelectErase b source flag constant)⊆W := by
    cases constant <;>
      simp [transcriptSelectCompute,transcriptSelectExpose,transcriptSelectErase,
        wires,Instr.wires,correctionWires,Finset.subset_iff] <;> aesop
  simp only [transcriptSelectWindow,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨sides.1,sides.2.1⟩,hbody⟩,sides.2.1⟩,sides.2.2⟩

theorem mixedCells (w : Nat → Wire) (b g swap effG effS : Wire) (cg cs : Bool) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W)
    (hb : b∈W) (hg : g∈W) (hs : swap∈W) (heG : effG∈W) (heS : effS∈W) :
    wires (mixedTranscriptFieldCell w b g swap effG effS cg cs)⊆W ∧
    wires (mixedTranscriptInverseFieldCell w b g swap effG effS cg cs)⊆W := by
  have cells := externalCells w effG effS W hW heG heS
  simp only [mixedTranscriptFieldCell,mixedTranscriptInverseFieldCell]
  constructor
  · exact selectWindow b g effG cg _ W hb hg heG
      (selectWindow b swap effS cs _ W hb hs heS cells.1)
  · exact selectWindow b g effG cg _ W hb hg heG
      (selectWindow b swap effS cs _ W hb hs heS cells.2)

theorem mixedReplay (w : Nat → Wire) (b effG effS : Wire) (ls : List MixedTranscriptLetter)
    (W : Finset Wire) (hW : (skywalkSharedWires w).toFinset⊆W)
    (hb : b∈W) (hg : effG∈W) (hs : effS∈W)
    (ht : ∀ l∈ls,l.1.1∈W ∧ l.1.2∈W) :
    wires (mixedTranscriptReplay w b effG effS ls)⊆W ∧
    wires (mixedTranscriptInverseReplay w b effG effS ls)⊆W := by
  induction ls with
  | nil => simp [mixedTranscriptReplay,mixedTranscriptInverseReplay,wires]
  | cons l ls ih =>
    have hl := ht l (by simp)
    have hc := mixedCells w b l.1.1 l.1.2 effG effS l.2.1 l.2.2 W hW hb hl.1 hl.2 hg hs
    have hi := ih (fun k hk => ht k (by simp [hk]))
    simp only [mixedTranscriptReplay,mixedTranscriptInverseReplay,wires_append,Finset.union_subset_iff]
    exact ⟨⟨hc.1,hi.1⟩,⟨hi.2,hc.2⟩⟩

private theorem zip_record (rs : List (Wire×Wire)) (cs : List (Bool×Bool))
    (l : MixedTranscriptLetter) (hl : l∈rs.zip cs) : l.1∈rs := by
  induction rs generalizing cs with
  | nil => simp at hl
  | cons r rs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      simp only [List.zip_cons_cons,List.mem_cons] at hl
      rcases hl with rfl|hl
      · simp
      · exact List.mem_cons_of_mem r (ih cs hl)

theorem tapeSupport (w : Nat → Wire) (W : Finset Wire)
    (hW : (skywalkSharedWires w).toFinset⊆W) :
    ∀ l∈mixedTranscriptTape w,l.1.1∈W ∧ l.1.2∈W := by
  intro l hl
  have recorded := zip_record (skywalkSharedTape w) mixedTranscriptUnitTrace l hl
  have hh := retained_tape_subset_shared w l.1 recorded
  exact ⟨hW (List.mem_toFinset.mpr hh.1),hW (List.mem_toFinset.mpr hh.2)⟩

end ECDSAAdd.Arithmetic.DirectSupport
