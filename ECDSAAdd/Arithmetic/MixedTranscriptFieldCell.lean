import ECDSAAdd.Arithmetic.TranscriptSelectFlag
import ECDSAAdd.Arithmetic.FusedSharedInverseCell
namespace ECDSAAdd.Arithmetic
open Secp256k1
/-- The effective transcript equals the recorded bit in the enabled branch,
and the supplied fixed transcript bit in the inactive branch. -/
def mixedTranscriptBit (base : BasisState) (b source : Wire) (constant : Bool) : Bool :=
  if base b then base source else constant
def mixedTranscriptBase (base : BasisState) (b source flag : Wire)
    (constant : Bool) : BasisState :=
  writeBit base flag (mixedTranscriptBit base b source constant)
private theorem select_start (b source flag : Wire) (constant : Bool)
    (hn : [b,source,flag].Nodup) (s : State) (m : List Bool)
    (hf : s.basis flag=false) :
    run (transcriptSelectCompute b source flag constant ++
      transcriptSelectExpose flag constant) m s=
      ⟨s.phase,mixedTranscriptBase s.basis b source flag constant⟩ := by
  rw [run_append,transcriptSelectCompute_correct b source flag constant hn]
  apply State.extensionality
  · cases constant <;> rfl
  · funext q
    by_cases hq : q=flag
    · subst q
      cases hb : s.basis b <;> cases hs : s.basis source <;> cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,mixedTranscriptBit,
          writeBit,Function.update,hf,hb,hs]
    · cases constant <;>
        simp [transcriptSelectExpose,run,mixedTranscriptBase,writeBit,Function.update,hq]

/-- Lift an exact pair-framed body through a complete measured selection
window. The body's frame preserves the selected flag and both inputs. -/
theorem transcriptSelectWindow_pairFrame (b source flag : Wire) (constant : Bool)
    (z a : List Wire) (hn : [b,source,flag].Nodup)
    (hb : b∉z ∧ b∉a) (hs : source∉z ∧ source∉a)
    (hf : flag∉z ∧ flag∉a) (base : BasisState) (hzero : base flag=false)
    (X Y X' Y' : Nat) (body : Program)
    (hbody : Triple (PairFrame z a (mixedTranscriptBase base b source flag constant) X Y)
      body (PairFrame z a (mixedTranscriptBase base b source flag constant) X' Y')) :
    Triple (PairFrame z a base X Y) (transcriptSelectWindow b source flag constant body)
      (PairFrame z a base X' Y') := by
  let selected := mixedTranscriptBase base b source flag constant
  have hstart : Triple (PairFrame z a base X Y)
      (transcriptSelectCompute b source flag constant ++ transcriptSelectExpose flag constant)
      (PairFrame z a selected X Y) := by
    intro s m h
    have hz : s.basis flag=false := (h.2.2 flag hf.1 hf.2).trans hzero
    rw [select_start b source flag constant hn s m hz]
    refine ⟨rfl,?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
          fun he => hf.1 (he ▸ hq)])).trans h.1
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from
          fun he => hf.2 (he ▸ hq)])).trans h.2.1
    · intro q hqz hqa
      by_cases hq : q=flag
      · subst q
        simp [selected,mixedTranscriptBase,mixedTranscriptBit,writeBit,
          h.2.2 b hb.1 hb.2,h.2.2 source hs.1 hs.2]
      · simpa [selected,mixedTranscriptBase,writeBit,Function.update,hq] using h.2.2 q hqz hqa
  have hfinish : Triple (PairFrame z a selected X' Y')
      (transcriptSelectExpose flag constant ++ transcriptSelectErase b source flag constant)
      (PairFrame z a base X' Y') := by
    intro s m h
    have hd := List.nodup_cons.mp hn
    have hbs : b≠flag := by
      intro he
      exact hd.1 (by simp [he])
    have hsf : source≠flag := by
      simpa using (List.nodup_cons.mp hd.2).1
    have hv : s.basis flag=(if s.basis b then s.basis source else constant) := by
      rw [h.2.2 flag hf.1 hf.2,h.2.2 b hb.1 hb.2,h.2.2 source hs.1 hs.2]
      simp [selected,mixedTranscriptBase,mixedTranscriptBit,writeBit,hbs,hsf]
    rw [transcriptSelect_finish_correct b source flag constant hn s m hv]
    refine ⟨rfl,?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [writeBit,Function.update,show q≠flag from fun he => hf.1 (he ▸ hq)])).trans h.1
    · exact (regValue_congr _ _ _ (fun q hq => by
        simp [writeBit,Function.update,show q≠flag from fun he => hf.2 (he ▸ hq)])).trans h.2.1
    · intro q hqz hqa
      by_cases hq : q=flag
      · subst q
        simpa [writeBit] using hzero.symm
      · simpa [selected,mixedTranscriptBase,writeBit,Function.update,hq] using h.2.2 q hqz hqa
  simpa only [transcriptSelectWindow,List.append_assoc] using (hstart.seq hbody).seq hfinish

/-- Two external clean flags surround a forward retained cell. The second
flag is erased first; every measured cleanup is emitted in forward order. -/
def mixedTranscriptFieldCell (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) : Program :=
  transcriptSelectWindow b g effG inactiveG
    (transcriptSelectWindow b swap effS inactiveS (fusedSharedRetainedCell w effG effS))

/-- Independently emitted inverse arithmetic, with the same transcript
selection windows. This does not reverse any measurement instruction. -/
def mixedTranscriptInverseFieldCell (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) : Program :=
  transcriptSelectWindow b g effG inactiveG
    (transcriptSelectWindow b swap effS inactiveS (fusedSharedInverseCell w effG effS))

/-- All transcript wires are external to the canonical field layout. Only
the two effective flags must also avoid the retained kernel's borrowed sites. -/
structure MixedTranscriptFieldLayout (w : Nat → Wire) (b g swap effG effS : Wire) : Prop where
  shared : (skywalkSharedWires w).Nodup
  controls : (b::g::swap::effG::effS::(skywalkSharedField w).wires).Nodup
  gKernel : effG∉fusedSharedIds.map w
  gUnused : effG∉skywalkSharedUnused w
  sUnused : effS∉skywalkSharedUnused w

namespace MixedTranscriptFieldLayout

theorem selection_g {w : Nat → Wire} {b g swap effG effS : Wire}
    (h : MixedTranscriptFieldLayout w b g swap effG effS) : [b,g,effG].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hc := List.nodup_iff_count.mp h.controls q
  simp only [List.count_cons,List.count_nil] at hc ⊢
  omega

theorem selection_s {w : Nat → Wire} {b g swap effG effS : Wire}
    (h : MixedTranscriptFieldLayout w b g swap effG effS) : [b,swap,effS].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hc := List.nodup_iff_count.mp h.controls q
  simp only [List.count_cons,List.count_nil] at hc ⊢
  omega

theorem cell {w : Nat → Wire} {b g swap effG effS : Wire}
    (h : MixedTranscriptFieldLayout w b g swap effG effS) :
    (b::effS::effG::(skywalkSharedField w).wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hc := List.nodup_iff_count.mp h.controls q
  simp only [List.count_cons] at hc ⊢
  omega

theorem outside {w : Nat → Wire} {b g swap effG effS : Wire}
    (h : MixedTranscriptFieldLayout w b g swap effG effS) (q : Wire)
    (hq : q∈[b,g,swap,effG,effS]) : q∉(skywalkSharedField w).wires := by
  intro hm
  have hc := List.nodup_iff_count.mp h.controls q
  have hp := List.count_pos_iff.mpr hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl <;> simp [List.count_cons] at hc <;> omega

theorem pair_outside {w : Nat → Wire} {b g swap effG effS : Wire}
    (h : MixedTranscriptFieldLayout w b g swap effG effS) (q : Wire)
    (hq : q∈[b,g,swap,effG,effS]) :
    q∉(skywalkSharedField w).z ∧ q∉(skywalkSharedField w).a := by
  have ho := h.outside q hq
  exact ⟨fun hz => ho (by simp [ModInPlaceLayout.wires,hz]),
    fun ha => ho (by simp [ModInPlaceLayout.wires,ha])⟩

theorem eff_ne {w : Nat → Wire} {b g swap effG effS : Wire}
    (h : MixedTranscriptFieldLayout w b g swap effG effS) : effS≠effG := by
  have hd := List.nodup_cons.mp
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp h.controls).2).2).2
  exact fun he => hd.1 (by simp [he])

end MixedTranscriptFieldLayout
private theorem mixed_base_reg (base : BasisState) (b source flag : Wire) (constant : Bool)
    (r : List Wire) (hf : flag∉r) :
    regValue r (mixedTranscriptBase base b source flag constant)=regValue r base := by
  apply regValue_congr
  intro q hq
  simp [mixedTranscriptBase,writeBit,Function.update,show q≠flag from fun he => hf (he ▸ hq)]

private theorem mixed_base_other (base : BasisState) (b source flag q : Wire)
    (constant : Bool) (hq : q≠flag) :
    mixedTranscriptBase base b source flag constant q=base q := by
  simp [mixedTranscriptBase,writeBit,Function.update,hq]
/-- A shared lifting theorem lets the forward and independently emitted
inverse cells use exactly the same selection and cleanup proof. -/
theorem mixedTranscriptFieldWindow_frame (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) (hl : MixedTranscriptFieldLayout w b g swap effG effS)
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0)
    (X Y : Fp) (body : Program) (result : Bool → Bool → Fp×Fp → Fp×Fp)
    (hbody : ∀ selected : BasisState,
      regValue (skywalkSharedField w).work selected=0 →
      regValue (skywalkSharedUnused w) selected=0 →
      Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a selected X.val Y.val)
        body (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a selected
          (result (selected effG) (selected effS) (X,Y)).1.val
          (result (selected effG) (selected effS) (X,Y)).2.val)) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (transcriptSelectWindow b g effG inactiveG (transcriptSelectWindow b swap effS inactiveS body))
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (result (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).1.val
        (result (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).2.val) := by
  let bg := mixedTranscriptBase base b g effG inactiveG
  let bs := mixedTranscriptBase bg b swap effS inactiveS
  have hne := hl.eff_ne
  have hbgS : bg effS=false := (mixed_base_other base b g effG effS inactiveG hne).trans hs0
  have hbgB : bg b=base b := mixed_base_other _ _ _ _ _ _ (by
    have hh := List.nodup_cons.mp hl.selection_g
    intro he; exact hh.1 (by simp [he]))
  have hbgSwap : bg swap=base swap := mixed_base_other _ _ _ _ _ _ (by
    have hh := List.nodup_cons.mp
      (List.nodup_cons.mp (List.nodup_cons.mp hl.controls).2).2
    intro he; exact hh.1 (by simp [he]))
  have hbsG : bs effG=mixedTranscriptBit base b g inactiveG := by
    change mixedTranscriptBase bg b swap effS inactiveS effG=_
    rw [mixed_base_other bg b swap effS effG inactiveS (Ne.symm hne)]
    simp [bg,mixedTranscriptBase,writeBit]
  have hbsS : bs effS=mixedTranscriptBit base b swap inactiveS := by
    simp [bs,mixedTranscriptBase,mixedTranscriptBit,writeBit,hbgB,hbgSwap]
  have hGwork : effG∉(skywalkSharedField w).work := fun hm =>
    hl.outside effG (by simp) (by simp [ModInPlaceLayout.wires,hm])
  have hSwork : effS∉(skywalkSharedField w).work := fun hm =>
    hl.outside effS (by simp) (by simp [ModInPlaceLayout.wires,hm])
  have hwork : regValue (skywalkSharedField w).work bs=0 := by
    exact (mixed_base_reg bg b swap effS inactiveS _ hSwork).trans
      ((mixed_base_reg base b g effG inactiveG _ hGwork).trans hk)
  have hunused : regValue (skywalkSharedUnused w) bs=0 := by
    exact (mixed_base_reg bg b swap effS inactiveS _ hl.sUnused).trans
      ((mixed_base_reg base b g effG inactiveG _ hl.gUnused).trans hu)
  have hc := hbody bs hwork hunused
  rw [hbsG,hbsS] at hc
  have hin := transcriptSelectWindow_pairFrame b swap effS inactiveS _ _ hl.selection_s
    (hl.pair_outside b (by simp)) (hl.pair_outside swap (by simp))
    (hl.pair_outside effS (by simp)) bg hbgS X.val Y.val _ _ body hc
  exact transcriptSelectWindow_pairFrame b g effG inactiveG _ _ hl.selection_g
    (hl.pair_outside b (by simp)) (hl.pair_outside g (by simp))
    (hl.pair_outside effG (by simp)) base hg0 X.val Y.val _ _ _ hin
/-- Exact canonical field pair, phase, all recorded controls and clean
effective flags, for both enable branches and arbitrary measurement records. -/
theorem mixedTranscriptFieldCell_frame (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) (hl : MixedTranscriptFieldLayout w b g swap effG effS)
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (mixedTranscriptFieldCell w b g swap effG effS inactiveG inactiveS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadCell (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).1.val
        (skywalkPayloadCell (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).2.val) := by
  apply mixedTranscriptFieldWindow_frame w b g swap effG effS inactiveG inactiveS hl
    base hg0 hs0 hk hu X Y (fusedSharedRetainedCell w effG effS) skywalkPayloadCell
  intro selected hwork hunused
  exact fusedSharedRetained_leaf_frame b effS effG w hl.shared hl.gKernel hl.cell
    hl.gUnused hl.sUnused selected hwork hunused X Y
theorem mixedTranscriptInverseFieldCell_frame (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) (hl : MixedTranscriptFieldLayout w b g swap effG effS)
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (mixedTranscriptInverseFieldCell w b g swap effG effS inactiveG inactiveS)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadUncell (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).1.val
        (skywalkPayloadUncell (mixedTranscriptBit base b g inactiveG)
          (mixedTranscriptBit base b swap inactiveS) (X,Y)).2.val) := by
  apply mixedTranscriptFieldWindow_frame w b g swap effG effS inactiveG inactiveS hl
    base hg0 hs0 hk hu X Y (fusedSharedInverseCell w effG effS) skywalkPayloadUncell
  intro selected hwork hunused
  exact fusedSharedInverse_leaf_frame b effS effG w hl.shared hl.gKernel hl.cell
    hl.gUnused selected hwork hunused X Y
private theorem mixed_swap_nodup (w : Nat → Wire) (b g swap effG effS : Wire)
    (hl : MixedTranscriptFieldLayout w b g swap effG effS) :
    (effS::(skywalkSharedField w).z++(skywalkSharedField w).a).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hc := List.nodup_iff_count.mp hl.cell q
  simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hc ⊢
  omega
/-- Exactly two Toffolis and two X measurements beyond the retained cell. -/
theorem mixedTranscriptFieldCell_counts (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) (hl : MixedTranscriptFieldLayout w b g swap effG effS) :
    toffoliCount (mixedTranscriptFieldCell w b g swap effG effS inactiveG inactiveS)=1796 ∧
    measurementCount (mixedTranscriptFieldCell w b g swap effG effS inactiveG inactiveS)=1540 := by
  have hc := fusedSharedRetainedCell_counts w effG effS (mixed_swap_nodup _ _ _ _ _ _ hl)
  have hi := transcriptSelectWindow_counts b swap effS inactiveS (fusedSharedRetainedCell w effG effS)
  have ho := transcriptSelectWindow_counts b g effG inactiveG
    (transcriptSelectWindow b swap effS inactiveS (fusedSharedRetainedCell w effG effS))
  simp only [mixedTranscriptFieldCell,ho.1,ho.2,hi.1,hi.2,hc.1,hc.2]
  trivial
theorem mixedTranscriptInverseFieldCell_counts (w : Nat → Wire) (b g swap effG effS : Wire)
    (inactiveG inactiveS : Bool) (hl : MixedTranscriptFieldLayout w b g swap effG effS) :
    toffoliCount (mixedTranscriptInverseFieldCell w b g swap effG effS inactiveG inactiveS)=1796 ∧
    measurementCount (mixedTranscriptInverseFieldCell w b g swap effG effS inactiveG inactiveS)=1540 := by
  have hc := fusedSharedInverseCell_counts w effG effS (mixed_swap_nodup _ _ _ _ _ _ hl)
  have hi := transcriptSelectWindow_counts b swap effS inactiveS (fusedSharedInverseCell w effG effS)
  have ho := transcriptSelectWindow_counts b g effG inactiveG
    (transcriptSelectWindow b swap effS inactiveS (fusedSharedInverseCell w effG effS))
  simp only [mixedTranscriptInverseFieldCell,ho.1,ho.2,hi.1,hi.2,hc.1,hc.2]
  trivial
end ECDSAAdd.Arithmetic
