import ECDSAAdd.Arithmetic.MeasuredFoldPhysical
import ECDSAAdd.Arithmetic.MappedSquarePhysical
import ECDSAAdd.Arithmetic.MeasuredStreamedMaskedProof
import ECDSAAdd.Arithmetic.MeasuredStreamedViews
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareSupport

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
open RecordedQuantum

theorem measuredFold_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (f : MeasuredSquareFold)
    (hs : ∀ q, f.src.count q ≤ L.core.product.count q) : GatePhysical (L.measuredFold f) := by
  rw [L.measuredFold_eq_copied hw]
  exact measuredCopiedFold_physical _ _ _ _ _ _ _ (L.measuredFold_interfaces hn f.src hs)

theorem reflectOutput_physical (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    GatePhysical L.reflectOutput := by
  let N : MeasuredSourceNormalizeLayout :=
    {word:=L.core.out,carry:=L.shortCarry,cin:=L.core.cin,flag:=L.core.normFlag}
  have nd : N.wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist 255 L.foldCarry).count_le q
    simp only [N,MeasuredSourceNormalizeLayout.wires,shortCarry,foldCarry,foldPad,
      wires,CuccaroStreamedSquareLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ht ⊢
    omega
  exact (N.physical SquareReduction.p SquareReduction.c nd).2.2

theorem measuredFolds_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (orientation : Bool) (items : List MeasuredSquareFold)
    (hs : ∀ f ∈ items, ∀ q, f.src.count q ≤ L.core.product.count q) :
    GatePhysical (L.measuredFolds orientation items) := by
  induction items generalizing orientation with
  | nil => simp [measuredFolds,GatePhysical]
  | cons f fs ih =>
    have ht := ih f.negative (fun z hz => hs z (by simp [hz]))
    have hf := L.measuredFold_physical hw hn f (hs f (by simp))
    have hr := L.reflectOutput_physical hn
    simp only [measuredFolds,gatePhysical_append]
    refine ⟨⟨?_,hf⟩,ht⟩
    split
    · simp [GatePhysical]
    · exact hr

theorem withMeasuredSquare_physical (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control :: L.wires).Nodup) (src dst : List Wire)
    (hs : ∀ q, src.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q)
    (hd : ∀ q, dst.count q ≤ L.core.product.count q) (body : Program)
    (hb : GatePhysical body) : GatePhysical (L.withMeasuredSquare control src dst body) := by
  have nd := L.measured_leaf_nodup control hn src dst hs hd
  have nc : (src ++ L.inputBank.take src.length).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have hc : ∀ q ∈ some control, q ∉ L.inputBank.take src.length := by
    intro q hq hm
    have he : control = q := by simpa using hq
    subst q
    have h := List.nodup_iff_count.mp nd control
    have hh := List.count_pos_iff.mpr hm
    simp only [List.count_cons,List.count_append,beq_self_eq_true,ite_true] at h; omega
  have ns : (L.core.cin :: L.inputBank.take src.length ++ dst ++ L.leafPad ++ L.leafCarry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have cp := copyRegister_physical (some control) src (L.inputBank.take src.length) nc hc
  have sq := mappedSignedSquare_physical _ _ _ _ _ ns
  have er := eraseMask_physical control src (L.inputBank.take src.length)
  simp only [withMeasuredSquare,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨cp,sq.1⟩,er⟩,hb⟩,cp⟩,sq.2⟩,er⟩

/-- Layout bounds for all static fold lists; extracting counts on a zero
basis introduces no assumption about the circuit's actual input state. -/
theorem measuredItems_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀ f ∈ L.measuredAItems, ∀ q, f.src.count q ≤ L.core.product.count q) ∧
    (∀ f ∈ L.measuredBItems, ∀ q, f.src.count q ≤ L.core.product.count q) ∧
    (∀ f ∈ L.measuredCItems, ∀ q, f.src.count q ≤ L.core.product.count q) := by
  let z : BasisState := fun _ => false
  have hz : regValue L.core.product z = 0^2 := by
    simpa using (regValue_zero L.core.product z).mpr (fun _ _ => rfl)
  exact ⟨fun f hf => (L.measuredA_views hw z 0 (by decide) hz f hf).count,
    (fun f hf => (L.measuredB_views hw z 0 (by decide) hz f hf).count),
    (fun f hf => (L.measuredC_views hw z 0 hz f hf).count)⟩

theorem measuredProgram_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control :: L.wires).Nodup) :
    GatePhysical (L.measuredProgram control) := by
  have nd := (List.nodup_cons.mp hn).2
  have hc := L.measuredItems_counts hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have a := L.withMeasuredSquare_physical control hn _ _ hl hp _
    (L.measuredFolds_physical hw nd false _ hc.1)
  have b := L.withMeasuredSquare_physical control hn _ _ hb hp _
    (L.measuredFolds_physical hw nd false _ hc.2.1)
  have c := L.withMeasuredSquare_physical control hn _ _ hs (fun _ => le_rfl) _
    (L.measuredFolds_physical hw nd true _ hc.2.2)
  have prep := (physical_embed _).mp (physical_of_proper _ (L.sum_certified hw nd).1.1)
  have clear := (physical_embed _).mp (physical_of_proper _ (L.sum_certified hw nd).2.1)
  simp only [measuredProgram,measuredBranchA,measuredBranchB,measuredBranchC,gatePhysical_append]
  exact ⟨⟨⟨a,b⟩,⟨prep,c⟩,clear⟩,L.reflectOutput_physical nd⟩

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
