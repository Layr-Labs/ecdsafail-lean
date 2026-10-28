import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredCopiedFold

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem MeasuredSourceNormalizeLayout.physical (L : MeasuredSourceNormalizeLayout)
    (p c : Nat) (hn : L.wires.Nodup) :
    GatePhysical (L.normalize p c) ∧ GatePhysical (L.restore p) ∧ GatePhysical (L.reflect p) := by
  have nd : (L.cin :: L.word ++ L.carry).Nodup := (List.nodup_cons.mp hn).2
  have hc : ∀ q ∈ some L.flag, q ∉ L.cin :: L.word ++ L.carry := by
    intro q hq; have he : L.flag = q := by simpa using hq
    subst q; exact (List.nodup_cons.mp hn).1
  have nc : ([L.cin,L.flag] ++ L.word ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simpa [wires,List.count_append,List.count_cons,List.count_nil,Nat.add_comm,
      Nat.add_left_comm,Nat.add_assoc] using h
  simp only [normalize,restore,reflect,gatePhysical_append]
  exact ⟨⟨compareConstantGe_physical _ _ _ _ _ nc,mappedConstAdd_physical _ _ _ _ _ nd hc⟩,
    ⟨mappedConstAdd_physical _ _ _ _ _ nd hc,compareConstantGe_physical _ _ _ _ _ nc⟩,
    notRegister_physical _,mappedConstAdd_physical _ _ _ _ _ nd (by simp)⟩

theorem measuredFoldKernel_physical (K : MeasuredCanonicalModLayout) (flag : Wire)
    (canonical : Bool) (c p : Nat) (hn : (flag :: K.wires).Nodup) :
    GatePhysical (measuredFoldKernel K flag canonical c p) := by
  have nd : (measuredFoldNormalize K flag).wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist (K.src.length-1) K.carry).count_le q
    simp only [measuredFoldNormalize,MeasuredSourceNormalizeLayout.wires,
      MeasuredCanonicalModLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have hN := (measuredFoldNormalize K flag).physical p c nd
  have hK := K.physical c p (List.nodup_cons.mp hn).2
  cases canonical with
  | false =>
    simpa only [measuredFoldKernel,Bool.false_eq_true,ite_false,gatePhysical_append]
      using (show (GatePhysical ((measuredFoldNormalize K flag).normalize p c) ∧
        GatePhysical (K.program c p)) ∧ GatePhysical ((measuredFoldNormalize K flag).restore p)
        from ⟨⟨hN.1,hK⟩,hN.2.1⟩)
  | true => simpa [measuredFoldKernel] using hK

theorem copySlice_physical (src dst : List Wire) (shift : Nat) (hn : (src ++ dst).Nodup) :
    GatePhysical (copySlice src dst shift) := by
  apply copyRegister_physical none _ _ _ (by simp)
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp hn q
  have hdrop := (List.drop_sublist shift dst).count_le q
  have htake := (List.take_sublist src.length (dst.drop shift)).count_le q
  simp only [List.count_append] at h ⊢; omega

theorem measuredCopiedFold_physical (K : MeasuredCanonicalModLayout) (flag : Wire)
    (src : List Wire) (shift : Nat) (canonical : Bool) (c p : Nat)
    (hn : (src ++ flag :: K.wires).Nodup) :
    GatePhysical (measuredCopiedFold K flag src shift canonical c p) := by
  have nk : (flag :: K.wires).Nodup := (List.nodup_append.mp hn).2.1
  have nc : (src ++ K.src).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [MeasuredCanonicalModLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [measuredCopiedFold,gatePhysical_append]
  exact ⟨⟨copySlice_physical _ _ _ nc,measuredFoldKernel_physical _ _ _ _ _ nk⟩,
    copySlice_physical _ _ _ nc⟩

end ECDSAAdd.Arithmetic
