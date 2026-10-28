import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.CompactRecoveryNegateProof
import ECDSAAdd.Arithmetic.CompactRecoveryConstant
import ECDSAAdd.Arithmetic.PointOutput
namespace ECDSAAdd.Arithmetic
open RecordedQuantum Secp256k1

theorem zeroControlled_physical (c target : Wire) (bs : List ZeroBit)
    (hn : (c :: target :: bs.flatMap ZeroBit.wires).Nodup) :
    GatePhysical (zeroControlled c target bs) := by
  induction bs generalizing c with
  | nil =>
    have h : c ≠ target := by simpa using (List.nodup_cons.mp hn).1
    simpa [zeroControlled,GatePhysical,PhysicalInstr,ProperGate] using h
  | cons b bs ih =>
    have ht : (b.work :: target :: bs.flatMap ZeroBit.wires).Nodup := by
      apply List.nodup_iff_count.mpr; intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [List.flatMap_cons,ZeroBit.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
      omega
    have hcw : c ≠ b.work := by
      intro he; subst c
      have h := List.nodup_iff_count.mp hn b.work
      simp only [List.flatMap_cons,ZeroBit.wires,List.count_cons,List.count_append,List.count_nil,
        beq_self_eq_true,ite_true] at h; omega
    have hiw : b.input ≠ b.work := by
      intro he
      have h := List.nodup_iff_count.mp hn b.work
      simp only [List.flatMap_cons,ZeroBit.wires,List.count_cons,List.count_append,List.count_nil,
        he,beq_self_eq_true,ite_true] at h; omega
    change GatePhysical ([.X b.input,.CCX c b.input b.work,.X b.input] ++
      zeroControlled b.work target bs ++ [.X b.input,.measureX b.work [] [.CZ c b.input],.X b.input])
    simp only [gatePhysical_append]
    exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate,hcw,hiw],ih _ ht⟩,
      by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem equalConstant_physical (c target : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c :: target :: bs.flatMap ZeroBit.wires).Nodup) :
    GatePhysical (equalConstant c target bs k) := by
  simp only [equalConstant,gatePhysical_append]
  exact ⟨⟨xorConstant_physical _ _,zeroControlled_physical _ _ _ hn⟩,xorConstant_physical _ _⟩

theorem compactRecoveryConstant_physical (K : MeasuredCanonicalModLayout) (control : Wire)
    (c p k : Nat) (hn : (control :: K.wires).Nodup) :
    GatePhysical (compactRecoveryConstant K control c p k) := by
  have hc : control ∉ K.src := by
    intro h; exact (List.nodup_cons.mp hn).1 (by simp [MeasuredCanonicalModLayout.wires,h])
  simp only [compactRecoveryConstant,gatePhysical_append]
  exact ⟨⟨maskedConstant_physical _ _ _ hc,K.physical c p (List.nodup_cons.mp hn).2⟩,
    maskedConstant_physical _ _ _ hc⟩

theorem CompactRecoveryNegateLayout.reflection_physical (L : CompactRecoveryNegateLayout)
    (control : Wire) (p : Nat) (hn : (L.wires control).Nodup) :
    GatePhysical (L.reflection control p) := by
  have count := List.nodup_iff_count.mp hn
  have hc : control ∉ L.word := by
    intro hm; have h := count control; have hh := List.count_pos_iff.mpr hm
    simp only [wires,List.count_cons,List.count_append,beq_self_eq_true,ite_true] at h; omega
  have nd : (L.cin :: L.word ++ L.carries).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    have ht := (List.take_sublist (L.word.length-1) L.work).count_le q
    simp only [wires,carries,List.count_cons,List.count_append] at h ⊢; omega
  have hs : ∀ q ∈ some control, q ∉ L.cin :: L.word ++ L.carries := by
    intro q hq hm
    have he : control = q := by simpa using hq
    subst q
    have h := count control; have hh := List.count_pos_iff.mpr hm
    have ht := (List.take_sublist (L.word.length-1) L.work).count_le control
    simp only [wires,carries,List.count_cons,List.count_append,beq_self_eq_true,ite_true] at h hh
    omega
  simp only [reflection,complement,add,gatePhysical_append]
  exact ⟨maskedConstant_physical _ _ _ hc,mappedConstAdd_physical _ _ _ _ _ nd hs⟩

theorem maskedPointConstant_physical (c : Wire) (r : PointReg) (C : Point)
    (hc : c ∉ PointAddLayout.pointWires r) : GatePhysical (maskedPointConstant c r C) := by
  have hf : c ∉ [r.finite] := fun h => hc (by simpa [PointAddLayout.pointWires] using Or.inl h)
  have hx : c ∉ r.x := fun h => hc (by simp [PointAddLayout.pointWires,h])
  have hy : c ∉ r.y := fun h => hc (by simp [PointAddLayout.pointWires,h])
  simp only [maskedPointConstant,gatePhysical_append]
  exact ⟨⟨maskedConstant_physical _ _ _ hf,maskedConstant_physical _ _ _ hx⟩,
    maskedConstant_physical _ _ _ hy⟩

end ECDSAAdd.Arithmetic
