import ECDSAAdd.Arithmetic.PointInPlaceClassification

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem xorFour (b o d i g : Wire) (ho : o≠g) (hd : d≠g) (hi : i≠g)
    (s : State) (m : List Bool) :
    run [.CX b g,.CX o g,.CX d g,.CX i g] m s=
      ⟨s.phase,writeBit s.basis g ((((s.basis g ^^ s.basis b) ^^ s.basis o) ^^ s.basis d) ^^ s.basis i)⟩ := by
  simp [run,writeBit,ho,hd,hi]

theorem pointInPlaceGenericFlag_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) :
    run (pointInPlaceGenericFlag L) m s=
      ⟨s.phase,writeBit s.basis L.core.generic
        ((((s.basis L.core.generic ^^ s.basis L.control) ^^ s.basis L.infinitySelect) ^^
          s.basis L.doubleSelect) ^^ s.basis L.genericSelect)⟩ := by
  have hc := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hn) L.core.generic
  simp only [inPlaceFlags,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at hc
  have ho : L.infinitySelect≠L.core.generic := by intro he; simp only [he,beq_self_eq_true,if_true] at hc; omega
  have hd : L.doubleSelect≠L.core.generic := by intro he; simp only [he,beq_self_eq_true,if_true] at hc; omega
  have hi : L.genericSelect≠L.core.generic := by intro he; simp only [he,beq_self_eq_true,if_true] at hc; omega
  exact xorFour _ _ _ _ _ ho hd hi s m

theorem pointInPlaceDoubleEnable_correct (L : ControlledPointLayout) (cy : Fp) (s : State) (m : List Bool) :
    run (pointInPlaceDoubleEnable L cy) m s=
      ⟨s.phase,writeBit s.basis L.core.double
        (s.basis L.core.double ^^ (s.basis L.control && decide (cy≠-cy)))⟩ := by
  by_cases hc : cy≠-cy
  · simp [pointInPlaceDoubleEnable,hc,run]
  · simp [pointInPlaceDoubleEnable,hc,run,writeBit]

end ECDSAAdd.Arithmetic
