import ECDSAAdd.Arithmetic.ControlledPointSupport
import ECDSAAdd.Arithmetic.PointDialogResources
import ECDSAAdd.Arithmetic.CompressedPointDialogResources

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem controlledPointOutput_counts (L : ControlledPointLayout) (h : L.Widths) (C : Point) :
    toffoliCount (controlledPointOutput L C)=518 ∧ measurementCount (controlledPointOutput L C)=0 := by
  simp only [controlledPointOutput,toffoliCount_append,measurementCount_append,
    (pointSelectors_counts L).1,(pointSelectors_counts L).2,
    (selectedPointOutput_counts L h C).1,(selectedPointOutput_counts L h C).2]
  exact ⟨trivial,trivial⟩

theorem controlledPointAddOut_finite_resources (L : ControlledPointLayout) (h : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (controlledPointAddOut L (.some hc))=9295112 ∧
    measurementCount (controlledPointAddOut L (.some hc))=6126846 ∧
    qubitCount (controlledPointAddOut L (.some hc))=6731 := by
  have cc := pointCandidate_counts L.core h (L.core_nodup hn) cx cy
  have cf := pointFlags_counts L.core h cx cy
  have co := controlledPointOutput_counts L h (.some hc)
  refine ⟨?_,?_,?_⟩
  · simp only [controlledPointAddOut,toffoliCount_append,cc.1.1,cc.2.1,cf.1.1,cf.2.1,co.1]
  · simp only [controlledPointAddOut,measurementCount_append,cc.1.2,cc.2.2,cf.1.2,cf.2.2,co.2]
  · rw [qubitCount,controlledPointAddOut_support L h cx cy hc,List.toFinset_card_of_nodup (L.used_nodup h hn)]
    simp [ControlledPointLayout.usedWires,ControlledPointLayout.extras,ControlledPointLayout.selectors,L.core.usedWires_length h]

/-- Exact costs of the same complete Skywalk point program, with a physical support bound. -/
theorem controlledPointAdd_finite_resources (L : ControlledPointLayout) (h : L.Widths)
    (hn : L.wires.Nodup) (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (controlledPointAdd L (.some hc))=2217386 ∧
    measurementCount (controlledPointAdd L (.some hc))=1557928 ∧
    qubitCount (controlledPointAdd L (.some hc))≤1899 := by
  have hh := CompressedPointDialog.finite_counts L h hn (.some hc) cx cy
  exact ⟨hh.1,hh.2,CompressedPointDialog.finite_qubits L h hn (.some hc) cx cy⟩

/-- C=O 在构造期为空程序，故实际门数、测量和线路集合均为空。 -/
theorem controlledPointAdd_zero_resources (L : ControlledPointLayout) :
    toffoliCount (controlledPointAdd L 0)=0 ∧ measurementCount (controlledPointAdd L 0)=0 ∧
    qubitCount (controlledPointAdd L 0)=0 := by
  simp [controlledPointAdd,toffoliCount,measurementCount,qubitCount,wires]

end ECDSAAdd.Arithmetic
