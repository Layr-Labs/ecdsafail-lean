import ECDSAAdd.Arithmetic.PointDialogLayout

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout

def pointDialogStreamedSquareCandidate (L : ControlledPointLayout) : Program :=
  L.dialogStreamedSquareWide.program

def ControlledPointLayout.dialogStreamedSquareStageWires
    (L : ControlledPointLayout) : List Wire :=
  L.dialogStreamedSquareWide.wires++[L.point.finite,L.control]++L.inPlaceFlags

theorem pointDialogStreamedSquareCandidate_counts (L : ControlledPointLayout)
    (hw : L.Widths) :
    toffoliCount (pointDialogStreamedSquareCandidate L)=287768 ∧
      measurementCount (pointDialogStreamedSquareCandidate L)=0 := by
  simpa [pointDialogStreamedSquareCandidate] using
    L.dialogStreamedSquareWide.program_counts (L.dialogStreamedSquareWide_widths hw)

theorem ControlledPointLayout.dialogStreamedSquareStageWires_length
    (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogStreamedSquareStageWires.length=1296 := by
  simp [dialogStreamedSquareStageWires,
    L.dialogStreamedSquareWide_static_sites hw,inPlaceFlags]

theorem ControlledPointLayout.dialogStreamedSquareStageWires_nodup
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.dialogStreamedSquareStageWires.Nodup := by
  have wideEq : L.dialogStreamedSquareWide.wires=
      L.point.y++L.point.x++L.dialogPool.take 775 := by
    calc
      L.dialogStreamedSquareWide.wires =
          L.dialogStreamedSquareWide.core.y++L.dialogStreamedSquareWide.core.out++
            (L.dialogStreamedSquareWide.core.product++
              L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
              [L.dialogStreamedSquareWide.core.productHigh,
                L.dialogStreamedSquareWide.core.outHigh,
                L.dialogStreamedSquareWide.core.workHigh,
                L.dialogStreamedSquareWide.core.cin,
                L.dialogStreamedSquareWide.core.normFlag,
                L.dialogStreamedSquareWide.core.modFlag,
                L.dialogStreamedSquareWide.core.sumCarry]++
              L.dialogStreamedSquareWide.overflowPad) := by
                simp [CuccaroStreamedSquareWideLayout.wires,
                  CuccaroStreamedSquareLayout.wires,List.append_assoc]
      _ = L.point.y++L.point.x++L.dialogPool.take 775 := by
            rw [L.dialogStreamedSquareWide_pool hw]
            simp [dialogStreamedSquareWide,dialogStreamedSquare]
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 775 L.dialogPool).count_le q
  simp only [dialogStreamedSquareStageWires,wideEq,dialogUsedWires,
    PointAddLayout.pointWires,inPlaceFlags,List.count_append,List.count_cons,
    List.count_nil] at h ⊢
  omega

end ECDSAAdd.Arithmetic
