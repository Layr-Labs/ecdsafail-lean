import ECDSAAdd.Arithmetic.OneBitRecords
import ECDSAAdd.Arithmetic.HalvingLoop
import ECDSAAdd.Arithmetic.NegativeInitResources

namespace ECDSAAdd.Arithmetic

theorem loopEnd_shared_perm (L : KaliskiRoundLayout) (n : Nat) :
    (loopEndLayout L n).sharedWires.Perm L.sharedWires := by
  induction n generalizing L with
  | zero => exact List.Perm.refl _
  | succ n ih => exact (ih L.swapCounter).trans L.shared_swap_perm

theorem loopEnd_data (L : KaliskiRoundLayout) (n : Nat) : (loopEndLayout L n).data=L.data := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih => exact (ih L.swapCounter).trans L.swapCounter_data

theorem loopEnd_counter_width (L : KaliskiRoundLayout) (n : Nat) :
    (loopEndLayout L n).counter.width=L.counter.width := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    rw [loopEndLayout,ih,L.swapCounter_counter]
    exact L.counter.swapCounter_fields.2.2.2.2.2

/-- I4 使用已初始化的第一阶段寄存器；第二阶段复用其计数比较线路。 -/
structure InverseLoopLayout where
  first : KaliskiRoundLayout
  records : List RoundRecord
  arithmetic : ModLayout
  a : List Wire
  temp : List Wire
  out : List Wire

namespace InverseLoopLayout

def middle (L : InverseLoopLayout) : KaliskiRoundLayout := loopEndLayout L.first L.records.length

def halving (L : InverseLoopLayout) : HalvingLayout :=
  ⟨L.a, L.arithmetic.reg .modulus, L.arithmetic.lowReg .carrySum,
    L.arithmetic.high.carrySum, L.arithmetic.cinSum, L.arithmetic.cinDiff,
    L.middle.active, L.middle.counterLow, L.middle.counterHigh, L.middle.compareCin⟩

def extra (L : InverseLoopLayout) : List Wire := L.a++L.temp++L.arithmetic.wires

def wires (L : InverseLoopLayout) : List Wire := L.first.tapeWires L.records++L.extra++L.out

def phaseWires (L : InverseLoopLayout) : List Wire :=
  L.extra ++ [L.middle.compareCin] ++ L.middle.counter.wires

theorem middle_perm (L : InverseLoopLayout) :
    (L.middle.tapeWires L.records).Perm (L.first.tapeWires L.records) :=
  List.Perm.append_left _ (loopEnd_shared_perm L.first L.records.length)

theorem middle_nodup (L : InverseLoopLayout) (hnd : L.wires.Nodup) :
    (L.middle.tapeWires L.records).Nodup :=
  L.middle_perm.nodup_iff.mpr (List.nodup_append'.mp (List.nodup_append'.mp hnd).1).1

theorem phase_nodup (L : InverseLoopLayout) (hnd : L.wires.Nodup) : L.phaseWires.Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hh := List.nodup_iff_count.mp hnd w
  have hm := L.middle_perm.count_eq w
  simp only [wires,phaseWires,KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,List.count_append,
    List.count_cons,List.count_nil] at hh hm ⊢
  omega

theorem first_nodup (L : InverseLoopLayout) (hnd : L.wires.Nodup) :
    (L.first.tapeWires L.records).Nodup := (List.nodup_append'.mp (List.nodup_append'.mp hnd).1).1

def restWires (L : InverseLoopLayout) : List Wire :=
  L.records.flatMap RoundRecord.wires ++ [L.middle.done,L.middle.oddWork,L.middle.bothWork] ++ L.middle.data.wires

theorem rest_phase_perm (L : InverseLoopLayout) :
    (L.restWires ++ L.phaseWires ++ L.out).Perm L.wires := by
  apply List.perm_iff_count.mpr
  intro w
  have hm := L.middle_perm.count_eq w
  simp only [wires,restWires,phaseWires,KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,
    List.count_append,List.count_cons,List.count_nil] at hm ⊢
  omega

theorem rest_phase_disjoint (L : InverseLoopLayout) (hnd : L.wires.Nodup) :
    L.restWires.Disjoint L.phaseWires :=
  (List.nodup_append'.mp (List.nodup_append'.mp (L.rest_phase_perm.nodup_iff.mpr hnd)).1).2.2

end InverseLoopLayout

end ECDSAAdd.Arithmetic
