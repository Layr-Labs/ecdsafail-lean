import ECDSAAdd.Arithmetic.PointDialogLayout
import ECDSAAdd.Arithmetic.MeasuredStreamedResources
import ECDSAAdd.Arithmetic.MeasuredStreamedSupport
import ECDSAAdd.Arithmetic.MeasuredStreamedSquareProof

set_option maxHeartbeats 3000000

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

/-- Exact measured Step 4 binding in the existing point-layout pool. -/
def pointMeasuredSquareCandidate (L : ControlledPointLayout) : Program :=
  L.dialogStreamedSquareWide.measuredProgram L.core.generic

theorem pointMeasuredSquareCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointMeasuredSquareCandidate L)=99902 ∧
    measurementCount (pointMeasuredSquareCandidate L)=99382 :=
  L.dialogStreamedSquareWide.measuredProgram_counts (L.dialogStreamedSquareWide_widths hw) L.core.generic

theorem pointMeasuredSquareCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointMeasuredSquareCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
  have support := L.dialogStreamedSquareWide.measuredProgram_support
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn) L.core.generic
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro q hq
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hq
      exact List.mem_of_mem_take hq
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp : q∈L.dialogPool.take 775 → q∈L.dialogPool.take 776 := fun h => small h
    tauto
  exact support.trans embed

/-- The resident point/control/classification registers and all workspace
fit in 1,297 distinct allocated sites, giving a safe peak-live ceiling. -/
theorem pointMeasuredSquareCandidate_stage_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointMeasuredSquareCandidate L)⊆L.streamedSquareStageSites.toFinset := by
  intro q hq
  have h := pointMeasuredSquareCandidate_support L hw hn hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  simp only [ControlledPointLayout.streamedSquareStageSites,PointAddLayout.pointWires,
    ControlledPointLayout.inPlaceFlags,List.mem_toFinset,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false]
  tauto

theorem pointMeasuredSquareCandidate_stage_sites (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    L.streamedSquareStageSites.Nodup ∧ L.streamedSquareStageSites.length=1297 ∧
      qubitCount (pointMeasuredSquareCandidate L)≤1297 := by
  have sites := pointStreamedSquare_stage_sites L hw hn
  refine ⟨sites.1,sites.2.1,?_⟩
  rw [qubitCount]
  calc
    _ ≤ L.streamedSquareStageSites.toFinset.card :=
      Finset.card_le_card (pointMeasuredSquareCandidate_stage_support L hw hn)
    _ = 1297 := by rw [List.toFinset_card_of_nodup sites.1,sites.2.1]

theorem pointMeasuredSquareCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointMeasuredSquareCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointMeasuredSquareCandidate L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (pointMeasuredSquareCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have kernel := K.measuredProgram_correct hwK L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean
  simpa only [pointMeasuredSquareCandidate,hb,hp,pow_two] using kernel

end ECDSAAdd.Arithmetic
