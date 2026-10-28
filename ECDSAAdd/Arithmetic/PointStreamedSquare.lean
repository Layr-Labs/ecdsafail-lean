import ECDSAAdd.Arithmetic.PointDialogLayout
import ECDSAAdd.Arithmetic.CuccaroStreamedControlledResources
import ECDSAAdd.Framework.UnitaryControl

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def pointStreamedSquare (L : ControlledPointLayout) : Program :=
  L.dialogStreamedSquareWide.controlledProgram L.core.generic (L.core.poolWire 775)

theorem ControlledPointLayout.streamedSquare_wires_eq (L : ControlledPointLayout)
    (hw : L.Widths) :
    L.dialogStreamedSquareWide.wires=L.point.y++L.point.x++L.dialogPool.take 775 := by
  calc
    L.dialogStreamedSquareWide.wires =
      L.dialogStreamedSquareWide.core.y++L.dialogStreamedSquareWide.core.out++
        (L.dialogStreamedSquareWide.core.product++L.dialogStreamedSquareWide.core.pad++
         L.dialogStreamedSquareWide.core.work++
         [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
          L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
          L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
          L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad) := by
            simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
              List.append_assoc]
    _ = _ := by
      rw [L.dialogStreamedSquareWide_pool hw]
      rfl

theorem ControlledPointLayout.streamedSquare_control_nodup
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic::L.core.poolWire 775::L.dialogStreamedSquareWide.wires).Nodup := by
  rw [L.streamedSquare_wires_eq hw]
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
  have hp := (List.take_sublist 776 L.dialogPool).count_le q
  have he := congrArg (List.count q) (L.dialogBit_prefix hw 775 (by omega))
  norm_num only at he
  simp only [dialogUsedWires,PointAddLayout.pointWires,inPlaceFlags,List.count_cons,
    List.count_append,List.count_nil] at h he ⊢
  omega

theorem pointStreamedSquare_exact_control (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    ExactControl L.core.generic (L.core.poolWire 775) L.dialogStreamedSquareWide.program
      (pointStreamedSquare L) := by
  have nd := L.streamedSquare_control_nodup hw hn
  have n0 := List.nodup_cons.mp nd
  have n1 := List.nodup_cons.mp n0.2
  exact L.dialogStreamedSquareWide.controlledProgram_exact
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn)
    L.core.generic (L.core.poolWire 775)
    (fun h => n0.1 (List.mem_cons_of_mem _ h)) n1.1
    (fun h => n0.1 (by simp [h]))

theorem pointStreamedSquare_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointStreamedSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointStreamedSquare L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (pointStreamedSquare L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have support := K.program_certified hwK ndK
  have nd := L.streamedSquare_control_nodup hw hn
  have n0 := List.nodup_cons.mp nd
  have n1 := List.nodup_cons.mp n0.2
  have controlAway : L.core.generic∉wires K.program := by
    intro h
    exact n0.1 (List.mem_cons_of_mem _ (List.mem_toFinset.mp (support.2 h)))
  have scratchAway : L.core.poolWire 775∉wires K.program := by
    intro h
    exact n1.1 (List.mem_toFinset.mp (support.2 h))
  have scratchIn : L.core.poolWire 775∈L.dialogPool := by
    have h : L.core.poolWire 775∈L.dialogPool.take 775++[L.core.poolWire 775] := by simp
    rw [L.dialogBit_prefix hw 775 (by omega)] at h
    exact List.mem_of_mem_take h
  have scratchZero : s.basis (L.core.poolWire 775)=false :=
    (regValue_zero _ _).mp hc _ scratchIn
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
  have kernel := K.program_square_correct hwK ndK Y X (by simpa only [hp] using hX)
    s m hy hx prod0 sum0 clean
  have guard := (pointStreamedSquare_exact_control L hw hn).execute s m scratchZero
  change run (pointStreamedSquare L) m s=_ at guard
  rw [guard,hb]
  cases B
  · simp [hx,Nat.mod_eq_of_lt hX]
  · simpa only [if_true,hp,pow_two] using kernel

def pointStreamedSquareCost (_L : ControlledPointLayout) : Nat := 749338

theorem pointStreamedSquare_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (pointStreamedSquare L)=pointStreamedSquareCost L ∧
    measurementCount (pointStreamedSquare L)=0 :=
  L.dialogStreamedSquareWide.controlledProgram_counts
    (L.dialogStreamedSquareWide_widths hw) L.core.generic (L.core.poolWire 775)

theorem pointStreamedSquare_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointStreamedSquare L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
  have supp := (L.dialogStreamedSquareWide.program_certified
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn)).2
  have embed : L.dialogStreamedSquareWide.wires.toFinset⊆
      (L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    intro q hq
    simp only [List.mem_toFinset,List.mem_append] at hq ⊢
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro v hv
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hv
      exact List.mem_of_mem_take hv
    tauto
  have scratch : L.core.poolWire 775∈L.dialogPool.take 776 := by
    have h : L.core.poolWire 775∈L.dialogPool.take 775++[L.core.poolWire 775] := by simp
    simpa only [L.dialogBit_prefix hw 775 (by omega)] using h
  intro q hq
  have h := (pointStreamedSquare_exact_control L hw hn).support hq
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with (rfl|rfl)|h
  · simp
  · simp [scratch]
  · have h' := embed (supp h)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h' ⊢
    tauto

def ControlledPointLayout.streamedSquareStageSites (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags++L.dialogPool.take 776

theorem pointStreamedSquare_stage_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (pointStreamedSquare L)⊆L.streamedSquareStageSites.toFinset := by
  intro q hq
  have h := pointStreamedSquare_support L hw hn hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
  simp only [List.mem_toFinset,streamedSquareStageSites,PointAddLayout.pointWires,
    inPlaceFlags,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  tauto

theorem pointStreamedSquare_stage_sites (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    L.streamedSquareStageSites.Nodup ∧ L.streamedSquareStageSites.length=1297 ∧
      qubitCount (pointStreamedSquare L)≤1297 := by
  have nd : L.streamedSquareStageSites.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have ht := (List.take_sublist 776 L.dialogPool).count_le q
    simp only [streamedSquareStageSites,dialogUsedWires,List.count_append] at h ⊢
    omega
  have len : L.streamedSquareStageSites.length=1297 := by
    simp only [streamedSquareStageSites,PointAddLayout.pointWires,inPlaceFlags,
      List.length_cons,List.length_append,List.length_nil,List.length_take,
      show L.point.x.length=256 from hw.inputX,
      show L.point.y.length=256 from hw.inputY,L.dialogPool_length hw]
    norm_num
  refine ⟨nd,len,?_⟩
  rw [qubitCount]
  calc
    _ ≤ L.streamedSquareStageSites.toFinset.card :=
      Finset.card_le_card (pointStreamedSquare_stage_support L hw hn)
    _ = 1297 := by rw [List.toFinset_card_of_nodup nd,len]

end ECDSAAdd.Arithmetic
