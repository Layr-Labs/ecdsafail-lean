import ECDSAAdd.Submission.Entrant.SquareFolds
import ECDSAAdd.Arithmetic.CompressedPointSquareCorrect
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SkywalkSlots

/-! Point-layout binding of the sign-grouped streamed square, with the same
pool relabeling as the Skywalk Step 4 square. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant
open Arithmetic ControlledPointLayout Secp256k1 CompressedPointSquare

def fastCandidate (L : ControlledPointLayout) : Program :=
  fastProgram L.dialogStreamedSquareWide L.core.generic

theorem fastCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastCandidate L)=95822 ∧ measurementCount (fastCandidate L)=95302 :=
  fastProgram_counts L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

def fastCandidateNR (L : ControlledPointLayout) : Program :=
  fastNR L.dialogStreamedSquareWide L.core.generic

theorem fastCandidate_split (L : ControlledPointLayout) :
    fastCandidate L=fastCandidateNR L++L.dialogStreamedSquareWide.reflectOutput := rfl

theorem fastCandidateNR_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastCandidateNR L)=95567 ∧ measurementCount (fastCandidateNR L)=95047 :=
  fastNR_counts L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

theorem fastCandidateNR_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (fastCandidateNR L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
  have support := fastNR_support L.dialogStreamedSquareWide
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

theorem fastCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776).toFinset := by
  have support := fastProgram_support L.dialogStreamedSquareWide
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

theorem fastCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidate L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (fastCandidate L) m s).basis q=s.basis q := by
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
  have kernel := fastProgram_correct K hwK L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean
  simpa only [fastCandidate,hb,hp,pow_two] using kernel

theorem fastCandidateNR_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidateNR L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidateNR L) m s).basis=
      p-1-(X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (fastCandidateNR L) m s).basis q=s.basis q := by
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
  have kernel := fastNR_correct K hwK L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean
  simpa only [fastCandidateNR,hb,hp,pow_two] using kernel

theorem fastCandidateNR_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidateNR L) := by
  apply fastNR_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢; omega

theorem fastCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidate L) := by
  apply fastProgram_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr; intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢; omega

/-- Computable relabeled square: the emitted Step 4 program. -/
def fastSquare (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidate L)

def fastSquareNR (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidateNR L)

theorem fastSquare_split (L : ControlledPointLayout) :
    fastSquare L=fastSquareNR L++
      renameProgram (labelFn L.core.poolWire) L.dialogStreamedSquareWide.reflectOutput := by
  simp only [fastSquare,fastSquareNR,fastCandidate_split,renameProgram,List.map_append]

theorem fastSquareNR_wires (L : ControlledPointLayout) :
    wires (fastSquareNR L)⊆wires (fastSquare L) := by
  rw [fastSquare_split,wires_append]
  exact Finset.subset_union_left

noncomputable def fastSquareN (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (fastCandidate L)

theorem fastSquare_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    fastSquare L=fastSquareN L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

private theorem pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

private theorem pull_injective' (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

section StateEq
attribute [local irreducible] run wires fastCandidate

theorem fastSquare_state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (fastSquare L) m s=run (fastCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_x' L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidate L) m s) cleanOut
  rw [fastSquare_eq L hw hn,fastSquareN]
  apply pull_injective' e
  have semantic := run_rename e e.injective (fastCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem fastSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquare L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (fastSquare L) m s).basis q=s.basis q := by
  rw [fastSquare_state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc

noncomputable def fastSquareNRN (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (fastCandidateNR L)

theorem fastSquareNR_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    fastSquareNR L=fastSquareNRN L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

theorem fastSquareNR_state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (fastSquareNR L) m s=run (fastCandidateNR L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := fastCandidateNR_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidateNR L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_x' L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidateNR L) m s) cleanOut
  rw [fastSquareNR_eq L hw hn,fastSquareNRN]
  apply pull_injective' e
  have semantic := run_rename e e.injective (fastCandidateNR L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem fastSquareNR_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquareNR L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquareNR L) m s).basis=
      p-1-(X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (fastSquareNR L) m s).basis q=s.basis q := by
  rw [fastSquareNR_state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact fastCandidateNR_correct L hw hn X Y B hX s m hb hx hy hc

theorem fastSquare_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastSquare L)=95822 ∧ measurementCount (fastSquare L)=95302 := by
  have renamed := renameProgram_counts (labelFn L.core.poolWire) (fastCandidate L)
  have old := fastCandidate_counts L hw
  rw [fastSquare]
  exact ⟨renamed.1.trans old.1,renamed.2.trans old.2⟩

theorem fastSquareNR_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastSquareNR L)=95567 ∧ measurementCount (fastSquareNR L)=95047 := by
  have renamed := renameProgram_counts (labelFn L.core.poolWire) (fastCandidateNR L)
  have old := fastCandidateNR_counts L hw
  rw [fastSquareNR]
  exact ⟨renamed.1.trans old.1,renamed.2.trans old.2⟩

theorem fastSquareNR_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (fastSquareNR L)⊆(residents L++sharedPool L).toFinset :=
  (fastSquareNR_wires L).trans (fastSquare_support L hw hn)

theorem fastSquare_support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (fastSquare L)⊆(residents L++sharedPool L).toFinset := by
  rw [fastSquare_eq L hw hn]
  intro q hq
  rw [fastSquareN,renameProgram_support] at hq
  obtain ⟨old,used,rfl⟩ := Finset.mem_image.mp hq
  have supp := fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at supp
  have res : old∈residents L ∨ old∈L.dialogPool.take 776 := by
    simp only [residents,PointAddLayout.pointWires,inPlaceFlags,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false]
    tauto
  rcases res with res|mem
  · rw [resident_fixed L hw hn old res]
    exact List.mem_toFinset.mpr (List.mem_append_left _ res)
  · have prefixView : L.dialogPool.take 776=wireBlock L.core.poolWire 0 776 := by
      simp only [dialogPool,List.take_take,Nat.min_eq_left (show 776 ≤ 2613 by omega)]
      exact (L.core.pool_prefix hw 776 (by omega)).symm
    rw [prefixView] at mem
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
    rw [show poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) (L.core.poolWire i)=
      L.core.poolWire (indexPermutation i) from
        wire_apply L.core.poolWire (layout_bounded_injective L hw hn) i (by omega)]
    apply List.mem_toFinset.mpr
    apply List.mem_append_right
    rcases prefix_allowed i bound with lo|hi
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
        ⟨indexPermutation i,by simp [List.mem_range'_1]; omega,rfl⟩))

end StateEq


theorem fastSquareNR_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (fastSquareNR L) := by
  rw [fastSquareNR_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact fastCandidateNR_physical L hw hn

theorem fastSquareNR_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquareNR L) ≤ 5000000 := by
  simpa only [fastSquareNR,Baselines.rename_gateSlots,fastCandidateNR]
    using fastNR_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

theorem fastSquare_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact fastCandidate_physical L hw hn

theorem fastSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquare L) ≤ 5000000 := by
  simpa only [fastSquare,Baselines.rename_gateSlots,fastCandidate]
    using fastProgram_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) L.core.generic

end ECDSAAdd.Entrant
