import ECDSAAdd.Arithmetic.MeasuredStreamedSquareProof
import ECDSAAdd.Arithmetic.PointMeasuredSquareCandidate
import ECDSAAdd.Arithmetic.CompressedPointSquareCorrect
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Baselines.SkywalkSlots

/-! The measured streamed square without its final output reflection.

The unchanged Skywalk square ends with one reflection `O ↦ p-1-O` of the
output.  Dropping it leaves the reflected value `p-1-(X - Y²)`; the following
classical correction absorbs the reflection at no extra Toffoli cost. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout CuccaroStreamedSquareWideLayout

def squareKernelNR (K : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  K.measuredBranchA control++K.measuredBranchB control++K.measuredBranchC control

theorem measuredProgram_split (K : CuccaroStreamedSquareWideLayout) (control : Wire) :
    K.measuredProgram control=squareKernelNR K control++K.reflectOutput := rfl

theorem squareKernelNR_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (squareKernelNR L control) records s).phase=s.phase ∧
    regValue L.core.out (run (squareKernelNR L control) records s).basis=
      SquareReduction.p-1-
        (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (squareKernelNR L control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OA := measuredAResult PA O
  let OB := measuredBResult PB OA
  let OC := measuredCMiddleResult PC OB
  let restA := records.drop (measurementCount (L.measuredBranchA control))
  let restB := restA.drop (measurementCount (L.measuredBranchB control))
  let u := run (L.measuredBranchA control) (records.take (measurementCount (L.measuredBranchA control))) s
  let v := run (L.measuredBranchB control) (restA.take (measurementCount (L.measuredBranchB control))) u
  let w := run (L.measuredBranchC control) restB v
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ea := L.measuredBranchA_correct hw control hn A O hO s
    (records.take (measurementCount (L.measuredBranchA control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := L.measuredBranchB_correct hw control hn B OA (measured_results_lt PA O).1 u
    (restA.take (measurementCount (L.measuredBranchB control))) highU ea.2.1 productU cleanU
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ea.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A := regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have sumV : regValue L.core.sum v.basis=B :=
    (regValue_congr _ _ _ (fun q hq => sameV q (sumAway q hq))).trans sumB
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ec := L.measuredBranchC_correct hw control hn A B OB (measured_results_lt PB OA).2.1 v
    restB lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have ocBound : OC<SquareReduction.p := (measured_results_lt PC OB).2.2
  have fullValue : regValue L.core.out w.basis=
      SquareReduction.p-1-
        (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := measuredCompleteResult_exact enabled A B O
    rw [split] at exactResult
    unfold measuredCompleteResult subModValue at exactResult
    change SquareReduction.p-1-OC=_ at exactResult
    rw [ec.2.1]
    change OC=_
    omega
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      SquareReduction.p-1-
        (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ec.1.trans (eb.1.trans ea.1),fullValue,sameW⟩
  simpa [squareKernelNR,u,v,w,restA,restB,enabled,run_append,Nat.add_assoc] using final

/-- Point-layout binding, mirroring `pointMeasuredSquareCandidate`. -/
def pointSquareNR (L : ControlledPointLayout) : Program :=
  squareKernelNR L.dialogStreamedSquareWide L.core.generic

theorem pointSquareNR_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointSquareNR L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointSquareNR L) m s).basis=
      p-1-(X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (pointSquareNR L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
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
  have kernel := squareKernelNR_correct K hwK L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean
  simpa only [pointSquareNR,hb,hp,pow_two] using kernel

/-- Computable relabelled emission, as for the Skywalk square. -/
def squareNR (L : ControlledPointLayout) : Program :=
  renameProgram (CompressedPointSquare.labelFn L.core.poolWire) (pointSquareNR L)

theorem computable_split (L : ControlledPointLayout) :
    CompressedPointSquare.computableProgram L=squareNR L++
      renameProgram (CompressedPointSquare.labelFn L.core.poolWire) L.dialogStreamedSquareWide.reflectOutput := by
  simp only [CompressedPointSquare.computableProgram,pointMeasuredSquareCandidate,squareNR,
    pointSquareNR,measuredProgram_split,renameProgram,List.map_append]

private theorem pull_injective (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

theorem squareNR_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (squareNR L) m s).phase=s.phase ∧
    regValue L.point.x (run (squareNR L) m s).basis=p-1-(X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (squareNR L) m s).basis q=s.basis q := by
  have old := pointSquareNR_correct L hw hn X Y B hX s m hb hx hy hc
  suffices eq : run (squareNR L) m s=run (pointSquareNR L) m s by rw [eq]; exact old
  let e := CompressedPointSquare.poolPermutation L.core.poolWire
    (CompressedPointSquare.layout_bounded_injective L hw hn)
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (pointSquareNR L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_x L hn q hq)).trans (cleanIn q hq)
  have input := CompressedPointSquare.zero_pool_boundary L hw hn s cleanIn
  have output := CompressedPointSquare.zero_pool_boundary L hw hn (run (pointSquareNR L) m s) cleanOut
  have relabel : squareNR L=renameProgram e (pointSquareNR L) := by
    apply renameProgram_congr_support
    intro q _
    exact CompressedPointSquare.label_matches _ (CompressedPointSquare.layout_bounded_injective L hw hn) q
  rw [relabel]
  apply pull_injective e
  have semantic := run_rename e e.injective (pointSquareNR L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem squareNR_wires (L : ControlledPointLayout) :
    wires (squareNR L)⊆wires (CompressedPointSquare.computableProgram L) := by
  rw [computable_split,wires_append]
  exact Finset.subset_union_left

theorem reflect_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (renameProgram (CompressedPointSquare.labelFn L.core.poolWire)
      L.dialogStreamedSquareWide.reflectOutput)=255 ∧
    measurementCount (renameProgram (CompressedPointSquare.labelFn L.core.poolWire)
      L.dialogStreamedSquareWide.reflectOutput)=255 := by
  have r := renameProgram_counts (CompressedPointSquare.labelFn L.core.poolWire)
    L.dialogStreamedSquareWide.reflectOutput
  have hwK := L.dialogStreamedSquareWide_widths hw
  have short := (L.dialogStreamedSquareWide.measured_bank_widths hwK).2.2.2.2
  have a := mappedConstAdd_counts none L.dialogStreamedSquareWide.core.out
    L.dialogStreamedSquareWide.shortCarry L.dialogStreamedSquareWide.core.cin SquareReduction.p
    (by rw [short,hwK.core.out])
  have nr := notRegister_counts L.dialogStreamedSquareWide.core.out
  rw [r.1,r.2]
  simp only [reflectOutput,toffoliCount_append,measurementCount_append,nr.1,nr.2,a.1,a.2,hwK.core.out]
  decide

theorem squareNR_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (squareNR L)=99647 ∧ measurementCount (squareNR L)=99127 := by
  have full := CompressedPointSquare.counts L hw
  have r := reflect_counts L hw
  rw [computable_split,toffoliCount_append,measurementCount_append] at full
  omega

theorem squareNR_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (squareNR L) := by
  have full := CompressedPointSquare.computableProgram_physical L hw hn
  rw [computable_split,gatePhysical_append] at full
  exact full.1

theorem squareNR_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (squareNR L) ≤ 5000000 := by
  have full := Baselines.skywalkSquare_gateSlots_le L hw
  rw [computable_split,Challenge.gateSlots_append] at full
  omega

end ECDSAAdd.Entrant
