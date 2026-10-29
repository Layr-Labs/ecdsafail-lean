import ECDSAAdd.Submission.Entrant.FastSquare
import ECDSAAdd.Submission.Entrant.SquareNR

/-! The sign-grouped streamed square without its final restoring reflection.

`fastProgram` ends with one output reflection `O ↦ p-1-O` (255 Toffoli).  Dropping
it leaves `p-1-(X - Y²)`, which the following `3cx` correction absorbs as a
controlled reverse subtraction (`fastConstRefl`), as in `SquareNR`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant
open Arithmetic Secp256k1 ControlledPointLayout CuccaroStreamedSquareWideLayout CompressedPointSquare

def fastKernelNR (K : CuccaroStreamedSquareWideLayout) (control : Wire) : Program :=
  fastBranchA K control++fastBranchB K control++fastBranchC K control

theorem fastProgram_split (K : CuccaroStreamedSquareWideLayout) (control : Wire) :
    fastProgram K control=fastKernelNR K control++K.reflectOutput := by
  simp only [fastProgram,fastKernelNR,List.append_assoc]

theorem fastKernelNR_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (fastKernelNR L control) records s).phase=s.phase ∧
    regValue L.core.out (run (fastKernelNR L control) records s).basis=
      SquareReduction.p-1-
        (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (fastKernelNR L control) records s).basis q=s.basis q := by
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
  let OA := resA PA O
  let OB := resB PB OA
  let OC := resC PC OB
  let restA := records.drop (measurementCount (fastBranchA L control))
  let restB := restA.drop (measurementCount (fastBranchB L control))
  let u := run (fastBranchA L control) (records.take (measurementCount (fastBranchA L control))) s
  let v := run (fastBranchB L control) (restA.take (measurementCount (fastBranchB L control))) u
  let w := run (fastBranchC L control) restB v
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
  have ea := fastBranchA_correct L hw control hn A O hO s
    (records.take (measurementCount (fastBranchA L control))) rfl ho hp0 hc
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OA ⟨ea.2.1,ea.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ea.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B :=
    regValue_congr _ _ _ (fun q hq => ea.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ea.2.2 control ctrlAway
  have eb := fastBranchB_correct L hw control hn B OA (ofCast_lt _ _) u
    (restA.take (measurementCount (fastBranchB L control))) highU ea.2.1 productU cleanU
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
  have ec := fastBranchC_correct L hw control hn A B OB (ofCast_lt _ _) v
    restB lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have ocBound : OC<SquareReduction.p := ofCast_lt _ _
  have fullValue : regValue L.core.out w.basis=
      SquareReduction.p-1-
        (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := fast_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    change SquareReduction.p-1-OC=_ at exactResult
    rw [ec.2.1]
    change OC=_
    omega
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      SquareReduction.p-1-
        (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ec.1.trans (eb.1.trans ea.1),fullValue,sameW⟩
  simpa [fastKernelNR,u,v,w,restA,restB,enabled,run_append,Nat.add_assoc] using final

def fastCandidateNR (L : ControlledPointLayout) : Program :=
  fastKernelNR L.dialogStreamedSquareWide L.core.generic

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
  have kernel := fastKernelNR_correct K hwK L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean
  simpa only [fastCandidateNR,hb,hp,pow_two] using kernel

/-- Computable relabelled emission, as for `fastSquare`. -/
def fastSquareNR (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidateNR L)

theorem fastSquare_split (L : ControlledPointLayout) :
    fastSquare L=fastSquareNR L++
      renameProgram (labelFn L.core.poolWire) L.dialogStreamedSquareWide.reflectOutput := by
  simp only [fastSquare,fastCandidate,fastSquareNR,fastCandidateNR,fastProgram_split,
    renameProgram,List.map_append]

private theorem pull_injectiveNR (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

private theorem pool_away_xNR (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

section StateEq
attribute [local irreducible] run wires fastCandidateNR

theorem fastSquareNR_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquareNR L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquareNR L) m s).basis=p-1-(X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (fastSquareNR L) m s).basis q=s.basis q := by
  have old := fastCandidateNR_correct L hw hn X Y B hX s m hb hx hy hc
  suffices eq : run (fastSquareNR L) m s=run (fastCandidateNR L) m s by rw [eq]; exact old
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidateNR L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_xNR L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidateNR L) m s) cleanOut
  have relabel : fastSquareNR L=renameProgram e (fastCandidateNR L) := by
    apply renameProgram_congr_support
    intro q _
    exact label_matches _ (layout_bounded_injective L hw hn) q
  rw [relabel]
  apply pull_injectiveNR e
  have semantic := run_rename e e.injective (fastCandidateNR L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

end StateEq

theorem fastSquareNR_wires (L : ControlledPointLayout) :
    wires (fastSquareNR L)⊆wires (fastSquare L) := by
  rw [fastSquare_split,wires_append]
  exact Finset.subset_union_left

theorem fastSquareNR_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastSquareNR L)=95567 ∧ measurementCount (fastSquareNR L)=95047 := by
  have full := fastSquare_counts L hw
  have r := reflect_counts L hw
  rw [fastSquare_split,toffoliCount_append,measurementCount_append] at full
  omega

theorem fastSquareNR_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (fastSquareNR L) := by
  have full := fastSquare_physical L hw hn
  rw [fastSquare_split,gatePhysical_append] at full
  exact full.1

theorem fastSquareNR_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquareNR L) ≤ 5000000 := by
  have full := fastSquare_gateSlots_le L hw
  rw [fastSquare_split,Challenge.gateSlots_append] at full
  omega

end ECDSAAdd.Entrant
