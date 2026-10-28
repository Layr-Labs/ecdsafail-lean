import ECDSAAdd.Arithmetic.MeasuredStreamedCProof
import ECDSAAdd.Arithmetic.MeasuredStreamedResult

set_option maxHeartbeats 3000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem measured_input_out_disjoint (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    (L.core.y++[L.core.sumCarry]).Disjoint L.core.out := by
  apply List.disjoint_left.mpr
  intro q hi ho
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hi
  have b := List.count_pos_iff.mpr ho
  simp only [wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h a
  omega

/-- The complete emitted controlled square subtraction, for every 256-bit
source, canonical output and every measurement record. Every non-output
wire, including control and all shared scratch, and the phase are restored. -/
theorem measuredProgram_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) :
    (run (L.measuredProgram control) records s).phase=s.phase ∧
    regValue L.core.out (run (L.measuredProgram control) records s).basis=
      (O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (L.measuredProgram control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [wires,CuccaroStreamedSquareLayout.wires,bad])
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
  let restC := restB.drop (measurementCount (L.measuredBranchC control))
  let u := run (L.measuredBranchA control) (records.take (measurementCount (L.measuredBranchA control))) s
  let v := run (L.measuredBranchB control) (restA.take (measurementCount (L.measuredBranchB control))) u
  let w := run (L.measuredBranchC control) (restB.take (measurementCount (L.measuredBranchC control))) v
  let out := run L.reflectOutput restC w
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
    (restB.take (measurementCount (L.measuredBranchC control))) lowV sumV sumBound eb.2.1 productV cleanV
  rw [ctrlV] at ec
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ec.2.2 q hq).trans (sameV q hq)
  have cleanW : L.PairClean w.basis :=
    L.squareFrame_clean nd s.basis w.basis OC ⟨ec.2.1,sameW⟩ hc
  have er := L.reflectOutput_correct hw nd OC (measured_results_lt PC OB).2.2 w restC ec.2.1 cleanW
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p := by
    have exactResult := measuredCompleteResult_exact enabled A B O
    rw [split] at exactResult
    exact er.2.1.trans exactResult
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      (O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨er.1.trans (ec.1.trans (eb.1.trans ea.1)),fullValue,?_⟩
    intro q hq
    exact (er.2.2 q hq).trans (sameW q hq)
  simpa [measuredProgram,u,v,w,out,restA,restB,restC,enabled,run_append,Nat.add_assoc] using final

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
