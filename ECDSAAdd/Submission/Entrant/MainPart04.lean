import ECDSAAdd.Submission.Entrant.MainPart03

set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProgram =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18LowK

/-! The checked675/BF719 square with only the18 carry-free low-bit changes. -/
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

abbrev target := SquareCarryLoan719.target
abbrev earlyHost := SquareCarryLoan719.earlyHost
abbrev earlyPerm := SquareCarryLoan719.earlyPerm
abbrev foldPerm := SquareCarryLoan719.foldPerm
abbrev patchKG := SquareCarryLoan719.patchKG
abbrev K : Nat := ControlLoan1589BFFold.K

def make (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.make (patchKG L R)

def clear (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.clear (patchKG L R)

def clearPrefix (R : KG) : Program :=
  R.R.smk++R.R.c8z++R.R.c7t++R.R.c6h++R.Q5c++R.R.scl1591++R.Q2c

def withLowK2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program) : Program :=
  let R := LowZero18LowK.kg L ext src dst
  copyRegister (some control) src (L.inputBank.take src.length)++make L R++
    eraseMask control src (L.inputBank.take src.length)++
    renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)++clear L R++
    eraseMask control src (L.inputBank.take src.length)

def branchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    withLowK2 L ext control L.core.sum L.core.product (CodexCKAccTail.bodyCTail L control)++
    OwnDiagAll12Square.gClear L

set_option maxHeartbeats 4000000 in
theorem withLowK2_bodyCK (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) :
    toffoliCount (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))+31=
      toffoliCount (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    measurementCount (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))=
      measurementCount (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    wires (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))⊆
      wires (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    Challenge.gateSlots (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))≤
      Challenge.gateSlots (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) := by
  have r := CodexCKAccTail.bodyCTail_rel L hw control
  refine ⟨?_,?_,?_,?_⟩
  · simp only [withLowK2,toffoliCount_append,(renameProgram_counts _ _).1]; omega
  · simp only [withLowK2,measurementCount_append,(renameProgram_counts _ _).2]; omega
  · simp only [withLowK2,wires_append,renameProgram_support]
    repeat' apply Finset.union_subset_union
    all_goals first | exact Finset.image_subset_image r.2.2.1 | exact Finset.Subset.refl _
  · simp only [withLowK2,Challenge.gateSlots_append,Baselines.rename_gateSlots]; omega

def branchBF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.high (L.core.product.take 256) (ControlLoan1589BFFold.bBody L control)

def branchAF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.low (L.core.product.take 256) (ControlLoan1589BFFold.aBody L control)

def reflection (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Program :=
  renameProgram (foldPerm L ext) L.reflectOutput

def raw (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control++reflection L ext

def fastCandidate (L : ControlledPointLayout) : Program :=
  raw L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def place (L : ControlledPointLayout) (P : Program) : Program :=
  let p0 := renameProgram (Square5Placement.blockPerm L 202) P
  let p1 := renameProgram (OwnPlusSquare.swap L) p0
  let p2 := renameProgram (OwnGuardSquare.swap L) p1
  let p3 := renameProgram (OwnQ4Square.swap L) p2
  let p4 := renameProgram (OwnQ5Square.swap L) p3
  let p5 := renameProgram (OwnDiagAll12PlacedQ6.swap L) p4
  let p6 := renameProgram (OwnDiagAll12PlacedQ7.swap L) p5
  let p7 := renameProgram (PrefixFrontierSquare1591.swap L) p6
  let p8 := renameProgram (Prefix1590Square.swap L) p7
  renameProgram (ControlLoan1589Square.swap L) p8

def program (L : ControlledPointLayout) : Program := place L (fastCandidate L)

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareSupport =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProgram

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18SquareSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout LowZero18Square
attribute [local irreducible] wires

theorem kg_X1_eq (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (LowZero18LowK.kg L ext src dst).X1=(OwnDiagLowK.kg L ext src dst).X1 :=
  (LowZero18LowK.kg_metadata L ext src dst).2.1.trans
    (SquareCarryLoan719BFSupport.kg_X1_eq L ext src dst)

section Normal
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hw in
theorem target_mem_X1 : target L∈(LowZero18LowK.kg L ext src dst).X1 := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).2.1]
  exact SquareCarryLoan719BFSupport.target_mem_X1 L hw ext src dst

include hw h128 in
theorem earlyHost_mem_outer : earlyHost L∈(LowZero18LowK.kg L ext src dst).R.S := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).1]
  exact SquareCarryLoan719BFSupport.earlyHost_mem_outer L hw ext src dst h128

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem earlyHost_Q1_free :
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1 ∧
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1c := by
  have old := SquareCarryLoan719BFSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  exact ⟨fun used=>old.1 (LowZero18LowK.kg_Q1_subset L hw ext src dst h128 hsmax hlen he used),
    fun used=>old.2 (LowZero18LowK.kg_Q1c_subset L ext src dst used)⟩

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem target_clearPrefix_free :
    target L∉wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst)) := by
  have old := SquareCarryLoan719BFSupport.target_clearPrefix_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))⊆
      wires (SquareCarryLoan719BF.clearPrefix (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
    by_cases h : src.length=128
    all_goals simp only [LowZero18Square.clearPrefix,SquareCarryLoan719BF.clearPrefix,
      LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,
      LowZero18LowK.kgH,LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
      KRegs.c5,KRegs.c2,wires_append]
    all_goals repeat' apply Finset.union_subset_union
    all_goals first | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (TrimSquare4.tsqcM4_wires_le _ _ _ _ _).trans (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact LowZero18Diagonal.clear_support_subset _ |
      exact (LowZero18LowK.oregs L ext src dst).c8z_wires w |
      exact (LowZero18LowK.oregs L ext src dst).c7t_wires | exact (LowZero18LowK.oregs L ext src dst).c6h_wires w |
      exact Finset.Subset.refl _
  exact fun used=>old (sub used)

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem make_tail_free :
    target L∉wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6h++(LowZero18LowK.kg L ext src dst).R.m7k++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591) := by
  have old := SquareCarryLoan719BFSupport.make_tail_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6h++(LowZero18LowK.kg L ext src dst).R.m7k++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591)⊆
    wires ((FrontierSumCleanup1591LowK.kg L ext src dst).Q2++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.smk++(FrontierSumCleanup1591LowK.kg L ext src dst).Q5++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m6++(FrontierSumCleanup1591LowK.kg L ext src dst).R.m7++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m8++(FrontierSumCleanup1591LowK.kg L ext src dst).R.scl1591) := by
    have ro : FrontierSumCleanup1591LowK.oregs L ext src dst = LowZero18LowK.oregs L ext src dst := rfl
    have a6 := (LowZero18LowK.oregs L ext src dst).m6h_wires_smk w
    have a7 := (LowZero18LowK.oregs L ext src dst).m7k_wires w
    have a8 := (LowZero18LowK.oregs L ext src dst).m8z_wires w
    by_cases h : src.length=128
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsH L ext src dst)
        (LowZero18LowK.jregsH_W L hw ext src dst h hlen he)
      have rj : FrontierSumCleanup1591LowK.jregsH L ext src dst = LowZero18LowK.jregsH L ext src dst := rfl
      have q5 := (TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).S (LowZero18LowK.oregs L ext src dst).T (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).1
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,
        LowZero18LowK.kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append,ro,rj]
      exact CodexBorrowedUnion.seven jp q5 a6 a7 a8
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsS L ext src dst)
        (LowZero18LowK.jregsS_W L hw ext src dst (by omega) hlen he)
      have rj : FrontierSumCleanup1591LowK.jregsS L ext src dst = LowZero18LowK.jregsS L ext src dst := rfl
      have q2 := (TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).hi (LowZero18LowK.oregs L ext src dst).dhi (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).1
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_false,
        LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append,ro,rj]
      exact CodexBorrowedUnion.seven q2 jp a6 a7 a8
  exact fun used=>old (sub used)

end Normal
end ECDSAAdd.Entrant.LowZero18SquareSupport
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareSupport

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] run wires

abbrev fold_run_eq := SquareCarryLoan719.fold_run_eq

theorem patchKG_make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (K : KG)
    (sp : K.Spec) (targetX1 : target L∈K.X1) (hostS : earlyHost L∈K.R.S)
    (hostFree : earlyHost L∉wires K.Q1)
    (innerZero : ∀v t,K.I1 v t → t (target L)=false) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hX0 : regValue K.X s.basis=0) (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    run (LowZero18Square.make L K) m s=run (LowZero18KG.make K) m s := by
  have dlo0 : regValue K.R.dlo s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hd0 q (List.mem_of_mem_take hq))
  have x10 : regValue K.X1 s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hX0 q (by simp only [KG.X,List.mem_append];tauto))
  have headEq (records : List Bool) := SquareCarryLoan719.q1_run_eq L hw K sp targetX1 hostFree innerZero
    s records dlo0 x10 hp0 hc0 hz0 hi0 ((regValue_zero _ _).mp hS0 _ hostS)
  let tail := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
  have oldShape : LowZero18KG.make K=K.Q1++tail := by simp only [LowZero18KG.make,tail,List.append_assoc]
  have newShape : LowZero18Square.make L K=renameProgram (earlyPerm L) K.Q1++tail := by
    simp only [LowZero18Square.make,SquareCarryLoan719.patchKG,LowZero18KG.make,tail,List.append_assoc]
  simp only [newShape,oldShape,run_append,(renameProgram_counts _ _).2]
  rw [headEq]

theorem make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (sp : (LowZero18LowK.kg L ext src dst).Spec) (s : State) (m : List Bool)
    (hd0 : regValue (LowZero18LowK.kg L ext src dst).R.dst s.basis=0)
    (hS0 : regValue (LowZero18LowK.kg L ext src dst).R.S s.basis=0)
    (hX0 : regValue (LowZero18LowK.kg L ext src dst).X s.basis=0)
    (hz0 : regValue (LowZero18LowK.kg L ext src dst).R.z s.basis=0)
    (hp0 : regValue (LowZero18LowK.kg L ext src dst).R.pad s.basis=0)
    (hc0 : regValue (LowZero18LowK.kg L ext src dst).R.carry s.basis=0)
    (hi0 : s.basis (LowZero18LowK.kg L ext src dst).R.cin=false) :
    run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) m s=
      run (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) m s := by
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  apply patchKG_make_run_eq L hw (LowZero18LowK.kg L ext src dst) sp
    (LowZero18SquareSupport.target_mem_X1 L hw ext src dst)
    (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128) free.1
    ?_ s m hd0 hS0 hX0 hz0 hp0 hc0 hi0
  intro v t inv
  rw [LowZero18LowK.kg_I1] at inv
  exact (regValue_zero _ _).mp inv.1 _
    (SquareCarryLoan719Support.target_mem_inner L hw ext src dst)

theorem clear_run_eq_of_boundaries (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (K : KG) (s : State) (m : List Bool)
    (prefixFree : target L∉wires (clearPrefix K))
    (hostFree : earlyHost L∉wires K.Q1c)
    (targetIn : s.basis (target L)=false)
    (targetOut : (run (LowZero18KG.clear K) m s).basis (target L)=false)
    (hostOut : (run (LowZero18KG.clear K) m s).basis (earlyHost L)=false) :
    run (LowZero18Square.clear L K) m s=run (LowZero18KG.clear K) m s := by
  let middle := run (clearPrefix K) (m.take (measurementCount (clearPrefix K))) s
  let records := m.drop (measurementCount (clearPrefix K))
  have oldShape : LowZero18KG.clear K=clearPrefix K++K.Q1c := by
    simp only [LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have newShape : LowZero18Square.clear L K=clearPrefix K++renameProgram (earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,SquareCarryLoan719.patchKG,LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have oldRun : run (LowZero18KG.clear K) m s=run K.Q1c records middle := by rw [oldShape,run_append]
  have targetMid : middle.basis (target L)=false :=
    (run_preserves_outside _ _ s _ prefixFree).trans targetIn
  rw [oldRun] at targetOut hostOut
  have hostMid : middle.basis (earlyHost L)=false :=
    (run_preserves_outside _ records middle _ hostFree).symm.trans hostOut
  have lastEq := NewFieldFrameOB5.rebind_swap_run (target L) (earlyHost L) K.Q1c
    middle records targetMid hostMid targetOut hostOut
  rw [←SquareCarryLoan719.earlyPerm_eq L hw] at lastEq
  rw [newShape,oldShape,run_append,run_append]
  exact lastEq

theorem cross_host_zero (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)
    (h128 : 128≤src.length) (he : 300≤ext.length) (s : BasisState) (a b : Nat)
    (value : regValue (LowZero18LowK.oregs L ext src dst).T s=2*a*b) :
    s (ext.getD 0 0)=false :=
  SquareCarryLoan719.cross_host_zero L ext src dst h128 he s a b value

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProof =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff

/-! The checked BF719 state proof with only the LowZero producer/cleanup constructors changed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

private theorem k2_xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem withLowK2_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (LowZero18Square.withLowK2 L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  let P := if s.basis control then regValue src s.basis else 0
  obtain ⟨a6,r7,e7⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) records s
  obtain ⟨a5,r6,e6⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)) (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body)
    (copyRegister (some control) src (L.inputBank.take src.length)) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)) (renameProgram (foldPerm L ext) body) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)) (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) a2 s
  rw [show LowZero18Square.withLowK2 L ext control src dst body=copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length) from rfl,e7,e6,e5,e4,e3,e2]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- erase
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask u1 r3 (by
    rw [bank1,ctl1,src1])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r3 u1=u2 at ep1 ef1 ev1 ⊢
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev1 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · exact (ef1 q hb).trans ((u1z q hq hx).trans (u0s q hb))
  have u2ext : ∀q∈ext,u2.basis q=u1.basis q := fun q h => ef1 q (extB q h)
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact ef1 q (fun h => bD q h hq)
  have cb := callback u2' r4 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r4 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r4 u2'=v' at cb loc
  generalize hv : run body r4 u2=v at loc
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r4 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r4 u2 q hb,run_preserves_outside body r4 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply k2_xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r4 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r4 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
  -- second copy
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB v r5
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r5 v=w0 at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := by
    rw [cv2,show regValue (L.inputBank.take src.length) v.basis=0 from (regValue_congr _ _ _ vB).trans banks.1,Nat.zero_xor]
    change (if v.basis control then regValue src v.basis else 0)=P
    rw [show v.basis control=s.basis control from (vFrame _ ctlO).trans (u2s _ ctlD ctlE),regValue_congr _ _ _ vSrc]
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    rw [cf2 q hb,vFrame q ho]
    by_cases hx : q∈ext
    · exact u2ext q hx
    · exact ef1 q hb
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r6
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r6
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r6 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2 q (srcB q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2 _ ctlB).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r7 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r7 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (cp2.trans (vPhase.trans (ep1.trans (mk.1.trans cp1))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2 q (fun h => bOut q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX,cf2 q hb,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx


theorem reflection_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (O : Nat) (hO : O<SquareReduction.p)
    (s : State) (m : List Bool) (ho : regValue L.core.out s.basis=O)
    (hc : L.PairClean s.basis) (hz : regValue ext s.basis=0) :
    (run (reflection L ext) m s).phase=s.phase ∧
    regValue L.core.out (run (reflection L ext) m s).basis=SquareReduction.p-1-O ∧
    ∀q,q∉L.core.out → (run (reflection L ext) m s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have old := L.reflectOutput_correct hw nd O hO s m ho hc
  have len := OwnDiagLowK.ktmp_length L hw
  have member : target L∈OwnDiagLowK.ktmp L := DiagSq.getD_in _ 67 (by omega)
  have pad : target L∈L.foldPad := List.mem_of_mem_drop member
  have away : target L∉L.core.out :=
    (L.pairAuxAway nd _ (by simp only [List.mem_append];tauto)).2
  have tin : s.basis (target L)=false := (regValue_zero _ _).mp hc.pad _ pad
  have tout : (run L.reflectOutput m s).basis (target L)=false := (old.2.2 _ away).trans tin
  have host : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by have h:=he.len;omega)
  have hin : s.basis (ext.getD 0 0)=false := (regValue_zero _ _).mp hz _ host
  have free : ext.getD 0 0∉wires L.reflectOutput := fun used=>
    he.away _ host (List.mem_toFinset.mp (ControlLoan1589BFFold.reflect_support L control used))
  have eq := SquareCarryLoan719.fold_run_eq L hw ext L.reflectOutput s m tin tout hin free
  simpa only [reflection,eq] using old

def middleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (CodexCKAccTail.bodyCTail L control)

theorem middleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (middleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (middleCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (middleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (CodexCKAccTail.bodyCTail L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (CodexCKAccTail.bodyCTail_support L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (CodexCKAccTail.bodyCTail L control) hbody
    s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := CodexCKAccTail.accMiddleCFTail_body L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem branchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (LowZero18Square.branchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.branchCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.branchCK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := middleCK L ext control
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let rest := records.drop mp
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (OwnDiagAll12Square.gClear L) (rest.drop (measurementCount middle)) v
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (OwnDiagAll12Square.sum_in L control q bad)))).trans hz
  have used := middleCK_correct L hw ext control hn (A+B) O hO u
    (rest.take (measurementCount middle)) prep.2.1 outU productU cleanU he hzU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have workRestore : regValue L.core.work restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hc.work
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [hq])).2
    simp [restoreBase,away]
  have cleared := OwnDiagAll12Square.gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [LowZero18Square.branchCK,middleCK,middle,u,v,out,rest,mp,run_append] using final


theorem branchBF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchBF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchBF L ext control) records s).basis=
      ControlLoan1589BFFold.resBF ((if s.basis control then B else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchBF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ControlLoan1589BFFold.bBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ControlLoan1589BFFold.bBody_support L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len
    (ControlLoan1589BFFold.bBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have frame := ControlLoan1589BFFold.bBody_frame L hw nd control hcw t.basis M mb full clean O hO t m ⟨outO,fun _ _ => rfl⟩
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  rw [ControlLoan1589BFFold.bO4_eq M O (t.basis control) mb hg hO,ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

theorem branchAF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchAF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchAF L ext control) records s).basis=
      ControlLoan1589BFFold.resAF ((if s.basis control then A else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchAF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ControlLoan1589BFFold.aBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ControlLoan1589BFFold.aBody_support L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len
    (ControlLoan1589BFFold.aBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [ha] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have frame := ControlLoan1589BFFold.aBody_frame L hw nd control hcw t.basis M mb full clean O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩


theorem raw_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (raw L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (raw L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (raw L ext control) records s).basis q=s.basis q := by
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
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
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
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepR : Triple (SquareFrame L.core.out s.basis OA) (reflection L ext)
      (SquareFrame L.core.out s.basis (SquareReduction.p-1-OA)) := by
    intro t m hf
    have h := reflection_correct L hw control hn ext he OA (ofCast_lt _ _) t m hf.1
      (L.squareFrame_clean nd s.basis t.basis OA hf hc) (extZ _ _ hf)
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := ((stepC.seq stepB).seq stepA).seq stepR
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  exact ⟨phase,value.trans exactResult,frame⟩


theorem raw_state_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (m mOld : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) (he : ECDSAAdd.Entrant.ExtOK L control ext)
    (hz : regValue ext s.basis=0) :
    run (raw L ext control) m s=run (ControlLoan1589BFFold.program L ext control) mOld s := by
  have fresh := raw_correct L hw ext control hn Y O hO s m hy ho hp0 hs0 hc he hz
  have prior := ControlLoan1589BFFold.correct L hw ext control hn Y O hO s mOld hy ho hp0 hs0 hc he hz
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases inside : q∈L.core.out
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q inside
    · exact (fresh.2.2 q inside).trans (prior.2.2 q inside).symm

open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCandidate_state_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (hX : X<p) (s : State) (m mOld : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (fastCandidate L) m s=run (ControlLoan1589BFSquare.fastCandidate L) mOld s := by
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
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_state_eq K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m mOld hy hx prod0 sum0 clean
    (ECDSAAdd.Entrant.kext_ok L hw hn) hz
  simpa only [fastCandidate,ControlLoan1589BFSquare.fastCandidate] using kernel

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (fastCandidate L) := by
  intro X Y G origin s m v
  have old := ControlLoan1589BFSquare.candidate_correct L hw hn X Y G origin s m v
  have eq := fastCandidate_state_eq L hw hn X.val Y.val X.isLt s m m v.x v.y v.clean
  simpa only [eq] using old

private theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (old : ControlLoan1589BFSquare.SquareCorrectK L K P) :
    ControlLoan1589BFSquare.SquareCorrectK L K (renameProgram e P) := by
  intro X Y G origin s m v
  have result := old X Y G origin s m v
  have eq := Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean result.2.clean
  simpa only [eq] using result

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (program L) := by
  have a0 := relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have a1 := relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw) _ a0
  have a2 := relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw) _ a1
  have a3 := relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw) _ a2
  have a4 := relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw) _ a3
  have a5 := relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw) (OwnDiagAll12PlacedQ6.outside L hw) _ a4
  have a6 := relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw) (OwnDiagAll12PlacedQ7.outside L hw) _ a5
  have a7 := relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw) (PrefixFrontierSquare1591.outside L hw) _ a6
  have a8 := relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw) (Prefix1590Square.outside L hw) _ a7
  have a9 := relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw) (ControlLoan1589Square.outside L hw) _ a8
  exact a9

theorem step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (K:Fp) else 0)) Y G origin) :=
  correct L hw hn X Y G origin

private theorem values_unique {L : ControlledPointLayout} {X Y : Fp} {G : Bool}
    {origin a b : BasisState} (ha : PointDialogValues L X Y G origin a)
    (hb : PointDialogValues L X Y G origin b) : a=b := by
  funext q
  by_cases hx : q∈L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ha.x.trans hb.x.symm) q hx
  · by_cases hy : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp (ha.y.trans hb.y.symm) q hy
    · have away : q∉L.point.x++L.point.y := by
        simpa only [List.mem_append,not_or] using And.intro hx hy
      exact (ha.rest q away).trans (hb.rest q away).symm

theorem state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (ControlLoan1589BFSquare.program L) mOld s := by
  have fresh := correct L hw hn X Y G origin s m v
  have prior := ControlLoan1589BFSquare.correct L hw hn X Y G origin s mOld v
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · exact values_unique fresh.2 prior.2

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 :=
  (correct L hw hn X Y G origin s m v).2.clean

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareResources =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProof

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

private theorem source_counts (L : CuccaroStreamedSquareWideLayout) :
    (∀q,L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,(L.core.product.take 256).count q≤L.core.product.count q) := by
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans ((List.drop_sublist 128 L.core.y).count_le q)
  refine ⟨?_,?_,?_,fun q=>(List.take_sublist 256 L.core.product).count_le q⟩
  · intro q
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢;omega
  · intro q;have h := hh q;simp only [List.count_append];omega
  · intro q;have h := hh q;simp only [CuccaroStreamedSquareLayout.sum,List.count_append];omega

theorem patchKG_counts (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    toffoliCount (LowZero18Square.make L R)=toffoliCount (LowZero18KG.make R) ∧
    measurementCount (LowZero18Square.make L R)=measurementCount (LowZero18KG.make R) ∧
    toffoliCount (LowZero18Square.clear L R)=toffoliCount (LowZero18KG.clear R) ∧
    measurementCount (LowZero18Square.clear L R)=measurementCount (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem patchKG_slots (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    Challenge.gateSlots (LowZero18Square.make L R)=Challenge.gateSlots (LowZero18KG.make R) ∧
    Challenge.gateSlots (LowZero18Square.clear L R)=Challenge.gateSlots (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,Challenge.gateSlots_append,
    Baselines.rename_gateSlots,and_self]

theorem withLowK2_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (withLowK2 L ext control src dst body)+66+5*(if src.length=128 then 0 else 1)=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (withLowK2 L ext control src dst body)+24+4*(if src.length=128 then 0 else 1)=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have d := LowZero18LowK.kg_counts_diff L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,toffoliCount_append,measurementCount_append,
    (patchKG_counts L _).1,(patchKG_counts L _).2.1,(patchKG_counts L _).2.2.1,(patchKG_counts L _).2.2.2,
    (SquareCarryLoan719BF.patchKG_counts L _).1,(SquareCarryLoan719BF.patchKG_counts L _).2.1,
    (SquareCarryLoan719BF.patchKG_counts L _).2.2.1,(SquareCarryLoan719BF.patchKG_counts L _).2.2.2,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem withLowK2_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have m := LowZero18LowK.loan_make_support_subset L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_support_subset L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,make,clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact m | exact c | exact Finset.Subset.refl _

theorem withLowK2_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have m := LowZero18LowK.loan_make_slots_le L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_slots_le L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,make,clear,patchKG,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

theorem raw_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (raw L ext control)+234=toffoliCount (SquareCarryLoan719BF.raw L ext control) ∧
    measurementCount (raw L ext control)+76=measurementCount (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_counts_diff L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_counts_diff L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_counts_diff L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  rw [if_neg (show ¬L.core.sum.length=128 by omega)] at c
  rw [if_pos high] at b
  rw [if_pos low] at a
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,
    toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem raw_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (raw L ext control)⊆wires (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_support_subset L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_support_subset L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_support_subset L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact k3.trans c | exact c | exact b | exact a | exact Finset.Subset.refl _

theorem raw_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (raw L ext control)≤Challenge.gateSlots (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_slots_le L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_slots_le L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_slots_le L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

private theorem tRename (f : Wire→Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem mRename (f : Wire→Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+234=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+76=measurementCount (SquareCarryLoan719BF.program L) := by
  have h := raw_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,tRename,mRename] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52025 ∧ measurementCount (program L)=52999 := by
  have a := counts_diff L hw
  have b := SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  have h := raw_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,Baselines.rename_gateSlots] using h

theorem slots (L : ControlledPointLayout) (hw : L.Widths) : Challenge.gateSlots (program L)≤8000000 :=
  (slots_le L hw).trans (SquareCarryLoan719BF.slots L hw)

private theorem place_support_mono (L : ControlledPointLayout) (P Q : Program) (sub : wires P⊆wires Q) :
    wires (place L P)⊆wires (SquareCarryLoan719BF.place L Q) := by
  unfold place SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact sub

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  apply place_support_mono
  exact raw_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (SquareCarryLoan719BF.support L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire k∉wires (program L) :=
  fun used=>SquareCarryLoan719BF.square_free L hw hn k hk (support_subset L hw used)

theorem retired_free719 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 719∉wires (program L) := square_free L hw hn 719 (by simp)
theorem retired_free768 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 768∉wires (program L) := square_free L hw hn 768 (by simp)
theorem retired_free718 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (program L) := square_free L hw hn 718 (by simp)

private theorem patchKG_physical (L : CuccaroStreamedSquareWideLayout) (R : KG)
    (hm : GatePhysical (LowZero18KG.make R))
    (hc : GatePhysical (LowZero18KG.clear R)) :
    GatePhysical (LowZero18Square.make L R) ∧ GatePhysical (LowZero18Square.clear L R) := by
  simp only [LowZero18KG.make,gatePhysical_append] at hm
  simp only [LowZero18KG.clear,gatePhysical_append] at hc
  have first : GatePhysical (renameProgram (earlyPerm L) R.Q1) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  have last : GatePhysical (renameProgram (earlyPerm L) R.Q1c) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,gatePhysical_append]
  tauto

private theorem withLowK2_physical_of_old (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (src dst : List Wire) (body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hlen : dst.length=2*src.length)
    (old : GatePhysical (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst body)) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  simp only [FrontierSumCleanup1591LowK.withLowK2,gatePhysical_append] at old
  have nd := LowZero18LowK.kg_nodup L control hn ext src dst hs hd he.nodup he.away
  have ph := LowZero18LowK.kg_physical L hw ext src dst h128 h129 hlen he.len nd
  have kernels := patchKG_physical L (LowZero18LowK.kg L ext src dst) ph.1 ph.2
  have bodyNew : GatePhysical (renameProgram (foldPerm L ext) body) :=
    gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ (by tauto)
  simp only [withLowK2,gatePhysical_append]
  tauto

private theorem raw_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) : GatePhysical (raw L ext control) := by
  have old := ControlLoan1589BFFold.physical L hw ext control hn he
  simp only [ControlLoan1589BFFold.program,FrontierSumCleanup1591Raw.accBranchCK,
    FrontierSumCleanup1591Raw.accMiddleCK,ControlLoan1589BFFold.branchBF,
    ControlLoan1589BFFold.branchAF,gatePhysical_append] at old
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sc := source_counts L
  have c := withLowK2_physical_of_old L hw ext control hn he L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) sc.2.2.1 (fun _=>le_rfl)
    (by omega) (by omega) (by rw [hw.core.product,sum]) old.1.1.1.1.2
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have c : GatePhysical (withLowK2 L ext control L.core.sum L.core.product (CodexCKAccTail.bodyCTail L control)) := by
    have pb := CodexCKAccTail.bodyCTail_physical L hw (List.nodup_cons.mp hn).2 control (List.nodup_cons.mp hn).1
    have pr := gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ pb
    simp only [withLowK2,gatePhysical_append] at c ⊢
    tauto
  have b := withLowK2_physical_of_old L hw ext control hn he L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) sc.2.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.1.2
  have a := withLowK2_physical_of_old L hw ext control hn he L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) sc.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.2
  have r := gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ old.2
  simp only [raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,reflection,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨old.1.1.1.1.1,c⟩,old.1.1.1.2⟩,b⟩,a⟩,r⟩

private theorem control_nd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢
  omega

private theorem place_physical (L : ControlledPointLayout) (P : Program) (hp : GatePhysical P) :
    GatePhysical (place L P) := by
  unfold place
  apply gatePhysical_rename (ControlLoan1589Square.swap L) (ControlLoan1589Square.swap L).injective
  apply gatePhysical_rename (Prefix1590Square.swap L) (Prefix1590Square.swap L).injective
  apply gatePhysical_rename (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.swap L).injective
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202) (Square5Placement.blockPerm L 202).injective _ hp

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (program L) :=
  place_physical L _ (raw_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (control_nd L hw hn) (ECDSAAdd.Entrant.kext_ok L hw hn))

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588LowZeroFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588BFFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588LowZeroFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
  ControlLoan1589BFFinal
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  Offset.gen L (division Rolling1588.entryKernel L) (LowZero18Square.program L)
    (exit Rolling1588.exitKernel L) cx cy

private def Metrics (P Q : Program) : Prop :=
  toffoliCount P+234=toffoliCount Q ∧ measurementCount P+76=measurementCount Q ∧
    gateSlots P≤gateSlots Q

private theorem gen_metrics_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : Metrics S Old) : Metrics G G0 := by
  subst G G0
  simp only [Metrics,Offset.gen,Offset.mid,Offset.generic,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at hs ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Metrics (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) := by
  have counts:=LowZero18Square.counts_diff L hw
  exact gen_metrics_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    ⟨counts.1,counts.2,LowZero18Square.slots_le L hw⟩

theorem gen_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+234=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+76=measurementCount (Rolling1588BFFinal.gen L cx cy) :=
  ⟨(gen_metrics L hw cx cy).1,(gen_metrics L hw cx cy).2.1⟩

private theorem wrapper_metrics (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Metrics P Q) :
    Metrics (Edges.wrapper L C cy P) (Edges.wrapper L C cy Q) := by
  simp only [Metrics,Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at h ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_subset_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : wires S⊆wires Old) : wires G⊆wires G0 := by
  subst G G0
  simp only [Offset.gen,Offset.mid,Offset.generic,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact hs | exact Finset.Subset.refl _

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (Rolling1588BFFinal.gen L cx cy) :=
  gen_subset_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    (LowZero18Square.support_subset L hw)

private theorem wrapper_subset (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P⊆wires Q) :
    wires (Edges.wrapper L C cy P)⊆wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact h | exact Finset.Subset.refl _

private theorem qubits_mono (P Q : Program) (h : wires P⊆wires Q) : qubits P≤qubits Q := by
  change (ioWires∪wires P).card≤(ioWires∪wires Q).card
  exact Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _) h)

theorem gen_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  exact Offset.genFFused_ok L hw hn _ _ _
    (FrontierEntry1591Callers.exit_correct Rolling1588.exitKernel
      Rolling1588.exitKernel_support Rolling1588.exit_correct L hw hn)
    (FrontierEntry1591Callers.division_step Rolling1588.entryKernel
      Rolling1588.entryKernel_support Rolling1588.entry_correct
      L hw hn config.1 above config.2.1 config.2.2)
    (LowZero18Square.step L hw hn) hc

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (Rolling1588BFFinal.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) :=
  Offset.gen_physical L hw hn _ _ _
    (division_physical Rolling1588.entryKernel Rolling1588.entryKernel_support
      Rolling1588.entryKernel_physical L hw hn)
    (LowZero18Square.physical L hw hn)
    (placed_physical Rolling1588.exitKernel Rolling1588.exitKernel_support
      Rolling1588.exitKernel_physical L hw hn) cx cy

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 :=
  (qubits_mono _ _ (wrapper_subset layout C cy _ _
    (gen_support_subset layout layout_widths cx cy))).trans
    (Rolling1588BFFinal.wrapper_qubits C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2152269 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).1
  have old:=Rolling1588BFFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499935 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).2.1
  have old:=Rolling1588BFFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50119199+Rolling1588.slotGrowth :=
  (wrapper_metrics layout C cy _ _ (gen_metrics layout layout_widths cx cy)).2.2.trans
    (Rolling1588BFFinal.wrapper_slots C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152269,1499935,1588,50119199+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (gen_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2152269 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1499935 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50119199+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499935
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50119199+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.Rolling1588LowZeroFinal
end -- original module boundary

-- Selected checked E1 branch follows; the audited LowZero18 branch is omitted.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.SquareCarryLoan719BFProof

/-! Remove only the BF square's final reflection. All719 loans stay intact. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  SquareCarryLoan719BF
attribute [local irreducible] run wires

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program := place L (fastCore L)

def reflectedTail (L : ControlledPointLayout) : Program :=
  place L (reflection L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    raw L ext control=core L ext control++reflection L ext := rfl

theorem place_append (L : ControlledPointLayout) (P Q : Program) :
    place L (P++Q)=place L P++place L Q := by
  simp only [place,renameProgram,List.map_append]

theorem program_split (L : ControlledPointLayout) :
    SquareCarryLoan719BF.program L=program L++reflectedTail L := by
  simp only [SquareCarryLoan719BF.program,SquareCarryLoan719BF.fastCandidate,
    raw_split,place_append,program,fastCore,reflectedTail]

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
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
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
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
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (SquareCarryLoan719BF.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := SquareCarryLoan719BF.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
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
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  have prior:=ControlLoan1589BFSquare.fastCandidate_correct L hw hn X.val Y.val G X.isLt s []
    v.generic v.x v.y v.clean
  have canonical:=SquareCarryLoan719BF.candidate_correct L hw hn X Y G origin s [] v
  have eq:=SquareCarryLoan719BF.fastCandidate_state_eq L hw hn X.val Y.val X.isLt s [] []
    v.x v.y v.clean
  rw [eq] at canonical
  have value:=prior.2.1.symm.trans canonical.2.x
  rw [value] at fresh
  exact fresh

private theorem place_relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (renameProgram e P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L e hp hf P s m before after

/-- Transport the complete State before taking any projection. -/
theorem place_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (place L P) m s=run P m s := by
  have a0:=place_relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) P s m before after
  have a1:=place_relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw)
    _ s m before (by rw [a0];exact after)
  have a2:=place_relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw)
    _ s m before (by rw [a1,a0];exact after)
  have a3:=place_relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw)
    _ s m before (by rw [a2,a1,a0];exact after)
  have a4:=place_relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw)
    _ s m before (by rw [a3,a2,a1,a0];exact after)
  have a5:=place_relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw)
    (OwnDiagAll12PlacedQ6.outside L hw) _ s m before (by rw [a4,a3,a2,a1,a0];exact after)
  have a6:=place_relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw)
    (OwnDiagAll12PlacedQ7.outside L hw) _ s m before (by rw [a5,a4,a3,a2,a1,a0];exact after)
  have a7:=place_relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw)
    (PrefixFrontierSquare1591.outside L hw) _ s m before (by rw [a6,a5,a4,a3,a2,a1,a0];exact after)
  have a8:=place_relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw)
    (Prefix1590Square.outside L hw) _ s m before (by rw [a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  have a9:=place_relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw)
    (ControlLoan1589Square.outside L hw) _ s m before (by rw [a8,a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  simpa only [place,a8,a7,a6,a5,a4,a3,a2,a1,a0] using a9


private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem support_subset (L : ControlledPointLayout) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  rw [program_split,wires_append]
  exact Finset.subset_union_left

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L).trans (SquareCarryLoan719BF.support L hw hn)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have old:=SquareCarryLoan719BF.physical L hw hn
  rw [program_split,gatePhysical_append] at old
  exact old.1

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) := by
  by_cases h : i=719
  · subst i;exact fun used=>SquareCarryLoan719BF.retired_free719 L hw hn (support_subset L used)
  · exact fun used=>SquareCarryLoan719BF.square_free L hw hn i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto) (support_subset L used)

theorem place_counts (L : ControlledPointLayout) (P : Program) :
    toffoliCount (place L P)=toffoliCount P ∧ measurementCount (place L P)=measurementCount P := by
  simp only [place,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem reflectedTail_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (reflectedTail L)=255 ∧ measurementCount (reflectedTail L)=255 := by
  have r:=(L.dialogStreamedSquareWide.measured_small_operation_counts
    (L.dialogStreamedSquareWide_widths hw)).2.2
  simpa only [reflectedTail,(place_counts _ _).1,(place_counts _ _).2,reflection,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using r

theorem counts_delta (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+255=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+255=measurementCount (SquareCarryLoan719BF.program L) := by
  rw [program_split,toffoliCount_append,measurementCount_append,
    (reflectedTail_counts L hw).1,(reflectedTail_counts L hw).2]
  exact ⟨rfl,rfl⟩

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52004 ∧ measurementCount (program L)=52820 := by
  have d:=counts_delta L hw
  have c:=SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  rw [program_split,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.ReflectionE1Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.E1Merge =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectValues
-- consolidated import: import ECDSAAdd.Arithmetic.Compare
-- consolidated import: import ECDSAAdd.Arithmetic.ComparePhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MaskedConstant
-- consolidated import: import ECDSAAdd.Arithmetic.MappedSources
-- consolidated import: import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Copy
-- consolidated import: import ECDSAAdd.Arithmetic.Rotate
-- consolidated import: import ECDSAAdd.Arithmetic.Reduction
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredGateSupport
-- consolidated import: import ECDSAAdd.Arithmetic.NativeFirstDirectSupport
-- consolidated import: import ECDSAAdd.Baselines.SlotAlgebra
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Baselines.SlotNativeFirst

set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.E1Merge
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum

/-! ### Arithmetic of the merged first tick -/

theorem p_val : p = 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [ECDSAAdd.p]

/-- bit 0 of the selected constant `g·k − f·p`. -/
def ksel0 (k : Nat) (G f : Bool) : Bool := (G && decide (k%2=1)) ^^ f
/-- low bit of the input implied by `(g,f,par)`. -/
def x0 (k : Nat) (G f par : Bool) : Bool := par ^^ ksel0 k G f

/-- Constant added to `x>>1` to obtain the first-tick `K` word directly. -/
def tk (k : Nat) (G f par : Bool) : Nat :=
  if f then (if G then (kConstant false par+2^258-(p+par.toNat-(x0 k G f par).toNat-k)/2)%2^258 else 0)
  else if G then (kConstant false par+((x0 k G f par).toNat+k-par.toNat)/2)%2^258
  else kConstant false par

def delta (par : Bool) : Nat := if par then p else 2^257-p

def thr (k : Nat) (G par : Bool) : Nat := if G then (if par then (k+p+1)/2 else (k+1)/2) else 0

theorem hC_val : hConstant = 57896044618658097711785492504343953926634992332820282019728792003954417335832 := by
  norm_num [hConstant, ECDSAAdd.p]
theorem kC_val (par : Bool) : kConstant false par =
    if par then 405272312330606683982498447530407677486444946329741974138101544027698101223913
    else 115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  cases par <;> norm_num [kConstant, ECDSAAdd.p]


theorem arith (k X : Nat) (hk : k<p) (hX : X<p) (G : Bool) :
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    decide (X%2=1)=x0 k G f par ∧
    (X/2+tk k G f par)%2^258=K ∧
    H=dx/2+(if par then hConstant else 0) ∧
    f=decide (H<thr k G par) ∧
    tk k G f par<2^258 := by
  intro f dx par K H
  rw [p_val] at hk hX
  simp only [f,dx,par,K,H,tk,delta,thr,x0,ksel0,kC_val,hC_val,p_val,Nat.reducePow]
  clear H K par dx f
  cases G
  · have e1 : (X+0)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X := Nat.mod_eq_of_lt (by omega)
    have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-0<X)=false := by
      simp only [decide_eq_false_iff_not]; omega
    simp only [if_false,Bool.false_eq_true,e1,e2,Bool.false_and,Bool.false_xor,Bool.xor_false]
    rcases Nat.mod_two_eq_zero_or_one X with h|h <;>
    simp only [h,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
      Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true] <;>
    exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
  · simp only [if_true,Bool.true_and]
    by_cases hf : 115792089237316195423570985008687907853269984665640564039457584007908834671663≤X+k
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
        rw [Nat.mod_eq_sub_mod hf,Nat.mod_eq_of_lt (by omega)]
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=true := by
        simp only [decide_eq_true_iff]; omega
      simp only [e1,e2,Bool.xor_true]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k-115792089237316195423570985008687907853269984665640564039457584007908834671663) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩
    · have e1 : (X+k)%115792089237316195423570985008687907853269984665640564039457584007908834671663=X+k := Nat.mod_eq_of_lt (by omega)
      have e2 : decide (115792089237316195423570985008687907853269984665640564039457584007913129639936-1-(115792089237316195423570985008687907853269984665640564039457584007913129639936-115792089237316195423570985008687907853269984665640564039457584007908834671663+k)<X)=false := by
        simp only [decide_eq_false_iff_not]; omega
      simp only [e1,e2,Bool.xor_false]
      clear e1 e2
      rcases Nat.mod_two_eq_zero_or_one (X+k) with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one k with h2|h2 <;>
      simp only [h,h2,show (0=1)=False from by decide,decide_false,decide_true,if_false,if_true,
        Bool.false_eq_true,Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.xor_true,Bool.xor_false,Bool.true_xor,Bool.false_xor] <;>
      exact ⟨by (first | exact True.intro | (rw [decide_eq_true_iff]; omega) | (rw [decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega),by (first | exact True.intro | omega),by (first | exact True.intro | (rw [eq_comm, decide_eq_true_iff]; omega) | (rw [eq_comm, decide_eq_false_iff_not]; omega)),by (first | exact True.intro | omega)⟩

/-! ### Circuit -/

def cmpC : Nat := 2^256-p

def srcR (w : Nat → Wire) : List Wire := wireBlock w 0 256
def xR (w : Nat → Wire) : List Wire := wireBlock w 770 256
def cR (w : Nat → Wire) : List Wire := wireBlock w 256 256
def hR (w : Nat → Wire) : List Wire := wireBlock w 0 258
def kR (w : Nat → Wire) : List Wire := wireBlock w 770 258
def tR (w : Nat → Wire) : List Wire := wireBlock w 1029 256
def hpR (w : Nat → Wire) : List Wire := wireBlock w 1 257
def aC (w : Nat → Wire) : List Wire := wireBlock w 1540 257
def hC2 (w : Nat → Wire) : List Wire := wireBlock w 1540 256
def hp8 (w : Nat → Wire) : List Wire := wireBlock w 1 256
def hC3 (w : Nat → Wire) : List Wire := wireBlock w 1540 255

def comparePart (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (srcR w) (cmpC+k)++notRegister (srcR w)++
  compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)++
  notRegister (srcR w)++maskedConstant g (srcR w) (cmpC+k)

def parGates (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  [.CX (w 770) (w 1028)]++(if k%2=1 then [.CX g (w 1028)] else [])++[.CX (w 514) (w 1028)]++
  [.CX (w 1028) (w 770)]++(if k%2=1 then [.CX g (w 770)] else [])++[.CX (w 514) (w 770)]

def prodPart (w : Nat → Wire) (g : Wire) : Program :=
  [.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)]

def c1 (k : Nat) : Nat := tk k false false false
def cg (k : Nat) : Nat := tk k true false false ^^^ tk k false false false
def cf (k : Nat) : Nat := tk k true true false ^^^ tk k true false false
def cp (k : Nat) : Nat := tk k false false true ^^^ tk k false false false
def cgp (k : Nat) : Nat :=
  tk k true false true ^^^ tk k true false false ^^^ tk k false false true ^^^ tk k false false false
def cfp (k : Nat) : Nat :=
  tk k true true true ^^^ tk k true true false ^^^ tk k true false true ^^^ tk k true false false

def loadK (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  xorConstant (hR w) (c1 k)++maskedConstant g (hR w) (cg k)++maskedConstant (w 514) (hR w) (cf k)++
  maskedConstant (w 1028) (hR w) (cp k)++maskedConstant (w 721) (hR w) (cgp k)++
  maskedConstant (w 722) (hR w) (cfp k)

def kAddM (w : Nat → Wire) : Program := mappedAdd (mappedRead (hR w) false) (kR w) (aC w) (w 1797)

def dBits (w : Nat → Wire) : List MappedBit := (List.range 257).map (fun j =>
  let a := (2^257-p).testBit j
  let b := p.testBit j
  if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some (w 1028),flip:=a})

def hAddM (w : Nat → Wire) : Program := mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)

/-- `hAddM` with its first carry trimmed. The first mapped bit is the literal `1`
(`2^257-p` and `p` are both odd) and the carry-in `w 1797` is clean, so the first
majority's Toffoli `CCX (w 1) (w 1797) (w 1540)` never fires; it is dropped. -/
def hPost (w : Nat → Wire) : Program :=
  mappedAdd (dBits w).tail (hpR w).tail (hC2 w).tail (w 1540) ++
    mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540) ++
    mappedSum {wire:=none,flip:=true} (w 1) (w 1797)

def hAddT (w : Nat → Wire) : Program := [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ hPost w


def thrA (k : Nat) : Nat := (k+1)/2
def thrB (k : Nat) : Nat := (k+1)/2 ^^^ (k+p+1)/2

def loadT (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  maskedConstant g (tR w) (thrA k)++maskedConstant (w 721) (tR w) (thrB k)

/-- Compare-first constant addition `x ↦ x + g·k mod p` merged into the direct first tick. -/
def merged (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  comparePart w g k++(parGates w g k++rotateRight (kR w))++prodPart w g++loadK w g k++kAddM w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]

/-! ### Layout facts -/

section Layout
variable (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
include hn

theorem mem_blk (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) :
    w i ∈ wireBlock w a n ↔ a ≤ i ∧ i < a + n := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := skywalkPool_index_inj w hn i j hi (by omega) he.symm
    omega
  · intro h
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem w_ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
  index_ne w hn i j hi hj h

omit hn in
theorem blk_sub (a n b m : Nat) (h1 : b≤a) (h2 : a+n≤b+m) : ∀q∈wireBlock w a n,q∈wireBlock w b m := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

theorem blk_nd (a n : Nat) (ha : a+n≤1798) : (wireBlock w a n).Nodup := block_nodup w hn a n ha

theorem blk_dis (a n b m : Nat) (ha : a+n≤1798) (hb : b+m≤1798) (sep : a+n≤b ∨ b+m≤a) :
    List.Disjoint (wireBlock w a n) (wireBlock w b m) := block_disjoint w hn a n b m ha hb sep

theorem g_out (g : Wire) (hg : g∉skywalkPoolWires w) (a n : Nat) (ha : a+n≤1798) : g∉wireBlock w a n :=
  fun h => hg (blk_sub w a n 0 1798 (by omega) (by omega) g h)

theorem g_ne (g : Wire) (hg : g∉skywalkPoolWires w) (i : Nat) (hi : i<1798) : g≠w i := by
  intro e; apply hg; rw [e]
  exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩

end Layout


/-! ### Frame -/

def mutL (w : Nat → Wire) : List Wire := hR w++kR w++tR w++[w 1028,w 514,w 721,w 722]

def MF (w : Nat → Wire) (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState) : Prop :=
  regValue (hR w) s=H ∧ regValue (kR w) s=X ∧ regValue (tR w) s=T ∧
  s (w 1028)=par ∧ s (w 514)=f ∧ s (w 721)=gp ∧ s (w 722)=fp ∧ ∀q,q∉mutL w → s q=b0 q

theorem keep (R : List Wire) (s t : BasisState) (hf : ∀q,q∉R → t q=s q) (C : List Wire)
    (hC : ∀q∈C,q∉R) : regValue C t=regValue C s :=
  regValue_congr C t s (fun q hq => hf q (hC q hq))

section Steps
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem hR_nd : (hR w).Nodup := blk_nd w hn 0 258 (by omega)
theorem kR_nd : (kR w).Nodup := blk_nd w hn 770 258 (by omega)
theorem tR_nd : (tR w).Nodup := blk_nd w hn 1029 256 (by omega)

theorem hR_kR : ∀q∈kR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 770 258 (by omega) (by omega) (by omega)) h hq
theorem hR_tR : ∀q∈tR w,q∉hR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 0 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem kR_hR : ∀q∈hR w,q∉kR w := fun q hq h => hR_kR w hn q h hq
theorem kR_tR : ∀q∈tR w,q∉kR w := fun q hq h =>
  List.disjoint_left.mp (blk_dis w hn 770 258 1029 256 (by omega) (by omega) (by omega)) h hq
theorem tR_hR : ∀q∈hR w,q∉tR w := fun q hq h => hR_tR w hn q h hq
theorem tR_kR : ∀q∈kR w,q∉tR w := fun q hq h => kR_tR w hn q h hq

theorem nb (i a n : Nat) (hi : i<1798) (ha : a+n≤1798) (sep : i < a ∨ a + n ≤ i) : w i ∉ wireBlock w a n :=
  block_not_mem w hn i a n hi ha sep

theorem out_of_mut (R : List Wire) (hR' : ∀q∈R,q∈mutL w) (q : Wire) (hq : q∉mutL w) : q∉R :=
  fun h => hq (hR' q h)

theorem hR_mut : ∀q∈hR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem kR_mut : ∀q∈kR w,q∈mutL w := fun q hq => by simp [mutL,hq]
theorem tR_mut : ∀q∈tR w,q∈mutL w := fun q hq => by simp [mutL,hq]

/-- An operation that changes only the `H` block. -/
theorem stepH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉hR w → t.basis q=s.basis q) (H' : Nat)
    (hv : regValue (hR w) t.basis=H') : MF w b0 H' X T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨hv,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (hR_kR w hn)]; exact h2
  · rw [keep _ _ _ hf _ (hR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 0 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 0 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 0 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 0 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (hR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the `K` block. -/
theorem stepK (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉kR w → t.basis q=s.basis q) (X' : Nat)
    (hv : regValue (kR w) t.basis=X') : MF w b0 H X' T par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,hv,?_,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (kR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (kR_tR w hn)]; exact h3
  · rw [hf _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 770 258 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 770 258 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 770 258 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (kR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes only the threshold block. -/
theorem stepT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q∉tR w → t.basis q=s.basis q) (T' : Nat)
    (hv : regValue (tR w) t.basis=T') : MF w b0 H X T' par f gp fp t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_⟩
  · rw [keep _ _ _ hf _ (tR_hR w hn)]; exact h1
  · rw [keep _ _ _ hf _ (tR_kR w hn)]; exact h2
  · rw [hf _ (nb w hn 1028 1029 256 (by omega) (by omega) (by omega))]; exact h4
  · rw [hf _ (nb w hn 514 1029 256 (by omega) (by omega) (by omega))]; exact h5
  · rw [hf _ (nb w hn 721 1029 256 (by omega) (by omega) (by omega))]; exact h6
  · rw [hf _ (nb w hn 722 1029 256 (by omega) (by omega) (by omega))]; exact h7
  · intro q hq; rw [hf q (out_of_mut w hn _ (tR_mut w hn) q hq)]; exact h8 q hq

/-- An operation that changes one scalar wire `w j` of the frame. -/
theorem stepBit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s t : State) (j : Nat)
    (hj : j=1028 ∨ j=514 ∨ j=721 ∨ j=722)
    (h : MF w b0 H X T par f gp fp s.basis) (hf : ∀q,q≠w j → t.basis q=s.basis q) :
    MF w b0 H X T (if j=1028 then t.basis (w j) else par) (if j=514 then t.basis (w j) else f)
      (if j=721 then t.basis (w j) else gp) (if j=722 then t.basis (w j) else fp) t.basis := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have hjr : j<1798 := by omega
  have nh : w j∉hR w := nb w hn j 0 258 hjr (by omega) (by omega)
  have nk : w j∉kR w := nb w hn j 770 258 hjr (by omega) (by omega)
  have nt : w j∉tR w := nb w hn j 1029 256 hjr (by omega) (by omega)
  have ne (i : Nat) (hi : i<1798) (hij : i≠j) : w i≠w j := w_ne w hn i j hi hjr hij
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nh (e ▸ hq)))]; exact h1
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nk (e ▸ hq)))]; exact h2
  · rw [regValue_congr _ _ s.basis (fun q hq => hf q (fun e => nt (e ▸ hq)))]; exact h3
  · by_cases e : j=1028
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 1028 (by omega) (Ne.symm e))]; exact h4
  · by_cases e : j=514
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 514 (by omega) (Ne.symm e))]; exact h5
  · by_cases e : j=721
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 721 (by omega) (Ne.symm e))]; exact h6
  · by_cases e : j=722
    · simp [e]
    · simp only [e,if_false]; rw [hf _ (ne 722 (by omega) (Ne.symm e))]; exact h7
  · intro q hq
    have : q≠w j := by
      intro e; apply hq; rw [e]
      rcases hj with rfl|rfl|rfl|rfl <;> simp [mutL]
    rw [hf q this]; exact h8 q hq

end Steps


/-! ### Concrete steps -/

theorem run_cx (a b : Wire) (m : List Bool) (s : State) :
    run [.CX a b] m s=⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis a)⟩ := rfl
theorem run_ccx (a b c : Wire) (m : List Bool) (s : State) :
    run [.CCX a b c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl
theorem run_x (a : Wire) (m : List Bool) (s : State) :
    run [.X a] m s=⟨s.phase,writeBit s.basis a (!s.basis a)⟩ := rfl

theorem run_meas_and (t a b : Wire) (m : List Bool) (s : State) (ha : a≠t) (hb : b≠t)
    (ht : s.basis t=(s.basis a && s.basis b)) :
    run [.measureX t [] [.CZ a b]] m s=⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases m.headD false <;> simp [correct,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,ht]

section Concrete
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem kR_split (s : BasisState) :
    regValue (kR w) s=(s (w 770)).toNat+2*regValue (wireBlock w 771 257) s := by
  have e : kR w=w 770::wireBlock w 771 257 := by
    simp [kR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 770) <;> simp [regValue,h]

theorem hR_split (s : BasisState) :
    regValue (hR w) s=(s (w 0)).toNat+2*regValue (hpR w) s := by
  have e : hR w=w 0::hpR w := by
    simp [hR,hpR,wireBlock,List.range'_succ]
  rw [e]; cases h : s (w 0) <;> simp [regValue,h]

theorem hR_src (s : BasisState) :
    regValue (hR w) s=regValue (srcR w) s+2^256*regValue (wireBlock w 256 2) s := by
  have e : hR w=srcR w++wireBlock w 256 2 := by
    rw [hR,srcR,wireBlock_append]
  rw [e,regValue_append,srcR,wireBlock_length]

theorem kR_x (s : BasisState) :
    regValue (kR w) s=regValue (xR w) s+2^256*regValue (wireBlock w 1026 2) s := by
  have e : kR w=xR w++wireBlock w 1026 2 := by
    rw [kR,xR,wireBlock_append]
  rw [e,regValue_append,xR,wireBlock_length]

theorem kR_low (s : BasisState) :
    regValue (kR w) s=regValue (wireBlock w 770 257) s+2^257*regValue (wireBlock w 1027 1) s := by
  have e : kR w=wireBlock w 770 257++wireBlock w 1027 1 := by
    rw [kR,wireBlock_append]
  rw [e,regValue_append,wireBlock_length]

/-- A CX targeting the parity wire. -/
theorem stepParCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 1028) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) :
    Triple (MF w b0 H X T par f gp fp) [.CX c (w 1028)] (MF w b0 H X T (par ^^ cv) f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 1028)
    (s.basis (w 1028) ^^ s.basis c)⟩ 1028 (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit,h.2.2.2.1,hcv s.basis h] using this

/-- A CX targeting bit 0 of the K block. -/
theorem stepLowCX (b0 : BasisState) (H Y T : Nat) (b par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c≠w 770) (hcv : ∀s : BasisState,MF w b0 H (2*Y+b.toNat) T par f gp fp s → s c=cv) :
    Triple (MF w b0 H (2*Y+b.toNat) T par f gp fp) [.CX c (w 770)]
      (MF w b0 H (2*Y+(b ^^ cv).toNat) T par f gp fp) := by
  intro s m h
  rw [run_cx]
  refine ⟨rfl,?_⟩
  have m770 : w 770∈kR w := (mem_blk w hn 770 770 258 (by omega) (by omega)).mpr (by omega)
  have rest : ∀q∈wireBlock w 771 257,q≠w 770 := fun q hq e =>
    nb w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
  apply stepK w hn b0 H _ T par f gp fp s _ h
  · intro q hq; have : q≠w 770 := fun e => hq (e ▸ m770)
    simp [writeBit,Function.update_of_ne this]
  · have sp := kR_split w hn s.basis
    have sp2 := kR_split w hn (writeBit s.basis (w 770) (s.basis (w 770) ^^ s.basis c))
    rw [h.2.1] at sp
    rw [sp2,regValue_congr _ _ s.basis (fun q hq => by simp [writeBit,Function.update_of_ne (rest q hq)])]
    rw [hcv s.basis h]
    simp only [writeBit,Function.update_self]
    cases hb : s.basis (w 770) <;> cases b <;> cases cv <;> simp [hb] at sp ⊢ <;> omega

end Concrete


section Concrete2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepXorH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (xorConstant (hR w) v) (MF w b0 (H^^^v) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := xorConstant_correct (hR w) (hR_nd w hn) v (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1])⟩

theorem stepMaskH (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉hR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^258) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (hR w) v)
      (MF w b0 (H^^^(if cv then v else 0)) X T par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (hR w) v (hR_nd w hn) hc
    (by simpa [hR,wireBlock_length] using hv) s m
  exact ⟨hp,stepH w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.1,hcv s.basis h])⟩

theorem stepMaskT (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (c : Wire) (cv : Bool)
    (hc : c∉tR w) (hcv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s c=cv) (v : Nat) (hv : v<2^256) :
    Triple (MF w b0 H X T par f gp fp) (maskedConstant c (tR w) v)
      (MF w b0 H X (T^^^(if cv then v else 0)) par f gp fp) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (tR w) v (tR_nd w hn) hc
    (by simpa [tR,wireBlock_length] using hv) s m
  exact ⟨hp,stepT w hn b0 H X T par f gp fp s _ h he _ (by rw [hval,h.2.2.1,hcv s.basis h])⟩

theorem stepCCX (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (a b : Wire) (j : Nat)
    (hj : j=721 ∨ j=722) (av bv : Bool) (ha : a≠w j) (hb : b≠w j)
    (hav : ∀s : BasisState,MF w b0 H X T par f gp fp s → s a=av)
    (hbv : ∀s : BasisState,MF w b0 H X T par f gp fp s → s b=bv) :
    Triple (MF w b0 H X T par f gp fp) [.CCX a b (w j)]
      (MF w b0 H X T par f (if j=721 then gp ^^ (av && bv) else gp)
        (if j=722 then fp ^^ (av && bv) else fp)) := by
  intro s m h
  rw [run_ccx]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w j)
    (s.basis (w j) ^^ (s.basis a && s.basis b))⟩ j (by omega) h
    (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  rcases hj with rfl|rfl
  · simpa [writeBit,h.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this
  · simpa [writeBit,h.2.2.2.2.2.2.1,hav s.basis h,hbv s.basis h] using this

theorem stepKAdd (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 H X T par f gp fp) (kAddM w) (MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m h
  have caway : ∀q∈aC w,q∉mutL w := by
    intro q hq hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
    · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
    · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
    all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm
  have m1797 : w 1797∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have nd : (w 1797::(kR w++aC w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),
      blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
  have src : ∀q∈mappedWires (mappedRead (hR w) false),q∉w 1797::(kR w++aC w) := by
    rw [mappedRead_wires]
    intro q hq hm
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|e|e
    · exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq)
    · exact hR_kR w hn q e hq
    · exact List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq e
  have cl : ∀q∈aC w,s.basis q=false := fun q hq => (h.2.2.2.2.2.2.2 q (caway q hq)).trans (hc q hq)
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (mappedRead (hR w) false) (kR w) (aC w) (w 1797) nd src
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length]) s m cl
  refine ⟨hp,stepK w hn b0 H X T par f gp fp s _ h he _ ?_⟩
  rw [hval,mappedRead_value,h.1,h.2.1,(h.2.2.2.2.2.2.2 _ m1797).trans hcin]
  simp [kR,wireBlock_length]

end Concrete2


def CF (w : Nat → Wire) (b0 : BasisState) (S : Nat) (F : Bool) (s : BasisState) : Prop :=
  regValue (srcR w) s=S ∧ s (w 514)=F ∧ ∀q,q∉srcR w → q≠w 514 → s q=b0 q

section Compare
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem src_nd : (srcR w).Nodup := blk_nd w hn 0 256 (by omega)
theorem w514_src : w 514∉srcR w := nb w hn 514 0 256 (by omega) (by omega) (by omega)

theorem cfMask (b0 : BasisState) (S : Nat) (F : Bool) (c : Wire) (hc : c∉srcR w) (hc' : c≠w 514)
    (v : Nat) (hv : v<2^256) :
    Triple (CF w b0 S F) (maskedConstant c (srcR w) v) (CF w b0 (S^^^(if b0 c then v else 0)) F) := by
  intro s m h
  obtain ⟨hp,he,hval⟩ := maskedConstant_correct c (srcR w) v (src_nd w hn) hc
    (by simpa [srcR,wireBlock_length] using hv) s m
  refine ⟨hp,?_,?_,?_⟩
  · rw [hval,h.1,h.2.2 c hc hc']
  · rw [he _ (w514_src w hn)]; exact h.2.1
  · intro q h1 h2; rw [he q h1]; exact h.2.2 q h1 h2

theorem cfNot (b0 : BasisState) (S : Nat) (F : Bool) :
    Triple (CF w b0 S F) (notRegister (srcR w)) (CF w b0 (2^256-1-S) F) := by
  intro s m h
  rw [notRegister_correct (srcR w) (src_nd w hn)]
  refine ⟨rfl,?_,?_,?_⟩
  · change regValue (srcR w) (fun q => if q∈srcR w then !s.basis q else s.basis q)=_
    rw [regValue_congr (srcR w) _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
    simp [srcR,wireBlock_length]
  · change (if w 514∈srcR w then !s.basis (w 514) else s.basis (w 514))=_
    simp [w514_src w hn,h.2.1]
  · intro q h1 h2
    change (if q∈srcR w then !s.basis q else s.basis q)=_
    simp [h1,h.2.2 q h1 h2]

theorem cfCmp (b0 : BasisState) (S : Nat) (F : Bool) (X : Nat) (hx : regValue (xR w) b0=X)
    (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false) :
    Triple (CF w b0 S F) (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))
      (CF w b0 S (F ^^ decide (S<X))) := by
  intro s m h
  have xs : ∀q∈xR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)) h' hq
  have x514 : ∀q∈xR w,q≠w 514 := fun q hq e => nb w hn 514 770 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have cs : ∀q∈cR w,q∉srcR w := fun q hq h' =>
    List.disjoint_left.mp (blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)) h' hq
  have c514 : ∀q∈cR w,q≠w 514 := fun q hq e => nb w hn 514 256 256 (by omega) (by omega) (by omega) (e ▸ hq)
  have n513 : w 513∉srcR w := nb w hn 513 0 256 (by omega) (by omega) (by omega)
  have e513 : w 513≠w 514 := w_ne w hn 513 514 (by omega) (by omega) (by omega)
  have nd : (w 514::w 513::(srcR w++xR w++cR w)).Nodup := by
    have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
    have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
    have l2 : (srcR w++xR w++cR w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨e513.symm,⟨w514_src w hn,nb w hn 514 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨n513,nb w hn 513 770 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hv⟩ := compareLt_correct none (srcR w) (xR w) (cR w) (w 513) (w 514) nd (by simp)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length]) s m
    ((h.2.2 _ n513 e513).trans hcin) (fun q hq => (h.2.2 q (cs q hq) (c514 q hq)).trans (hc q hq))
  refine ⟨hp,?_,?_,?_⟩
  · rw [regValue_congr _ _ s.basis (fun q hq => he q (fun e => w514_src w hn (e ▸ hq)))]; exact h.1
  · rw [hv,h.2.1,h.1,regValue_congr _ _ b0 (fun q hq => h.2.2 q (xs q hq) (x514 q hq)),hx]
    simp [controlValue]
  · intro q h1 h2; rw [he q h2]; exact h.2.2 q h1 h2

theorem cfCompare (b0 : BasisState) (F : Bool) (k X : Nat) (hk : cmpC+k<2^256)
    (hx : regValue (xR w) b0=X) (hc : ∀q∈cR w,b0 q=false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) :
    Triple (CF w b0 0 F) (comparePart w g k)
      (CF w b0 0 (F ^^ decide (2^256-1-(if b0 g then cmpC+k else 0)<X))) := by
  have t := ((((cfMask w hn b0 0 F g gs g514 (cmpC+k) hk).seq
    (cfNot w hn b0 _ F)).seq (cfCmp w hn b0 _ F X hx hc hcin)).seq
    (cfNot w hn b0 _ _)).seq (cfMask w hn b0 _ _ g gs g514 (cmpC+k) hk)
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have lt : (if b0 g then cmpC+k else 0)<2^256 := by split <;> omega
  refine ⟨?_,?_,h.2.2⟩
  · rw [h.1]
    have e : 2^256-1-(2^256-1-(0^^^(if b0 g then cmpC+k else 0)))=(if b0 g then cmpC+k else 0) := by
      simp only [Nat.zero_xor]; omega
    rw [e,Nat.xor_self]
  · rw [h.2.1]; simp only [Nat.zero_xor]

end Compare


def dScalar (par : Bool) : Nat :=
  (List.range 257).foldr (fun j acc => (if par then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0

theorem dScalar_value (par : Bool) : dScalar par=delta par := by
  cases par <;> decide

private theorem selected_bit_value (flag : Wire) (a b : Bool) (s : BasisState) :
    (if a=b then ({wire:=none,flip:=a} : MappedBit)
      else {wire:=some flag,flip:=a}).value s=if s flag then b else a := by
  cases a <;> cases b <;> cases hf : s flag <;> simp [MappedBit.value,hf]

private theorem d_list_value (is : List Nat) (flag : Wire) (s : BasisState) :
    mappedValue (is.map (fun j =>
      let a := (2^257-p).testBit j
      let b := p.testBit j
      if a=b then ({wire:=none,flip:=a} : MappedBit) else {wire:=some flag,flip:=a})) s=
      is.foldr (fun j acc => (if s flag then p.testBit j else (2^257-p).testBit j).toNat+2*acc) 0 := by
  induction is with
  | nil => rfl
  | cons j is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons]
    rw [ih,selected_bit_value]

theorem dBits_value (w : Nat → Wire) (s : BasisState) : mappedValue (dBits w) s=delta (s (w 1028)) := by
  rw [dBits,d_list_value]
  exact dScalar_value (s (w 1028))

theorem dBits_length (w : Nat → Wire) : (dBits w).length=257 := by simp [dBits]

theorem dBits_cons (w : Nat → Wire) :
    ∃ b' bs, dBits w = {wire:=none,flip:=true} :: b' :: bs := by
  have e : List.range 257 = 0 :: 1 :: List.range' 2 255 := by
    rw [List.range_eq_range']; rfl
  have t1 : (2^257-p).testBit 0 = true := by rw [p_val]; decide
  have t2 : p.testBit 0 = true := by rw [p_val]; decide
  rw [dBits, e, List.map_cons, List.map_cons]
  simp only [t1, t2, ite_true]
  exact ⟨_, _, rfl⟩

theorem hpR_cons (w : Nat → Wire) : ∃ y' ys, hpR w = w 1 :: y' :: ys :=
  ⟨w 2, (List.range' 3 255).map w, by
    rw [hpR, wireBlock, show (257:Nat) = 255+1+1 from rfl, List.range'_succ, List.range'_succ]; rfl⟩

theorem hC2_cons (w : Nat → Wire) : ∃ cs, hC2 w = w 1540 :: cs :=
  ⟨(List.range' 1541 255).map w, by
    rw [hC2, wireBlock, show (256:Nat) = 255+1 from rfl, List.range'_succ]; rfl⟩

theorem hAddM_split (w : Nat → Wire) :
    hAddM w = [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++ [.CCX (w 1) (w 1797) (w 1540)] ++ hPost w := by
  obtain ⟨b', bs, hD⟩ := dBits_cons w
  obtain ⟨y', ys, hY⟩ := hpR_cons w
  obtain ⟨cs, hC⟩ := hC2_cons w
  simp only [hAddM, hPost, hD, hY, hC, List.tail_cons, mappedAdd, mappedMajority, List.append_assoc,
    List.cons_append, List.nil_append, if_true]

/-- Dropping a Toffoli whose second control is false after a measurement-free prefix. -/
theorem run_drop_ccx (P Q : Program) (a b t : Wire) (m : List Bool) (s : State)
    (hP : measurementCount P = 0) (hb : (run P [] s).basis b = false) :
    run (P ++ [.CCX a b t] ++ Q) m s = run (P ++ Q) m s := by
  rw [List.append_assoc, run_append, run_append P Q, hP]
  simp only [List.take_zero, List.drop_zero, List.cons_append, List.nil_append, run, hb,
    Bool.and_false, Bool.xor_false, writeBit, Function.update_eq_self]

theorem hAddT_run (w : Nat → Wire) (h17 : w 1797 ≠ w 1540) (m : List Bool) (s : State)
    (hc : s.basis (w 1797) = false) : run (hAddT w) m s = run (hAddM w) m s := by
  rw [hAddM_split, hAddT, run_drop_ccx]
  · rfl
  · simp only [run, writeBit, Function.update_of_ne h17, hc]

theorem hAddT_counts (w : Nat → Wire) :
    toffoliCount (hAddT w) + 1 = toffoliCount (hAddM w) ∧
      measurementCount (hAddT w) = measurementCount (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [toffoliCount_append, measurementCount_append]
  constructor
  · simp [toffoliCount]; omega
  · simp [measurementCount]

theorem hAddT_wires (w : Nat → Wire) : wires (hAddT w) ⊆ wires (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.subset_union_left) (Finset.Subset.refl _)

theorem hAddT_physical (w : Nat → Wire) (h : GatePhysical (hAddM w)) : GatePhysical (hAddT w) := by
  rw [hAddM_split] at h
  rw [hAddT]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨h.1.1, h.2⟩

theorem hAddT_slots (w : Nat → Wire) :
    Challenge.gateSlots (hAddT w) + 1 = Challenge.gateSlots (hAddM w) := by
  rw [hAddM_split, hAddT]
  simp only [Challenge.gateSlots_append]
  simp [Challenge.gateSlots, Challenge.instructionSlots]
  omega


theorem dBits_wire (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (dBits w)) : q=w 1028 := by
  simp only [dBits,mappedWires,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨j,_,rfl⟩,hb⟩ := hq
  split at hb <;> simp_all

section Rest
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepCompareMF (b0 : BasisState) (k X : Nat) (hk : cmpC+k<2^256) (hX : X<2^256)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (gs : g∉srcR w) (g514 : g≠w 514) (gm : g∉mutL w) :
    Triple (MF w b0 0 X 0 false false false false) (comparePart w g k)
      (MF w b0 0 X 0 false (decide (2^256-1-(if b0 g then cmpC+k else 0)<X)) false false) := by
  intro s m h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
  have sp := hR_src w hn s.basis
  have kx := kR_x w hn s.basis
  have xl := regValue_lt (xR w) s.basis
  have sl := regValue_lt (srcR w) s.basis
  simp only [xR,srcR,wireBlock_length] at xl sl
  rw [h1] at sp; rw [h2] at kx
  have hx : regValue (xR w) s.basis=X := by
    have : regValue (wireBlock w 1026 2) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 1026 2) s.basis := Nat.le_mul_of_pos_right _ this
      omega
    omega
  have src0 : regValue (srcR w) s.basis=0 := by omega
  have top0 : regValue (wireBlock w 256 2) s.basis=0 := by
    by_contra hne; have : 1≤regValue (wireBlock w 256 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have : 2^256≤2^256*regValue (wireBlock w 256 2) s.basis := Nat.le_mul_of_pos_right _ this
    omega
  have hzero := (regValue_zero _ _).mp h1
  have cc : ∀q∈cR w,s.basis q=false := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    by_cases hi2 : i<258
    · exact hzero _ ((mem_blk w hn i 0 258 (by omega) (by omega)).mpr (by omega))
    · rw [h8 _ ?_]; exact hc i (by omega) (by omega)
      simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨⟨⟨nb w hn i 0 258 (by omega) (by omega) (by omega),nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
        nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
        exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have m513 : w 513∉mutL w := by
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨nb w hn 513 0 258 (by omega) (by omega) (by omega),nb w hn 513 770 258 (by omega) (by omega) (by omega)⟩,
      nb w hn 513 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
      exact w_ne w hn _ _ (by omega) (by omega) (by omega)
  have cfr := cfCompare w g hn s.basis false k X hk hx cc ((h8 _ m513).trans hcin) gs g514 s m
    ⟨src0,h5,fun _ _ _ => rfl⟩
  obtain ⟨tp,c1',c2',c3'⟩ := cfr
  refine ⟨tp,?_⟩
  simp only [Bool.false_xor] at c2'
  have gv : s.basis g=b0 g := h8 g gm
  rw [gv] at c2'
  have same : ∀q,q∉srcR w → q≠w 514 → (run (comparePart w g k) m s).basis q=s.basis q := c3'
  have srcm : ∀q∈srcR w,q∈mutL w := fun q hq => hR_mut w hn q (blk_sub w 0 256 0 258 (by omega) (by omega) q hq)
  have m514 : w 514∈mutL w := by simp [mutL]
  refine ⟨?_,?_,?_,?_,c2',?_,?_,?_⟩
  · rw [hR_src w hn,c1',regValue_congr _ _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 256 2 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 256 2 (by omega) (by omega) (by omega) (e ▸ hq))),top0]; simp
  · rw [regValue_congr (kR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 770 258 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 770 258 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h2
  · rw [regValue_congr (tR w) _ s.basis (fun q hq => same q (fun h' =>
      List.disjoint_left.mp (blk_dis w hn 0 256 1029 256 (by omega) (by omega) (by omega)) h' hq)
      (fun e => nb w hn 514 1029 256 (by omega) (by omega) (by omega) (e ▸ hq)))]; exact h3
  · rw [same _ (nb w hn 1028 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h4
  · rw [same _ (nb w hn 721 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h6
  · rw [same _ (nb w hn 722 0 256 (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))]; exact h7
  · intro q hq
    rw [same q (fun h' => hq (srcm q h')) (fun e => hq (e ▸ m514))]; exact h8 q hq

theorem stepMeasFp (b0 : BasisState) (H X T : Nat) (par f gp : Bool) :
    Triple (MF w b0 H X T par f gp (f && par)) [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]
      (MF w b0 H X T par f gp false) := by
  intro s m h
  rw [run_meas_and (w 722) (w 514) (w 1028) m s (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.1])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp (f && par) s ⟨s.phase,writeBit s.basis (w 722) false⟩ 722
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepMeasGp (b0 : BasisState) (H X T : Nat) (par f fp : Bool) (gm : g∉mutL w)
    (g515 : g≠w 721) :
    Triple (MF w b0 H X T par f (b0 g && par) fp) [.measureX (w 721) [] [.CZ g (w 1028)]]
      (MF w b0 H X T par f false fp) := by
  intro s m h
  rw [run_meas_and (w 721) g (w 1028) m s g515
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (by rw [h.2.2.2.2.2.1,h.2.2.2.1,h.2.2.2.2.2.2.2 g gm])]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f (b0 g && par) fp s ⟨s.phase,writeBit s.basis (w 721) false⟩ 721
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

theorem stepCopy (b0 : BasisState) (X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 X T par f gp fp) (copyRegister none (wireBlock w 770 257) (hpR w))
      (MF w b0 (2*(X%2^257)) X T par f gp fp) := by
  intro s m h
  have nd : (wireBlock w 770 257++hpR w).Nodup := List.nodup_append'.mpr
    ⟨blk_nd w hn 770 257 (by omega),blk_nd w hn 1 257 (by omega),
      blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩
  obtain ⟨hp,he,hval⟩ := copyRegister_correct none (wireBlock w 770 257) (hpR w)
    (by simp [hpR,wireBlock_length]) nd (by simp) s m
  refine ⟨hp,stepH w hn b0 0 X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (copyRegister none (wireBlock w 770 257) (hpR w)) m s).basis
    have kl := kR_low w hn s.basis
    have ll := regValue_lt (wireBlock w 770 257) s.basis
    simp only [wireBlock_length] at ll
    rw [h.1] at sp; rw [h.2.1] at kl
    rw [sp2,hval,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega))]
    simp only [copyValue]
    have e0 : regValue (hpR w) s.basis=0 := by omega
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    rw [e0,b0',Nat.zero_xor]
    have : regValue (wireBlock w 770 257) s.basis=X%2^257 := by omega
    rw [this]; simp

end Rest


section Rest2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem aC_out : ∀q∈aC w,q∉mutL w := by
  intro q hq hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with ((hm|hm)|hm)|hm|hm|hm|hm
  · exact nb w hn i 0 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 770 258 (by omega) (by omega) (by omega) hm
  · exact nb w hn i 1029 256 (by omega) (by omega) (by omega) hm
  all_goals exact w_ne w hn _ _ (by omega) (by omega) (by omega) hm

theorem w1797_out : w 1797∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨nb w hn 1797 0 258 (by omega) (by omega) (by omega),nb w hn 1797 770 258 (by omega) (by omega) (by omega)⟩,
    nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩ <;>
    exact w_ne w hn _ _ (by omega) (by omega) (by omega)

theorem stepHAdd (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddM w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  rw [hAddM]
  have nd : (w 1797::(hpR w++hC2 w)).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),
      blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)⟩⟩
    simp only [List.mem_append,not_or]
    exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
  have srcw : ∀q∈mappedWires (dBits w),q∉w 1797::(hpR w++hC2 w) := by
    intro q hq
    rw [dBits_wire w q hq]
    simp only [List.mem_cons,List.mem_append,not_or]
    exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
      nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC2 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 256 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  obtain ⟨hp,he,hval⟩ := mappedAdd_correct (dBits w) (hpR w) (hC2 w) (w 1797) nd srcw
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length]) s m cl
  refine ⟨hp,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq; exact he q (fun h' => hq (blk_sub w 1 257 0 258 (by omega) (by omega) q h'))
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (run (mappedAdd (dBits w) (hpR w) (hC2 w) (w 1797)) m s).basis
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have e0 : regValue (hpR w) s.basis=Y := by rw [b0'] at sp; simp at sp; omega
    rw [sp2,he _ (nb w hn 0 1 257 (by omega) (by omega) (by omega)),b0',hval,dBits_value,e0,
      h.2.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin]
    simp [hpR,wireBlock_length]

theorem stepHAddT (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) (hY : Y<2^257)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) :
    Triple (MF w b0 (2*Y) X T par f gp fp) (hAddT w)
      (MF w b0 (2*((delta par+Y)%2^257)) X T par f gp fp) := by
  intro s m h
  have c17 : s.basis (w 1797)=false := (h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin
  rw [hAddT_run w (w_ne w hn 1797 1540 (by omega) (by omega) (by omega)) m s c17]
  exact stepHAdd w hn b0 Y X T par f gp fp hY hc hcin s m h

theorem stepW0 (b0 : BasisState) (Y X T : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 (2*Y) X T par f gp fp) [.CX (w 1028) (w 0),.X (w 0)]
      (MF w b0 (2*Y+(!par).toNat) X T par f gp fp) := by
  intro s m h
  have e : run [.CX (w 1028) (w 0),.X (w 0)] m s=⟨s.phase,writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028)))⟩ := by
    simp [run,writeBit]
  rw [e]
  refine ⟨rfl,stepH w hn b0 (2*Y) X T par f gp fp s _ h ?_ _ ?_⟩
  · intro q hq
    have : q≠w 0 := fun e' => hq (e' ▸ (mem_blk w hn 0 0 258 (by omega) (by omega)).mpr (by omega))
    simp [writeBit,Function.update_of_ne this]
  · have sp := hR_split w hn s.basis
    have sp2 := hR_split w hn (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))
    rw [h.1] at sp
    have b0' : s.basis (w 0)=false := by
      cases hb : s.basis (w 0)
      · rfl
      · simp [hb] at sp; omega
    have rest : regValue (hpR w) (writeBit s.basis (w 0) (!(s.basis (w 0) ^^ s.basis (w 1028))))=
        regValue (hpR w) s.basis := regValue_congr _ _ _ (fun q hq => by
      have : q≠w 0 := fun e' => nb w hn 0 1 257 (by omega) (by omega) (by omega) (e' ▸ hq)
      simp [writeBit,Function.update_of_ne this])
    rw [sp2,rest,b0',h.2.2.2.1]
    rw [b0'] at sp
    simp [writeBit] at sp ⊢
    omega

theorem stepErase (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈aC w,b0 q=false) (hcin : b0 (w 1797)=false) (hH : H<2^257) (hf : f=decide (H/2<T)) :
    Triple (MF w b0 H X T par f gp fp) (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))
      (MF w b0 H X T par false gp fp) := by
  intro s m h
  have nd : (w 514::w 1797::(hp8 w++tR w++hC3 w)).Nodup := by
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,l2⟩⟩
    · simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨w_ne w hn _ _ (by omega) (by omega) (by omega),⟨nb w hn 514 1 256 (by omega) (by omega) (by omega),
        nb w hn 514 1029 256 (by omega) (by omega) (by omega)⟩,nb w hn 514 1540 255 (by omega) (by omega) (by omega)⟩
    · simp only [List.mem_append,not_or]
      exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
        nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cl : ∀q∈hC3 w,s.basis q=false := fun q hq =>
    have hq' : q∈aC w := blk_sub w 1540 255 1540 257 (by omega) (by omega) q hq
    (h.2.2.2.2.2.2.2 q (aC_out w hn q hq')).trans (hc q hq')
  have sp := hR_split w hn s.basis
  rw [h.1] at sp
  have e8 : hpR w=hp8 w++wireBlock w 257 1 := by rw [hpR,hp8,wireBlock_append]
  have sp8 := regValue_append (hp8 w) (wireBlock w 257 1) s.basis
  rw [←e8] at sp8
  have l8 := regValue_lt (hp8 w) s.basis
  simp only [hp8,wireBlock_length] at sp8 l8
  have hpv : regValue (hp8 w) s.basis=H/2 := by
    have : regValue (wireBlock w 257 1) s.basis=0 := by
      by_contra hne; have : 1≤regValue (wireBlock w 257 1) s.basis := Nat.one_le_iff_ne_zero.mpr hne
      have : 2^256≤2^256*regValue (wireBlock w 257 1) s.basis := Nat.le_mul_of_pos_right _ this
      cases hb : s.basis (w 0) <;> simp [hb] at sp <;> omega
    cases hb : s.basis (w 0) <;> simp [hb] at sp <;> simp only [hp8] at * <;> omega
  have r := eraseLtChain_correct (hp8 w) (tR w) (hC3 w) (w 1797) (w 514) nd
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length]) s m cl
    (by rw [h.2.2.2.2.1,hpv,h.2.2.1,(h.2.2.2.2.2.2.2 _ (w1797_out w hn)).trans hcin,hf]; simp)
  rw [r]
  refine ⟨rfl,?_⟩
  have := stepBit w hn b0 H X T par f gp fp s ⟨s.phase,writeBit s.basis (w 514) false⟩ 514
    (by omega) h (fun q hq => by simp [writeBit,Function.update_of_ne hq])
  simpa [writeBit] using this

end Rest2


section Compose
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem g_mut (hg : g∉skywalkPoolWires w) : g∉mutL w := by
  simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
  refine ⟨⟨⟨g_out w hn g hg 0 258 (by omega),g_out w hn g hg 770 258 (by omega)⟩,g_out w hn g hg 1029 256 (by omega)⟩,
    g_ne w hn g hg 1028 (by omega),g_ne w hn g hg 514 (by omega),g_ne w hn g hg 721 (by omega),g_ne w hn g hg 722 (by omega)⟩

theorem low_bit (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool) (s : BasisState)
    (h : MF w b0 H X T par f gp fp s) : s (w 770)=decide (X%2=1) := by
  have sp := kR_split w hn s
  rw [h.2.1] at sp
  cases hb : s (w 770) <;> simp [hb] at sp ⊢ <;> omega

omit hn in
theorem xor_clear (a b c : Bool) : (((a ^^ (((false ^^ a) ^^ b) ^^ c)) ^^ b) ^^ c)=false := by
  cases a <;> cases b <;> cases c <;> rfl
omit hn in
theorem xor_clear2 (a c : Bool) : ((a ^^ ((false ^^ a) ^^ c)) ^^ c)=false := by
  cases a <;> cases c <;> rfl

theorem stepPar (b0 : BasisState) (k X : Nat) (f : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 0 X 0 false f false false) (parGates w g k)
      (MF w b0 0 (2*(X/2)) 0 (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f) f false false) := by
  have gm := g_mut w g hn hg
  have g1028 : g≠w 1028 := g_ne w hn g hg 1028 (by omega)
  have g770 : g≠w 770 := g_ne w hn g hg 770 (by omega)
  have e1 : w 770≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e2 : w 514≠w 1028 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e3 : w 1028≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have e4 : w 514≠w 770 := w_ne w hn _ _ (by omega) (by omega) (by omega)
  have gv (H X T : Nat) (par f gp fp : Bool) : ∀s : BasisState,MF w b0 H X T par f gp fp s → s g=b0 g :=
    fun s h => h.2.2.2.2.2.2.2 g gm
  have xs : X=2*(X/2)+(decide (X%2=1)).toNat := by
    rcases Nat.mod_two_eq_zero_or_one X with hx|hx <;> simp [hx] <;> omega
  apply Triple.conseq (fun s h => by rw [xs] at h; exact h) ?_ (fun s h => h)
  by_cases hk : k%2=1
  · rw [parGates,if_pos hk,if_pos hk]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false g (b0 g) g1028 (gv _ _ _ _ _ _ _)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 _ _ f false false g (b0 g) g770 (gv _ _ _ _ _ _ _)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear] at h
    simpa [hk] using h
  · rw [parGates,if_neg hk,if_neg hk]
    try simp only [List.nil_append]
    have t := (stepParCX w hn b0 0 _ 0 false f false false (w 770) (decide (X%2=1)) e1
      (fun s h => by have := low_bit w hn b0 _ _ _ _ _ _ _ s h; rw [this]; simp; omega)).seq
      ((stepParCX w hn b0 0 _ 0 _ f false false (w 514) f e2 (fun s h => h.2.2.2.2.1)).seq
      ((stepLowCX w hn b0 0 (X/2) 0 (decide (X%2=1)) _ f false false (w 1028) _ e3 (fun s h => h.2.2.2.1)).seq
      (stepLowCX w hn b0 0 (X/2) 0 _ _ f false false (w 514) f e4 (fun s h => h.2.2.2.2.1))))
    apply Triple.conseq (fun _ h => h) t
    intro s h
    rw [xor_clear2] at h
    simpa [hk] using h

theorem stepRot (b0 : BasisState) (X : Nat) (par f gp fp : Bool) :
    Triple (MF w b0 0 (2*(X/2)) 0 par f gp fp) (rotateRight (kR w)) (MF w b0 0 (X/2) 0 par f gp fp) := by
  intro s m h
  have r := rotateRight_spec (kR w) (kR_nd w hn) (2*(X/2)) (by omega) s m h.2.1
  have fr := rotate_frame (kR w) s m
  refine ⟨r.1,stepK w hn b0 0 _ 0 par f gp fp s _ h fr.2.1 _ ?_⟩
  have := r.2
  change regValue (kR w) _=_ at this
  rw [this]; omega

end Compose


theorem kC_lt (par : Bool) : kConstant false par<2^258 := by
  cases par <;> norm_num [kConstant,ECDSAAdd.p]

theorem tk_lt (k : Nat) (G f par : Bool) : tk k G f par<2^258 := by
  unfold tk
  split_ifs
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num
  · exact Nat.mod_lt _ (by norm_num)
  · exact kC_lt par

theorem xlt (a b : Nat) (ha : a<2^258) (hb : b<2^258) : a^^^b<2^258 := Nat.xor_lt_two_pow ha hb

theorem c1_lt (k : Nat) : c1 k<2^258 := tk_lt k _ _ _
theorem cg_lt (k : Nat) : cg k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cf_lt (k : Nat) : cf k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cp_lt (k : Nat) : cp k<2^258 := xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)
theorem cgp_lt (k : Nat) : cgp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)
theorem cfp_lt (k : Nat) : cfp k<2^258 :=
  xlt _ _ (xlt _ _ (xlt _ _ (tk_lt k _ _ _) (tk_lt k _ _ _)) (tk_lt k _ _ _)) (tk_lt k _ _ _)

def lkv (k : Nat) (G f par gp fp : Bool) : Nat :=
  c1 k ^^^ (if G then cg k else 0) ^^^ (if f then cf k else 0) ^^^ (if par then cp k else 0) ^^^
    (if gp then cgp k else 0) ^^^ (if fp then cfp k else 0)

theorem lkv_eq (k : Nat) (G f par : Bool) (hfg : f=true → G=true) :
    lkv k G f par (G && par) (f && par)=tk k G f par := by
  cases G <;> cases f <;> cases par <;> simp at hfg <;>
    simp [lkv,c1,cg,cf,cp,cgp,cfp,Nat.xor_assoc,Nat.xor_comm,Nat.xor_left_comm,Nat.xor_self]

def ltv (k : Nat) (G gp : Bool) : Nat := (if G then thrA k else 0) ^^^ (if gp then thrB k else 0)

theorem ltv_eq (k : Nat) (G par : Bool) : ltv k G (G && par)=thr k G par := by
  cases G <;> cases par <;> simp [ltv,thr,thrA,thrB,Nat.xor_assoc,Nat.xor_self]

section Compose2
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn

theorem stepLoadK (b0 : BasisState) (k H X T : Nat) (par f gp fp : Bool) (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadK w g k)
      (MF w b0 (H^^^lkv k (b0 g) f par gp fp) X T par f gp fp) := by
  have gm := g_mut w g hn hg
  have gh : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h515 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h516 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t := (stepXorH w hn b0 H X T par f gp fp (c1 k) (c1_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp g (b0 g) gh (fun s h => h.2.2.2.2.2.2.2 g gm) (cg k) (cg_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 514) f h514 (fun s h => h.2.2.2.2.1) (cf k) (cf_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 1028) par h1028 (fun s h => h.2.2.2.1) (cp k) (cp_lt k)).seq
    ((stepMaskH w hn b0 _ X T par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (cgp k) (cgp_lt k)).seq
    (stepMaskH w hn b0 _ X T par f gp fp (w 722) fp h516 (fun s h => h.2.2.2.2.2.2.1) (cfp k) (cfp_lt k))))))
  unfold loadK
  simp only [List.append_assoc]
  apply Triple.conseq (fun _ h => h) t
  intro s h
  have e : H^^^c1 k^^^(if b0 g then cg k else 0)^^^(if f then cf k else 0)^^^(if par then cp k else 0)^^^
      (if gp then cgp k else 0)^^^(if fp then cfp k else 0)=H^^^lkv k (b0 g) f par gp fp := by
    simp only [lkv,Nat.xor_assoc]
  rw [e] at h; exact h

theorem stepLoadT (b0 : BasisState) (k H X T : Nat) (hk : k<p) (par f gp fp : Bool)
    (hg : g∉skywalkPoolWires w) :
    Triple (MF w b0 H X T par f gp fp) (loadT w g k)
      (MF w b0 H X (T^^^ltv k (b0 g) gp) par f gp fp) := by
  have gm := g_mut w g hn hg
  have gt : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have h515 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  rw [p_val] at hk
  have la : thrA k<2^256 := by unfold thrA; omega
  have lb : thrB k<2^256 := Nat.xor_lt_two_pow la (by rw [p_val]; omega)
  have t := (stepMaskT w hn b0 H X T par f gp fp g (b0 g) gt (fun s h => h.2.2.2.2.2.2.2 g gm) (thrA k) la).seq
    (stepMaskT w hn b0 H X _ par f gp fp (w 721) gp h515 (fun s h => h.2.2.2.2.2.1) (thrB k) lb)
  unfold loadT
  apply Triple.conseq (fun _ h => h) t
  intro s h
  simpa only [ltv,Nat.xor_assoc] using h

end Compose2


section Main
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_triple (k : Nat) (hk : k<p) (b0 : BasisState) (X : Nat) (hX : X<p)
    (hc : ∀ i, 258 ≤ i → i < 512 → b0 (w i) = false) (hcin : b0 (w 513)=false)
    (hac : ∀q∈aC w,b0 q=false) (h1797 : b0 (w 1797)=false) :
    let G := b0 g
    let f := decide (2^256-1-(if G then 2^256-p+k else 0)<X)
    let dx := (X+(if G then k else 0))%p
    let par := decide (dx%2=1)
    let K := (dx/2+kConstant false par)%2^258
    let H := (K%2^257+delta par)%2^257
    Triple (MF w b0 0 X 0 false false false false) (merged w g k)
      (MF w b0 (2*H+(!par).toNat) K 0 par false false false) := by
  intro G f dx par K H
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX G
  change decide (X%2=1)=x0 k G f par at a1
  change (X/2+tk k G f par)%2^258=K at a2
  change H=dx/2+(if par then hConstant else 0) at a3
  change f=decide (H<thr k G par) at a4
  have gm := g_mut w g hn hg
  have hp' := p_val
  have hpar : (decide (X%2=1) ^^ (G && decide (k%2=1)) ^^ f)=par := by
    have e : decide (X%2=1)=x0 k G f par := a1
    rw [e]; unfold x0 ksel0
    generalize (G && decide (k%2=1))=a
    cases par <;> cases a <;> cases f <;> rfl
  have hfg : f=true → G=true := by
    intro hf; cases hG : G
    · have : f=false := by
        simp only [f,hG,Bool.false_eq_true,if_false,decide_eq_false_iff_not]; rw [p_val] at hX; omega
      rw [this] at hf; exact absurd hf (by simp)
    · rfl
  have fC : decide (2^256-1-(if b0 g then cmpC+k else 0)<X)=f := by simp [f,G,cmpC]
  have s1 := stepCompareMF w g hn b0 k X (by unfold cmpC; rw [p_val] at hk ⊢; omega) (by rw [p_val] at hX; omega)
    hc hcin (g_out w hn g hg 0 256 (by omega)) (g_ne w hn g hg 514 (by omega)) gm
  rw [fC] at s1
  have s2 := stepPar w g hn b0 k X f hg
  rw [show (decide (X%2=1) ^^ (b0 g && decide (k%2=1)) ^^ f)=par from hpar] at s2
  have s3 := stepRot w hn b0 X par f false false
  have s4a := stepCCX w hn b0 0 (X/2) 0 par f false false g (w 1028) 721 (by omega) G par
    (g_ne w hn g hg 721 (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.2.2.2 g gm) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (721=722) from by decide,if_false,Bool.false_xor] at s4a
  have s4b := stepCCX w hn b0 0 (X/2) 0 par f (G && par) false (w 514) (w 1028) 722 (by omega) f par
    (w_ne w hn _ _ (by omega) (by omega) (by omega)) (w_ne w hn _ _ (by omega) (by omega) (by omega))
    (fun s h => h.2.2.2.2.1) (fun s h => h.2.2.2.1)
  simp only [if_true,show ¬ (722=721) from by decide,if_false,Bool.false_xor] at s4b
  have s5 := stepLoadK w g hn b0 k 0 (X/2) 0 par f (G && par) (f && par) hg
  rw [Nat.zero_xor,show b0 g=G from rfl,lkv_eq k G f par hfg] at s5
  have s6 := stepKAdd w hn b0 (tk k G f par) (X/2) 0 par f (G && par) (f && par) hac h1797
  rw [show (tk k G f par+X/2)%2^258=K by rw [Nat.add_comm]; exact a2] at s6
  have s7 := stepLoadK w g hn b0 k (tk k G f par) K 0 par f (G && par) (f && par) hg
  rw [show b0 g=G from rfl,lkv_eq k G f par hfg,Nat.xor_self] at s7
  have s8 := stepMeasFp w hn b0 0 K 0 par f (G && par)
  have s9 := stepCopy w hn b0 K 0 par f (G && par) false
  have s10 := stepHAddT w hn b0 (K%2^257) K 0 par f (G && par) false (Nat.mod_lt _ (by norm_num)) hac h1797
  rw [show (delta par+K%2^257)%2^257=H by simp only [H]; rw [Nat.add_comm]] at s10
  have s11 := stepW0 w hn b0 H K 0 par f (G && par) false
  have s12 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K 0 hk par f (G && par) false hg
  rw [Nat.zero_xor,show b0 g=G from rfl,ltv_eq] at s12
  have hHlt : 2*H+(!par).toNat<2^257 := by
    have dxl : dx<p := Nat.mod_lt _ (by rw [p_val]; norm_num)
    rw [a3]; rw [p_val] at dxl
    cases par <;> simp [hC_val] <;> omega
  have s13 := stepErase w hn b0 (2*H+(!par).toNat) K (thr k G par) par f (G && par) false hac h1797 hHlt
    (by rw [show (2*H+(!par).toNat)/2=H by cases par <;> simp <;> omega]; exact a4)
  have s14 := stepLoadT w g hn b0 k (2*H+(!par).toNat) K (thr k G par) hk par false (G && par) false hg
  rw [show b0 g=G from rfl,ltv_eq,Nat.xor_self] at s14
  have s15 := stepMeasGp w g hn b0 (2*H+(!par).toNat) K 0 par false false gm (g_ne w hn g hg 721 (by omega))
  have t := s1.seq (s2.seq (s3.seq (s4a.seq (s4b.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq s15))))))))))))))
  unfold merged prodPart
  simp only [List.append_assoc,List.cons_append,List.nil_append] at t ⊢
  exact t

end Main


section Final
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

/-- The merged circuit leaves exactly the state of the old compare-first constant addition
followed by the direct first tick, on every measurement record. -/
theorem merged_eq_forward (k : Nat) (hk : k<p) (X : Nat) (hX : X<p) (t u : State) (m m' : List Bool)
    (tk0 : regValue (kR w) t.basis=X) (th0 : regValue (hR w) t.basis=0) (tt0 : regValue (tR w) t.basis=0)
    (t1028 : t.basis (w 1028)=false) (t514 : t.basis (w 514)=false) (t515 : t.basis (w 721)=false)
    (t516 : t.basis (w 722)=false)
    (hc : ∀ i, 258 ≤ i → i < 512 → t.basis (w i) = false) (hcin : t.basis (w 513)=false)
    (hac : ∀q∈aC w,t.basis q=false) (h1797 : t.basis (w 1797)=false)
    (hu : u.phase=t.phase) (hu2 : ∀q,q∉kR w → u.basis q=t.basis q)
    (hu3 : regValue (kR w) u.basis=(X+(if t.basis g then k else 0))%p) :
    run (merged w g k) m t=run (NativeFirstDirect.forward w) m' u := by
  have mf0 : MF w t.basis 0 X 0 false false false false t.basis :=
    ⟨th0,tk0,tt0,t1028,t514,t515,t516,fun _ _ => rfl⟩
  have tri := merged_triple w g hn hg k hk t.basis X hX hc hcin hac h1797 t m mf0
  obtain ⟨a1,a2,a3,a4,a5⟩ := arith k X hk hX (t.basis g)
  generalize hG : t.basis g=G at tri a1 a2 a3 a4 a5 hu3
  generalize hdx : (X+(if G then k else 0))%p=dx at tri a1 a2 a3 a4 a5 hu3
  generalize hpar : decide (dx%2=1)=par at tri a1 a2 a3 a4 a5
  generalize hK : (dx/2+kConstant false par)%2^258=K at tri a1 a2 a3 a4 a5
  generalize hH : (K%2^257+delta par)%2^257=H at tri a1 a2 a3 a4 a5
  obtain ⟨lp,l1,l2,l3,l4,l5,l6,l7,l8⟩ := tri
  have dxlt : dx<p := by rw [←hdx]; exact Nat.mod_lt _ (by rw [p_val]; norm_num)
  have kh : ∀q∈hR w,q∉kR w := kR_hR w hn
  have kt : ∀q∈tR w,q∉kR w := kR_tR w hn
  have hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 dx u.basis := by
    constructor
    · change regValue (wireBlock w 0 258) u.basis=0
      rw [show wireBlock w 0 258=hR w from rfl,regValue_congr _ _ t.basis (fun q hq => hu2 q (kh q hq)),th0]
    · change regValue (wireBlock w 770 258) u.basis=dx
      exact hu3
    · change regValue (wireBlock w 1540 257) u.basis=0
      apply (regValue_zero _ _).mpr
      intro q hq
      rw [hu2 q (fun h' => List.disjoint_left.mp (blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)) h' hq)]
      exact hac q hq
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
    · change u.basis (w 1028)=false
      rw [hu2 _ (nb w hn 1028 770 258 (by omega) (by omega) (by omega))]; exact t1028
    · change u.basis (w 1797)=false
      rw [hu2 _ (nb w hn 1797 770 258 (by omega) (by omega) (by omega))]; exact h1797
  obtain ⟨zp,zh,zk,z0,z1028,zrest⟩ := forward_spec w hn dx dxlt u m' hin
  have e770 : u.basis (w 770)=par := by
    have sp := kR_split w hn u.basis
    rw [hu3] at sp
    rw [←hpar]
    cases hb : u.basis (w 770) <;> simp [hb] at sp ⊢ <;> omega
  rw [e770] at zh zk z1028
  rw [hK] at zk
  have hv : 2*(dx/2+(if par then hConstant else 0))+(!par).toNat=2*H+(!par).toNat := by rw [a3]
  rw [hv] at zh
  apply State.extensionality
  · rw [lp,zp,hu]
  · funext q
    by_cases qh : q∈hR w
    · exact (regValue_eq_iff (hR w) _ _).mp (l1.trans zh.symm) q qh
    by_cases qk : q∈kR w
    · exact (regValue_eq_iff (kR w) _ _).mp (l2.trans zk.symm) q qk
    by_cases q1 : q=w 1028
    · rw [q1,l4,z1028]
    have nmut : q∉NativeFirstDirect.mutable w := by
      simp only [NativeFirstDirect.mutable,List.mem_append,List.mem_singleton,not_or]
      exact ⟨⟨fun h' => qh (blk_sub w 0 257 0 258 (by omega) (by omega) q h'),qk⟩,q1⟩
    rw [zrest q nmut,hu2 q qk]
    by_cases qt : q∈tR w
    · rw [(regValue_zero _ _).mp l3 q qt,(regValue_zero _ _).mp tt0 q qt]
    by_cases q4 : q=w 514
    · rw [q4,l5,t514]
    by_cases q5 : q=w 721
    · rw [q5,l6,t515]
    by_cases q6 : q=w 722
    · rw [q6,l7,t516]
    apply l8
    simp only [mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨⟨qh,qk⟩,qt⟩,q1,q4,q5,q6⟩

end Final


/-! ### Resources -/

def mSites (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 515++wireBlock w 770 515++wireBlock w 1540 258++[w 721,w 722,g]

theorem in_mSites (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : i < 515 ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722) : w i∈mSites w g := by
  simp only [mSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hi with h|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)))
  · exact Or.inl (Or.inr (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩))
  · subst h; exact Or.inr (Or.inl rfl)
  · subst h; exact Or.inr (Or.inr (Or.inl rfl))

theorem blk_mSites (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 515 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀q∈wireBlock w a n,q∈mSites w g := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_mSites w g i (by omega)

theorem g_mSites (w : Nat → Wire) (g : Wire) : g∈mSites w g := by simp [mSites]

theorem dBits_wires_sub (w : Nat → Wire) : ∀q∈mappedWires (dBits w),q=w 1028 := dBits_wire w

theorem lsub (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀q∈l,q∈mSites w g) :
    l.toFinset⊆(mSites w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀q∈i.wires,q∈mSites w g) :
    wires [i]⊆(mSites w g).toFinset := by
  intro q hq
  simp only [wires,Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem merged_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mSites w g).toFinset := by
  have B := blk_mSites w g
  have I := in_mSites w g
  have G := g_mSites w g
  have mskH (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mSites w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mSites w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mSites w g).toFinset := by
    rw [notRegister_wires]; exact lsub w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514))⊆(mSites w g).toFinset := by
    rw [(compareLt_wires none (srcR w) (xR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,xR,wireBlock_length])).1]
    apply lsub; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 0 256 (by omega) q hq
    · exact B 770 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mSites w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨mskS _,notS⟩,cmp⟩,notS⟩,mskS _⟩
  have cx (a b : Nat) (ha : a < 515 ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : b < 515 ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mSites w g).toFinset := gate_sub w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mSites w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mSites w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mSites w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mSites w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub w g _ (B 0 258 (by omega)))
  have hK : wires (kAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mSites w g).toFinset := by
    apply gate_sub; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mSites w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mSites w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mSites w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mSites w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mSites w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mSites w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,hP,hR'⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


theorem merged_counts (w : Nat → Wire) (g : Wire) (k : Nat) :
    toffoliCount (merged w g k)=1025 ∧ measurementCount (merged w g k)=1027 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := maskedConstant_counts c r v
  have x1 (r : List Wire) (v : Nat) := xorConstant_counts r v
  have n1 := notRegister_counts (srcR w)
  have c1' := compareLt_counts none (srcR w) (xR w) (cR w) (w 513) (w 514)
    (by simp [srcR,xR,wireBlock_length]) (by simp [cR,xR,wireBlock_length])
  have r1 := rotate_counts (kR w)
  have k1 := mappedAdd_counts (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
    (by simp [mappedRead_length,hR,kR,wireBlock_length]) (by simp [aC,kR,wireBlock_length])
  have h1 := mappedAdd_counts (dBits w) (hpR w) (hC2 w) (w 1797)
    (by simp [dBits_length,hpR,wireBlock_length]) (by simp [hC2,hpR,wireBlock_length])
  have e1 := eraseLtChain_counts (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
    (by simp [hp8,tR,wireBlock_length]) (by simp [hC3,tR,wireBlock_length])
  have cp1 := copyRegister_counts none (wireBlock w 770 257) (hpR w) (by simp [hpR,wireBlock_length])
  have pg : toffoliCount (parGates w g k)=0 ∧ measurementCount (parGates w g k)=0 := by
    unfold parGates; split_ifs <;> simp [toffoliCount,measurementCount]
  have lx : (xR w).length=256 := by simp [xR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hpR w).length=257 := by simp [hpR,wireBlock_length]
  have lt : (tR w).length=256 := by simp [tR,wireBlock_length]
  rw [lx] at c1'
  rw [lk] at k1
  rw [lh] at h1
  rw [lt] at e1
  have hT := hAddT_counts w
  rw [hAddM,h1.1,h1.2] at hT
  have hT' : toffoliCount (hAddT w)=255 ∧ measurementCount (hAddT w)=256 := by omega
  simp only [merged,comparePart,prodPart,loadK,kAddM,hT'.1,hT'.2,loadT,toffoliCount_append,
    measurementCount_append,(m1 _ _ _).1,(m1 _ _ _).2,(x1 _ _).1,(x1 _ _).2,n1.1,n1.2,c1'.1,c1'.2.1,
    r1.1,r1.2.1,k1.1,k1.2,h1.1,h1.2,e1.1,e1.2,cp1.1,cp1.2,pg.1,pg.2]
  simp [toffoliCount,measurementCount]

section Phys
variable (w : Nat → Wire) (g : Wire) (hn : (skywalkPoolWires w).Nodup) (hg : g∉skywalkPoolWires w)
include hn hg

theorem merged_physical (k : Nat) : GatePhysical (merged w g k) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j := w_ne w hn i j hi hj h
  have gn (i : Nat) (hi : i<1798) : g≠w i := g_ne w hn g hg i hi
  have cxp (a b : Wire) (h : a≠b) : GatePhysical [.CX a b] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h]
  have ccxp (a b c : Wire) (h1 : a≠c) (h2 : b≠c) : GatePhysical [.CCX a b c] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,h1,h2]
  have mp (c : Wire) (c' : Wire) : GatePhysical [.measureX c [] [.CZ c' c]] ∧
      GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by
    simp [GatePhysical,PhysicalInstr]
  have gS : g∉srcR w := g_out w hn g hg 0 256 (by omega)
  have gH : g∉hR w := g_out w hn g hg 0 258 (by omega)
  have gT : g∉tR w := g_out w hn g hg 1029 256 (by omega)
  have cmpP : GatePhysical (compareLt none (srcR w) (xR w) (cR w) (w 513) (w 514)) := by
    apply compareLt_physical
    · have a1 := blk_dis w hn 0 256 770 256 (by omega) (by omega) (by omega)
      have a2 := blk_dis w hn 0 256 256 256 (by omega) (by omega) (by omega)
      have a3 := blk_dis w hn 770 256 256 256 (by omega) (by omega) (by omega)
      have l1 : (srcR w++xR w).Nodup := List.nodup_append'.mpr ⟨src_nd w hn,blk_nd w hn 770 256 (by omega),a1⟩
      have l2 : (srcR w++xR w++cR w).Nodup := by
        apply List.nodup_append'.mpr
        refine ⟨l1,blk_nd w hn 256 256 (by omega),?_⟩
        apply List.disjoint_left.mpr
        intro q hq hc'
        rcases List.mem_append.mp hq with h1|h1
        · exact List.disjoint_left.mp a2 h1 hc'
        · exact List.disjoint_left.mp a3 h1 hc'
      simp only [List.cons_append,List.append_assoc] at l2 ⊢
      refine List.nodup_cons.mpr ⟨?_,List.nodup_cons.mpr ⟨?_,by simpa [List.append_assoc] using l2⟩⟩
      · simp only [List.mem_cons,List.mem_append,not_or]
        exact ⟨ne 514 513 (by omega) (by omega) (by omega),nb w hn 514 0 256 (by omega) (by omega) (by omega),
          nb w hn 514 770 256 (by omega) (by omega) (by omega),nb w hn 514 256 256 (by omega) (by omega) (by omega)⟩
      · simp only [List.mem_append,not_or]
        exact ⟨nb w hn 513 0 256 (by omega) (by omega) (by omega),nb w hn 513 770 256 (by omega) (by omega) (by omega),
          nb w hn 513 256 256 (by omega) (by omega) (by omega)⟩
    · simp
  have kP : GatePhysical (kAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 770 258 1540 257 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨kR_nd w hn,blk_nd w hn 1540 257 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 770 258 (by omega) (by omega) (by omega),nb w hn 1797 1540 257 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      simp only [mappedRead,List.mem_map] at hb
      obtain ⟨q',hq',rfl⟩ := hb
      simp only [Option.mem_def,Option.some.injEq] at hq
      subst hq
      rw [List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      refine ⟨?_,?_,?_⟩
      · intro e; exact nb w hn 1797 0 258 (by omega) (by omega) (by omega) (e ▸ hq')
      · exact fun h' => hR_kR w hn _ h' hq'
      · exact fun h' => List.disjoint_left.mp (blk_dis w hn 0 258 1540 257 (by omega) (by omega) (by omega)) hq' h'
  have hP : GatePhysical (hAddM w) := by
    apply mappedAdd_physical
    · rw [List.cons_append]
      have d := blk_dis w hn 1 257 1540 256 (by omega) (by omega) (by omega)
      refine List.nodup_cons.mpr ⟨?_,List.nodup_append'.mpr ⟨blk_nd w hn 1 257 (by omega),blk_nd w hn 1540 256 (by omega),d⟩⟩
      simp only [List.mem_append,not_or]
      exact ⟨nb w hn 1797 1 257 (by omega) (by omega) (by omega),nb w hn 1797 1540 256 (by omega) (by omega) (by omega)⟩
    · intro b hb q hq
      have : q∈mappedWires (dBits w) := List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
      rw [dBits_wire w q this,List.cons_append]
      simp only [List.mem_cons,List.mem_append,not_or]
      exact ⟨ne 1028 1797 (by omega) (by omega) (by omega),nb w hn 1028 1 257 (by omega) (by omega) (by omega),
        nb w hn 1028 1540 256 (by omega) (by omega) (by omega)⟩
  have eP : GatePhysical (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)) := by
    apply eraseLtChain_physical
    have a1 := blk_dis w hn 1 256 1029 256 (by omega) (by omega) (by omega)
    have a2 := blk_dis w hn 1 256 1540 255 (by omega) (by omega) (by omega)
    have a3 := blk_dis w hn 1029 256 1540 255 (by omega) (by omega) (by omega)
    have l1 : (hp8 w++tR w).Nodup := List.nodup_append'.mpr ⟨blk_nd w hn 1 256 (by omega),tR_nd w hn,a1⟩
    have l2 : (hp8 w++tR w++hC3 w).Nodup := by
      apply List.nodup_append'.mpr
      refine ⟨l1,blk_nd w hn 1540 255 (by omega),?_⟩
      apply List.disjoint_left.mpr
      intro q hq hc'
      rcases List.mem_append.mp hq with h1|h1
      · exact List.disjoint_left.mp a2 h1 hc'
      · exact List.disjoint_left.mp a3 h1 hc'
    rw [List.cons_append,List.cons_append]
    refine List.nodup_cons.mpr ⟨?_,l2⟩
    simp only [List.mem_append,not_or]
    exact ⟨⟨nb w hn 1797 1 256 (by omega) (by omega) (by omega),nb w hn 1797 1029 256 (by omega) (by omega) (by omega)⟩,
      nb w hn 1797 1540 255 (by omega) (by omega) (by omega)⟩
  have cpP : GatePhysical (copyRegister none (wireBlock w 770 257) (hpR w)) :=
    copyRegister_physical none _ _ (List.nodup_append'.mpr ⟨blk_nd w hn 770 257 (by omega),
      blk_nd w hn 1 257 (by omega),blk_dis w hn 770 257 1 257 (by omega) (by omega) (by omega)⟩) (by simp)
  have parP : GatePhysical (parGates w g k) := by
    unfold parGates
    split_ifs <;> simp only [gatePhysical_append] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first
        | exact cxp _ _ (ne _ _ (by omega) (by omega) (by omega))
        | exact cxp _ _ (gn _ (by omega))
        | simp [GatePhysical]
  have rotP := (rotate_physical (kR w) (kR_nd w hn)).1
  have prodP : GatePhysical (prodPart w g) := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,gatePhysical_append]
    exact ⟨ccxp _ _ _ (gn _ (by omega)) (ne _ _ (by omega) (by omega) (by omega)),
      ccxp _ _ _ (ne _ _ (by omega) (by omega) (by omega)) (ne _ _ (by omega) (by omega) (by omega))⟩
  have h514 : w 514∉hR w := nb w hn 514 0 258 (by omega) (by omega) (by omega)
  have h1028 : w 1028∉hR w := nb w hn 1028 0 258 (by omega) (by omega) (by omega)
  have h1286 : w 721∉hR w := nb w hn 721 0 258 (by omega) (by omega) (by omega)
  have h1287 : w 722∉hR w := nb w hn 722 0 258 (by omega) (by omega) (by omega)
  have t1286 : w 721∉tR w := nb w hn 721 1029 256 (by omega) (by omega) (by omega)
  have lkP : GatePhysical (loadK w g k) := by
    simp only [loadK,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨xorConstant_physical _ _,maskedConstant_physical _ _ _ gH⟩,maskedConstant_physical _ _ _ h514⟩,
      maskedConstant_physical _ _ _ h1028⟩,maskedConstant_physical _ _ _ h1286⟩,maskedConstant_physical _ _ _ h1287⟩
  have ltP : GatePhysical (loadT w g k) := by
    simp only [loadT,gatePhysical_append]
    exact ⟨maskedConstant_physical _ _ _ gT,maskedConstant_physical _ _ _ t1286⟩
  have w0P : GatePhysical [.CX (w 1028) (w 0),.X (w 0)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,ne 1028 0 (by omega) (by omega) (by omega)]
  have cP : GatePhysical (comparePart w g k) := by
    simp only [comparePart,gatePhysical_append]
    exact ⟨⟨⟨⟨maskedConstant_physical _ _ _ gS,notRegister_physical _⟩,cmpP⟩,notRegister_physical _⟩,
      maskedConstant_physical _ _ _ gS⟩
  have m1 : GatePhysical [.measureX (w 722) [] [.CZ (w 514) (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have m2 : GatePhysical [.measureX (w 721) [] [.CZ g (w 1028)]] := by simp [GatePhysical,PhysicalInstr]
  have hPT : GatePhysical (hAddT w) := hAddT_physical w hP
  simp only [merged,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨cP,parP,rotP⟩,prodP⟩,lkP⟩,kP⟩,lkP⟩,m1⟩,cpP⟩,hPT⟩,w0P⟩,ltP⟩,eP⟩,ltP⟩,m2⟩

end Phys

theorem gs1 (i : Instr) : Challenge.gateSlots [i]=Challenge.instructionSlots i := by
  simp [Challenge.gateSlots]

theorem merged_slots (w : Nat → Wire) (g : Wire) (k : Nat) : Challenge.gateSlots (merged w g k)≤25000 := by
  have m1 (c : Wire) (r : List Wire) (v : Nat) := Baselines.maskedConstant_gateSlots_le c r v
  have x1 (r : List Wire) (v : Nat) := Baselines.xorConstant_gateSlots_le r v
  have c1' := Baselines.compareLt_gateSlots_le none (srcR w) (xR w) (cR w) (w 513) (w 514)
  have r1 := (Baselines.rotate_gateSlots_le (kR w)).1
  have k1 := Baselines.mappedAdd_gateSlots_le (mappedRead (hR w) false) (kR w) (aC w) (w 1797)
  have h1 := Baselines.mappedAdd_gateSlots_le (dBits w) (hpR w) (hC2 w) (w 1797)
  have e1 := Baselines.eraseLt_gateSlots_le (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)
  have pg : Challenge.gateSlots (parGates w g k)≤6 := by
    unfold parGates; split_ifs <;> simp [Challenge.gateSlots,Challenge.instructionSlots]
  have pr : Challenge.gateSlots (prodPart w g)=2 := by simp [prodPart,Challenge.gateSlots,Challenge.instructionSlots]
  have w0 : Challenge.gateSlots [.CX (w 1028) (w 0),.X (w 0)]=2 := by simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q1 : Challenge.gateSlots [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have q2 : Challenge.gateSlots [.measureX (w 721) [] [.CZ g (w 1028)]]=2 := by
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  have lK : Challenge.gateSlots (loadK w g k)≤6*258 := by
    simp only [loadK,Challenge.gateSlots_append]
    have := x1 (hR w) (c1 k); have := m1 g (hR w) (cg k); have := m1 (w 514) (hR w) (cf k)
    have := m1 (w 1028) (hR w) (cp k); have := m1 (w 721) (hR w) (cgp k); have := m1 (w 722) (hR w) (cfp k)
    simp only [hR,wireBlock_length] at *
    omega
  have lT : Challenge.gateSlots (loadT w g k)≤2*256 := by
    simp only [loadT,Challenge.gateSlots_append]
    have := m1 g (tR w) (thrA k); have := m1 (w 721) (tR w) (thrB k)
    simp only [tR,wireBlock_length] at *
    omega
  have cP : Challenge.gateSlots (comparePart w g k)≤4*256+12*256+4 := by
    simp only [comparePart,Challenge.gateSlots_append,Baselines.notRegister_gateSlots]
    have := m1 g (srcR w) (cmpC+k)
    simp only [srcR,xR,wireBlock_length] at *
    omega
  have cp : Challenge.gateSlots (copyRegister none (wireBlock w 770 257) (hpR w))=257 := by
    simp [hpR,wireBlock_length]
  have lk : (kR w).length=258 := by simp [kR,wireBlock_length]
  have lh : (hp8 w).length=256 := by simp [hp8,wireBlock_length]
  have lhR : (hR w).length=258 := by simp [hR,wireBlock_length]
  rw [lk] at r1
  rw [mappedRead_length,lhR] at k1
  rw [dBits_length] at h1
  rw [lh] at e1
  have hS := hAddT_slots w
  rw [hAddM] at hS
  simp only [merged,Challenge.gateSlots_append,pr,w0,q1,q2,cp,kAddM]
  omega

end ECDSAAdd.Entrant.E1Merge

end -- original module boundary


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
