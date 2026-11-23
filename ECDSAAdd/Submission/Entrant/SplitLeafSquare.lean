import ECDSAAdd.Submission.Entrant.Stair44Stock

/-! # Split 65-bit Karatsuba leaves for the concrete square -/

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.SplitLeafSquare
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  StairSquareContract StairSquareAssembly StairSquareHolesCore StairSquareDirectFold
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Common wire definitions and allowed-site table -/

abbrev hs : List Wire := StairSqLoopA.hostDomain

/-- All non-hole, non-flag/swap wires in the concrete square layout and external pool. -/
def allowedWires : List Wire :=
  (K0.wires ++ E0 ++ [G0, D0]).filter (fun q => !hs.contains q && q != 4761 && q != 4834 && q != 4875)

theorem K0_eq : K0 = StairSquareBChecks.K4DQ.LBF := StairSquareBChecks.K4DQ.LB_eq

def E0F : List Wire := List.range' 5093 51 ++ List.range' 5399 246 ++ List.range' 5648 3

theorem E0_eq : E0 = E0F := by
  change (List.range' 978 51).map Baselines.layout.core.poolWire ++
      (List.range' 1284 246).map Baselines.layout.core.poolWire ++
      (List.range' 1533 3).map Baselines.layout.core.poolWire = E0F
  rw [StairSquareBChecks.K4DQ.blk 978 51 (by decide),
      StairSquareBChecks.K4DQ.blk 1284 246 (by decide),
      StairSquareBChecks.K4DQ.blk 1533 3 (by decide)]
  rfl

theorem G0_eq : G0 = 4113 := by decide +kernel
theorem D0_eq : D0 = 5655 := StairSquareBChecks.K4DQ.pw_lt 1540 (by decide)

private theorem holesA_lit : StairSqLoopA.holes = List.range' 4840 35 ++ List.range' 4876 4 := by
  rw [StairSqLoopA.holes, List.map_append, StairSquareBChecks.K4DQ.blk 725 35 (by decide),
      StairSquareBChecks.K4DQ.blk 761 4 (by decide)]

private theorem hs_lit : hs = (List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5 := by
  rw [hs, StairSqLoopA.hostDomain, holesA_lit, StairSquareBChecks.K4DQ.blk 720 5 (by decide)]

theorem allowedWires_eq :
    allowedWires = (StairSquareBChecks.K4DQ.LBF.wires ++ E0F ++ [4113, 5655]).filter
      (fun q => !((List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5).contains q &&
        q != 4761 && q != 4834 && q != 4875) := by
  rw [allowedWires, K0_eq, E0_eq, G0_eq, D0_eq, hs_lit]

private theorem sub_allowedWires (L : List Wire)
    (hIn : ∀ q ∈ L, q ∈ K0.wires ++ E0 ++ [G0, D0])
    (hOut : ∀ q ∈ L, q ∉ 4761 :: 4834 :: 4875 :: hs) :
    ∀ q ∈ L, q ∈ allowedWires := by
  intro q hq
  rw [allowedWires, List.mem_filter]
  refine ⟨hIn q hq, ?_⟩
  have ho := hOut q hq
  simp only [List.mem_cons, not_or] at ho
  simp [ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]

private theorem not_mem_allowedWires_4834 : (4834 : Wire) ∉ allowedWires := by
  rw [allowedWires, List.mem_filter]; simp

private theorem not_mem_allowedWires_4875 : (4875 : Wire) ∉ allowedWires := by
  rw [allowedWires, List.mem_filter]; simp

private theorem hosts88_fast : LowAccCarryDevelop.hosts88 =
    FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
      (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4) := by
  rw [LowAccCarryDevelop.hosts88, LowAccCarryDevelop.loans88]
  change FullBTemp.hostR K0 :: FullBTemp.hostP K0 :: (FullBTemp.loans K0 ++ (accReg K0).take 4) = _
  rw [K0_eq]

private theorem hostsBSup_fast : ReorderedBSupportResearch.hosts =
    StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4)) := by
  rw [ReorderedBSupportResearch.hosts, hosts88_fast]
  change K0.core.sumCarry :: _ = _
  rw [K0_eq]

private theorem hostsB95_fast : B95Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4))) ++
      [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [B95Research.hosts, hostsBSup_fast]

private theorem keepKB_fast : B95Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.sumCarry ::
      (FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4))) ++
      [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !(((FullBTemp.hostR StairSquareBChecks.K4DQ.LBF :: FullBTemp.hostP StairSquareBChecks.K4DQ.LBF ::
        (FullBTemp.loans StairSquareBChecks.K4DQ.LBF ++ (accReg StairSquareBChecks.K4DQ.LBF).take 4)).take 44).contains q)) := by
  rw [B95Research.keepK, hostsB95_fast, hosts88_fast]

private theorem hsC_fast : C163Low4Middle.hs =
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4 := by
  change (K0.core.work.drop 165 ++ [D0]) ++ K0.core.work.take 4 = _
  rw [K0_eq, D0_eq]

private theorem hostsCFix_fast : ReorderedCFixed.hosts =
    StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
    StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
    StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
    ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4) := by
  rw [ReorderedCFixed.hosts, hsC_fast]
  change K0.core.work.getD 163 0 :: K0.core.work.getD 164 0 :: K0.core.product.getD 1 0 :: _ = _
  rw [K0_eq]

private theorem hostsC105_fast : C105Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
     StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
     StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
     ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4)) ++
      [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [C105Research.hosts, hostsCFix_fast]

private theorem keepKC_fast : C105Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.work.getD 163 0 ::
      StairSquareBChecks.K4DQ.LBF.core.work.getD 164 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 ::
      ((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4)) ++
      [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !((((StairSquareBChecks.K4DQ.LBF.core.work.drop 165 ++ [5655]) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4).take 44).contains q)) := by
  rw [C105Research.keepK, hostsC105_fast, hsC_fast]

private def hsAF : List Wire :=
  ((((StairSquareBChecks.K4DQ.LBF.core.work.drop 163).take 33 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 255).take 1 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 227).take 28 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 201).take 10 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 212).take 15 ++ (StairSquareBChecks.K4DQ.LBF.core.work.drop 211).take 1 ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 5) ++
    (StairSquareBChecks.K4DQ.LBF.core.work.drop 161).take 2) ++ StairSquareBChecks.K4DQ.LBF.core.work.take 4) ++ [5655]

private theorem hsA_fast : ReorderedAFixed.hs = hsAF := by
  rw [show ReorderedAFixed.hs = A161Low4Geometry.hs100 from rfl, A161Low4Geometry.hs100,
      A161Low4Geometry.hs99, A161Low4Geometry.loans93, hsAF]
  change ((((K0.core.work.drop 163).take 33 ++ (K0.core.work.drop 255).take 1 ++
      (K0.core.work.drop 227).take 28 ++ (K0.core.work.drop 201).take 10 ++
      (K0.core.work.drop 212).take 15 ++ (K0.core.work.drop 211).take 1 ++
      (K0.core.work.drop 196).take 5) ++
      (K0.core.work.drop 161).take 2) ++ K0.core.work.take 4) ++ [D0] = _
  rw [K0_eq, D0_eq]

private theorem hostsAFix_fast : ReorderedAFixed.hosts =
    StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF := by
  rw [ReorderedAFixed.hosts, hsA_fast]
  change K0.core.sumCarry :: (K0.core.product.drop 256).getD 1 0 :: K0.core.product.getD 1 0 :: _ = _
  rw [K0_eq]

private theorem hostsA109_fast : A109Research.hosts =
    (StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF) ++ [4757, 4758, 4759, 4505, 4506, 4507] := by
  rw [A109Research.hosts, hostsAFix_fast]

private theorem keepKA_fast : A109Research.keepK =
    ((StairSquareBChecks.K4DQ.LBF.core.sumCarry :: (StairSquareBChecks.K4DQ.LBF.core.product.drop 256).getD 1 0 ::
      StairSquareBChecks.K4DQ.LBF.core.product.getD 1 0 :: hsAF) ++ [4757, 4758, 4759, 4505, 4506, 4507]).filter
      (fun q => !((hsAF.take 44).contains q)) := by
  rw [A109Research.keepK, hostsA109_fast, hsA_fast]

/-- Spilled T5 wires inside `K0.core.work` (evicted from carry caches during the body). -/
def workTA : List Wire :=
  (A109Research.keepK.filter (fun q => (K0.core.work.drop 163).contains q)).take 32

def workTB : List Wire :=
  (B95Research.keepK.filter (fun q => (K0.core.work.drop 207).contains q)) ++
  (K0.core.work.drop 196).take 2 ++ [D0]

def workTC : List Wire := (K0.core.work.drop 209).take 34

/-- Twenty-wire swap moving `work[196..197]` and `work[207..224]` off `StairSquareBEFoldK.efold` onto clean `work[225..255]` hosts. -/
def efSwapB : List (Wire × Wire) :=
  ((B95Research.keepK.filter (fun q => (K0.core.work.drop 207).contains q && !((K0.core.work.drop 225).contains q))) ++
    (K0.core.work.drop 196).take 2).zip
    ((LowAccCarryDevelop.hosts88.take 44).filter (fun q => (K0.core.work.drop 225).contains q))

theorem workTA_def :
    workTA = (A109Research.keepK.filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 163).contains q)).take 32 := by
  rw [workTA, K0_eq]

theorem workTB_def :
    workTB = (B95Research.keepK.filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 207).contains q)) ++
      (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 2 ++ [5655] := by
  rw [workTB, K0_eq, D0_eq]

theorem workTC_def :
    workTC = (StairSquareBChecks.K4DQ.LBF.core.work.drop 209).take 34 := by
  rw [workTC, K0_eq]

theorem efSwapB_def :
    efSwapB = ((B95Research.keepK.filter (fun q =>
        (StairSquareBChecks.K4DQ.LBF.core.work.drop 207).contains q &&
        !((StairSquareBChecks.K4DQ.LBF.core.work.drop 225).contains q))) ++
      (StairSquareBChecks.K4DQ.LBF.core.work.drop 196).take 2).zip
      ((LowAccCarryDevelop.hosts88.take 44).filter (fun q => (StairSquareBChecks.K4DQ.LBF.core.work.drop 225).contains q)) := by
  rw [efSwapB, K0_eq]

private def workTAF : List Wire :=
  [4738, 4739, 4740, 4741, 4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753,
   4754, 4755, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4713, 4714, 4715, 4716]

private def workTBF : List Wire :=
  [4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4708, 4709, 4710, 4711, 4712, 4714, 4715,
   4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4713, 4697, 4698, 5655]

private def workTCF : List Wire := List.range' 4710 34

private def efSwapBF : List (Wire × Wire) :=
  [(4708, 4756), (4709, 4728), (4710, 4729), (4711, 4730), (4712, 4731),
   (4714, 4732), (4715, 4733), (4716, 4734), (4717, 4735), (4718, 4736),
   (4719, 4737), (4720, 4738), (4721, 4739), (4722, 4740), (4723, 4741),
   (4724, 4742), (4725, 4743), (4713, 4744), (4697, 4745), (4698, 4746)]

theorem workTA_lit : workTA = workTAF := by rw [workTA_def, keepKA_fast]; decide +kernel
theorem workTB_lit : workTB = workTBF := by rw [workTB_def, keepKB_fast]; decide +kernel
theorem workTC_lit : workTC = workTCF := by rw [workTC_def]; decide +kernel
theorem efSwapB_lit : efSwapB = efSwapBF := by rw [efSwapB_def, keepKB_fast, hosts88_fast]; decide +kernel

theorem work_T_geometry :
    workTA.length = 32 ∧ workTA.Nodup ∧
    workTB.length = 32 ∧ workTB.Nodup ∧
    workTC.length = 34 ∧ workTC.Nodup ∧
    efSwapB.length = 20 ∧
    (holesOf efSwapB ++ hostsOf efSwapB).Nodup ∧
    (∀ q ∈ workTA, q ∈ A109Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTB.take 31, q ∈ B95Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTC, q ∈ C105Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
    (∀ q ∈ workTA, q ∈ allowedWires) ∧
    (∀ q ∈ workTB, q ∈ allowedWires) ∧
    (∀ q ∈ workTC, q ∈ allowedWires) ∧
    (∀ ab ∈ efSwapB, ab.1 ∈ workTB ∧ ab.2 ∈ K0.core.work.drop 207 ∧
      ab.2 ∈ LowAccCarryDevelop.hosts88.take 44 ∧ ab.2 ∉ workTB ∧ ab.2 ∈ allowedWires ∧ ab.2 ≠ K0.core.normFlag) ∧
    (∀ q ∈ workTB, q ∉ holesOf efSwapB → q ∉ StairSquareBEFold.carryB K0) := by
  have hAllowedAll : ∀ q ∈ workTA ++ workTB ++ workTC ++ hostsOf efSwapB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, hs_lit]; decide +kernel))
  have hAllowedA : ∀ q ∈ workTA, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedB : ∀ q ∈ workTB, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedC : ∀ q ∈ workTC, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hAllowedEf : ∀ q ∈ hostsOf efSwapB, q ∈ allowedWires := fun q hq => hAllowedAll q (by simp [hq])
  have hRest : workTA.length = 32 ∧ workTA.Nodup ∧
      workTB.length = 32 ∧ workTB.Nodup ∧
      workTC.length = 34 ∧ workTC.Nodup ∧
      efSwapB.length = 20 ∧
      (holesOf efSwapB ++ hostsOf efSwapB).Nodup ∧
      (∀ q ∈ workTA, q ∈ A109Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ q ∈ workTB.take 31, q ∈ B95Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ q ∈ workTC, q ∈ C105Research.keepK ∧ q ∈ K0.core.work.drop 163) ∧
      (∀ ab ∈ efSwapB, ab.1 ∈ workTB ∧ ab.2 ∈ K0.core.work.drop 207 ∧
        ab.2 ∈ LowAccCarryDevelop.hosts88.take 44 ∧ ab.2 ∉ workTB ∧ ab.2 ≠ K0.core.normFlag) ∧
      (∀ q ∈ workTB, q ∉ holesOf efSwapB → q ∉ StairSquareBEFold.carryB K0) := by
    rw [workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, keepKA_fast, keepKB_fast, keepKC_fast, hosts88_fast, K0_eq]; decide +kernel
  refine ⟨hRest.1, hRest.2.1, hRest.2.2.1, hRest.2.2.2.1, hRest.2.2.2.2.1, hRest.2.2.2.2.2.1,
    hRest.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.2.1, hRest.2.2.2.2.2.2.2.2.2.1,
    hRest.2.2.2.2.2.2.2.2.2.2.1, hAllowedA, hAllowedB, hAllowedC, ?_, hRest.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro ab hab
  have hr := hRest.2.2.2.2.2.2.2.2.2.2.2.1 ab hab
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hAllowedEf ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩), hr.2.2.2.2⟩

/-! ## Clean-sum diagonal leaf wrappers (`makeC` / `clearC`) -/

section CleanDiag
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

theorem makeC_clean (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue Q.dst s.basis = 0) (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 0) (hz0 : regValue Q.z s.basis = 0)
    (hp0 : regValue Q.pad s.basis = 0) (hc0 : regValue Q.carry s.basis = 0)
    (hi0 : s.basis Q.cin = false) :
    (run (LowZero18Diagonal.makeC Q) m s).phase = s.phase ∧
    regValue Q.dst (run (LowZero18Diagonal.makeC Q) m s).basis = (regValue Q.bank s.basis) ^ 2 ∧
    regValue Q.T (run (LowZero18Diagonal.makeC Q) m s).basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (LowZero18Diagonal.makeC Q) m s).basis q = s.basis q := by
  have hX0 : regValue (Q.S ++ Q.T) s.basis = 0 := by rw [regValue_append, hS0, hT0]; simp
  have r := LowZero18Diagonal.diag_sq_cl_make Q w he hh hn Q.z (fun _ h => h) s m hd0 hX0 hp0 hc0 hz0 hi0
  refine ⟨r.1, r.2.1, ?_, ?_⟩
  · rw [r.2.2.1.2, Q.lo_mod w, Q.hi_div w]
  · intro q hd hT
    by_cases hS : q ∈ Q.S
    · exact ((regValue_zero Q.S _).mp r.2.2.1.1 q hS).trans ((regValue_zero Q.S _).mp hS0 q hS).symm
    · exact r.2.2.2 q hd (fun hx => (List.mem_append.mp hx).elim hS hT)

theorem clearC_clean (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) (hh : Q.h = 32 ∨ Q.h = 33)
    (hn : Q.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue Q.dst s.basis = (regValue Q.bank s.basis) ^ 2)
    (hS0 : regValue Q.S s.basis = 0)
    (hT0 : regValue Q.T s.basis = 2 * regValue Q.lo s.basis * regValue Q.hi s.basis)
    (hz0 : regValue Q.z s.basis = 0) (hp0 : regValue Q.pad s.basis = 0)
    (hc0 : regValue Q.carry s.basis = 0) (hi0 : s.basis Q.cin = false) :
    (run (LowZero18Diagonal.clearC Q) m s).phase = s.phase ∧
    regValue Q.dst (run (LowZero18Diagonal.clearC Q) m s).basis = 0 ∧
    regValue Q.T (run (LowZero18Diagonal.clearC Q) m s).basis = 0 ∧
    ∀ q, q ∉ Q.dst → q ∉ Q.T → (run (LowZero18Diagonal.clearC Q) m s).basis q = s.basis q := by
  have hI : Q.invC (regValue Q.bank s.basis) s.basis := by
    refine ⟨hS0, ?_⟩
    rw [hT0, Q.lo_mod w, Q.hi_div w]
  have r := RawClearSquare.diag_sq_cl_clear Q w he hh hn Q.z (fun _ h => h) s m hd0 hI hp0 hc0 hz0 hi0
  have hST := (regValue_append Q.S Q.T _).symm.trans r.2.2.1
  have hST0 := Nat.add_eq_zero_iff.mp hST
  have hS1 : regValue Q.S (run (LowZero18Diagonal.clearC Q) m s).basis = 0 := hST0.1
  have hT1 : regValue Q.T (run (LowZero18Diagonal.clearC Q) m s).basis = 0 :=
    (Nat.mul_eq_zero.mp hST0.2).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos _))
  refine ⟨r.1, r.2.1, hT1, ?_⟩
  intro q hd hT
  by_cases hS : q ∈ Q.S
  · exact ((regValue_zero Q.S _).mp hS1 q hS).trans ((regValue_zero Q.S _).mp hS0 q hS).symm
  · exact r.2.2.2 q hd (fun hx => (List.mem_append.mp hx).elim hS hT)

theorem makeC_physical (Q : KRegs) (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (LowZero18Diagonal.makeC Q) :=
  (gatePhysical_append _ _).mpr ⟨LowZero18Diagonal.make_physical Q w hn, Q.scl1591_physical w hn⟩

theorem clearC_physical (Q : KRegs) (w : Q.W) (hn : Q.all.Nodup) :
    GatePhysical (LowZero18Diagonal.clearC Q) :=
  (gatePhysical_append _ _).mpr
    ⟨Q.smkT_physical w hn (Q.piece_physical hn).1, LowZero18Diagonal.clear_physical Q w hn⟩

theorem makeC_support (Q : KRegs) (w : Q.W) :
    wires (LowZero18Diagonal.makeC Q) ⊆ Q.all.toFinset := by
  rw [LowZero18Diagonal.makeC, wires_append]
  exact Finset.union_subset (LowZero18Diagonal.make_support Q w) (Q.scl1591_support w)

theorem clearC_support (Q : KRegs) (w : Q.W) :
    wires (LowZero18Diagonal.clearC Q) ⊆ Q.all.toFinset := by
  rw [LowZero18Diagonal.clearC, RawClearSquare.clearC, wires_append]
  exact Finset.union_subset (Q.smkT_support w (Q.piece_support w).1) (LowZero18Diagonal.clear_support Q w)

theorem makeC_counts (Q : KRegs) (w : Q.W) (he : Q.bank.length = 2 * Q.h) :
    toffoliCount (LowZero18Diagonal.makeC Q) = DiagSq.cost Q - 11 - DiagSq.parR Q ∧
    measurementCount (LowZero18Diagonal.makeC Q) = DiagSq.cost Q - 4 - DiagSq.parR Q + (Q.bank.length - Q.h) := by
  have m := LowZero18Diagonal.make_counts Q w he
  have sc := Q.scl1591_counts w
  simp only [LowZero18Diagonal.makeC, toffoliCount_append, measurementCount_append]
  exact ⟨by omega, by omega⟩

theorem diag32_counts (Q : KRegs) (w : Q.W) (hh : Q.h = 32) (hb : Q.bank.length = 64) :
    toffoliCount (LowZero18Diagonal.makeC Q) = toffoliCount (LowZero18Diagonal.make Q) ∧
    measurementCount (LowZero18Diagonal.makeC Q) = measurementCount (LowZero18Diagonal.make Q) + 32 ∧
    toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (LowZero18Diagonal.clear Q) + 31 ∧
    measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (LowZero18Diagonal.clear Q) + 32 := by
  have sc := Q.scl1591_counts w
  have sm := Q.smkT_counts w
  have pc := Q.piece_counts w
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, LowZero18Diagonal.clear, RawClearSquare.clearC,
    toffoliCount_append, measurementCount_append]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem diag33_counts (Q : KRegs) (w : Q.W) (hh : Q.h = 33) (hb : Q.bank.length = 66) :
    toffoliCount (LowZero18Diagonal.makeC Q) = toffoliCount (LowZero18Diagonal.make Q) ∧
    measurementCount (LowZero18Diagonal.makeC Q) = measurementCount (LowZero18Diagonal.make Q) + 33 ∧
    toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (LowZero18Diagonal.clear Q) + 32 ∧
    measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (LowZero18Diagonal.clear Q) + 33 := by
  have sc := Q.scl1591_counts w
  have sm := Q.smkT_counts w
  have pc := Q.piece_counts w
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, LowZero18Diagonal.clear, RawClearSquare.clearC,
    toffoliCount_append, measurementCount_append]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem diag33_exact (Q : KRegs) (w : Q.W) (hh : Q.h = 33) (hb : Q.bank.length = 66) :
    toffoliCount (LowZero18Diagonal.makeC Q) + toffoliCount (LowZero18Diagonal.clearC Q) = 3881 ∧
    measurementCount (LowZero18Diagonal.makeC Q) + measurementCount (LowZero18Diagonal.clearC Q) = 4152 := by
  have he : Q.bank.length = 2 * Q.h := by omega
  have ⟨mt, mm⟩ := LowZero18Diagonal.make_counts Q w he
  have ⟨ct, cm⟩ := RawClearSquare.clear_counts Q w he
  have ⟨d1, d2, d3, d4⟩ := diag33_counts Q w hh hb
  have hc : DiagSq.cost Q = 2048 := by simp only [DiagSq.cost, hb, hh]; decide +kernel
  have hlo : Q.lo.length = 33 := by simp [KRegs.lo, hb, hh]
  have hhi : Q.hi.length = 33 := by simp [KRegs.hi, hb, hh]
  have hS : Q.S.length = 34 := by have := w.S; omega
  have hp : DiagSq.parR Q = 2 := by simp only [DiagSq.parR, hlo, hhi, hS]; decide +kernel
  rw [hc, hp] at mt mm
  rw [hc, hh] at ct
  rw [hc] at cm
  change toffoliCount (LowZero18Diagonal.clearC Q) = toffoliCount (RawClearSquare.clear Q) + 32 at d3
  change measurementCount (LowZero18Diagonal.clearC Q) = measurementCount (RawClearSquare.clear Q) + 33 at d4
  exact ⟨by omega, by omega⟩

theorem tsq65_exact (xs dst pad carry : List Wire) (cin : Wire)
    (hx : xs.length = 65) (hd : dst.length = 130) (hp : 1 ≤ pad.length) (hc : 129 ≤ carry.length) :
    toffoliCount (TrimMid.tsqM xs dst pad carry cin) +
      toffoliCount (PlainKnownClear.program xs dst pad carry cin) = 4286 ∧
    measurementCount (TrimMid.tsqM xs dst pad carry cin) +
      measurementCount (PlainKnownClear.program xs dst pad carry cin) = 4413 := by
  have q := TrimSquare3.tsq3_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have qm := TrimMid.tsqM_counts_rel xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have q4 := TrimSquare4.tsqcM4_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have qn := PlainKnownClear.program_counts xs dst pad carry cin (by omega) (by omega) hp (by omega)
  have hk : signedSquareRowsCount 65 + 130 - 3 = 2207 := by decide +kernel
  rw [hx, hd] at q
  rw [hx, TrimMid.par_65] at qm qn
  exact ⟨by omega, by omega⟩

end CleanDiag

/-! ## Split-65 Karatsuba core (`R` + `R8` + three clean-sum diagonal leaves) -/

/-- Configuration of one 128- or 129-bit split Karatsuba leaf with `R8.z` reusing `R.S.take 62`. -/
structure SplitCfg where
  n : Nat
  src : List Wire
  dst : List Wire
  workT : List Wire
  zReal4 : List Wire
  zpad : Wire
  zdst0 : Wire
  zdst1 : Wire
  carry : List Wire
  T1 : List Wire
  T2 : List Wire
  T5 : List Wire

namespace SplitCfg
variable (c : SplitCfg)

def bank : List Wire := K0.inputBank.take c.n
def S : List Wire := ((LowZero18LowK.ktmp K0).take 66).take (c.n - 63)
def T : List Wire := (E0.take 132).take (2 * (c.n - 63))

def R : KRegs :=
  { h := 64, bank := c.bank, dst := c.dst, S := c.S, T := c.T,
    z := c.zReal4 ++ List.range' 20000 58, pad := K0.leafPad, carry := c.carry, cin := K0.core.cin }

def R8 : KRegs :=
  { h := 64, bank := c.bank, dst := c.dst, S := List.range' 20100 (c.n - 63), T := c.T,
    z := c.S.take 62, pad := K0.leafPad, carry := c.carry, cin := K0.core.cin }

def qCarry : List Wire := c.carry.take 100
def qZ30 : List Wire := (c.carry.drop 100).take 30
def qZ31 : List Wire := (c.carry.drop 100).take 31
def qS33 : List Wire := (c.carry.drop 131).take 33
def qS34 : List Wire := (c.carry.drop 131).take 34

def Q1 : KRegs :=
  { h := 32, bank := c.R.lo, dst := c.R.dlo, S := c.qS33, T := c.T1,
    z := c.qZ30, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

def Q2 : KRegs :=
  if c.n = 128 then
    { h := 32, bank := c.R.hi, dst := c.R.dhi, S := c.qS33, T := c.T2,
      z := c.qZ30, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }
  else
    { h := 33, bank := c.R.hi ++ [c.zpad], dst := c.R.dhi ++ [c.zdst0, c.zdst1], S := c.qS34, T := c.T2,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

def Q5 : KRegs :=
  if c.n = 128 then
    { h := 33, bank := c.S ++ [c.zpad], dst := c.T ++ [c.zdst0, c.zdst1], S := c.qS34, T := c.T5,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }
  else
    { h := 33, bank := c.S, dst := c.T, S := c.qS34, T := c.T5,
      z := c.qZ31, pad := K0.leafPad, carry := c.qCarry, cin := K0.core.cin }

/-- Wires that remain non-zero between `make` and `clear` (in addition to `dst`). -/
def liveT : List Wire := c.T ++ c.T1 ++ c.T2 ++ c.T5

/-- All real wires (all `< 20000`) used by `make` and `clear`. -/
def realAll : List Wire :=
  K0.core.cin :: c.bank ++ c.dst ++ c.S ++ c.T ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++
    K0.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5

/-- All scratch wires that must start zero and return to zero after `make`. -/
def cleanScratch : List Wire :=
  c.S ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++ K0.leafPad ++ c.carry

def make : Program :=
  LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591 ++ c.R8.m8z

def clear : Program :=
  c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591 ++
    LowZero18Diagonal.clearC c.Q2 ++ LowZero18Diagonal.clearC c.Q1

end SplitCfg

/-! ### Concrete configurations for Branches A, B, and C -/

private def cleanRem (n : Nat) (wT : List Wire) : List Wire :=
  (K0.leafCarry.filter (fun q => !wT.contains q)) ++
  (if n = 128 then [(LowZero18LowK.ktmp K0).getD 65 0] else []) ++
  [(LowZero18LowK.ktmp K0).getD 66 0] ++
  ((LowZero18LowK.ktmp K0).drop 113).take 10

def cfgA : SplitCfg :=
  let rem := cleanRem 128 workTA
  { n := 128, src := K0.core.low, dst := K0.core.product.take 256, workT := workTA,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 66,
    T5 := [E0.getD 231 0] ++ (E0.drop 198).take 33 ++ workTA ++ [E0.getD 298 0, E0.getD 299 0] }

def cfgB : SplitCfg :=
  let rem := cleanRem 128 workTB
  { n := 128, src := K0.core.high, dst := K0.core.product.take 256, workT := workTB,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 66,
    T5 := [E0.getD 231 0] ++ (E0.drop 198).take 33 ++ workTB ++ [E0.getD 298 0, E0.getD 299 0] }

def cfgC : SplitCfg :=
  let rem := cleanRem 129 workTC
  { n := 129, src := K0.core.sum, dst := K0.core.product, workT := workTC,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0.drop 132).take 66, T2 := (E0.drop 232).take 68,
    T5 := (E0.drop 198).take 34 ++ workTC }

/-! ### Fast `K4DQ.LBF` / `E0F` / literal mirrors for kernel evaluation -/

private def cleanRemF (n : Nat) (wT : List Wire) : List Wire :=
  (StairSquareBChecks.K4DQ.LBF.leafCarry.filter (fun q => !wT.contains q)) ++
  (if n = 128 then [(LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).getD 65 0] else []) ++
  [(LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).getD 66 0] ++
  ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).drop 113).take 10

private def cfgAF : SplitCfg :=
  let rem := cleanRemF 128 workTAF
  { n := 128, src := StairSquareBChecks.K4DQ.LBF.core.low, dst := StairSquareBChecks.K4DQ.LBF.core.product.take 256, workT := workTAF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 66,
    T5 := [E0F.getD 231 0] ++ (E0F.drop 198).take 33 ++ workTAF ++ [E0F.getD 298 0, E0F.getD 299 0] }

private def cfgBF : SplitCfg :=
  let rem := cleanRemF 128 workTBF
  { n := 128, src := StairSquareBChecks.K4DQ.LBF.core.high, dst := StairSquareBChecks.K4DQ.LBF.core.product.take 256, workT := workTBF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 66,
    T5 := [E0F.getD 231 0] ++ (E0F.drop 198).take 33 ++ workTBF ++ [E0F.getD 298 0, E0F.getD 299 0] }

private def cfgCF : SplitCfg :=
  let rem := cleanRemF 129 workTCF
  { n := 129, src := StairSquareBChecks.K4DQ.LBF.core.sum, dst := StairSquareBChecks.K4DQ.LBF.core.product, workT := workTCF,
    zReal4 := (rem.drop 193).take 4, zpad := rem.getD 197 0,
    zdst0 := rem.getD 198 0, zdst1 := rem.getD 199 0, carry := rem.take 193,
    T1 := (E0F.drop 132).take 66, T2 := (E0F.drop 232).take 68,
    T5 := (E0F.drop 198).take 34 ++ workTCF }

private theorem cfgA_fast : cfgA = cfgAF := by rw [cfgA, cfgAF, cleanRem, cleanRemF, workTA_lit, K0_eq, E0_eq]
private theorem cfgB_fast : cfgB = cfgBF := by rw [cfgB, cfgBF, cleanRem, cleanRemF, workTB_lit, K0_eq, E0_eq]
private theorem cfgC_fast : cfgC = cfgCF := by rw [cfgC, cfgCF, cleanRem, cleanRemF, workTC_lit, K0_eq, E0_eq]

private theorem SplitCfg.bank_fast (c : SplitCfg) :
    c.bank = StairSquareBChecks.K4DQ.LBF.inputBank.take c.n := by rw [SplitCfg.bank, K0_eq]
private theorem SplitCfg.S_fast (c : SplitCfg) :
    c.S = ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) := by rw [SplitCfg.S, K0_eq]
private theorem SplitCfg.T_fast (c : SplitCfg) :
    c.T = (E0F.take 132).take (2 * (c.n - 63)) := by rw [SplitCfg.T, E0_eq]
private theorem SplitCfg.liveT_fast (c : SplitCfg) :
    c.liveT = (E0F.take 132).take (2 * (c.n - 63)) ++ c.T1 ++ c.T2 ++ c.T5 := by
  rw [SplitCfg.liveT, SplitCfg.T_fast]
private theorem SplitCfg.realAll_fast (c : SplitCfg) :
    c.realAll = StairSquareBChecks.K4DQ.LBF.core.cin :: StairSquareBChecks.K4DQ.LBF.inputBank.take c.n ++
      c.dst ++ ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++
      (E0F.take 132).take (2 * (c.n - 63)) ++ c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++
      StairSquareBChecks.K4DQ.LBF.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5 := by
  rw [SplitCfg.realAll, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.cleanScratch_fast (c : SplitCfg) :
    c.cleanScratch = ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++
      c.zReal4 ++ [c.zpad, c.zdst0, c.zdst1] ++ StairSquareBChecks.K4DQ.LBF.leafPad ++ c.carry := by
  rw [SplitCfg.cleanScratch, SplitCfg.S_fast, K0_eq]
private def SplitCfg.RF (c : SplitCfg) : KRegs :=
  { h := 64, bank := StairSquareBChecks.K4DQ.LBF.inputBank.take c.n, dst := c.dst,
    S := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63),
    T := (E0F.take 132).take (2 * (c.n - 63)), z := c.zReal4 ++ List.range' 20000 58,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.carry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.R8F (c : SplitCfg) : KRegs :=
  { h := 64, bank := StairSquareBChecks.K4DQ.LBF.inputBank.take c.n, dst := c.dst,
    S := List.range' 20100 (c.n - 63), T := (E0F.take 132).take (2 * (c.n - 63)),
    z := (((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63)).take 62,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.carry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q1F (c : SplitCfg) : KRegs :=
  { h := 32, bank := c.RF.lo, dst := c.RF.dlo, S := c.qS33, T := c.T1, z := c.qZ30,
    pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q2F (c : SplitCfg) : KRegs :=
  if c.n = 128 then
    { h := 32, bank := c.RF.hi, dst := c.RF.dhi, S := c.qS33, T := c.T2, z := c.qZ30,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }
  else
    { h := 33, bank := c.RF.hi ++ [c.zpad], dst := c.RF.dhi ++ [c.zdst0, c.zdst1],
      S := c.qS34, T := c.T2, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private def SplitCfg.Q5F (c : SplitCfg) : KRegs :=
  if c.n = 128 then
    { h := 33, bank := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63) ++ [c.zpad],
      dst := (E0F.take 132).take (2 * (c.n - 63)) ++ [c.zdst0, c.zdst1],
      S := c.qS34, T := c.T5, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }
  else
    { h := 33, bank := ((LowZero18LowK.ktmp StairSquareBChecks.K4DQ.LBF).take 66).take (c.n - 63),
      dst := (E0F.take 132).take (2 * (c.n - 63)),
      S := c.qS34, T := c.T5, z := c.qZ31,
      pad := StairSquareBChecks.K4DQ.LBF.leafPad, carry := c.qCarry, cin := StairSquareBChecks.K4DQ.LBF.core.cin }

private theorem SplitCfg.R_fast (c : SplitCfg) : c.R = c.RF := by
  rw [SplitCfg.R, SplitCfg.RF, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.R8_fast (c : SplitCfg) : c.R8 = c.R8F := by
  rw [SplitCfg.R8, SplitCfg.R8F, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]
private theorem SplitCfg.Q1_fast (c : SplitCfg) : c.Q1 = c.Q1F := by
  rw [SplitCfg.Q1, SplitCfg.Q1F, SplitCfg.R_fast, K0_eq]
private theorem SplitCfg.Q2_fast (c : SplitCfg) : c.Q2 = c.Q2F := by
  rw [SplitCfg.Q2, SplitCfg.Q2F, SplitCfg.R_fast, K0_eq]
private theorem SplitCfg.Q5_fast (c : SplitCfg) : c.Q5 = c.Q5F := by
  rw [SplitCfg.Q5, SplitCfg.Q5F, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq]

/-- Valid geometry bundle for a concrete `SplitCfg`. -/
structure CfgValid (c : SplitCfg) : Prop where
  hn : c.n = 128 ∨ c.n = 129
  realNd : c.realAll.Nodup
  realLt : ∀ q ∈ c.realAll, q < 20000
  realAllowed : ∀ q ∈ c.realAll, q ∈ allowedWires
  bankLen : c.bank.length = c.n
  dstLen : c.dst.length = 2 * c.n
  sLen : c.S.length = c.n - 63
  tLen : c.T.length = 2 * (c.n - 63)
  z4Len : c.zReal4.length = 4
  carryLen : c.carry.length = 193
  padLen : K0.leafPad.length = 1
  t1Len : c.T1.length = 66
  t2Len : c.T2.length = if c.n = 128 then 66 else 68
  t5Len : c.T5.length = 68

theorem cfgA_valid : CfgValid cfgA := by
  have hnd : cfgA.realAll.Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgA_fast]; decide +kernel)
  have hlt : ∀ q ∈ cfgA.realAll, q < 20000 := fun q hq =>
    of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgA_fast]; decide +kernel :
      cfgA.realAll.all (fun x => decide (x < 20000)) = true) q hq)
  have hall : ∀ q ∈ cfgA.realAll, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgA_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgA_fast, hs_lit]; decide +kernel))
  refine ⟨Or.inl rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgA_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

theorem cfgB_valid : CfgValid cfgB := by
  have hnd : cfgB.realAll.Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgB_fast]; decide +kernel)
  have hlt : ∀ q ∈ cfgB.realAll, q < 20000 := fun q hq =>
    of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgB_fast]; decide +kernel :
      cfgB.realAll.all (fun x => decide (x < 20000)) = true) q hq)
  have hall : ∀ q ∈ cfgB.realAll, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgB_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgB_fast, hs_lit]; decide +kernel))
  refine ⟨Or.inl rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgB_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

theorem cfgC_valid : CfgValid cfgC := by
  have hnd : cfgC.realAll.Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [SplitCfg.realAll_fast, cfgC_fast]; decide +kernel)
  have hlt : ∀ q ∈ cfgC.realAll, q < 20000 := fun q hq =>
    of_decide_eq_true (List.all_eq_true.mp (by simp only [SplitCfg.realAll_fast, cfgC_fast]; decide +kernel :
      cfgC.realAll.all (fun x => decide (x < 20000)) = true) q hq)
  have hall : ∀ q ∈ cfgC.realAll, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgC_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by simp only [SplitCfg.realAll_fast, cfgC_fast, hs_lit]; decide +kernel))
  refine ⟨Or.inr rfl, hnd, hlt, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, K0_eq, E0_eq]; decide +kernel)

/-! ### Generic support, physicality, correctness, and counts for any valid `SplitCfg` -/

section SplitCore
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical

private def zeroHigh (s : State) : State :=
  { phase := s.phase, basis := fun q => if 20000 ≤ q then false else s.basis q }

private theorem run_below20000 (P : Program) (hsub : ∀ q ∈ wires P, q < 20000) (s : State) (m : List Bool) :
    (run P m s).phase = (run P m (zeroHigh s)).phase ∧
    ∀ q, q < 20000 → (run P m s).basis q = (run P m (zeroHigh s)).basis q := by
  have loc := ECDSAAdd.run_measured_locality P (wires P) (Finset.Subset.refl _) s (zeroHigh s) m rfl
    (fun q hq => by simp [zeroHigh, Nat.not_le.mpr (hsub q hq)])
  exact ⟨loc.1, fun q hq => by
    by_cases hw : q ∈ wires P
    · exact loc.2 q hw
    · rw [run_preserves_outside P m s q hw, run_preserves_outside P m (zeroHigh s) q hw]
      simp [zeroHigh, Nat.not_le.mpr hq]⟩

private theorem run_ge20000 (P : Program) (hsub : ∀ q ∈ wires P, q < 20000) (s : State) (m : List Bool)
    (q : Wire) (hq : 20000 ≤ q) : (run P m s).basis q = s.basis q :=
  run_preserves_outside P m s q (fun hw => absurd (hsub q hw) (Nat.not_lt.mpr hq))

private theorem list_nodup_of_count_le {A B : List Wire} (hB : B.Nodup) (h : ∀ q, A.count q ≤ B.count q) : A.Nodup :=
  List.nodup_iff_count_le_one.mpr (fun q => (h q).trans (List.nodup_iff_count_le_one.mp hB q))

theorem cfg_R_W (c : SplitCfg) (v : CfgValid c) : c.R.W := by
  rcases v.hn with hn | hn <;>
    exact ⟨by simp [SplitCfg.R], by simp [SplitCfg.R, v.bankLen, hn], by simp [SplitCfg.R, v.bankLen, hn],
      by simp [SplitCfg.R, v.dstLen, v.bankLen], by simp [SplitCfg.R, v.sLen, v.bankLen, hn],
      by simp [SplitCfg.R, v.tLen, v.sLen], by simp [SplitCfg.R, v.z4Len],
      by simp [SplitCfg.R, v.padLen], by simp [SplitCfg.R, v.bankLen, v.carryLen, hn]⟩

theorem cfg_R8_W (c : SplitCfg) (v : CfgValid c) : c.R8.W := by
  rcases v.hn with hn | hn <;>
    exact ⟨by simp [SplitCfg.R8], by simp [SplitCfg.R8, v.bankLen, hn], by simp [SplitCfg.R8, v.bankLen, hn],
      by simp [SplitCfg.R8, v.dstLen, v.bankLen], by simp [SplitCfg.R8, v.bankLen, hn],
      by simp [SplitCfg.R8, v.tLen, hn], by simp [SplitCfg.R8, v.sLen, hn],
      by simp [SplitCfg.R8, v.padLen], by simp [SplitCfg.R8, v.bankLen, v.carryLen, hn]⟩

theorem cfg_Q1_W (c : SplitCfg) (v : CfgValid c) : c.Q1.W ∧ c.Q1.bank.length = 2 * c.Q1.h := by
  have hlo : c.R.lo.length = 64 := by simp [KRegs.lo, SplitCfg.R, v.bankLen]; rcases v.hn with h | h <;> omega
  have hdlo : c.R.dlo.length = 128 := by simp [KRegs.dlo, SplitCfg.R, v.dstLen]; rcases v.hn with h | h <;> omega
  refine ⟨⟨by simp [SplitCfg.Q1], by simp [SplitCfg.Q1, hlo], by simp [SplitCfg.Q1, hlo],
    by simp [SplitCfg.Q1, hdlo, hlo], by simp [SplitCfg.Q1, SplitCfg.qS33, v.carryLen, hlo],
    by simp [SplitCfg.Q1, SplitCfg.qS33, v.carryLen, v.t1Len],
    by simp [SplitCfg.Q1, SplitCfg.qZ30, v.carryLen], by simp [SplitCfg.Q1, v.padLen],
    by simp [SplitCfg.Q1, SplitCfg.qCarry, v.carryLen, hlo]⟩, by simp [SplitCfg.Q1, hlo]⟩

theorem cfg_Q2_W (c : SplitCfg) (v : CfgValid c) :
    c.Q2.W ∧ c.Q2.bank.length = 2 * c.Q2.h ∧ (c.Q2.h = 32 ∨ c.Q2.h = 33) := by
  rcases v.hn with hn | hn
  · have hhi : c.R.hi.length = 64 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    have hdhi : c.R.dhi.length = 128 := by simp [KRegs.dhi, SplitCfg.R, v.dstLen, hn]
    have ht2 : c.T2.length = 66 := by simpa [hn] using v.t2Len
    refine ⟨⟨by simp [SplitCfg.Q2, hn], by simp [SplitCfg.Q2, hn, hhi], by simp [SplitCfg.Q2, hn, hhi],
      by simp [SplitCfg.Q2, hn, hdhi, hhi], by simp [SplitCfg.Q2, hn, SplitCfg.qS33, v.carryLen, hhi],
      by simp [SplitCfg.Q2, hn, SplitCfg.qS33, v.carryLen, ht2],
      by simp [SplitCfg.Q2, hn, SplitCfg.qZ30, v.carryLen], by simp [SplitCfg.Q2, hn, v.padLen],
      by simp [SplitCfg.Q2, hn, SplitCfg.qCarry, v.carryLen, hhi]⟩,
      by simp [SplitCfg.Q2, hn, hhi], Or.inl (by simp [SplitCfg.Q2, hn])⟩
  · have hne : c.n ≠ 128 := by omega
    have hhi : c.R.hi.length = 65 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    have hdhi : c.R.dhi.length = 130 := by simp [KRegs.dhi, SplitCfg.R, v.dstLen, hn]
    have ht2 : c.T2.length = 68 := by simpa [hne] using v.t2Len
    refine ⟨⟨by simp [SplitCfg.Q2, hne], by simp [SplitCfg.Q2, hne, hhi], by simp [SplitCfg.Q2, hne, hhi],
      by simp [SplitCfg.Q2, hne, hdhi, hhi], by simp [SplitCfg.Q2, hne, SplitCfg.qS34, v.carryLen, hhi],
      by simp [SplitCfg.Q2, hne, SplitCfg.qS34, v.carryLen, ht2],
      by simp [SplitCfg.Q2, hne, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q2, hne, v.padLen],
      by simp [SplitCfg.Q2, hne, SplitCfg.qCarry, v.carryLen, hhi]⟩,
      by simp [SplitCfg.Q2, hne, hhi], Or.inr (by simp [SplitCfg.Q2, hne])⟩

theorem cfg_Q5_W (c : SplitCfg) (v : CfgValid c) :
    c.Q5.W ∧ c.Q5.bank.length = 2 * c.Q5.h ∧ c.Q5.h = 33 := by
  rcases v.hn with hn | hn
  · have hS : c.S.length = 65 := by rw [v.sLen, hn]
    have hT : c.T.length = 130 := by rw [v.tLen, hn]
    refine ⟨⟨by simp [SplitCfg.Q5, hn], by simp [SplitCfg.Q5, hn, hS], by simp [SplitCfg.Q5, hn, hS],
      by simp [SplitCfg.Q5, hn, hT, hS], by simp [SplitCfg.Q5, hn, SplitCfg.qS34, v.carryLen, hS],
      by simp [SplitCfg.Q5, hn, SplitCfg.qS34, v.carryLen, v.t5Len],
      by simp [SplitCfg.Q5, hn, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q5, hn, v.padLen],
      by simp [SplitCfg.Q5, hn, SplitCfg.qCarry, v.carryLen, hS]⟩,
      by simp [SplitCfg.Q5, hn, hS], by simp [SplitCfg.Q5, hn]⟩
  · have hne : c.n ≠ 128 := by omega
    have hS : c.S.length = 66 := by rw [v.sLen, hn]
    have hT : c.T.length = 132 := by rw [v.tLen, hn]
    refine ⟨⟨by simp [SplitCfg.Q5, hne], by simp [SplitCfg.Q5, hne, hS], by simp [SplitCfg.Q5, hne, hS],
      by simp [SplitCfg.Q5, hne, hT, hS], by simp [SplitCfg.Q5, hne, SplitCfg.qS34, v.carryLen, hS],
      by simp [SplitCfg.Q5, hne, SplitCfg.qS34, v.carryLen, v.t5Len],
      by simp [SplitCfg.Q5, hne, SplitCfg.qZ31, v.carryLen], by simp [SplitCfg.Q5, hne, v.padLen],
      by simp [SplitCfg.Q5, hne, SplitCfg.qCarry, v.carryLen, hS]⟩,
      by simp [SplitCfg.Q5, hne, hS], by simp [SplitCfg.Q5, hne]⟩

private theorem count_take_drop_split3 (l : List Wire) (q : Wire) :
    (l.take 100).count q + ((l.drop 100).take 31).count q + ((l.drop 131).take 34).count q ≤ l.count q := by
  have s1 := congrArg (List.count q) (List.take_append_drop 100 l)
  have s2 := congrArg (List.count q) (List.take_append_drop 31 (l.drop 100))
  have d3 : (l.drop 100).drop 31 = l.drop 131 := by simp [List.drop_drop]
  rw [d3] at s2
  have s3 := (List.take_sublist 34 (l.drop 131)).count_le q
  simp only [List.count_append] at s1 s2
  omega

theorem cfg_nodups (c : SplitCfg) (v : CfgValid c) :
    c.R.all.Nodup ∧ c.R8.all.Nodup ∧ c.Q1.all.Nodup ∧ c.Q2.all.Nodup ∧ c.Q5.all.Nodup := by
  have hr := v.realNd
  have count_q (q : Wire) :
      c.qCarry.count q + c.qZ30.count q + c.qS33.count q ≤ c.carry.count q ∧
      c.qCarry.count q + c.qZ31.count q + c.qS34.count q ≤ c.carry.count q := by
    have h : c.qCarry.count q + c.qZ31.count q + c.qS34.count q ≤ c.carry.count q :=
      count_take_drop_split3 c.carry q
    have h30 : c.qZ30.count q ≤ c.qZ31.count q := by
      have : c.qZ30 = c.qZ31.take 30 := by simp [SplitCfg.qZ30, SplitCfg.qZ31, List.take_take]
      rw [this]; exact (List.take_sublist 30 _).count_le q
    have h33 : c.qS33.count q ≤ c.qS34.count q := by
      have : c.qS33 = c.qS34.take 33 := by simp [SplitCfg.qS33, SplitCfg.qS34, List.take_take]
      rw [this]; exact (List.take_sublist 33 _).count_le q
    exact ⟨by omega, h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply List.nodup_iff_count_le_one.mpr; intro q
    by_cases hq : q < 20000
    · have hr0 : (List.range' 20000 58).count q = 0 :=
        List.count_eq_zero.mpr (fun h => Nat.not_le.mpr hq (List.mem_range'_1.mp h).1)
      have hc := List.nodup_iff_count_le_one.mp hr q
      simp only [KRegs.all, SplitCfg.R, SplitCfg.realAll, List.count_cons, List.count_append, hr0] at hc ⊢; omega
    · have hreal0 : c.realAll.count q = 0 := List.count_eq_zero.mpr (fun h => hq (v.realLt q h))
      have hr1 := List.nodup_iff_count_le_one.mp (List.nodup_range' (s := 20000) (n := 58)) q
      simp only [KRegs.all, SplitCfg.R, SplitCfg.realAll, List.count_cons, List.count_append] at hreal0 ⊢; omega
  · apply List.nodup_iff_count_le_one.mpr; intro q
    by_cases hq : q < 20000
    · have hr0 : (List.range' 20100 (c.n - 63)).count q = 0 :=
        List.count_eq_zero.mpr (fun h => Nat.not_le.mpr (Nat.lt_trans hq (by decide : 20000 < 20100)) (List.mem_range'_1.mp h).1)
      have hc := List.nodup_iff_count_le_one.mp hr q
      have ht := (List.take_sublist 62 c.S).count_le q
      simp only [KRegs.all, SplitCfg.R8, SplitCfg.realAll, List.count_cons, List.count_append, hr0] at hc ⊢; omega
    · have hreal0 : c.realAll.count q = 0 := List.count_eq_zero.mpr (fun h => hq (v.realLt q h))
      have hr1 := List.nodup_iff_count_le_one.mp (List.nodup_range' (s := 20100) (n := c.n - 63)) q
      have ht := (List.take_sublist 62 c.S).count_le q
      simp only [KRegs.all, SplitCfg.R8, SplitCfg.realAll, List.count_cons, List.count_append] at hreal0 ⊢; omega
  · apply list_nodup_of_count_le hr; intro q
    have h1 := (List.take_sublist 64 c.bank).count_le q
    have h2 := (List.take_sublist (2 * 64) c.dst).count_le q
    have h3 := (count_q q).1
    simp only [KRegs.all, SplitCfg.Q1, SplitCfg.R, KRegs.lo, KRegs.dlo, SplitCfg.realAll,
      List.count_cons, List.count_append]; omega
  · apply list_nodup_of_count_le hr; intro q
    have h1 := (List.drop_sublist 64 c.bank).count_le q
    have h2 := (List.drop_sublist (2 * 64) c.dst).count_le q
    have h3 := count_q q
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_true, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.realAll,
        List.count_cons, List.count_append]; omega
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_false, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.realAll,
        List.count_cons, List.count_append, List.count_nil]; omega
  · apply list_nodup_of_count_le hr; intro q
    have h3 := (count_q q).2
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_true, SplitCfg.realAll,
        List.count_cons, List.count_append, List.count_nil]; omega
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_false, SplitCfg.realAll,
        List.count_cons, List.count_append]; omega

theorem cfg_physical (c : SplitCfg) (v : CfgValid c) :
    GatePhysical c.make ∧ GatePhysical c.clear := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := (cfg_Q1_W c v).1; have w2 := (cfg_Q2_W c v).1; have w5 := (cfg_Q5_W c v).1
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have pR := c.R.piece_physical nR
  have p6 : GatePhysical c.R.m6h := c.R.m6h_physical wR nR (by
    have h := pR.2.2.1; simp only [gatePhysical_append] at h; exact h.1.1)
  have pc6 : GatePhysical c.R.c6h := c.R.c6h_physical wR nR (by
    have h := pR.2.2.2.1; simp only [gatePhysical_append] at h; exact h.2)
  refine ⟨?_, ?_⟩
  · simp only [SplitCfg.make, gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨makeC_physical c.Q1 w1 n1, makeC_physical c.Q2 w2 n2⟩, pR.1⟩,
      makeC_physical c.Q5 w5 n5⟩, p6⟩, c.R.m7k_physical wR nR⟩, c.R.scl1591_physical wR nR⟩,
      c.R8.m8z_physical nR8⟩
  · simp only [SplitCfg.clear, gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨c.R8.c8z_physical wR8 nR8, c.R.smkT_physical wR nR pR.1⟩,
      c.R.c7t_physical nR⟩, pc6⟩, clearC_physical c.Q5 w5 n5⟩,
      c.R.scl1591_physical wR nR⟩, clearC_physical c.Q2 w2 n2⟩, clearC_physical c.Q1 w1 n1⟩

private theorem take_z_in_z4 (c : SplitCfg) (v : CfgValid c) (k : Nat) (hk : k ≤ 4) :
    ∀ q ∈ c.R.z.take k, q ∈ c.zReal4 := by
  intro q hq
  have e : c.R.z.take k = c.zReal4.take k := by
    rw [SplitCfg.R, List.take_append_of_le_length (by rw [v.z4Len]; omega)]
  rw [e] at hq
  exact List.mem_of_mem_take hq

theorem cfg_support (c : SplitCfg) (v : CfgValid c) :
    wires c.make ⊆ c.realAll.toFinset ∧ wires c.clear ⊆ c.realAll.toFinset := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := (cfg_Q1_W c v).1; have w2 := (cfg_Q2_W c v).1; have w5 := (cfg_Q5_W c v).1
  have mCin : K0.core.cin ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mBank {q} (h : q ∈ c.bank) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mDst {q} (h : q ∈ c.dst) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mS {q} (h : q ∈ c.S) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT {q} (h : q ∈ c.T) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mZ4 {q} (h : q ∈ c.zReal4) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mZpad : c.zpad ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mZdst0 : c.zdst0 ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mZdst1 : c.zdst1 ∈ c.realAll.toFinset := by simp [SplitCfg.realAll]
  have mPad {q} (h : q ∈ K0.leafPad) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mCarry {q} (h : q ∈ c.carry) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT1 {q} (h : q ∈ c.T1) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT2 {q} (h : q ∈ c.T2) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have mT5 {q} (h : q ∈ c.T5) : q ∈ c.realAll.toFinset := by simp [SplitCfg.realAll, h]
  have sQ1 : c.Q1.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    simp only [KRegs.all, SplitCfg.Q1, SplitCfg.R, KRegs.lo, KRegs.dlo, SplitCfg.qCarry, SplitCfg.qZ30,
      SplitCfg.qS33, List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h | h | h | h
    · exact mCin
    · exact mBank (List.mem_of_mem_take h)
    · exact mDst (List.mem_of_mem_take h)
    · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
    · exact mT1 h
    · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
    · exact mPad h
    · exact mCarry (List.mem_of_mem_take h)
  have sQ2 : c.Q2.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_true, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.qCarry,
        SplitCfg.qZ30, SplitCfg.qS33, List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mDst (List.mem_of_mem_drop h)
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT2 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
    · simp only [KRegs.all, SplitCfg.Q2, hn, if_false, SplitCfg.R, KRegs.hi, KRegs.dhi, SplitCfg.qCarry,
        SplitCfg.qZ31, SplitCfg.qS34, List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_nil_iff, or_false, or_assoc] at hq
      rcases hq with rfl | h | rfl | h | rfl | rfl | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZpad
      · exact mDst (List.mem_of_mem_drop h)
      · exact mZdst0
      · exact mZdst1
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT2 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
  have sQ5 : c.Q5.all.toFinset ⊆ c.realAll.toFinset := by
    intro q hq
    by_cases hn : c.n = 128
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_true, SplitCfg.qCarry, SplitCfg.qZ31, SplitCfg.qS34,
        List.mem_toFinset, List.mem_cons, List.mem_append, List.mem_singleton,
        List.mem_nil_iff, or_false, or_assoc] at hq
      rcases hq with rfl | h | rfl | h | rfl | rfl | h | h | h | h | h
      · exact mCin
      · exact mS h
      · exact mZpad
      · exact mT h
      · exact mZdst0
      · exact mZdst1
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT5 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
    · simp only [KRegs.all, SplitCfg.Q5, hn, if_false, SplitCfg.qCarry, SplitCfg.qZ31, SplitCfg.qS34,
        List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h | h | h | h
      · exact mCin
      · exact mS h
      · exact mT h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mT5 h
      · exact mCarry (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact mPad h
      · exact mCarry (List.mem_of_mem_take h)
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  have sSmk : wires c.R.smk ⊆ c.realAll.toFinset := by
    have w3 := copyRegister_wires_subset none c.R.lo (c.R.S.take c.R.h)
    have w4 := addInPlace_wires (c.R.hi ++ c.R.zS) c.R.S (c.R.carry.take (c.R.S.length - 1)) c.R.cin
      (by simp [L1, L5, wR.S]) (by simp [SplitCfg.R, v.carryLen, v.sLen]; rcases v.hn with hn | hn <;> omega)
    intro q hq
    simp only [KRegs.smk, KRegs.m3, KRegs.m4, wires_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have h := w3 hq
      simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at h
      rcases h with h | h
      · exact mBank (List.mem_of_mem_take h)
      · exact mS (List.mem_of_mem_take h)
    · rw [w4] at hq
      simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
      rcases hq with rfl | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZ4 (take_z_in_z4 c v 1 (by decide) q h)
      · exact mS h
      · exact mCarry (List.mem_of_mem_take h)
  have sSmkT : wires c.R.smkT ⊆ c.realAll.toFinset := by
    intro q hq
    rcases Finset.mem_union.mp (c.R.smkT_wires hq) with h | h
    · exact sSmk h
    · rw [Finset.mem_singleton.mp h]
      exact mT (DiagSq.getD_in c.T 1 (by have := v.tLen; rcases v.hn with hn | hn <;> omega))
  have sScl : wires c.R.scl1591 ⊆ c.realAll.toFinset := by
    have a := FrontierSumCleanup1591Primitive.sub_support (c.R.hi ++ c.R.zS) c.R.S c.R.sumExpected1591
      (c.R.carry.take (c.R.S.length - 1)) c.R.cin
    have p := copyRegister_wires_subset none c.R.lo (c.R.S.take c.R.h)
    intro q hq
    simp only [KRegs.scl1591, wires_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have h := a hq
      simp only [KRegs.sumExpected1591, KRegs.lo, KRegs.hi, KRegs.zS, List.mem_toFinset,
        List.mem_cons, List.mem_append, or_assoc] at h
      rcases h with rfl | h | h | h | h | h | h
      · exact mCin
      · exact mBank (List.mem_of_mem_drop h)
      · exact mZ4 (take_z_in_z4 c v 1 (by decide) q h)
      · exact mS h
      · exact mBank (List.mem_of_mem_take h)
      · exact mZ4 (take_z_in_z4 c v (c.R.S.length - c.R.lo.length)
          (by rw [L0, wR.S]; rcases v.hn with hn | hn <;> simp [SplitCfg.R, v.bankLen, hn]) q h)
      · exact mCarry (List.mem_of_mem_take h)
    · have h := p hq
      simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at h
      rcases h with h | h
      · exact mBank (List.mem_of_mem_take h)
      · exact mS (List.mem_of_mem_take h)
  have hL6 : (c.R.dlo ++ c.R.zA).length = c.R.T.length := by
    rw [List.length_append, L2, L6]; simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega
  have hC6 : (c.R.carry.take (c.R.T.length - 1)).length + 1 = c.R.T.length := by
    simp [SplitCfg.R, v.carryLen, v.tLen]; rcases v.hn with hn | hn <;> omega
  have sM6 : wires c.R.m6 ⊆ c.realAll.toFinset := by
    have w6 := subInPlace_wires (c.R.dlo ++ c.R.zA) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL6 hC6
    intro q hq; rw [KRegs.m6, w6] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_take h)
    · exact mZ4 (take_z_in_z4 c v (c.R.T.length - 2 * c.R.h) (by simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have sC6 : wires c.R.c6 ⊆ c.realAll.toFinset := by
    have w6 := addInPlace_wires (c.R.dlo ++ c.R.zA) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL6 hC6
    intro q hq; rw [KRegs.c6, w6] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_take h)
    · exact mZ4 (take_z_in_z4 c v (c.R.T.length - 2 * c.R.h) (by simp [SplitCfg.R, v.tLen]; rcases v.hn with hn | hn <;> omega) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have hL7 : (c.R.dhi ++ c.R.zB).length = c.R.T.length := by
    rw [List.length_append, L3, L7]; simp [SplitCfg.R, v.bankLen, v.tLen]; rcases v.hn with hn | hn <;> omega
  have sM7 : wires c.R.m7 ⊆ c.realAll.toFinset := by
    have w7 := subInPlace_wires (c.R.dhi ++ c.R.zB) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL7 hC6
    intro q hq; rw [KRegs.m7, w7] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_drop h)
    · exact mZ4 (take_z_in_z4 c v 2 (by decide) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  have sC7 : wires c.R.c7 ⊆ c.realAll.toFinset := by
    have w7 := addInPlace_wires (c.R.dhi ++ c.R.zB) c.R.T (c.R.carry.take (c.R.T.length - 1)) c.R.cin hL7 hC6
    intro q hq; rw [KRegs.c7, w7] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mDst (List.mem_of_mem_drop h)
    · exact mZ4 (take_z_in_z4 c v 2 (by decide) q h)
    · exact mT h
    · exact mCarry (List.mem_of_mem_take h)
  obtain ⟨_, _, _, _, M4, _, _, _, _, _, _⟩ := c.R8.lens wR8
  have hL8 : (c.R8.T ++ c.R8.zM).length = c.R8.dmid.length := by
    rw [List.length_append, KRegs.zM, List.length_take, M4]; simp [SplitCfg.R8, v.tLen, v.sLen, v.bankLen]; rcases v.hn with hn | hn <;> omega
  have hC8 : (c.R8.carry.take (c.R8.dmid.length - 1)).length + 1 = c.R8.dmid.length := by
    rw [List.length_take, M4]; simp [SplitCfg.R8, v.carryLen, v.bankLen]; rcases v.hn with hn | hn <;> omega
  have sM8 : wires c.R8.m8 ⊆ c.realAll.toFinset := by
    have w8 := addInPlace_wires (c.R8.T ++ c.R8.zM) c.R8.dmid (c.R8.carry.take (c.R8.dmid.length - 1)) c.R8.cin hL8 hC8
    intro q hq; rw [KRegs.m8, w8] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mT h
    · exact mS (List.mem_of_mem_take (List.mem_of_mem_take h))
    · exact mDst (List.mem_of_mem_drop h)
    · exact mCarry (List.mem_of_mem_take h)
  have sC8 : wires c.R8.c8 ⊆ c.realAll.toFinset := by
    have w8 := subInPlace_wires (c.R8.T ++ c.R8.zM) c.R8.dmid (c.R8.carry.take (c.R8.dmid.length - 1)) c.R8.cin hL8 hC8
    intro q hq; rw [KRegs.c8, w8] at hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at hq
    rcases hq with rfl | h | h | h | h
    · exact mCin
    · exact mT h
    · exact mS (List.mem_of_mem_take (List.mem_of_mem_take h))
    · exact mDst (List.mem_of_mem_drop h)
    · exact mCarry (List.mem_of_mem_take h)
  refine ⟨?_, ?_⟩
  · simp only [SplitCfg.make, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨(makeC_support c.Q1 w1).trans sQ1, (makeC_support c.Q2 w2).trans sQ2⟩, sSmk⟩,
      (makeC_support c.Q5 w5).trans sQ5⟩, (c.R.m6h_wires_smk wR).trans (Finset.union_subset sM6 sSmk)⟩,
      (c.R.m7k_wires wR).trans sM7⟩, sScl⟩, (c.R8.m8z_wires wR8).trans sM8⟩
  · simp only [SplitCfg.clear, wires_append, Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨(c.R8.c8z_wires wR8).trans sC8, sSmkT⟩, c.R.c7t_wires.trans sC7⟩,
      (c.R.c6h_wires wR).trans sC6⟩, (clearC_support c.Q5 w5).trans sQ5⟩, sScl⟩,
      (clearC_support c.Q2 w2).trans sQ2⟩, (clearC_support c.Q1 w1).trans sQ1⟩

private theorem regValue_snoc_zero (r : List Wire) (z : Wire) (b : BasisState) (hz : b z = false) :
    regValue (r ++ [z]) b = regValue r b := by
  simp [regValue_append, regValue, hz]

private theorem regValue_snoc2_lt (r : List Wire) (z0 z1 : Wire) (b : BasisState)
    (hlt : regValue (r ++ [z0, z1]) b < 2 ^ r.length) :
    b z0 = false ∧ b z1 = false ∧ regValue r b = regValue (r ++ [z0, z1]) b := by
  have h := regValue_append r [z0, z1] b
  rw [h] at hlt
  have h01 : regValue [z0, z1] b = 0 := by
    by_contra hne
    have hpos : 1 ≤ regValue [z0, z1] b := Nat.one_le_iff_ne_zero.mpr hne
    have : 2 ^ r.length ≤ 2 ^ r.length * regValue [z0, z1] b := Nat.le_mul_of_pos_right _ hpos
    omega
  have hb0 : b z0 = false := (regValue_zero [z0, z1] b).mp h01 z0 (by simp)
  have hb1 : b z1 = false := (regValue_zero [z0, z1] b).mp h01 z1 (by simp)
  exact ⟨hb0, hb1, by rw [h, h01]; simp⟩

private theorem dmid_val (c : SplitCfg) (v : CfgValid c) (b : BasisState) :
    regValue c.R8.dmid b = regValue c.R8.dlo b / 2 ^ 64 + 2 ^ 64 * regValue c.R8.dhi b := by
  have hd : 128 ≤ c.dst.length := by rw [v.dstLen]; rcases v.hn with h | h <;> omega
  have h1 : c.R8.dmid = (c.dst.take 128).drop 64 ++ c.dst.drop 128 := by
    have e := congrArg (List.drop 64) (List.take_append_drop 128 c.dst)
    rw [List.drop_append_of_le_length (by simp [hd])] at e
    exact e.symm
  have hlen : ((c.dst.take 128).drop 64).length = 64 := by simp [hd]
  have hdiv : regValue ((c.dst.take 128).drop 64) b = regValue (c.dst.take 128) b / 2 ^ 64 := by
    have ea := regValue_append ((c.dst.take 128).take 64) ((c.dst.take 128).drop 64) b
    rw [List.take_append_drop] at ea
    have hl64 : ((c.dst.take 128).take 64).length = 64 := by simp [hd]
    have hlt := regValue_lt ((c.dst.take 128).take 64) b
    rw [hl64] at ea hlt
    rw [ea, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [h1, regValue_append, hlen, hdiv]; rfl

private theorem realAll_count (c : SplitCfg) (x : Wire) :
    c.realAll.count x =
      [K0.core.cin].count x + c.bank.count x + c.dst.count x + c.S.count x + c.T.count x +
      c.zReal4.count x + [c.zpad].count x + [c.zdst0].count x + [c.zdst1].count x +
      K0.leafPad.count x + c.carry.count x + c.T1.count x + c.T2.count x + c.T5.count x := by
  have h1 : c.realAll = ([K0.core.cin] ++ c.bank) ++ c.dst ++ c.S ++ c.T ++ c.zReal4 ++
      ([c.zpad] ++ [c.zdst0] ++ [c.zdst1]) ++ K0.leafPad ++ c.carry ++ c.T1 ++ c.T2 ++ c.T5 := by
    simp only [SplitCfg.realAll, List.cons_append, List.nil_append]
  rw [h1]
  simp only [List.count_append]
  omega

/-- Exact postcondition of `c.make` on a clean initial state. -/
theorem cfg_make_correct (c : SplitCfg) (v : CfgValid c) (s : State) (m : List Bool)
    (hd0 : regValue c.dst s.basis = 0)
    (hT0 : regValue c.liveT s.basis = 0)
    (hSc0 : regValue c.cleanScratch s.basis = 0)
    (hi0 : s.basis K0.core.cin = false) :
    let a := regValue c.R.lo s.basis
    let b := regValue c.R.hi s.basis
    let u := run c.make m s
    u.phase = s.phase ∧
    regValue c.dst u.basis = (regValue c.bank s.basis) ^ 2 ∧
    regValue c.T u.basis = 2 * a * b ∧
    regValue c.T1 u.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) ∧
    regValue c.T2 u.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) ∧
    regValue c.T5 u.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) ∧
    ∀ q, q ∉ c.dst → q ∉ c.liveT → u.basis q = s.basis q := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have sup := cfg_support c v; have hr := v.realNd
  have dj {A B : List Wire} (h : ∀ q, A.count q + B.count q ≤ c.realAll.count q) : ∀ q ∈ A, q ∉ B := kdis hr h
  have zOf (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.cleanScratch) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hSc0 q (sub q hq))
  have zLive (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.liveT) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hT0 q (sub q hq))
  have hS0 : regValue c.S s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hz40 : regValue c.zReal4 s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hpad0 : regValue K0.leafPad s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hcar0 : regValue c.carry s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hzpad0 : s.basis c.zpad = false := (regValue_zero _ _).mp hSc0 c.zpad (by simp [SplitCfg.cleanScratch])
  have hzd0 : s.basis c.zdst0 = false := (regValue_zero _ _).mp hSc0 c.zdst0 (by simp [SplitCfg.cleanScratch])
  have hzd1 : s.basis c.zdst1 = false := (regValue_zero _ _).mp hSc0 c.zdst1 (by simp [SplitCfg.cleanScratch])
  have hT_0 : regValue c.T s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT1_0 : regValue c.T1 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT2_0 : regValue c.T2 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have hT5_0 : regValue c.T5 s.basis = 0 := zLive _ (fun q h => by simp [SplitCfg.liveT, h])
  have bv := c.R.bank_value wR s.basis
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  generalize ha : regValue c.R.lo s.basis = a
  generalize hb : regValue c.R.hi s.basis = b
  have aLt : a < 2 ^ 64 := by rw [← ha]; simpa [L0] using regValue_lt c.R.lo s.basis
  have bLt : b < 2 ^ (c.n - 64) := by
    rw [← hb]; have h := regValue_lt c.R.hi s.basis
    rw [L1, show c.R.bank.length = c.n from v.bankLen, show c.R.h = 64 from rfl] at h; exact h
  have realStep (P : Program) (hp : wires P ⊆ c.realAll.toFinset) : ∀ q ∈ wires P, q < 20000 :=
    fun q hq => v.realLt q (List.mem_toFinset.mp (hp hq))
  obtain ⟨a7, r8, e8⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k ++ c.R.scl1591) c.R8.m8z m s
  obtain ⟨a6, r7, e7⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h ++ c.R.m7k) c.R.scl1591 a7 s
  obtain ⟨a5, r6, e6⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5 ++ c.R.m6h) c.R.m7k a6 s
  obtain ⟨a4, r5, e5⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk ++
    LowZero18Diagonal.makeC c.Q5) c.R.m6h a5 s
  obtain ⟨a3, r4, e4⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2 ++ c.R.smk)
    (LowZero18Diagonal.makeC c.Q5) a4 s
  obtain ⟨a2, r3, e3⟩ := kseq (LowZero18Diagonal.makeC c.Q1 ++ LowZero18Diagonal.makeC c.Q2) c.R.smk a3 s
  obtain ⟨r1, r2, e2⟩ := kseq (LowZero18Diagonal.makeC c.Q1) (LowZero18Diagonal.makeC c.Q2) a2 s
  dsimp only
  rw [SplitCfg.make, e8, e7, e6, e5, e4, e3, e2]
  have st1 := makeC_clean c.Q1 w1.1 w1.2 (Or.inl rfl) n1 s r1
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hd0 q (List.mem_of_mem_take h)))
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    hT1_0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    hpad0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_take h)))
    hi0
  generalize hs1 : run (LowZero18Diagonal.makeC c.Q1) r1 s = s1 at st1 ⊢
  have F1 : ∀ q, q ∉ c.R.dlo → q ∉ c.T1 → s1.basis q = s.basis q := st1.2.2.2
  have h_hi_bank (q : Wire) : c.R.hi.count q ≤ c.bank.count q := (List.drop_sublist 64 c.bank).count_le q
  have h_dhi_dst (q : Wire) : c.R.dhi.count q ≤ c.dst.count q := (List.drop_sublist 128 c.dst).count_le q
  have mLo {q : Wire} (h : q ∈ c.R.lo) : q ∈ c.bank := List.mem_of_mem_take (show q ∈ c.bank.take 64 from h)
  have mHi {q : Wire} (h : q ∈ c.R.hi) : q ∈ c.bank := List.mem_of_mem_drop (show q ∈ c.bank.drop 64 from h)
  have mDlo {q : Wire} (h : q ∈ c.R.dlo) : q ∈ c.dst := List.mem_of_mem_take (show q ∈ c.dst.take 128 from h)
  have mDhi {q : Wire} (h : q ∈ c.R.dhi) : q ∈ c.dst := List.mem_of_mem_drop (show q ∈ c.dst.drop 128 from h)
  have bLtR : b < 2 ^ (c.R.bank.length - c.R.h) := by simpa [SplitCfg.R, v.bankLen] using bLt
  have s1_T1 : regValue c.T1 s1.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) := by
    have h := st1.2.2.1; rw [c.Q1.lo_mod w1.1, c.Q1.hi_div w1.1] at h; simpa [SplitCfg.Q1, ha] using h
  have s1_dlo : regValue c.R.dlo s1.basis = a ^ 2 := by simpa [SplitCfg.Q1, ha] using st1.2.1
  have o_dlo {r : List Wire} (h : ∀ q, r.count q + c.dst.count q ≤ c.realAll.count q) : ∀ q ∈ r, q ∉ c.R.dlo :=
    fun q hq hd => dj h q hq (mDlo hd)
  have o_dhi {r : List Wire} (h : ∀ q, r.count q + c.dst.count q ≤ c.realAll.count q) : ∀ q ∈ r, q ∉ c.R.dhi :=
    fun q hq hd => dj h q hq (mDhi hd)
  have dlo_dhi : ∀ q ∈ c.R.dhi, q ∉ c.R.dlo := by
    intro q h1 h2
    have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
    rw [← List.take_append_drop 128 c.dst] at hnd
    exact (List.nodup_append.mp hnd).2.2 q h2 q h1 rfl
  have s1_keep (r : List Wire) (hd : ∀ q ∈ r, q ∉ c.R.dlo) (ht : ∀ q ∈ r, q ∉ c.T1) :
      regValue r s1.basis = regValue r s.basis := regValue_congr _ _ _ (fun q hq => F1 q (hd q hq) (ht q hq))
  have s1_eq (q : Wire) (hd : q ∉ c.dst) (ht : q ∉ c.T1) : s1.basis q = s.basis q :=
    F1 q (fun h => hd (mDlo h)) ht
  have s1_Q2_bank : regValue c.Q2.bank s1.basis = b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q2, hn, if_true]
      rw [s1_keep _ (o_dlo (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega))
        (dj (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega)), hb]
    · simp only [SplitCfg.Q2, hn, if_false]
      rw [regValue_snoc_zero _ _ _ ((s1_eq c.zpad
        (dj (A := [c.zpad]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzpad0)]
      rw [s1_keep _ (o_dlo (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega))
        (dj (fun q => by clear * - c q h_hi_bank; have := h_hi_bank q; rw [realAll_count]; omega)), hb]
  have s1_Q2_dst0 : regValue c.Q2.dst s1.basis = 0 := by
    have hdhi0 : regValue c.R.dhi s1.basis = 0 :=
      (s1_keep _ dlo_dhi (dj (fun q => by clear * - c q h_dhi_dst; have := h_dhi_dst q; rw [realAll_count]; omega))).trans
        ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hd0 q (mDhi h)))
    by_cases hn : c.n = 128
    · simpa [SplitCfg.Q2, hn] using hdhi0
    · simp only [SplitCfg.Q2, hn, if_false, regValue_append, hdhi0, zero_add]
      have b0 : s1.basis c.zdst0 = false := (s1_eq _
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s1.basis c.zdst1 = false := (s1_eq _
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
  have s1_car0 : regValue c.carry s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hcar0
  have s1_pad0 : regValue K0.leafPad s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hpad0
  have s1_cin0 : s1.basis K0.core.cin = false :=
    (s1_eq _ (dj (A := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s1_T2_0 : regValue c.T2 s1.basis = 0 :=
    (s1_keep _ (o_dlo (fun q => by clear * - c q; rw [realAll_count]; omega))
      (dj (fun q => by clear * - c q; rw [realAll_count]; omega))).trans hT2_0
  have st2 := makeC_clean c.Q2 w2.1 w2.2.1 w2.2.2 n2 s1 r2 s1_Q2_dst0
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_T2_0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s1_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s1_cin0)
  generalize hs2 : run (LowZero18Diagonal.makeC c.Q2) r2 s1 = s2 at st2 ⊢
  have s2_dhi : regValue c.R.dhi s2.basis = b ^ 2 := by
    by_cases hn : c.n = 128
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simpa [SplitCfg.Q2, hn] using h
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simp only [SplitCfg.Q2, hn, if_false] at h
      have hlt : regValue (c.R.dhi ++ [c.zdst0, c.zdst1]) s2.basis < 2 ^ c.R.dhi.length := by
        rw [h, L3]; rcases v.hn with h128 | h129
        · exact absurd h128 hn
        · simp only [SplitCfg.R, v.bankLen, h129] at bLt ⊢
          have : b ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left bLt (by decide)
          simpa [← Nat.pow_mul] using this
      exact (regValue_snoc2_lt c.R.dhi c.zdst0 c.zdst1 s2.basis hlt).2.2.trans h
  have s2_zd0 : s2.basis c.zdst0 = false ∧ s2.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have f := st2.2.2.2
      have eq0 : s2.basis c.zdst0 = s1.basis c.zdst0 := f _ (by simp [SplitCfg.Q2, hn]; exact o_dhi (r := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      have eq1 : s2.basis c.zdst1 = s1.basis c.zdst1 := f _ (by simp [SplitCfg.Q2, hn]; exact o_dhi (r := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
      exact ⟨eq0.trans ((s1_eq _ (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        eq1.trans ((s1_eq _ (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun q => by clear * - c q; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
    · have h := st2.2.1; rw [s1_Q2_bank] at h; simp only [SplitCfg.Q2, hn, if_false] at h
      have hlt : regValue (c.R.dhi ++ [c.zdst0, c.zdst1]) s2.basis < 2 ^ c.R.dhi.length := by
        rw [h, L3]; rcases v.hn with h128 | h129
        · exact absurd h128 hn
        · simp only [SplitCfg.R, v.bankLen, h129] at bLt ⊢
          have : b ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left bLt (by decide)
          simpa [← Nat.pow_mul] using this
      have p := regValue_snoc2_lt c.R.dhi c.zdst0 c.zdst1 s2.basis hlt
      exact ⟨p.1, p.2.1⟩
  have s2_T2 : regValue c.T2 s2.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) := by
    have h := st2.2.2.1
    rw [c.Q2.lo_mod w2.1, c.Q2.hi_div w2.1, s1_Q2_bank] at h
    by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using h
  have F2 : ∀ q, q ∉ c.dst → q ∉ c.T1 → q ∉ c.T2 → s2.basis q = s.basis q := by
    intro q hd ht1 ht2
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s2_zd0.1.trans hzd0.symm
      · exact s2_zd0.2.trans hzd1.symm
    · have hq2d : q ∉ c.Q2.dst := by
        by_cases hn : c.n = 128
        · simp [SplitCfg.Q2, hn]; exact fun h => hd (mDhi h)
        · simp only [SplitCfg.Q2, hn, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hd (mDhi h)
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
      have hq2t : q ∉ c.Q2.T := by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using ht2
      exact (st2.2.2.2 q hq2d hq2t).trans (s1_eq q hd ht1)
  have s2_dlo : regValue c.R.dlo s2.basis = a ^ 2 := by
    rw [regValue_congr _ _ s1.basis (fun q hq => by
      have hnot_dhi : q ∉ c.R.dhi := fun h => dlo_dhi q h hq
      have hnot_z0 : q ≠ c.zdst0 := fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst0 (by simp) (h ▸ mDlo hq)
      have hnot_z1 : q ≠ c.zdst1 := fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst1 (by simp) (h ▸ mDlo hq)
      have hnot_t2 : q ∉ c.T2 := dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq)
      apply st2.2.2.2
      · by_cases hn : c.n = 128
        · simpa [SplitCfg.Q2, hn] using hnot_dhi
        · simp [SplitCfg.Q2, hn, hnot_dhi, hnot_z0, hnot_z1]
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hnot_t2), s1_dlo]
  have s2_T1 : regValue c.T1 s2.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) := by
    rw [regValue_congr _ _ s1.basis (fun q hq => by
      have hnot_dst : q ∉ c.dst := fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q h hq
      have hnot_z0 : q ≠ c.zdst0 := fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst0 (by simp) (h ▸ hq)
      have hnot_z1 : q ≠ c.zdst1 := fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) c.zdst1 (by simp) (h ▸ hq)
      have hnot_t2 : q ∉ c.T2 := dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq
      apply st2.2.2.2
      · by_cases hn : c.n = 128
        · simp [SplitCfg.Q2, hn]; exact fun h => hnot_dst (mDhi h)
        · simp [SplitCfg.Q2, hn, hnot_z0, hnot_z1]; exact fun h => hnot_dst (mDhi h)
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hnot_t2), s1_T1]
  have sup_parts : (∀ q ∈ wires c.R.smk, q < 20000) ∧ (∀ q ∈ wires c.R.m6h, q < 20000) ∧
      (∀ q ∈ wires c.R.m7k, q < 20000) ∧ (∀ q ∈ wires c.R.scl1591, q < 20000) ∧
      (∀ q ∈ wires c.R8.m8z, q < 20000) := by
    have sm := sup.1
    simp only [SplitCfg.make, wires_append, Finset.union_subset_iff] at sm
    exact ⟨realStep _ sm.1.1.1.1.1.2, realStep _ sm.1.1.1.2, realStep _ sm.1.1.2, realStep _ sm.1.2, realStep _ sm.2⟩
  have mk_zh_z (t : State) (ht : ∀ q ∈ c.zReal4, t.basis q = false) : regValue c.R.z (zeroHigh t).basis = 0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    simp only [SplitCfg.R, List.mem_append] at hq
    rcases hq with hq | hq
    · simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]; exact ht q hq
    · simp only [zeroHigh, (List.mem_range'_1.mp hq).1, if_true]
  have st3_zh := c.R.smk_correct wR nR (zeroHigh s2) r3
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hS0 q hq)))
    (mk_zh_z s2 (fun q hq => (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
    (by
      change (zeroHigh s2).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (F2 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0)
  have loc3 := run_below20000 c.R.smk sup_parts.1 s2 r3
  generalize hs3 : run c.R.smk r3 s2 = s3 at loc3 ⊢
  have s3_F (q : Wire) (hS : q ∉ c.S) : s3.basis q = s2.basis q := by
    by_cases hq : q < 20000
    · rw [loc3.2 q hq, st3_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs3]; exact run_ge20000 c.R.smk sup_parts.1 s2 r3 q (Nat.le_of_not_lt hq)
  have s3_S : regValue c.S s3.basis = a + b := by
    have e1 := regValue_congr c.S s3.basis (run c.R.smk r3 (zeroHigh s2)).basis (fun q hq => loc3.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))
    rw [e1, show c.S = c.R.S from rfl, st3_zh.2.1]
    have elo : regValue c.R.lo (zeroHigh s2).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s2).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact F2 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    rw [elo, ehi]
  have F3 : ∀ q, q ∉ c.dst → q ∉ c.S → q ∉ c.T1 → q ∉ c.T2 → s3.basis q = s.basis q :=
    fun q hd hS ht1 ht2 => (s3_F q hS).trans (F2 q hd ht1 ht2)
  have s3_Q5_bank : regValue c.Q5.bank s3.basis = a + b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true]
      rw [regValue_snoc_zero _ _ _ ((F3 c.zpad
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0), s3_S]
    · simpa [SplitCfg.Q5, hn] using s3_S
  have s3_car0 : regValue c.carry s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hcar0
  have s3_T0 : regValue c.T s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT_0
  have s3_Q5_dst0 : regValue c.Q5.dst s3.basis = 0 := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true, regValue_append, s3_T0, zero_add]
      have b0 : s3.basis c.zdst0 = false := (F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s3.basis c.zdst1 = false := (F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
    · simpa [SplitCfg.Q5, hn] using s3_T0
  have s3_T5_0 : regValue c.T5 s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT5_0
  have s3_pad0 : regValue K0.leafPad s3.basis = 0 :=
    (regValue_congr _ _ s.basis (fun q hq => F3 q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hpad0
  have s3_cin0 : s3.basis K0.core.cin = false :=
    (F3 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have st4 := makeC_clean c.Q5 w5.1 w5.2.1 (Or.inr w5.2.2) n5 s3 r4 s3_Q5_dst0
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_T5_0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s3_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s3_cin0)
  generalize hs4 : run (LowZero18Diagonal.makeC c.Q5) r4 s3 = s4 at st4 ⊢
  have s4_T : regValue c.T s4.basis = (a + b) ^ 2 := by
    by_cases hn : c.n = 128
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simp only [SplitCfg.Q5, hn, if_true] at h
      have hlt : regValue (c.T ++ [c.zdst0, c.zdst1]) s4.basis < 2 ^ c.T.length := by
        rw [h, v.tLen, hn]; simp only [hn] at bLt
        have hab : a + b < 2 ^ 65 := by omega
        have : (a + b) ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left hab (by decide)
        simpa [← Nat.pow_mul] using this
      exact (regValue_snoc2_lt c.T c.zdst0 c.zdst1 s4.basis hlt).2.2.trans h
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simpa [SplitCfg.Q5, hn] using h
  have s4_zd0 : s4.basis c.zdst0 = false ∧ s4.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have h := st4.2.1; rw [s3_Q5_bank] at h; simp only [SplitCfg.Q5, hn, if_true] at h
      have hlt : regValue (c.T ++ [c.zdst0, c.zdst1]) s4.basis < 2 ^ c.T.length := by
        rw [h, v.tLen, hn]; simp only [hn] at bLt
        have hab : a + b < 2 ^ 65 := by omega
        have : (a + b) ^ 2 < (2 ^ 65) ^ 2 := Nat.pow_lt_pow_left hab (by decide)
        simpa [← Nat.pow_mul] using this
      have p := regValue_snoc2_lt c.T c.zdst0 c.zdst1 s4.basis hlt
      exact ⟨p.1, p.2.1⟩
    · have eq0 : s4.basis c.zdst0 = s3.basis c.zdst0 := st4.2.2.2 _
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      have eq1 : s4.basis c.zdst1 = s3.basis c.zdst1 := st4.2.2.2 _
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      exact ⟨eq0.trans ((F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        eq1.trans ((F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
  have s4_T5 : regValue c.T5 s4.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) := by
    have h := st4.2.2.1
    rw [c.Q5.lo_mod w5.1, c.Q5.hi_div w5.1, s3_Q5_bank, w5.2.2] at h
    by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using h
  have s4_F (q : Wire) (hT : q ∉ c.T) (hT5 : q ∉ c.T5) : s4.basis q = s3.basis q := by
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s4_zd0.1.trans ((F3 _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
      · exact s4_zd0.2.trans ((F3 _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
    · apply st4.2.2.2
      · by_cases hn : c.n = 128
        · simp only [SplitCfg.Q5, hn, if_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hT h
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
        · simpa [SplitCfg.Q5, hn] using hT
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using hT5
  have F4 : ∀ q, q ∉ c.dst → q ∉ c.S → q ∉ c.liveT → s4.basis q = s.basis q := by
    intro q hd hS hL
    have hT : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT1 : q ∉ c.T1 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT2 : q ∉ c.T2 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT5 : q ∉ c.T5 := fun h => hL (by simp [SplitCfg.liveT, h])
    exact (s4_F q hT hT5).trans (F3 q hd hS hT1 hT2)
  have s4_dlo : regValue c.R.dlo (zeroHigh s4).basis = a ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDlo hq, true_or, or_true])), if_false]
      exact (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))).trans s2_dlo
  have s4_lo_zh : regValue c.R.lo (zeroHigh s4).basis = a :=
    (regValue_congr _ _ s.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
      exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mLo hq)))).trans ha
  have s4_hi_zh : regValue c.R.hi (zeroHigh s4).basis = b :=
    (regValue_congr _ _ s.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
      exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mHi hq)))).trans hb
  have s4_S_zh : regValue c.R.S (zeroHigh s4).basis = a + b :=
    (regValue_congr _ _ s3.basis (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s3_S
  have s4_T_zh : regValue c.R.T (zeroHigh s4).basis = (a + b) ^ 2 :=
    (regValue_congr _ _ s4.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s4_T
  have s4_car_zh : regValue c.R.carry (zeroHigh s4).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s4_cin_zh : (zeroHigh s4).basis c.R.cin = false := by
    change (zeroHigh s4).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  have s4_z_zh : regValue c.R.z (zeroHigh s4).basis = 0 := mk_zh_z s4 (fun q hq =>
    (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have s4_zA_zh : regValue c.R.zA (zeroHigh s4).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s4_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have hTl := wR.T; have hSl := wR.S; have hhR := wR.hh; have h4R := wR.h4; have hclR := wR.carry
  have ex : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
  have sumLt : a + b < 2 ^ c.R.S.length := by
    have hp : 2 ^ c.R.h ≤ 2 ^ (c.R.bank.length - c.R.h) := Nat.pow_le_pow_right (by decide) (by clear * - hhR; omega)
    have hq : 2 ^ c.R.S.length = 2 * 2 ^ (c.R.bank.length - c.R.h) := by rw [hSl, pow_succ]; ring
    have haR : a < 2 ^ c.R.h := aLt
    clear * - haR bLtR hp hq; omega
  have sqLt : (a + b) ^ 2 < 2 ^ c.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have st5_zh : (run c.R.m6h r5 (zeroHigh s4)).phase = (zeroHigh s4).phase ∧
      regValue c.R.T (run c.R.m6h r5 (zeroHigh s4)).basis = 2 * a * b + b ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.m6h r5 (zeroHigh s4)).basis q = (zeroHigh s4).basis q := by
    rw [c.R.m6h_square_run wR nR (zeroHigh s4) r5
      (fun q hq => (regValue_zero _ _).mp s4_car_zh q (List.mem_of_mem_take hq))
      s4_cin_zh a b aLt bLtR s4_T_zh s4_dlo s4_zA_zh s4_S_zh s4_lo_zh s4_hi_zh]
    unfold KRegs.m6
    obtain ⟨p, f, val⟩ := BalancedInverse.subInPlace_any_correct (c.R.dlo ++ c.R.zA) c.R.T
      (c.R.carry.take (c.R.T.length - 1)) c.R.cin
      (knd nR (fun q => by have := c.R.counts q; simp only [KRegs.all, List.count_cons, List.count_append]; omega))
      (by rw [List.length_append, L2, L6]; omega)
      (by rw [List.length_take]; omega)
      (zeroHigh s4) r5 (fun q hq => (regValue_zero _ _).mp s4_car_zh q (List.mem_of_mem_take hq))
    refine ⟨p, ?_, f⟩
    rw [val, regValue_append, s4_dlo, s4_zA_zh, s4_T_zh, s4_cin_zh]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt, ex]; omega
  have loc5 := run_below20000 c.R.m6h sup_parts.2.1 s4 r5
  generalize hs5 : run c.R.m6h r5 s4 = s5 at loc5 ⊢
  have s5_F (q : Wire) (hT : q ∉ c.T) : s5.basis q = s4.basis q := by
    by_cases hq : q < 20000
    · rw [loc5.2 q hq, st5_zh.2.2 q hT]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs5]; exact run_ge20000 c.R.m6h sup_parts.2.1 s4 r5 q (Nat.le_of_not_lt hq)
  have s5_T : regValue c.T s5.basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc5.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st5_zh.2.1
  have s5_dhi : regValue c.R.dhi (zeroHigh s5).basis = b ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDhi hq, true_or, or_true])), if_false]
      exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
          (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))).trans s2_dhi
  have s5_T_zh : regValue c.R.T (zeroHigh s5).basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ s5.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s5_T
  have s5_car_zh : regValue c.R.carry (zeroHigh s5).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      rw [s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s5_cin_zh : (zeroHigh s5).basis c.R.cin = false := by
    change (zeroHigh s5).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    rw [s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  have s5_z_zh : regValue c.R.z (zeroHigh s5).basis = 0 := mk_zh_z s5 (fun q hq => by
    rw [s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
    exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have s5_zB_zh : regValue c.R.zB (zeroHigh s5).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s5_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have xv5 : regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis = b ^ 2 := by
    rw [regValue_append, s5_dhi, s5_zB_zh]; simp
  have st6_zh : (run c.R.m7k r6 (zeroHigh s5)).phase = (zeroHigh s5).phase ∧
      regValue c.R.T (run c.R.m7k r6 (zeroHigh s5)).basis = 2 * a * b ∧
      ∀ q, q ∉ c.R.T → (run c.R.m7k r6 (zeroHigh s5)).basis q = (zeroHigh s5).basis q := by
    have hcl7 : ∀ q ∈ c.R.carry.take (c.R.T.length - 1), (zeroHigh s5).basis q = false :=
      fun q hq => (regValue_zero _ _).mp s5_car_zh q (List.mem_of_mem_take hq)
    have hnc7 : ((zeroHigh s5).basis ((c.R.dhi ++ c.R.zB).headD 0) && !(zeroHigh s5).basis (c.R.T.headD 0)) = false := by
      have hT := LowZero.head_bit c.R.T [] (zeroHigh s5).basis (c.R.T_ne wR)
      rw [List.append_nil] at hT
      rw [LowZero.head_bit c.R.dhi c.R.zB (zeroHigh s5).basis (c.R.dhi_ne wR), hT, s5_dhi, s5_T_zh,
        show 2 * a * b + b ^ 2 = b ^ 2 + 2 * (a * b) by ring, Nat.add_mul_mod_self_left]
      cases decide (b ^ 2 % 2 = 1) <;> rfl
    have h17 : (zeroHigh s5).basis ((c.R.dhi ++ c.R.zB).tail.headD 0) = false := by
      rw [KRegs.bit1 c.R.dhi c.R.zB (zeroHigh s5).basis (c.R.dhi_two wR), s5_dhi, KRegs.sq_bit1]; rfl
    have hA7 : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis < 2 ^ (c.R.T.length - 1) :=
      fun _ => by rw [xv5, hTl, hSl]; exact KRegs.sq_trim_bound c.R.bank.length c.R.h b bLtR
    have hb7 : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) :=
      fun tc => by
        have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
        rw [xv5, s5_T_zh, hTl, hSl, Nat.mod_eq_of_lt tb]; omega
    have hab7 : a * b < 2 ^ c.R.bank.length := by
      have e : 2 ^ c.R.bank.length = 2 ^ c.R.h * 2 ^ (c.R.bank.length - c.R.h) := by rw [← pow_add]; congr 1; omega
      rw [e]; exact Nat.mul_lt_mul'' aLt bLtR
    have p2b : 2 ^ (c.R.bank.length + 1) = 2 * 2 ^ c.R.bank.length := by rw [pow_succ]; ring
    have HT : c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis < 2 ^ (c.R.T.length - 1) ∧
        regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) ∧
        regValue c.R.T (zeroHigh s5).basis % 2 ^ (c.R.T.length - 1) < regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis + 2 ^ (c.R.T.length - 2) := by
      intro tc
      refine ⟨hA7 tc, hb7 tc, ?_⟩
      have tc' : 2 * c.R.h + 1 ≤ c.R.bank.length := tc
      have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
      have hpw : 2 ^ (c.R.bank.length + 1) ≤ 2 ^ (c.R.T.length - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [xv5, s5_T_zh, hTl, hSl, Nat.mod_eq_of_lt tb]
      rw [hTl, hSl] at hpw
      rw [show 2 * a * b + b ^ 2 = 2 * (a * b) + b ^ 2 by ring]; omega
    have HF : ¬c.R.trimOK → regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis ≤ regValue c.R.T (zeroHigh s5).basis ∧
        regValue c.R.T (zeroHigh s5).basis < regValue (c.R.dhi ++ c.R.zB) (zeroHigh s5).basis + 2 ^ (c.R.T.length - 1) := by
      intro _
      have hpw : 2 ^ (c.R.bank.length + 1) ≤ 2 ^ (c.R.T.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [xv5, s5_T_zh, show 2 * a * b + b ^ 2 = 2 * (a * b) + b ^ 2 by ring]
      constructor <;> omega
    rw [c.R.m7k_run wR nR (zeroHigh s5) r6 hcl7 hnc7 s5_cin_zh h17 HT HF]
    obtain ⟨p, f, val⟩ := c.R.m7t_correct wR nR (zeroHigh s5) r6 hcl7 hnc7 s5_cin_zh h17 hA7 hb7
    refine ⟨p, ?_, f⟩
    rw [val, xv5, s5_T_zh, s5_cin_zh]
    simp only [Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  have loc6 := run_below20000 c.R.m7k sup_parts.2.2.1 s5 r6
  generalize hs6 : run c.R.m7k r6 s5 = s6 at loc6 ⊢
  have s6_F (q : Wire) (hT : q ∉ c.T) : s6.basis q = s5.basis q := by
    by_cases hq : q < 20000
    · rw [loc6.2 q hq, st6_zh.2.2 q hT]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs6]; exact run_ge20000 c.R.m7k sup_parts.2.2.1 s5 r6 q (Nat.le_of_not_lt hq)
  have s6_T : regValue c.T s6.basis = 2 * a * b :=
    (regValue_congr _ _ _ (fun q hq => loc6.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st6_zh.2.1
  have s6_S_zh : regValue c.R.S (zeroHigh s6).basis = regValue c.R.lo (zeroHigh s6).basis + regValue c.R.hi (zeroHigh s6).basis := by
    have eS : regValue c.R.S (zeroHigh s6).basis = a + b :=
      (regValue_congr _ _ s3.basis (fun q hq => by
        change q ∈ c.S at hq
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
        exact (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
            (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
              (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s3_S
    have elo : regValue c.R.lo (zeroHigh s6).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)),
          s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))]
        exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s6).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)),
          s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))]
        exact F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q (mHi hq)))).trans hb
    rw [eS, elo, ehi]
  have st7_zh := c.R.scl1591_correct wR nR (zeroHigh s6) r7 s6_S_zh
    (mk_zh_z s6 (fun q hq => by
      rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      rw [s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
    (by
      change (zeroHigh s6).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      rw [s6_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
        s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
      exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0)
  have loc7 := run_below20000 c.R.scl1591 sup_parts.2.2.2.1 s6 r7
  generalize hs7 : run c.R.scl1591 r7 s6 = s7 at loc7 ⊢
  have s7_F (q : Wire) (hS : q ∉ c.S) : s7.basis q = s6.basis q := by
    by_cases hq : q < 20000
    · rw [loc7.2 q hq, st7_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs7]; exact run_ge20000 c.R.scl1591 sup_parts.2.2.2.1 s6 r7 q (Nat.le_of_not_lt hq)
  have s7_S0 : regValue c.S s7.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => loc7.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st7_zh.2.1
  have s7_dlo : regValue c.R8.dlo s7.basis = a ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq)))))))).trans s2_dlo
  have s7_dhi : regValue c.R8.dhi s7.basis = b ^ 2 :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))))).trans s2_dhi
  have s7_T : regValue c.R8.T s7.basis = 2 * a * b :=
    (regValue_congr _ _ s6.basis (fun q hq => by
      change q ∈ c.T at hq
      exact s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s6_T
  have s7_z8 : regValue c.R8.z s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s7_S0 q (List.mem_of_mem_take (show q ∈ c.S.take 62 from hq)))
  have s7_zM : regValue c.R8.zM s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s7_z8 q (List.mem_of_mem_take (show q ∈ c.R8.z.take _ from hq)))
  have s7_car : regValue c.R8.carry s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      rw [s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq),
        s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)]
      exact (F4 q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s7_cin : s7.basis c.R8.cin = false := by
    change s7.basis K0.core.cin = false
    rw [s7_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
      s6_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp)),
      s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))]
    exact (F4 _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append]; omega) _ (by simp))).trans hi0
  obtain ⟨p8, f8, v8⟩ := c.R8.m8z_correct wR8 nR8 s7 r8 (a * b)
    (fun q hq => (regValue_zero _ _).mp s7_car q (List.mem_of_mem_take hq))
    (by rw [s7_T]; ring) s7_cin
  generalize hs8 : run c.R8.m8z r8 s7 = s8 at p8 f8 v8 ⊢
  have s8_F (q : Wire) (hd : q ∉ c.dst) : s8.basis q = s7.basis q :=
    f8 q (fun h => hd (List.mem_of_mem_drop (show q ∈ c.dst.drop 64 from h)))
  have st8_dmid : regValue c.R8.dmid s8.basis = 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) := by
    have hm := dmid_val c v s7.basis; rw [s7_dlo, s7_dhi] at hm
    rw [v8, regValue_append, s7_T, s7_zM, hm, s7_cin]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false]
    apply Nat.mod_eq_of_lt
    have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
      simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
    have hlt : a + 2 ^ 64 * b < 2 ^ c.n := by
      have hbl : c.n = c.R.bank.length := v.bankLen.symm
      rw [← bv64, hbl]; exact regValue_lt c.R.bank s.basis
    have hsq : (a + 2 ^ 64 * b) ^ 2 < 2 ^ (2 * c.n) := by
      have := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0); simpa [← Nat.pow_mul, Nat.mul_comm] using this
    have hle : 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) ≤ (a + 2 ^ 64 * b) ^ 2 := by
      have h1 : 2 ^ 64 * (a ^ 2 / 2 ^ 64) ≤ a ^ 2 := Nat.mul_div_le (a ^ 2) (2 ^ 64)
      have h2 : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      have h3 : 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) =
          2 ^ 64 * (a ^ 2 / 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      rw [h2, h3]; exact Nat.add_le_add_right h1 _
    have hdmid : c.R8.dmid.length = 2 * c.n - 64 := by simp [KRegs.dmid, SplitCfg.R8, v.dstLen]
    rw [hdmid]
    have hpow : 2 ^ 64 * 2 ^ (2 * c.n - 64) = 2 ^ (2 * c.n) := by rw [← Nat.pow_add]; congr 1; rcases v.hn with h | h <;> omega
    exact Nat.lt_of_mul_lt_mul_left (hpow.symm ▸ Nat.lt_of_le_of_lt hle hsq)
  refine ⟨p8.trans (loc7.1.trans (st7_zh.1.trans (loc6.1.trans (st6_zh.1.trans (loc5.1.trans (st5_zh.1.trans (st4.1.trans (loc3.1.trans (st3_zh.1.trans (st2.1.trans st1.1)))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s8.basis
    rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
    have hlo64 : regValue (c.dst.take 64) s8.basis = a ^ 2 % 2 ^ 64 := by
      have e : regValue (c.dst.take 64) s8.basis = regValue (c.dst.take 64) s7.basis :=
        regValue_congr _ _ _ (fun q hq => by
          apply f8
          have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
          rw [← List.take_append_drop 64 c.dst] at hnd
          exact fun hm => (List.nodup_append.mp hnd).2.2 q hq q hm rfl)
      rw [e, show c.dst.take 64 = c.R8.dlo.take 64 from by simp [KRegs.dlo, SplitCfg.R8, List.take_take],
        regValue_take_mod c.R8.dlo 64 (by simp [KRegs.dlo, SplitCfg.R8, v.dstLen]; rcases v.hn with h | h <;> omega), s7_dlo]
    have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
    have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
      simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
    rw [hsplit, hlen64, hlo64, st8_dmid, show c.bank = c.R.bank from rfl, bv64]
    have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
    have hring : a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) =
        (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
    rw [hring, hdiv]; ring
  · exact (regValue_congr _ _ s7.basis (fun q hq => s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s7_T
  · exact (regValue_congr _ _ s2.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))))).trans s2_T1
  · exact (regValue_congr _ _ s2.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))))).trans s2_T2
  · exact (regValue_congr _ _ s4.basis (fun q hq =>
      (s8_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s7_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))))).trans s4_T5
  · intro q hd hL
    have hT : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    rw [s8_F q hd]
    by_cases hS : q ∈ c.S
    · exact ((regValue_zero _ _).mp s7_S0 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (s7_F q hS).trans ((s6_F q hT).trans ((s5_F q hT).trans (F4 q hd hS hL)))

/-- Exact postcondition of `c.clear` restoring `dst` and `liveT` to 0. -/
theorem cfg_clear_correct (c : SplitCfg) (v : CfgValid c) (s : State) (m : List Bool)
    (hd0 : regValue c.dst s.basis = (regValue c.bank s.basis) ^ 2)
    (hT : regValue c.T s.basis = 2 * regValue c.R.lo s.basis * regValue c.R.hi s.basis)
    (hT1 : regValue c.T1 s.basis = 2 * (regValue c.R.lo s.basis % 2 ^ 32) * (regValue c.R.lo s.basis / 2 ^ 32))
    (hT2 : regValue c.T2 s.basis = 2 * (regValue c.R.hi s.basis % 2 ^ c.Q2.h) * (regValue c.R.hi s.basis / 2 ^ c.Q2.h))
    (hT5 : regValue c.T5 s.basis = 2 * ((regValue c.R.lo s.basis + regValue c.R.hi s.basis) % 2 ^ 33) *
      ((regValue c.R.lo s.basis + regValue c.R.hi s.basis) / 2 ^ 33))
    (hSc0 : regValue c.cleanScratch s.basis = 0)
    (hi0 : s.basis K0.core.cin = false) :
    let u := run c.clear m s
    u.phase = s.phase ∧
    regValue c.dst u.basis = 0 ∧
    regValue c.liveT u.basis = 0 ∧
    ∀ q, q ∉ c.dst → q ∉ c.liveT → u.basis q = s.basis q := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  obtain ⟨nR, nR8, n1, n2, n5⟩ := cfg_nodups c v
  have sup := cfg_support c v; have hr := v.realNd
  have dj {A B : List Wire} (h : ∀ q, A.count q + B.count q ≤ c.realAll.count q) : ∀ q ∈ A, q ∉ B := kdis hr h
  have zOf (r : List Wire) (sub : ∀ q ∈ r, q ∈ c.cleanScratch) : regValue r s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hSc0 q (sub q hq))
  have hS0 : regValue c.S s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hz40 : regValue c.zReal4 s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hpad0 : regValue K0.leafPad s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hcar0 : regValue c.carry s.basis = 0 := zOf _ (fun q h => by simp [SplitCfg.cleanScratch, h])
  have hzpad0 : s.basis c.zpad = false := (regValue_zero _ _).mp hSc0 c.zpad (by simp [SplitCfg.cleanScratch])
  have hzd0 : s.basis c.zdst0 = false := (regValue_zero _ _).mp hSc0 c.zdst0 (by simp [SplitCfg.cleanScratch])
  have hzd1 : s.basis c.zdst1 = false := (regValue_zero _ _).mp hSc0 c.zdst1 (by simp [SplitCfg.cleanScratch])
  have bv := c.R.bank_value wR s.basis
  obtain ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10⟩ := c.R.lens wR
  generalize ha : regValue c.R.lo s.basis = a at hT hT1 hT5 ⊢
  generalize hb : regValue c.R.hi s.basis = b at hT hT2 hT5 ⊢
  have aLt : a < 2 ^ 64 := by rw [← ha]; simpa [L0] using regValue_lt c.R.lo s.basis
  have bLt : b < 2 ^ (c.n - 64) := by
    rw [← hb]; have h := regValue_lt c.R.hi s.basis
    rw [L1, show c.R.bank.length = c.n from v.bankLen, show c.R.h = 64 from rfl] at h; exact h
  have realStep (P : Program) (hp : wires P ⊆ c.realAll.toFinset) : ∀ q ∈ wires P, q < 20000 :=
    fun q hq => v.realLt q (List.mem_toFinset.mp (hp hq))
  have sup_parts : (∀ q ∈ wires c.R8.c8z, q < 20000) ∧ (∀ q ∈ wires c.R.smkT, q < 20000) ∧
      (∀ q ∈ wires c.R.c7t, q < 20000) ∧ (∀ q ∈ wires c.R.c6h, q < 20000) ∧
      (∀ q ∈ wires c.R.scl1591, q < 20000) := by
    have sc := sup.2
    simp only [SplitCfg.clear, wires_append, Finset.union_subset_iff] at sc
    exact ⟨realStep _ sc.1.1.1.1.1.1.1, realStep _ sc.1.1.1.1.1.1.2, realStep _ sc.1.1.1.1.1.2,
      realStep _ sc.1.1.1.1.2, realStep _ sc.1.1.2⟩
  obtain ⟨a7, r8, e8⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591 ++ LowZero18Diagonal.clearC c.Q2)
    (LowZero18Diagonal.clearC c.Q1) m s
  obtain ⟨a6, r7, e7⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5 ++ c.R.scl1591) (LowZero18Diagonal.clearC c.Q2) a7 s
  obtain ⟨a5, r6, e6⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h ++
    LowZero18Diagonal.clearC c.Q5) c.R.scl1591 a6 s
  obtain ⟨a4, r5, e5⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t ++ c.R.c6h)
    (LowZero18Diagonal.clearC c.Q5) a5 s
  obtain ⟨a3, r4, e4⟩ := kseq (c.R8.c8z ++ c.R.smkT ++ c.R.c7t) c.R.c6h a4 s
  obtain ⟨a2, r3, e3⟩ := kseq (c.R8.c8z ++ c.R.smkT) c.R.c7t a3 s
  obtain ⟨r1, r2, e2⟩ := kseq c.R8.c8z c.R.smkT a2 s
  dsimp only
  rw [SplitCfg.clear, e8, e7, e6, e5, e4, e3, e2]
  have mLo {q : Wire} (h : q ∈ c.R.lo) : q ∈ c.bank := List.mem_of_mem_take (show q ∈ c.bank.take 64 from h)
  have mHi {q : Wire} (h : q ∈ c.R.hi) : q ∈ c.bank := List.mem_of_mem_drop (show q ∈ c.bank.drop 64 from h)
  have mDlo {q : Wire} (h : q ∈ c.R.dlo) : q ∈ c.dst := List.mem_of_mem_take (show q ∈ c.dst.take 128 from h)
  have mDhi {q : Wire} (h : q ∈ c.R.dhi) : q ∈ c.dst := List.mem_of_mem_drop (show q ∈ c.dst.drop 128 from h)
  have bLtR : b < 2 ^ (c.R.bank.length - c.R.h) := by simpa [SplitCfg.R, v.bankLen] using bLt
  have hTl := wR.T; have hSl := wR.S; have hhR := wR.hh; have h4R := wR.h4; have hclR := wR.carry
  have ex : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
  have sumLt : a + b < 2 ^ c.R.S.length := by
    have hp : 2 ^ c.R.h ≤ 2 ^ (c.R.bank.length - c.R.h) := Nat.pow_le_pow_right (by decide) (by clear * - hhR; omega)
    have hq : 2 ^ c.R.S.length = 2 * 2 ^ (c.R.bank.length - c.R.h) := by rw [hSl, pow_succ]; ring
    have haR : a < 2 ^ c.R.h := aLt
    clear * - haR bLtR hp hq; omega
  have sqLt : (a + b) ^ 2 < 2 ^ c.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have bv64 : regValue c.R.bank s.basis = a + 2 ^ 64 * b := by
    simpa only [show c.R.h = 64 from rfl, ha, hb] using bv
  have hdmid_init : regValue c.R8.dmid s.basis = 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) := by
    have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s.basis
    rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
    have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
    rw [hsplit, hlen64, show c.bank = c.R.bank from rfl, bv64] at hd0
    have hlt64 : regValue (c.dst.take 64) s.basis < 2 ^ 64 := by have := regValue_lt (c.dst.take 64) s.basis; rwa [hlen64] at this
    have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
    have hmod_lt : a ^ 2 % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have hsq : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by
      calc (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
      _ = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by rw [hdiv]
      _ = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by ring
    rw [hsq] at hd0
    have hdivq := congrArg (· / 2 ^ 64) hd0
    dsimp only at hdivq
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64), Nat.add_mul_div_left _ _ (by decide : 0 < 2 ^ 64),
      Nat.div_eq_of_lt hlt64, Nat.div_eq_of_lt hmod_lt] at hdivq
    simpa only [Nat.zero_add] using hdivq
  obtain ⟨p1, f1, v1⟩ := c.R8.c8z_correct wR8 nR8 s r1
    (fun q hq => (regValue_zero _ _).mp hcar0 q (List.mem_of_mem_take hq))
    (by
      rw [LowZero.head_false_of_even c.R8.T c.R8.zM s.basis (a * b)
        (by rw [show c.R8.T = c.T from rfl, hT]; ring) (c.R8.T_ne wR8)]
      rfl)
    hi0
  generalize hs1 : run c.R8.c8z r1 s = s1 at p1 f1 v1 ⊢
  have s1_F (q : Wire) (hd : q ∉ c.dst) : s1.basis q = s.basis q :=
    f1 q (fun h => hd (List.mem_of_mem_drop (show q ∈ c.dst.drop 64 from h)))
  have st1_dmid : regValue c.R8.dmid s1.basis = a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2 := by
    have s_zM : regValue c.R8.zM s.basis = 0 :=
      (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hS0 q
        (List.mem_of_mem_take (show q ∈ c.S.take 62 from List.mem_of_mem_take (show q ∈ c.R8.z.take _ from hq))))
    have hlt : 2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2) < 2 ^ c.R8.dmid.length := by
      rw [← hdmid_init]; exact regValue_lt c.R8.dmid s.basis
    rw [v1, regValue_append, show c.R8.T = c.T from rfl, hT, s_zM, hdmid_init, show c.R8.cin = K0.core.cin from rfl, hi0]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false, Nat.sub_zero]
    rw [ksubmod _ _ _ (Nat.le_add_right _ _) hlt]
    exact Nat.add_sub_cancel_left _ _
  have s1_dst_eq : regValue c.dst s1.basis = a ^ 2 + 2 ^ 128 * b ^ 2 := by
    have hsplit := regValue_append (c.dst.take 64) c.R8.dmid s1.basis
    rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst] at hsplit
    have hlen64 : (c.dst.take 64).length = 64 := by simp [v.dstLen]; rcases v.hn with h | h <;> omega
    have hlo64 : regValue (c.dst.take 64) s1.basis = a ^ 2 % 2 ^ 64 := by
      have e : regValue (c.dst.take 64) s1.basis = regValue (c.dst.take 64) s.basis :=
        regValue_congr _ _ _ (fun q hq => by
          apply f1
          have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
          rw [← List.take_append_drop 64 c.dst] at hnd
          exact fun hm => (List.nodup_append.mp hnd).2.2 q hq q hm rfl)
      rw [e]
      have hsp := regValue_append (c.dst.take 64) c.R8.dmid s.basis
      rw [show c.dst.take 64 ++ c.R8.dmid = c.dst from List.take_append_drop 64 c.dst, hlen64] at hsp
      rw [hsp, hdmid_init, show c.bank = c.R.bank from rfl, bv64] at hd0
      have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
      have hsq : (a + 2 ^ 64 * b) ^ 2 = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by
        calc (a + 2 ^ 64 * b) ^ 2 = a ^ 2 + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by ring
        _ = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 64 * (2 * a * b + 2 ^ 64 * b ^ 2) := by rw [hdiv]
        _ = a ^ 2 % 2 ^ 64 + 2 ^ 64 * (2 * a * b + (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)) := by ring
      rw [hsq] at hd0
      exact Nat.add_right_cancel hd0
    rw [hsplit, hlen64, hlo64, st1_dmid]
    have hdiv := Nat.div_add_mod (a ^ 2) (2 ^ 64)
    calc a ^ 2 % 2 ^ 64 + 2 ^ 64 * (a ^ 2 / 2 ^ 64 + 2 ^ 64 * b ^ 2)
        = (2 ^ 64 * (a ^ 2 / 2 ^ 64) + a ^ 2 % 2 ^ 64) + 2 ^ 128 * b ^ 2 := by ring
      _ = a ^ 2 + 2 ^ 128 * b ^ 2 := by rw [hdiv]
  have s1_dlo : regValue c.R.dlo s1.basis = a ^ 2 := by
    have h128 := regValue_append c.R.dlo c.R.dhi s1.basis
    rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst, L2, show c.R.h = 64 from rfl, s1_dst_eq] at h128
    have ha2 : a ^ 2 < 2 ^ 128 := by have := Nat.pow_lt_pow_left aLt (by decide : 2 ≠ 0); simpa [← Nat.pow_mul] using this
    have hdloLt : regValue c.R.dlo s1.basis < 2 ^ 128 := by have := regValue_lt c.R.dlo s1.basis; rwa [L2, show c.R.h = 64 from rfl] at this
    have hmod := congrArg (· % 2 ^ 128) h128
    dsimp only at hmod
    rw [show (2 : Nat) ^ (2 * 64) = 2 ^ 128 from rfl,
      Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdloLt, Nat.mod_eq_of_lt ha2] at hmod
    exact hmod.symm
  have s1_dhi : regValue c.R.dhi s1.basis = b ^ 2 := by
    have h128 := regValue_append c.R.dlo c.R.dhi s1.basis
    rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst, L2, show c.R.h = 64 from rfl,
      show (2 : Nat) ^ (2 * 64) = 2 ^ 128 from rfl, s1_dst_eq, s1_dlo] at h128
    exact (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2 ^ 128) (Nat.add_left_cancel h128)).symm
  have mk_zh_z (t : State) (ht : ∀ q ∈ c.zReal4, t.basis q = false) : regValue c.R.z (zeroHigh t).basis = 0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    simp only [SplitCfg.R, List.mem_append] at hq
    rcases hq with hq | hq
    · simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]; exact ht q hq
    · simp only [zeroHigh, (List.mem_range'_1.mp hq).1, if_true]
  have s1_T_zh : regValue c.R.T (zeroHigh s1).basis = 2 * regValue c.R.lo (zeroHigh s1).basis * regValue c.R.hi (zeroHigh s1).basis := by
    have eT : regValue c.R.T (zeroHigh s1).basis = 2 * a * b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        change q ∈ c.T at hq
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT
    have elo : regValue c.R.lo (zeroHigh s1).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s1).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    rw [eT, elo, ehi]
  have s1_S0_zh : regValue c.R.S (zeroHigh s1).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.S at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hS0 q hq))
  have s1_car0_zh : regValue c.R.carry (zeroHigh s1).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s1_cin0_zh : (zeroHigh s1).basis c.R.cin = false := by
    change (zeroHigh s1).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s1_z0_zh : regValue c.R.z (zeroHigh s1).basis = 0 :=
    mk_zh_z s1 (fun q hq => (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))
  have smkT_eq := c.R.smkT_run wR nR (zeroHigh s1) r2 s1_T_zh s1_S0_zh s1_cin0_zh
  have st2_zh := c.R.smk_correct wR nR (zeroHigh s1) r2 s1_S0_zh s1_z0_zh s1_car0_zh s1_cin0_zh
  rw [← smkT_eq] at st2_zh
  have loc2 := run_below20000 c.R.smkT sup_parts.2.1 s1 r2
  generalize hs2 : run c.R.smkT r2 s1 = s2 at loc2 ⊢
  have s2_F (q : Wire) (hS : q ∉ c.S) : s2.basis q = s1.basis q := by
    by_cases hq : q < 20000
    · rw [loc2.2 q hq, st2_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs2]; exact run_ge20000 c.R.smkT sup_parts.2.1 s1 r2 q (Nat.le_of_not_lt hq)
  have s2_S : regValue c.S s2.basis = a + b := by
    have e1 := regValue_congr c.S s2.basis (run c.R.smkT r2 (zeroHigh s1)).basis
      (fun q hq => loc2.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))
    rw [e1, show c.S = c.R.S from rfl, st2_zh.2.1]
    have elo : regValue c.R.lo (zeroHigh s1).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s1).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    rw [elo, ehi]
  have s2_dhi_zh : regValue c.R.dhi (zeroHigh s2).basis = b ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDhi hq, true_or, or_true])), if_false]
      exact s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))).trans s1_dhi
  have s2_T_zh : regValue c.R.T (zeroHigh s2).basis = 2 * a * b :=
    (regValue_congr _ _ s.basis (fun q hq => by
      change q ∈ c.T at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        (s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))).trans hT
  have s2_z_zh : regValue c.R.z (zeroHigh s2).basis = 0 :=
    mk_zh_z s2 (fun q hq => (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq)))
  have s2_zB_zh : regValue c.R.zB (zeroHigh s2).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s2_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have s2_car_zh : regValue c.R.carry (zeroHigh s2).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq)))
  have s2_cin_zh : (zeroHigh s2).basis c.R.cin = false := by
    change (zeroHigh s2).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (s2_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
      ((s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0)
  have xv2 : regValue (c.R.dhi ++ c.R.zB) (zeroHigh s2).basis = b ^ 2 := by
    rw [regValue_append, s2_dhi_zh, s2_zB_zh]; simp
  have st3_zh : (run c.R.c7t r3 (zeroHigh s2)).phase = (zeroHigh s2).phase ∧
      regValue c.R.T (run c.R.c7t r3 (zeroHigh s2)).basis = 2 * a * b + b ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.c7t r3 (zeroHigh s2)).basis q = (zeroHigh s2).basis q := by
    obtain ⟨p, f, val⟩ := c.R.c7t_correct wR nR (zeroHigh s2) r3
      (fun q hq => (regValue_zero _ _).mp s2_car_zh q (List.mem_of_mem_take hq))
      (by
        have hT' := LowZero.head_false_of_even c.R.T [] (zeroHigh s2).basis (a * b) (by rw [s2_T_zh]; ring) (c.R.T_ne wR)
        rw [List.append_nil] at hT'
        rw [hT']; exact Bool.and_false _)
      s2_cin_zh
      (by rw [KRegs.bit1 c.R.dhi c.R.zB (zeroHigh s2).basis (c.R.dhi_two wR), s2_dhi_zh, KRegs.sq_bit1]; rfl)
      (fun _ => by rw [xv2, hTl, hSl]; exact KRegs.sq_trim_bound c.R.bank.length c.R.h b bLtR)
      (fun tc => by
        have tb := KRegs.trim_bound c.R.bank.length c.R.h a b tc aLt bLtR
        rw [xv2, s2_T_zh, hTl, hSl, Nat.mod_eq_of_lt (by clear * - tb; omega)]; clear * - tb; omega)
    refine ⟨p, ?_, f⟩
    rw [val, xv2, s2_T_zh, s2_cin_zh]
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by clear * - ex sqLt; omega)]; ring
  have loc3 := run_below20000 c.R.c7t sup_parts.2.2.1 s2 r3
  generalize hs3 : run c.R.c7t r3 s2 = s3 at loc3 ⊢
  have s3_F (q : Wire) (hT' : q ∉ c.T) : s3.basis q = s2.basis q := by
    by_cases hq : q < 20000
    · rw [loc3.2 q hq, st3_zh.2.2 q hT']; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs3]; exact run_ge20000 c.R.c7t sup_parts.2.2.1 s2 r3 q (Nat.le_of_not_lt hq)
  have s3_T : regValue c.T s3.basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc3.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st3_zh.2.1
  have s3_dlo_zh : regValue c.R.dlo (zeroHigh s3).basis = a ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq => by
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mDlo hq, true_or, or_true])), if_false]
      exact (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))).trans s1_dlo
  have s3_T_zh : regValue c.R.T (zeroHigh s3).basis = 2 * a * b + b ^ 2 :=
    (regValue_congr _ _ s3.basis (fun q hq => by
      change q ∈ c.T at hq; simp [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true]))])).trans s3_T
  have s3_z_zh : regValue c.R.z (zeroHigh s3).basis = 0 :=
    mk_zh_z s3 (fun q hq => (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))))
  have s3_zA_zh : regValue c.R.zA (zeroHigh s3).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp s3_z_zh q (List.mem_of_mem_take (show q ∈ c.R.z.take _ from hq)))
  have s3_car_zh : regValue c.R.carry (zeroHigh s3).basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s1_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))))
  have s3_cin_zh : (zeroHigh s3).basis c.R.cin = false := by
    change (zeroHigh s3).basis K0.core.cin = false
    simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
    exact (s3_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
      ((s2_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
      ((s1_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0))
  have st4_zh : (run c.R.c6h r4 (zeroHigh s3)).phase = (zeroHigh s3).phase ∧
      regValue c.R.T (run c.R.c6h r4 (zeroHigh s3)).basis = (a + b) ^ 2 ∧
      ∀ q, q ∉ c.R.T → (run c.R.c6h r4 (zeroHigh s3)).basis q = (zeroHigh s3).basis q := by
    have hn6 : (c.R.cin :: ((c.R.dlo ++ c.R.zA) ++ c.R.T ++ c.R.carry.take (c.R.T.length - 1))).Nodup :=
      knd nR (fun q => by
        have := c.R.counts q
        clear * - this
        simp only [KRegs.all, List.count_cons, List.count_append] at this ⊢; omega)
    rw [c.R.c6h_run wR hn6 (zeroHigh s3) r4
      (fun q hq => (regValue_zero _ _).mp s3_car_zh q (List.mem_of_mem_take hq))
      s3_cin_zh (c.R.c6c_bits wR (zeroHigh s3).basis a b s3_T_zh s3_dlo_zh)]
    unfold KRegs.c6
    obtain ⟨p, f, val⟩ := addInPlace_correct (c.R.dlo ++ c.R.zA) c.R.T
      (c.R.carry.take (c.R.T.length - 1)) c.R.cin hn6
      (by rw [List.length_append, L2, L6]; omega)
      (by rw [List.length_take]; omega)
      (zeroHigh s3) r4 (fun q hq => (regValue_zero _ _).mp s3_car_zh q (List.mem_of_mem_take hq))
    refine ⟨p, ?_, f⟩
    rw [val, regValue_append, s3_dlo_zh, s3_zA_zh, s3_T_zh, s3_cin_zh]
    simp only [Nat.mul_zero, Nat.add_zero, Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by linarith only [ex, sqLt]), ex]; ring
  have loc4 := run_below20000 c.R.c6h sup_parts.2.2.2.1 s3 r4
  generalize hs4 : run c.R.c6h r4 s3 = s4 at loc4 ⊢
  have s4_F (q : Wire) (hT' : q ∉ c.T) : s4.basis q = s3.basis q := by
    by_cases hq : q < 20000
    · rw [loc4.2 q hq, st4_zh.2.2 q hT']; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs4]; exact run_ge20000 c.R.c6h sup_parts.2.2.2.1 s3 r4 q (Nat.le_of_not_lt hq)
  have s4_T : regValue c.T s4.basis = (a + b) ^ 2 :=
    (regValue_congr _ _ _ (fun q hq => loc4.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st4_zh.2.1
  have s4_out (q : Wire) (hd : q ∉ c.dst) (hS : q ∉ c.S) (hT' : q ∉ c.T) : s4.basis q = s.basis q :=
    (s4_F q hT').trans ((s3_F q hT').trans ((s2_F q hS).trans (s1_F q hd)))
  have s4_S : regValue c.S s4.basis = a + b :=
    (regValue_congr _ _ s2.basis (fun q hq =>
      (s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      (s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)))).trans s2_S
  have s4_Q5_bank : regValue c.Q5.bank s4.basis = a + b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true]
      rw [regValue_snoc_zero _ _ _ ((s4_out c.zpad
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0), s4_S]
    · simpa [SplitCfg.Q5, hn] using s4_S
  have s4_Q5_dst : regValue c.Q5.dst s4.basis = (regValue c.Q5.bank s4.basis) ^ 2 := by
    rw [s4_Q5_bank]
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true, regValue_append, s4_T]
      have b0 : s4.basis c.zdst0 = false := (s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s4.basis c.zdst1 = false := (s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
    · simpa [SplitCfg.Q5, hn] using s4_T
  have s4_car0 : regValue c.carry s4.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s4_pad0 : regValue K0.leafPad s4.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s4_cin0 : s4.basis K0.core.cin = false :=
    (s4_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s4_T5 : regValue c.T5 s4.basis = 2 * ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) :=
    (regValue_congr _ _ s.basis (fun q hq => s4_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT5
  have st5 := clearC_clean c.Q5 w5.1 w5.2.1 (Or.inr w5.2.2) n5 s4 r5 s4_Q5_dst
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by
      rw [c.Q5.lo_mod w5.1, c.Q5.hi_div w5.1, s4_Q5_bank, w5.2.2]
      by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_T5)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q5, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s4_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using s4_cin0)
  generalize hs5 : run (LowZero18Diagonal.clearC c.Q5) r5 s4 = s5 at st5 ⊢
  have s5_T0 : regValue c.T s5.basis = 0 := by
    have h := st5.2.1
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q5, hn, if_true, regValue_append] at h; omega
    · simpa [SplitCfg.Q5, hn] using h
  have s5_T5_0 : regValue c.T5 s5.basis = 0 := by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using st5.2.2.1
  have s5_zd0 : s5.basis c.zdst0 = false ∧ s5.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · have h := st5.2.1; simp only [SplitCfg.Q5, hn, if_true] at h
      exact ⟨(regValue_zero _ _).mp h c.zdst0 (by simp), (regValue_zero _ _).mp h c.zdst1 (by simp)⟩
    · exact ⟨(st5.2.2.2 _ (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        (st5.2.2.2 _ (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (by simp [SplitCfg.Q5, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
  have s5_F (q : Wire) (hT' : q ∉ c.T) (hT5' : q ∉ c.T5) : s5.basis q = s4.basis q := by
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s5_zd0.1.trans ((s4_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
      · exact s5_zd0.2.trans ((s4_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
    · apply st5.2.2.2
      · by_cases hn : c.n = 128
        · simp only [SplitCfg.Q5, hn, if_true, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hT' h
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
        · simpa [SplitCfg.Q5, hn] using hT'
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q5, hn] using hT5'
  have s5_S_zh : regValue c.R.S (zeroHigh s5).basis = regValue c.R.lo (zeroHigh s5).basis + regValue c.R.hi (zeroHigh s5).basis := by
    have eS : regValue c.R.S (zeroHigh s5).basis = a + b :=
      (regValue_congr _ _ s4.basis (fun q hq => by
        change q ∈ c.S at hq
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
        exact s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s4_S
    have elo : regValue c.R.lo (zeroHigh s5).basis = a :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mLo hq, true_or, or_true])), if_false]
        exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))).trans
          (s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))))).trans ha
    have ehi : regValue c.R.hi (zeroHigh s5).basis = b :=
      (regValue_congr _ _ s.basis (fun q hq => by
        simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, mHi hq, true_or, or_true])), if_false]
        exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))).trans
          (s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
            (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))))).trans hb
    rw [eS, elo, ehi]
  have st6_zh := c.R.scl1591_correct wR nR (zeroHigh s5) r6 s5_S_zh
    (mk_zh_z s5 (fun q hq => (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
      ((s4_out q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hz40 q hq))))
    ((regValue_zero _ _).mpr (fun q hq => by
      change q ∈ c.carry at hq
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])), if_false]
      exact (s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp s4_car0 q hq)))
    (by
      change (zeroHigh s5).basis K0.core.cin = false
      simp only [zeroHigh, Nat.not_le.mpr (v.realLt K0.core.cin (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, true_or, or_true])), if_false]
      exact (s5_F _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans s4_cin0)
  have loc6 := run_below20000 c.R.scl1591 sup_parts.2.2.2.2 s5 r6
  generalize hs6 : run c.R.scl1591 r6 s5 = s6 at loc6 ⊢
  have s6_F (q : Wire) (hS : q ∉ c.S) : s6.basis q = s5.basis q := by
    by_cases hq : q < 20000
    · rw [loc6.2 q hq, st6_zh.2.2 q hS]; simp [zeroHigh, Nat.not_le.mpr hq]
    · rw [← hs6]; exact run_ge20000 c.R.scl1591 sup_parts.2.2.2.2 s5 r6 q (Nat.le_of_not_lt hq)
  have s6_S0 : regValue c.S s6.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => loc6.2 q (v.realLt q (by simp only [SplitCfg.realAll, List.mem_cons, List.mem_append, hq, true_or, or_true])))).trans st6_zh.2.1
  have s6_out (q : Wire) (hd : q ∉ c.dst) (hT' : q ∉ c.T) (hT5' : q ∉ c.T5) : s6.basis q = s.basis q := by
    by_cases hS : q ∈ c.S
    · exact ((regValue_zero _ _).mp s6_S0 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (s6_F q hS).trans ((s5_F q hT' hT5').trans (s4_out q hd hS hT'))
  have s6_Q2_bank : regValue c.Q2.bank s6.basis = b := by
    by_cases hn : c.n = 128
    · simp only [SplitCfg.Q2, hn, if_true]
      exact (regValue_congr _ _ s.basis (fun q hq => s6_out q
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
    · simp only [SplitCfg.Q2, hn, if_false]
      rw [regValue_snoc_zero _ _ _ ((s6_out c.zpad
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zpad]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzpad0)]
      exact (regValue_congr _ _ s.basis (fun q hq => s6_out q
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mHi hq)))).trans hb
  have s6_dhi : regValue c.R.dhi s6.basis = b ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq =>
      (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
      ((s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))))))).trans s1_dhi
  have s6_Q2_dst : regValue c.Q2.dst s6.basis = (regValue c.Q2.bank s6.basis) ^ 2 := by
    rw [s6_Q2_bank]
    by_cases hn : c.n = 128
    · simpa [SplitCfg.Q2, hn] using s6_dhi
    · simp only [SplitCfg.Q2, hn, if_false, regValue_append, s6_dhi]
      have b0 : s6.basis c.zdst0 = false := (s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0
      have b1 : s6.basis c.zdst1 = false := (s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1
      simp [regValue, b0, b1]
  have s6_car0 : regValue c.carry s6.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s6_pad0 : regValue K0.leafPad s6.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s6_cin0 : s6.basis K0.core.cin = false :=
    (s6_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have s6_T2 : regValue c.T2 s6.basis = 2 * (b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h) :=
    (regValue_congr _ _ s.basis (fun q hq => s6_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT2
  have st7 := clearC_clean c.Q2 w2.1 w2.2.1 w2.2.2 n2 s6 r7 s6_Q2_dst
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by
      rw [c.Q2.lo_mod w2.1, c.Q2.hi_div w2.1, s6_Q2_bank]
      by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_T2)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_pad0)
    ((regValue_zero _ _).mpr (fun q h => by
      by_cases hn : c.n = 128 <;> simp only [SplitCfg.Q2, hn, if_true, if_false] at h
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_take h)
      · exact (regValue_zero _ _).mp s6_car0 q (List.mem_of_mem_take h)))
    (by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using s6_cin0)
  generalize hs7 : run (LowZero18Diagonal.clearC c.Q2) r7 s6 = s7 at st7 ⊢
  have s7_dhi0 : regValue c.R.dhi s7.basis = 0 := by
    have h := st7.2.1
    by_cases hn : c.n = 128
    · simpa [SplitCfg.Q2, hn] using h
    · simp only [SplitCfg.Q2, hn, if_false, regValue_append] at h; omega
  have s7_T2_0 : regValue c.T2 s7.basis = 0 := by by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using st7.2.2.1
  have s7_zd0 : s7.basis c.zdst0 = false ∧ s7.basis c.zdst1 = false := by
    by_cases hn : c.n = 128
    · exact ⟨(st7.2.2.2 _ (by simp [SplitCfg.Q2, hn]; exact fun h => dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp) (mDhi h))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0),
        (st7.2.2.2 _ (by simp [SplitCfg.Q2, hn]; exact fun h => dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp) (mDhi h))
        (by simp [SplitCfg.Q2, hn]; exact dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans
        ((s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
        (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1)⟩
    · have h := st7.2.1; simp only [SplitCfg.Q2, hn, if_false] at h
      exact ⟨(regValue_zero _ _).mp h c.zdst0 (by simp), (regValue_zero _ _).mp h c.zdst1 (by simp)⟩
  have s7_F (q : Wire) (hd : q ∉ c.R.dhi) (hT2' : q ∉ c.T2) : s7.basis q = s6.basis q := by
    by_cases hzd : q = c.zdst0 ∨ q = c.zdst1
    · rcases hzd with rfl | rfl
      · exact s7_zd0.1.trans ((s6_out _ (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst0]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd0).symm
      · exact s7_zd0.2.trans ((s6_out _ (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
          (dj (A := [c.zdst1]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hzd1).symm
    · apply st7.2.2.2
      · by_cases hn : c.n = 128
        · simpa [SplitCfg.Q2, hn] using hd
        · simp only [SplitCfg.Q2, hn, if_false, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | rfl | rfl)
          · exact hd h
          · exact hzd (Or.inl rfl)
          · exact hzd (Or.inr rfl)
      · by_cases hn : c.n = 128 <;> simpa [SplitCfg.Q2, hn] using hT2'
  have dlo_dhi : ∀ q ∈ c.R.dlo, q ∉ c.R.dhi := by
    intro q h1 h2
    have hnd : c.dst.Nodup := list_nodup_of_count_le hr (fun x => by clear * - c x; rw [realAll_count]; omega)
    rw [← List.take_append_drop 128 c.dst] at hnd
    exact (List.nodup_append.mp hnd).2.2 q h1 q h2 rfl
  have s7_dlo : regValue c.R.dlo s7.basis = a ^ 2 :=
    (regValue_congr _ _ s1.basis (fun q hq =>
      (s7_F q (dlo_dhi q hq) (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s5_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s4_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
      ((s3_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))).trans
        (s2_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo hq))))))))).trans s1_dlo
  have s7_out (q : Wire) (hd : q ∉ c.dst) (hT' : q ∉ c.T) (hT2' : q ∉ c.T2) (hT5' : q ∉ c.T5) : s7.basis q = s.basis q :=
    (s7_F q (fun h => hd (mDhi h)) hT2').trans (s6_out q hd hT' hT5')
  have s7_lo : regValue c.Q1.bank s7.basis = a :=
    (regValue_congr _ _ s.basis (fun q hq => s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq))
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mLo hq)))).trans ha
  have s7_T1 : regValue c.T1 s7.basis = 2 * (a % 2 ^ 32) * (a / 2 ^ 32) :=
    (regValue_congr _ _ s.basis (fun q hq => s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans hT1
  have s7_car0 : regValue c.carry s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hcar0 q hq))
  have s7_pad0 : regValue K0.leafPad s7.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (s7_out q
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)
      (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans ((regValue_zero _ _).mp hpad0 q hq))
  have s7_cin0 : s7.basis K0.core.cin = false :=
    (s7_out _ (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))
      (dj (A := [K0.core.cin]) (fun x => by clear * - c x; rw [realAll_count]; omega) _ (by simp))).trans hi0
  have st8 := clearC_clean c.Q1 w1.1 w1.2 (Or.inl rfl) n1 s7 r8 (by rw [s7_lo]; exact s7_dlo)
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    (by rw [c.Q1.lo_mod w1.1, c.Q1.hi_div w1.1, s7_lo]; exact s7_T1)
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_drop (List.mem_of_mem_take h))))
    s7_pad0
    ((regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp s7_car0 q (List.mem_of_mem_take h)))
    s7_cin0
  generalize hs8 : run (LowZero18Diagonal.clearC c.Q1) r8 s7 = s8 at st8 ⊢
  have s8_F (q : Wire) (hd : q ∉ c.R.dlo) (hT1' : q ∉ c.T1) : s8.basis q = s7.basis q := st8.2.2.2 q hd hT1'
  refine ⟨st8.1.trans (st7.1.trans (loc6.1.trans (st6_zh.1.trans (st5.1.trans (loc4.1.trans (st4_zh.1.trans (loc3.1.trans (st3_zh.1.trans (loc2.1.trans (st2_zh.1.trans p1)))))))))),
    ?_, ?_, ?_⟩
  · have h128 := regValue_append c.R.dlo c.R.dhi s8.basis
    rw [show c.R.dlo ++ c.R.dhi = c.dst from List.take_append_drop 128 c.dst] at h128
    have hdhi : regValue c.R.dhi s8.basis = 0 :=
      (regValue_congr _ _ s7.basis (fun q hq => s8_F q (fun h => dlo_dhi q h hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi hq)))).trans s7_dhi0
    rw [h128, show c.R.dlo = c.Q1.dst from rfl, st8.2.1, hdhi]; simp
  · have hT_z : regValue c.T s8.basis = 0 :=
      (regValue_congr _ _ s5.basis (fun q hq =>
        (s8_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq (mDlo h))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s7_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq (mDhi h))
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s5_T0
    have hT2_z : regValue c.T2 s8.basis = 0 :=
      (regValue_congr _ _ s7.basis (fun q hq => s8_F q
        (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo h) hq)
        (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))).trans s7_T2_0
    have hT5_z : regValue c.T5 s8.basis = 0 :=
      (regValue_congr _ _ s5.basis (fun q hq =>
        (s8_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDlo h) hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
        ((s7_F q (fun h => dj (fun x => by clear * - c x; rw [realAll_count]; omega) q (mDhi h) hq)
          (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq)).trans
          (s6_F q (dj (fun x => by clear * - c x; rw [realAll_count]; omega) q hq))))).trans s5_T5_0
    simp only [SplitCfg.liveT, regValue_append, hT_z, show c.T1 = c.Q1.T from rfl, st8.2.2.1, hT2_z, hT5_z]
    simp
  · intro q hd hL
    have hT' : q ∉ c.T := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT1' : q ∉ c.T1 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT2' : q ∉ c.T2 := fun h => hL (by simp [SplitCfg.liveT, h])
    have hT5' : q ∉ c.T5 := fun h => hL (by simp [SplitCfg.liveT, h])
    exact (s8_F q (fun h => hd (mDlo h)) hT1').trans (s7_out q hd hT' hT2' hT5')

theorem cfg_counts_H (c : SplitCfg) (v : CfgValid c) (hn : c.n = 128) (src dst : List Wire)
    (hs : src.length = 128) (hd : dst.length = 256) :
    let oldK := LowZero18LowK.kg K0 E0 src dst
    toffoliCount c.make + toffoliCount c.clear + 374 =
      toffoliCount (LowZero18Square.make K0 oldK) + toffoliCount (LowZero18Square.clear K0 oldK) ∧
    measurementCount c.make + measurementCount c.clear + 197 =
      measurementCount (LowZero18Square.make K0 oldK) + measurementCount (LowZero18Square.clear K0 oldK) := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have wOld := LowZero18LowK.oregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wiOld := LowZero18LowK.iregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wjOld := LowZero18LowK.jregsH_W K0 hwK E0 src dst hs (by omega) hext.len
  have m8_R8 := c.R8.m8z_counts wR8; have c8_R8 := c.R8.c8z_counts wR8
  have m8_R := c.R.m8z_counts wR; have c8_R := c.R.c8z_counts wR
  have bR : c.R.bank.length = 128 := by simp [SplitCfg.R, v.bankLen, hn]
  have bOld : (LowZero18LowK.oregs K0 E0 src dst).bank.length = 128 := by
    simp [LowZero18LowK.oregs, (K0.measured_bank_widths hwK).1, hs]
  have hOldH : (LowZero18LowK.oregs K0 E0 src dst).h = 64 := rfl
  have biOld : (LowZero18LowK.iregs K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.iregs, KRegs.lo, bOld, hOldH]
  have bjOld : (LowZero18LowK.jregsH K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.jregsH, KRegs.hi, bOld, hOldH]
  have oldEq : LowZero18LowK.kg K0 E0 src dst = LowZero18LowK.kgH K0 E0 src dst := by simp [LowZero18LowK.kg, hs]
  have om := LowZero18KG.make_counts (LowZero18LowK.kgH K0 E0 src dst) wOld
  have oc := LowZero18KG.clear_counts (LowZero18LowK.kgH K0 E0 src dst) wOld
  have pm := LowZero18Square.patchKG_counts K0 (LowZero18LowK.kg K0 E0 src dst)
  let K :=
    { LowZero18LowK.kgH K0 E0 src dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have nm := LowZero18KG.make_counts K wR
  have nc := LowZero18KG.clear_counts K wR
  have m8z_eq : toffoliCount c.R8.m8z = toffoliCount c.R.m8z ∧ measurementCount c.R8.m8z = measurementCount c.R.m8z ∧
      toffoliCount c.R8.c8z = toffoliCount c.R.c8z ∧ measurementCount c.R8.c8z = measurementCount c.R.c8z := by
    have lR := c.R.m8z_lens wR; have lR8 := c.R8.m8z_lens wR8
    have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
    have a1 := addInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have a2 := addInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have s1 := subInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have s2 := subInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have m8t : toffoliCount c.R8.m8 = toffoliCount c.R.m8 := by simp only [KRegs.m8, a1.1, a2.1]; rw [hd8]
    have m8m : measurementCount c.R8.m8 = measurementCount c.R.m8 := by simp only [KRegs.m8, a1.2, a2.2]; rw [hd8]
    have c8t : toffoliCount c.R8.c8 = toffoliCount c.R.c8 := by simp only [KRegs.c8, s1.1, s2.1]; rw [hd8]
    have c8m : measurementCount c.R8.c8 = measurementCount c.R.c8 := by simp only [KRegs.c8, s1.2, s2.2]; rw [hd8]
    exact ⟨by linarith only [m8_R8.1, m8_R.1, m8t], by linarith only [m8_R8.2, m8_R.2, m8m],
      by linarith only [c8_R8.1, c8_R.1, c8t], by linarith only [c8_R8.2, c8_R.2, c8m]⟩
  have hNewM : toffoliCount c.make = toffoliCount (LowZero18KG.make K) ∧
      measurementCount c.make = measurementCount (LowZero18KG.make K) := by
    simp only [SplitCfg.make, LowZero18KG.make, K, toffoliCount_append, measurementCount_append, m8z_eq.1, m8z_eq.2.1]
    exact ⟨by ring, by ring⟩
  have hNewC : toffoliCount c.clear = toffoliCount (LowZero18KG.clear K) ∧
      measurementCount c.clear = measurementCount (LowZero18KG.clear K) := by
    simp only [SplitCfg.clear, LowZero18KG.clear, K, toffoliCount_append, measurementCount_append, m8z_eq.2.2.1, m8z_eq.2.2.2]
    exact ⟨by ring, by ring⟩
  have c_eq32 (A B : KRegs) (wA : A.W) (wB : B.W) (hA : A.h = 32) (hB : B.h = 32)
      (bA : A.bank.length = 64) (bB : B.bank.length = 64) :
      DiagSq.cost A = DiagSq.cost B ∧ DiagSq.parR A = DiagSq.parR B := by
    have sA : A.S.length = 33 := by have := wA.S; omega
    have sB : B.S.length = 33 := by have := wB.S; omega
    have loA : A.lo.length = 32 := by simp [KRegs.lo, bA, hA]
    have loB : B.lo.length = 32 := by simp [KRegs.lo, bB, hB]
    have hiA : A.hi.length = 32 := by simp [KRegs.hi, bA, hA]
    have hiB : B.hi.length = 32 := by simp [KRegs.hi, bB, hB]
    exact ⟨by simp [DiagSq.cost, bA, bB, hA, hB], by simp [DiagSq.parR, loA, loB, hiA, hiB, sA, sB]⟩
  have eQ1 := c_eq32 c.Q1 (LowZero18LowK.iregs K0 E0 src dst) w1.1 wiOld rfl rfl
    (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]) biOld
  have eQ2 := c_eq32 c.Q2 (LowZero18LowK.jregsH K0 E0 src dst) w2.1 wjOld
    (by simp [SplitCfg.Q2, hn]) rfl (by simp [SplitCfg.Q2, hn, KRegs.hi, SplitCfg.R, v.bankLen]) bjOld
  have q1_m := makeC_counts c.Q1 w1.1 w1.2; have q1_c := RawClearSquare.clear_counts c.Q1 w1.1 w1.2
  have q1_d := diag32_counts c.Q1 w1.1 rfl (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn])
  have qi_m := makeC_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_c := RawClearSquare.clear_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_d := diag32_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld rfl biOld
  have hQ1 : toffoliCount K.Q1 + toffoliCount K.Q1c =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q1 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q1c ∧
      measurementCount K.Q1 + measurementCount K.Q1c =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q1 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q1c := by
    have b1 : c.Q1.bank.length = 64 := by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]
    have h1 : c.Q1.h = 32 := rfl
    have hi : (LowZero18LowK.iregs K0 E0 src dst).h = 32 := rfl
    have ⟨_, _, q1d3, q1d4⟩ := q1_d
    have ⟨_, _, qid3, qid4⟩ := qi_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q1) = toffoliCount (RawClearSquare.clear c.Q1) + 31 at q1d3
    change measurementCount (LowZero18Diagonal.clearC c.Q1) = measurementCount (RawClearSquare.clear c.Q1) + 32 at q1d4
    change toffoliCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      toffoliCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 31 at qid3
    change measurementCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      measurementCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 32 at qid4
    simp only [K, LowZero18LowK.kgH]
    rw [b1, h1] at q1_m; rw [h1] at q1_c; rw [biOld, hi] at qi_m; rw [hi] at qi_c
    exact ⟨by clear * - q1_m q1_c q1d3 qi_m qi_c qid3 eQ1; omega,
      by clear * - q1_m q1_c q1d4 qi_m qi_c qid4 eQ1; omega⟩
  have q2_m := LowZero18Diagonal.make_counts c.Q2 w2.1 w2.2.1; have q2_c := RawClearSquare.clear_counts c.Q2 w2.1 w2.2.1
  have q2_d := diag32_counts c.Q2 w2.1 (by simp [SplitCfg.Q2, hn]) (by simp [SplitCfg.Q2, hn, KRegs.hi, SplitCfg.R, v.bankLen])
  have qj_m := LowZero18Diagonal.make_counts (LowZero18LowK.jregsH K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have qj_c := RawClearSquare.clear_counts (LowZero18LowK.jregsH K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have hQ2 : toffoliCount K.Q2 + toffoliCount K.Q2c =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q2 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q2c + 31 ∧
      measurementCount K.Q2 + measurementCount K.Q2c =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q2 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q2c + 64 := by
    have h2 : c.Q2.h = 32 := by simp [SplitCfg.Q2, hn]
    have hj : (LowZero18LowK.jregsH K0 E0 src dst).h = 32 := rfl
    have ⟨q2d1, q2d2, q2d3, q2d4⟩ := q2_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q2) = toffoliCount (RawClearSquare.clear c.Q2) + 31 at q2d3
    change measurementCount (LowZero18Diagonal.clearC c.Q2) = measurementCount (RawClearSquare.clear c.Q2) + 32 at q2d4
    simp only [K, LowZero18LowK.kgH, LowZero18Diagonal.clear]
    rw [h2] at q2_c; rw [hj] at qj_c
    exact ⟨by clear * - q2_m q2_c q2d1 q2d3 qj_m qj_c eQ2; omega,
      by clear * - q2_m q2_c q2d2 q2d4 qj_m qj_c eQ2; omega⟩
  have q5_e := diag33_exact c.Q5 w5.1 w5.2.2 (by rw [w5.2.1, w5.2.2])
  have q5_old := tsq65_exact (LowZero18LowK.oregs K0 E0 src dst).S (LowZero18LowK.oregs K0 E0 src dst).T
    (LowZero18LowK.oregs K0 E0 src dst).pad (LowZero18LowK.oregs K0 E0 src dst).carry
    (LowZero18LowK.oregs K0 E0 src dst).cin
    (by have hOS := wOld.S; rw [bOld, hOldH] at hOS; omega)
    (by have hOT := wOld.T; have hOS := wOld.S; rw [bOld, hOldH] at hOS; omega)
    wOld.pad (by have := wOld.carry; omega)
  have hQ5 : toffoliCount K.Q5 + toffoliCount K.Q5c + 405 =
      toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q5 + toffoliCount (LowZero18LowK.kgH K0 E0 src dst).Q5c ∧
      measurementCount K.Q5 + measurementCount K.Q5c + 261 =
      measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q5 + measurementCount (LowZero18LowK.kgH K0 E0 src dst).Q5c := by
    simp only [K, LowZero18LowK.kgH]
    exact ⟨by clear * - q5_e q5_old; omega, by clear * - q5_e q5_old; omega⟩
  have hOldT : toffoliCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.make (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.1, oldEq]
  have hOldM : measurementCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.make (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.1, oldEq]
  have hOldCT : toffoliCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.clear (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.2.1, oldEq]
  have hOldCM : measurementCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.clear (LowZero18LowK.kgH K0 E0 src dst)) := by rw [pm.2.2.2, oldEq]
  dsimp only
  rw [hNewM.1, hNewM.2, hNewC.1, hNewC.2, hOldT, hOldM, hOldCT, hOldCM]
  have hKR : K.R = c.R := rfl
  have hOR : (LowZero18LowK.kgH K0 E0 src dst).R = LowZero18LowK.oregs K0 E0 src dst := rfl
  have ht1 : ¬c.R.trimOK := by simp only [KRegs.trimOK, bR, show c.R.h = 64 from rfl]; decide
  have ht2 : ¬(LowZero18LowK.oregs K0 E0 src dst).trimOK := by simp only [KRegs.trimOK, bOld, hOldH]; decide
  rw [hKR] at nm nc; simp only [ht1, if_false] at nm nc; rw [bR, show c.R.h = 64 from rfl] at nm nc
  rw [hOR] at om oc; simp only [ht2, if_false] at om oc; rw [bOld, hOldH] at om oc
  exact ⟨by clear * - nm nc om oc hQ1 hQ2 hQ5; omega,
    by clear * - nm nc om oc hQ1 hQ2 hQ5; omega⟩

theorem cfg_counts_S (c : SplitCfg) (v : CfgValid c) (hn : c.n = 129) (src dst : List Wire)
    (hs : src.length = 129) (hd : dst.length = 258) :
    let oldK := LowZero18LowK.kg K0 E0 src dst
    toffoliCount c.make + toffoliCount c.clear + 373 =
      toffoliCount (LowZero18Square.make K0 oldK) + toffoliCount (LowZero18Square.clear K0 oldK) ∧
    measurementCount c.make + measurementCount c.clear + 195 =
      measurementCount (LowZero18Square.make K0 oldK) + measurementCount (LowZero18Square.clear K0 oldK) := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have wOld := LowZero18LowK.oregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wiOld := LowZero18LowK.iregs_W K0 hwK E0 src dst (by omega) (by omega) (by omega) hext.len
  have wjOld := LowZero18LowK.jregsS_W K0 hwK E0 src dst hs (by omega) hext.len
  have m8_R8 := c.R8.m8z_counts wR8; have c8_R8 := c.R8.c8z_counts wR8
  have m8_R := c.R.m8z_counts wR; have c8_R := c.R.c8z_counts wR
  have bR : c.R.bank.length = 129 := by simp [SplitCfg.R, v.bankLen, hn]
  have bOld : (LowZero18LowK.oregs K0 E0 src dst).bank.length = 129 := by
    simp [LowZero18LowK.oregs, (K0.measured_bank_widths hwK).1, hs]
  have hOldH : (LowZero18LowK.oregs K0 E0 src dst).h = 64 := rfl
  have biOld : (LowZero18LowK.iregs K0 E0 src dst).bank.length = 64 := by
    simp [LowZero18LowK.iregs, KRegs.lo, bOld, hOldH]
  have bjOld : (LowZero18LowK.jregsS K0 E0 src dst).bank.length = 66 := by
    have hOS := wOld.S; simp [LowZero18LowK.jregsS, hOS, bOld, hOldH]
  have oldEq : LowZero18LowK.kg K0 E0 src dst = LowZero18LowK.kgS K0 E0 src dst := by simp [LowZero18LowK.kg, hs]
  have om := LowZero18KG.make_counts (LowZero18LowK.kgS K0 E0 src dst) wOld
  have oc := LowZero18KG.clear_counts (LowZero18LowK.kgS K0 E0 src dst) wOld
  have pm := LowZero18Square.patchKG_counts K0 (LowZero18LowK.kg K0 E0 src dst)
  let K :=
    { LowZero18LowK.kgH K0 E0 src dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have nm := LowZero18KG.make_counts K wR
  have nc := LowZero18KG.clear_counts K wR
  have m8z_eq : toffoliCount c.R8.m8z = toffoliCount c.R.m8z ∧ measurementCount c.R8.m8z = measurementCount c.R.m8z ∧
      toffoliCount c.R8.c8z = toffoliCount c.R.c8z ∧ measurementCount c.R8.c8z = measurementCount c.R.c8z := by
    have lR := c.R.m8z_lens wR; have lR8 := c.R8.m8z_lens wR8
    have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
    have a1 := addInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have a2 := addInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have s1 := subInPlace_counts _ _ _ c.R.cin lR.1 lR.2.1; have s2 := subInPlace_counts _ _ _ c.R8.cin lR8.1 lR8.2.1
    have m8t : toffoliCount c.R8.m8 = toffoliCount c.R.m8 := by simp only [KRegs.m8, a1.1, a2.1]; rw [hd8]
    have m8m : measurementCount c.R8.m8 = measurementCount c.R.m8 := by simp only [KRegs.m8, a1.2, a2.2]; rw [hd8]
    have c8t : toffoliCount c.R8.c8 = toffoliCount c.R.c8 := by simp only [KRegs.c8, s1.1, s2.1]; rw [hd8]
    have c8m : measurementCount c.R8.c8 = measurementCount c.R.c8 := by simp only [KRegs.c8, s1.2, s2.2]; rw [hd8]
    exact ⟨by linarith only [m8_R8.1, m8_R.1, m8t], by linarith only [m8_R8.2, m8_R.2, m8m],
      by linarith only [c8_R8.1, c8_R.1, c8t], by linarith only [c8_R8.2, c8_R.2, c8m]⟩
  have hNewM : toffoliCount c.make = toffoliCount (LowZero18KG.make K) ∧
      measurementCount c.make = measurementCount (LowZero18KG.make K) := by
    simp only [SplitCfg.make, LowZero18KG.make, K, toffoliCount_append, measurementCount_append, m8z_eq.1, m8z_eq.2.1]
    exact ⟨by ring, by ring⟩
  have hNewC : toffoliCount c.clear = toffoliCount (LowZero18KG.clear K) ∧
      measurementCount c.clear = measurementCount (LowZero18KG.clear K) := by
    simp only [SplitCfg.clear, LowZero18KG.clear, K, toffoliCount_append, measurementCount_append, m8z_eq.2.2.1, m8z_eq.2.2.2]
    exact ⟨by ring, by ring⟩
  have hne : c.n ≠ 128 := by omega
  have c_eq (A B : KRegs) (wA : A.W) (wB : B.W) (h : Nat) (hA : A.h = h) (hB : B.h = h)
      (bA : A.bank.length = 2 * h) (bB : B.bank.length = 2 * h) :
      DiagSq.cost A = DiagSq.cost B ∧ DiagSq.parR A = DiagSq.parR B := by
    have sA : A.S.length = h + 1 := by have := wA.S; omega
    have sB : B.S.length = h + 1 := by have := wB.S; omega
    have loA : A.lo.length = h := by simp [KRegs.lo, bA, hA]; omega
    have loB : B.lo.length = h := by simp [KRegs.lo, bB, hB]; omega
    have hiA : A.hi.length = h := by simp [KRegs.hi, bA, hA]; omega
    have hiB : B.hi.length = h := by simp [KRegs.hi, bB, hB]; omega
    exact ⟨by simp [DiagSq.cost, bA, bB, hA, hB], by simp [DiagSq.parR, loA, loB, hiA, hiB, sA, sB]⟩
  have eQ1 := c_eq c.Q1 (LowZero18LowK.iregs K0 E0 src dst) w1.1 wiOld 32 rfl rfl
    (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]) biOld
  have eQ5 := c_eq c.Q5 (LowZero18LowK.jregsS K0 E0 src dst) w5.1 wjOld 33 w5.2.2 rfl
    (by rw [w5.2.1, w5.2.2]) bjOld
  have q1_m := makeC_counts c.Q1 w1.1 w1.2; have q1_c := RawClearSquare.clear_counts c.Q1 w1.1 w1.2
  have q1_d := diag32_counts c.Q1 w1.1 rfl (by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn])
  have qi_m := makeC_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_c := RawClearSquare.clear_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld (by rw [biOld]; rfl)
  have qi_d := diag32_counts (LowZero18LowK.iregs K0 E0 src dst) wiOld rfl biOld
  have hQ1 : toffoliCount K.Q1 + toffoliCount K.Q1c =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q1 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q1c ∧
      measurementCount K.Q1 + measurementCount K.Q1c =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q1 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q1c := by
    have b1 : c.Q1.bank.length = 64 := by simp [SplitCfg.Q1, KRegs.lo, SplitCfg.R, v.bankLen, hn]
    have h1 : c.Q1.h = 32 := rfl
    have hi : (LowZero18LowK.iregs K0 E0 src dst).h = 32 := rfl
    have ⟨_, _, q1d3, q1d4⟩ := q1_d
    have ⟨_, _, qid3, qid4⟩ := qi_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q1) = toffoliCount (RawClearSquare.clear c.Q1) + 31 at q1d3
    change measurementCount (LowZero18Diagonal.clearC c.Q1) = measurementCount (RawClearSquare.clear c.Q1) + 32 at q1d4
    change toffoliCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      toffoliCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 31 at qid3
    change measurementCount (LowZero18Diagonal.clearC (LowZero18LowK.iregs K0 E0 src dst)) =
      measurementCount (RawClearSquare.clear (LowZero18LowK.iregs K0 E0 src dst)) + 32 at qid4
    simp only [K, LowZero18LowK.kgS]
    rw [b1, h1] at q1_m; rw [h1] at q1_c; rw [biOld, hi] at qi_m; rw [hi] at qi_c
    exact ⟨by clear * - q1_m q1_c q1d3 qi_m qi_c qid3 eQ1; omega,
      by clear * - q1_m q1_c q1d4 qi_m qi_c qid4 eQ1; omega⟩
  have q2_e := diag33_exact c.Q2 w2.1 (by simp [SplitCfg.Q2, hne]) (by simp [SplitCfg.Q2, hne, KRegs.hi, SplitCfg.R, v.bankLen, hn])
  have q2_old := tsq65_exact (LowZero18LowK.oregs K0 E0 src dst).hi (LowZero18LowK.oregs K0 E0 src dst).dhi
    (LowZero18LowK.oregs K0 E0 src dst).pad (LowZero18LowK.oregs K0 E0 src dst).carry
    (LowZero18LowK.oregs K0 E0 src dst).cin
    (by simp [KRegs.hi, bOld, hOldH]) (by simp [KRegs.dhi, LowZero18LowK.oregs, hd, hOldH]) wOld.pad (by have := wOld.carry; omega)
  have hQ2 : toffoliCount K.Q2 + toffoliCount K.Q2c + 405 =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q2 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q2c ∧
      measurementCount K.Q2 + measurementCount K.Q2c + 261 =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q2 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q2c := by
    simp only [K, LowZero18LowK.kgS]
    exact ⟨by clear * - q2_e q2_old; omega, by clear * - q2_e q2_old; omega⟩
  have q5_m := LowZero18Diagonal.make_counts c.Q5 w5.1 w5.2.1; have q5_c := RawClearSquare.clear_counts c.Q5 w5.1 w5.2.1
  have q5_d := diag33_counts c.Q5 w5.1 w5.2.2 (by rw [w5.2.1, w5.2.2])
  have qj_m := LowZero18Diagonal.make_counts (LowZero18LowK.jregsS K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have qj_c := RawClearSquare.clear_counts (LowZero18LowK.jregsS K0 E0 src dst) wjOld (by rw [bjOld]; rfl)
  have hQ5 : toffoliCount K.Q5 + toffoliCount K.Q5c =
      toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q5 + toffoliCount (LowZero18LowK.kgS K0 E0 src dst).Q5c + 32 ∧
      measurementCount K.Q5 + measurementCount K.Q5c =
      measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q5 + measurementCount (LowZero18LowK.kgS K0 E0 src dst).Q5c + 66 := by
    have h5 : c.Q5.h = 33 := w5.2.2
    have hj : (LowZero18LowK.jregsS K0 E0 src dst).h = 33 := rfl
    have ⟨q5d1, q5d2, q5d3, q5d4⟩ := q5_d
    change toffoliCount (LowZero18Diagonal.clearC c.Q5) = toffoliCount (RawClearSquare.clear c.Q5) + 32 at q5d3
    change measurementCount (LowZero18Diagonal.clearC c.Q5) = measurementCount (RawClearSquare.clear c.Q5) + 33 at q5d4
    simp only [K, LowZero18LowK.kgS, LowZero18Diagonal.clear]
    rw [h5] at q5_c; rw [hj] at qj_c
    exact ⟨by clear * - q5_m q5_c q5d1 q5d3 qj_m qj_c eQ5; omega,
      by clear * - q5_m q5_c q5d2 q5d4 qj_m qj_c eQ5; omega⟩
  have hOldT : toffoliCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.make (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.1, oldEq]
  have hOldM : measurementCount (LowZero18Square.make K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.make (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.1, oldEq]
  have hOldCT : toffoliCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      toffoliCount (LowZero18KG.clear (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.2.1, oldEq]
  have hOldCM : measurementCount (LowZero18Square.clear K0 (LowZero18LowK.kg K0 E0 src dst)) =
      measurementCount (LowZero18KG.clear (LowZero18LowK.kgS K0 E0 src dst)) := by rw [pm.2.2.2, oldEq]
  dsimp only
  rw [hNewM.1, hNewM.2, hNewC.1, hNewC.2, hOldT, hOldM, hOldCT, hOldCM]
  have hKR : K.R = c.R := rfl
  have hOR : (LowZero18LowK.kgS K0 E0 src dst).R = LowZero18LowK.oregs K0 E0 src dst := rfl
  have ht1 : c.R.trimOK := by simp only [KRegs.trimOK, bR, show c.R.h = 64 from rfl]; decide
  have ht2 : (LowZero18LowK.oregs K0 E0 src dst).trimOK := by simp only [KRegs.trimOK, bOld, hOldH]; decide
  rw [hKR] at nm nc; simp only [ht1, if_true] at nm nc; rw [bR, show c.R.h = 64 from rfl] at nm nc
  rw [hOR] at om oc; simp only [ht2, if_true] at om oc; rw [bOld, hOldH] at om oc
  exact ⟨by clear * - nm nc om oc hQ1 hQ2 hQ5; omega,
    by clear * - nm nc om oc hQ1 hQ2 hQ5; omega⟩

end SplitCore

/-! ### Slot bounds for the concrete split Karatsuba kernels -/

section SplitSlots
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

private theorem addInPlace_slots_eq : ∀ (x y cs : List Wire) (c : Wire),
    x.length = y.length → x.length - 1 ≤ cs.length → 1 ≤ x.length →
    Challenge.gateSlots (addInPlace x y cs c) = 12 * x.length - 10
  | [a], [b], _, c, _, _, _ => by
      simp [addInPlace, Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots]
  | a :: a' :: as, b :: b' :: bs, d :: ds, c, hxy, hcs, _ => by
      simp only [List.length_cons] at hxy hcs
      have ih := addInPlace_slots_eq (a' :: as) (b' :: bs) ds d
        (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega) (by simp)
      simp only [addInPlace, Challenge.gateSlots_append, Baselines.majority_gateSlots,
        Baselines.eraseCarry_gateSlots, Baselines.gateSlots_cons, Baselines.gateSlots_nil,
        Challenge.instructionSlots, List.length_cons] at ih ⊢
      omega
  | [], _, _, _, _, _, hx => by simp at hx
  | [_], [], _, _, hxy, _, _ => by simp at hxy
  | [_], _ :: _ :: _, _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, [], _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, [_], _, _, hxy, _, _ => by simp at hxy
  | _ :: _ :: _, _ :: _ :: _, [], _, _, hcs, _ => by simp at hcs

private theorem m8z_slots_eq (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.m8z = 12 * (R.dmid.length - 1) - 9 := by
  have l := R.m8z_lens w
  have h1 := l.1; have h2 := l.2.1; have h3 := l.2.2
  have ha := addInPlace_slots_eq (R.T ++ R.zM).tail R.dmid.tail (R.carry.take (R.dmid.length - 1)).tail R.cin
    (by simp only [List.length_tail, h1])
    (by simp only [List.length_tail, h1]; omega)
    (by simp only [List.length_tail, h1]; omega)
  simp only [KRegs.m8z, LowZero.addLow0, Challenge.gateSlots_append, ha, List.length_tail, h1,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_nil]
  omega

private theorem c8z_slots_eq (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.c8z = 2 * R.dmid.length + 12 * (R.dmid.length - 1) - 7 := by
  have l := R.m8z_lens w
  have h1 := l.1; have h2 := l.2.1; have h3 := l.2.2
  have ha := addInPlace_slots_eq (R.T ++ R.zM).tail R.dmid.tail (R.carry.take (R.dmid.length - 1)).tail R.cin
    (by simp only [List.length_tail, h1])
    (by simp only [List.length_tail, h1]; omega)
    (by simp only [List.length_tail, h1]; omega)
  simp only [KRegs.c8z, LowZero.subLowNC, LowZero.addLowNC, Challenge.gateSlots_append, ha,
    Baselines.notRegister_gateSlots, List.length_tail, h1,
    Baselines.gateSlots_cons, Baselines.gateSlots_nil, Challenge.instructionSlots, List.length_nil]
  omega

private theorem diagC_slots_bound (R : KRegs) (w : R.W) (he : R.bank.length = 2 * R.h) (hh : R.h ≤ 33) :
    Challenge.gateSlots (LowZero18Diagonal.makeC R) + Challenge.gateSlots (LowZero18Diagonal.clearC R) ≤ 601600 := by
  have dt := LowZero18Diagonal.tiny_slots R w he hh
  have ot := R.tiny_slots w hh (by omega) (by omega)
  have ms := R.make_sub_slots w
  have sc := R.scl1591_slots
  have sk := R.smkT_slots
  simp only [LowZero18Diagonal.makeC, LowZero18Diagonal.clearC, RawClearSquare.clearC, LowZero18Diagonal.clear,
    Challenge.gateSlots_append] at dt ⊢
  clear * - dt ot ms sc sk; omega

theorem cfg_slots_bound (c : SplitCfg) (v : CfgValid c) :
    Challenge.gateSlots c.make + Challenge.gateSlots c.clear ≤ 1830000 := by
  have wR := cfg_R_W c v; have wR8 := cfg_R8_W c v
  have w1 := cfg_Q1_W c v; have w2 := cfg_Q2_W c v; have w5 := cfg_Q5_W c v
  have q1 := diagC_slots_bound c.Q1 w1.1 w1.2 (by change 32 ≤ 33; decide)
  have q2 := diagC_slots_bound c.Q2 w2.1 w2.2.1 (by rcases w2.2.2 with h | h <;> omega)
  have q5 := diagC_slots_bound c.Q5 w5.1 w5.2.1 (by omega)
  have m8 := m8z_slots_eq c.R wR; have m8' := m8z_slots_eq c.R8 wR8
  have c8 := c8z_slots_eq c.R wR; have c8' := c8z_slots_eq c.R8 wR8
  have hd8 : c.R8.dmid.length = c.R.dmid.length := by simp [KRegs.dmid, SplitCfg.R8, SplitCfg.R]
  have ad := c.R.adder_slots wR rfl (by simp only [SplitCfg.R, v.bankLen]; rcases v.hn with h | h <;> omega)
  let K :=
    { LowZero18LowK.kgH K0 E0 c.src c.dst with
      R := c.R, X1 := [], X2 := [], X5 := [],
      Q1 := LowZero18Diagonal.makeC c.Q1, Q1c := LowZero18Diagonal.clearC c.Q1,
      Q2 := LowZero18Diagonal.makeC c.Q2, Q2c := LowZero18Diagonal.clearC c.Q2,
      Q5 := LowZero18Diagonal.makeC c.Q5, Q5c := LowZero18Diagonal.clearC c.Q5,
      I1 := fun _ _ => True, I2 := fun _ _ => True, I5 := fun _ _ => True }
  have st := LowZero18KG.steps_slots2 K wR
  have hM : Challenge.gateSlots c.make = Challenge.gateSlots (LowZero18KG.make K) := by
    simp only [SplitCfg.make, LowZero18KG.make, K, Challenge.gateSlots_append, m8, m8', hd8]; ring
  have hC : Challenge.gateSlots c.clear = Challenge.gateSlots (LowZero18KG.clear K) := by
    simp only [SplitCfg.clear, LowZero18KG.clear, K, Challenge.gateSlots_append, c8, c8', hd8]; ring
  rw [hM, hC]
  dsimp only [K] at st ⊢
  clear * - q1 q2 q5 ad st; omega

end SplitSlots

/-! ## Direct-fold renaming helper (moves `workT` onto `K0.core.pad.take workT.length`) -/

section FoldMove
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem directFold_rename_run (pairs : List (Wire × Wire)) (f : MeasuredSquareFold)
    (hcnt : ∀ q, f.src.count q ≤ K0.core.product.count q)
    (hlen : f.src.length = 256) (hcan : f.canonical = true) (hsh : f.shift = 0)
    (hholes : ∀ ab ∈ pairs, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out)
    (hhosts : ∀ ab ∈ pairs, ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out)
    (base : BasisState) (hv : K0.MeasuredFoldView base f) (hc : K0.PairClean base)
    (O : Nat) (hO : O < SquareReduction.p) (s : State) (m : List Bool)
    (hf : SquareFrame K0.core.out base O s.basis) :
    run (hostRename pairs (directFoldQTq K0 f)) m s = run (directFoldQTq K0 f) m s := by
  have hn := (List.nodup_cons.mp controlND).2
  have cleanIn := K0.squareFrame_clean hn base s.basis O hf hc
  have frame := directFoldQ_frameTq K0 hwK hn base f hv hcan hc hlen hsh O hO s m hf
  have cleanOut := K0.squareFrame_clean hn base (run (directFoldQTq K0 f) m s).basis
    ((measuredFoldPayload base f + (SquareReduction.p - 1 - O)) % SquareReduction.p) frame.2 hc
  apply hostRename_run_eq pairs (directFoldQTq K0 f) s m
  · intro ab hab; exact (regValue_zero _ _).mp cleanIn.work ab.1 (hholes ab hab).1
  · intro ab hab; exact (regValue_zero _ _).mp cleanIn.pad ab.2 (List.mem_append_left _ (hhosts ab hab).1)
  · intro ab hab; exact (regValue_zero _ _).mp cleanOut.work ab.1 (hholes ab hab).1
  · intro ab hab
    exact directFoldQ_free K0 hn f hcnt ab.2 (by simp [directFree, (hhosts ab hab).1])

private theorem directFold_rename_support (pairs : List (Wire × Wire)) (f : MeasuredSquareFold)
    (hcnt : ∀ q, f.src.count q ≤ K0.core.product.count q)
    (hnd : (holesOf pairs ++ hostsOf pairs).Nodup)
    (hhosts : ∀ ab ∈ pairs, ab.2 ∈ K0.core.pad) :
    wires (hostRename pairs (directFoldQTq K0 f)) ⊆
      (wires (directFoldQTq K0 f) \ (holesOf pairs).toFinset) ∪ (hostsOf pairs).toFinset := by
  have hn := (List.nodup_cons.mp controlND).2
  exact hostRename_support pairs (directFoldQTq K0 f) hnd (fun ab hab =>
    directFoldQ_free K0 hn f hcnt ab.2 (by simp [directFree, hhosts ab hab]))

end FoldMove

/-! ## Branch A body (`keepA` = 33 carries, avoids `workTA` and `hs`) -/

section BodyA
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem la_eq_K0 : ReorderedAFixed.L = K0 := rfl

def keepA : List Wire := A109Research.keepK.filter (fun q => !workTA.contains q)

theorem keepA_geometry : keepA.Nodup ∧ keepA.length = 33 ∧
    (∀ q ∈ keepA, q ∈ A109Research.hosts) ∧
    (∀ q ∈ workTA, q ∉ keepA) ∧
    (∀ i, i < 44 → ReorderedAFixed.hs.getD i 0 ∉ keepA) ∧
    (∀ q ∈ keepA, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepA, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepA, keepKA_fast, workTA_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepA, keepKA_fast, workTA_lit, hs_lit]; decide +kernel))
  have hr : keepA.Nodup ∧ keepA.length = 33 ∧
      (∀ q ∈ keepA, q ∈ A109Research.hosts) ∧
      (∀ q ∈ workTA, q ∉ keepA) ∧
      (∀ i, i < 44 → ReorderedAFixed.hs.getD i 0 ∉ keepA) := by
    rw [keepA, keepKA_fast, hostsA109_fast, hsA_fast, workTA_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, hall⟩

def rawFA : Program := ReorderedGenericCache.cachedAdd 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
def newFA : Program := A109Research.head ++ A109LowEraseResearch.clear ++ rawFA ++ A109Research.top
def newIA : Program := A109Research.preInv ++ ReorderedConsumedSub.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
def coreA : Program := (newFA ++ A109Research.M ++ newIA) ++ (A109LowEraseResearch.clear ++ A109Research.tail)
def restA : Program := A109LowEraseResearch.clear ++ rawFA ++ A109Research.top ++ A109Research.M ++ newIA ++ A109LowEraseResearch.clear ++ A109Research.tail
def loopPCA : Program := SignAHead.head ++ restA
def loopA : Program := hostRename (StairSqLoopA.pairs hs) loopPCA
def foldPairsA : List (Wire × Wire) := workTA.zip (K0.core.pad.take 32)
def dF1A : Program := hostRename foldPairsA (directFoldQTq K0 (negP K0))
def dF2A : Program := hostRename foldPairsA (directFoldQTq K0 (rot128F K0))
def bodyA : Program := (dF1A ++ (dF2A ++ loopA)) ++ ReorderedRecordPadding.program 7 K0.core.cin
def bodyAPlain : Program := A109SignResearch.directBody loopA

theorem foldPairsA_geom :
    (holesOf foldPairsA ++ hostsOf foldPairsA).Nodup ∧
    holesOf foldPairsA = workTA ∧
    hostsOf foldPairsA = K0.core.pad.take 32 ∧
    (∀ ab ∈ foldPairsA, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsA, q ∉ hs ∧ q ≠ ControlLoan1589BFFold.eU K0 ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsA, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsA, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsA, workTA_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsA ++ hostsOf foldPairsA).Nodup ∧
      holesOf foldPairsA = workTA ∧
      hostsOf foldPairsA = K0.core.pad.take 32 ∧
      (∀ ab ∈ foldPairsA, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsA, q ∉ hs ∧ q ≠ ControlLoan1589BFFold.eU K0) := by
    rw [foldPairsA, workTA_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; have h := hr.2.2.2.2 q hq
    exact ⟨h.1, h.2, hK q hq, hall q hq⟩

private theorem keepA_sub (q : Wire) (hq : q ∈ keepA) : q ∈ A109Research.hosts := keepA_geometry.2.2.1 q hq

private theorem core_plainA (s : State) (m : List Bool)
    (hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ ReorderedBPrefixResearch.bank, s.basis q = false)
    (hi : s.basis ReorderedBPrefixResearch.cin = false) (ha : regValue ReorderedBPrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedAFixed.hosts, s.basis q = false)
    (after : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      (regValue ReorderedBPrefixResearch.src s.basis) (middleState A109Research.oldF A109Research.oldM s m))
    (flag : (run A109Research.oldF (m.take (measurementCount A109Research.oldF)) s).basis 4762 = false) :
    run coreA m s = run (A109Research.oldF ++ A109Research.oldM ++
      ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
  let H := regValue ReorderedBPrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 33 H (976 * H / 1024)
  have keepSubK (q : Wire) (hq : q ∈ keepA) : q ∈ A109Research.keepK := (List.mem_filter.mp hq).1
  have fwdM : measurementCount newFA = measurementCount A109Research.F := by
    have h := (ReorderedGenericCache.count_balance 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFA, rawFA, A109Research.F, A109Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIA = measurementCount A109Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)
    simp only [newIA, A109Research.I, A109Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((A109Research.cs.drop 4).take 33).map (run (carryPrefix (4 + 33) A109Research.xs A109Research.ys A109Research.cs ReorderedBPrefixResearch.cin) []
      (run (A109Research.head ++ A109LowEraseResearch.clear)
        ((m.take (measurementCount A109Research.F)).take (measurementCount (A109Research.head ++ A109LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount A109Research.F)).take (measurementCount (A109Research.head ++ A109LowEraseResearch.clear))
    let u := run A109Research.head m0 s
    let t := run (A109Research.head ++ A109LowEraseResearch.clear) m0 s
    have te : t = A109LowEraseResearch.erase u := A109Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 128 := by simpa only [H, ReorderedBPrefixResearch.source_length] using regValue_lt ReorderedBPrefixResearch.src s.basis
    have ready := ReorderedHeadArithmeticResearch.ready ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
      ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ A109Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact A109LowEraseResearch.bit_same _ q (A109Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ A109Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 33 H (((2 ^ 138 - 48 * H) % 2 ^ 138) / 1024) (976 * H / 1024)
      A109Research.xs A109Research.ys A109Research.cs ReorderedBPrefixResearch.cin t
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) A109Research.raw_nd
      (fun q hq => (eb q (A109Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ A109Research.cin_in).trans ready.2.1)
      ((er _ A109Research.x_in).trans ready.2.2.1)
      ((er _ A109Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 128 + 10 = 138 by decide] using ReorderedCacheArithmetic.high_add_low 128 (4 + j + 1) H (by omega) hH)
  have forward : run newFA (m.take (measurementCount A109Research.F)) s =
      scatterState keepA vs (run A109Research.F (m.take (measurementCount A109Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (A109Research.head ++ A109LowEraseResearch.clear) A109Research.top
      33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) keepA_geometry.1
      (fun q hq bad => A109Research.geometry.2.2 q (keepA_sub q hq) (by clear * - bad; simp only [A109Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => A109Research.rawF_off q (keepA_sub q hq)) (fun q hq => A109Research.top_off q (keepA_sub q hq))
      s (m.take (measurementCount A109Research.F))
      (fun q hq => A109Research.prefix_zeroK s _ hz hb hi ha zero q (keepSubK q hq))
    rw [fwdVal] at h; exact h
  have mid := A109Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFA ++ A109Research.M ++ newIA) m s = run (A109Research.F ++ A109Research.M ++ A109Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent A109Research.F newFA A109Research.M A109Research.I newIA keepA vs
      fwdM (fun q hq => A109Research.middle_fresh q (keepA_sub q hq))
      (fun q hq => A109Research.I_off q (keepA_sub q hq)) keepA_geometry.1 s m
      (fun q hq => A109Research.forward_zeroK s _ hz hb hi ha zero q (keepSubK q hq)) forward
    rw [mid]
    let ms := middleState A109Research.oldF A109Research.oldM s m
    let mr := m.drop (measurementCount A109Research.F + measurementCount A109Research.M)
    let t := scatterState keepA vs (A109LowEraseResearch.erase ms)
    have comm : run A109Research.preInv mr t = scatterState keepA vs (A109LowEraseResearch.erase (run A109Research.preInv mr ms)) := by
      rw [show t = scatterState keepA vs (A109LowEraseResearch.erase ms) from rfl,
        run_scatter A109Research.preInv keepA vs _ _ (fun q hq => A109Research.preInv_off q (keepA_sub q hq)),
        A109LowEraseResearch.commute A109Research.preInv mr ms (fun q hq => A109Research.preInv_off q (A109Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ A109Research.domain) : (run A109Research.preInv mr t).basis q = (run A109Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepA vs _ q (fun bad => A109Research.geometry.2.2 q (keepA_sub q bad) hq)]
      exact A109LowEraseResearch.bit_same _ q (A109Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ A109Research.domain) :
        regValue r (run A109Research.preInv mr t).basis = regValue r (run A109Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := A109Research.pre_raw_ready H ms mr after
    have saved : keepA.map t.basis = vs := scatter_saved_map keepA vs _ keepA_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepA_geometry.2.1, List.length_range])
    have same : keepA.map (run A109Research.preInv mr t).basis = keepA.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside A109Research.preInv mr t q (A109Research.preInv_off q (keepA_sub q hq)))
    simp only [newIA, A109Research.I, A109Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide)
      (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
      (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])
      A109Research.raw_nd keepA_geometry.1 keepA_geometry.2.1 (fun q hq => A109Research.geometry.2.2 q (keepA_sub q hq))
      (run A109Research.preInv mr t) _ (fun q hq => (bits q (A109Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ A109Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ A109Research.x_in).trans rr.2.2.1) ((regs _ A109Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFA ++ A109Research.M ++ newIA)
    (A109Research.F ++ A109Research.M ++ A109Research.I) (A109LowEraseResearch.clear ++ A109Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (A109Research.F ++ A109Research.M ++ A109Research.I) ++ (A109LowEraseResearch.clear ++ A109Research.tail) =
      A109Research.F ++ A109Research.M ++ (A109Research.I ++ A109LowEraseResearch.clear ++ A109Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (A109Research.plain_loop s m hz hb hi ha after flag))

private theorem coreA_frame (base : BasisState) (hc : ReorderedAFixed.L.PairClean base)
    (hsum : base A161Low4FixedFold.q = false) (hV : base A161Low4FixedFold.r = false)
    (hP : base A161Low4FixedFold.p = false) (hd : base ReorderedAFixed.d = false)
    (O : Nat) (hO : O < SquareReduction.p) :
    Triple (SquareFrame ReorderedAFixed.L.core.out base O) coreA
      (SquareFrame ReorderedAFixed.L.core.out base
        (((if base ReorderedAFixed.g then A161Low4Facts.Klow - 4294968272 * regValue ReorderedAFixed.src base
           else 4294968272 * regValue ReorderedAFixed.src base) + (SquareReduction.p - 1 - O)) % SquareReduction.p)) := by
  intro s m hf
  have clean := ReorderedAFixed.L.squareFrame_clean ReorderedAFixed.hn base s.basis O hf hc
  have hzFull : ∀ u ∈ accZ ReorderedAFixed.L, s.basis u = false := by
    intro u hu; rcases accZ_mem ReorderedAFixed.L u hu with hu | hu
    · exact (regValue_zero _ _).mp clean.pad u hu
    · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
  have hz : ∀ u ∈ ReorderedAFixed.pad, s.basis u = false := fun u hu => hzFull u ((FullPadDevelop.pad_sublist ReorderedAFixed.L).subset hu)
  have hb : ∀ u ∈ ReorderedAFixed.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue ReorderedAFixed.acc s.basis = 0 := A161Low4Ghost.ghostAcc_zero ReorderedAFixed.L s.basis clean
  have zeroU : ∀ u ∈ ReorderedAFixed.hs, s.basis u = false := fun u hu =>
    (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
  have zeroOld : ∀ u ∈ ReorderedAFixed.hosts, s.basis u = false := by
    have qz : s.basis ReorderedAFixed.q = false := (hf.2 ReorderedAFixed.q (by decide)).trans hsum
    have rz : s.basis ReorderedAFixed.r = false := (hf.2 ReorderedAFixed.r (by decide)).trans hV
    have pz : s.basis ReorderedAFixed.p = false := (hf.2 ReorderedAFixed.p (by decide)).trans hP
    change ∀ u ∈ ReorderedAFixed.q :: ReorderedAFixed.r :: ReorderedAFixed.p :: ReorderedAFixed.hs, s.basis u = false
    rw [List.forall_mem_cons, List.forall_mem_cons, List.forall_mem_cons]
    exact ⟨qz, rz, pz, zeroU⟩
  have offHs : ∀ u ∈ ReorderedAFixed.hs, u ∉ wires (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) :=
    fun u hu => (ReorderedAFixed.off_plain u (StairSqLoopA.hosts_of_hs u hu)).1
  have goodOriginal : WReady ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (regValue ReorderedAFixed.src s.basis)
      (middleState (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
        (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g) s m) := by
    rw [ReorderedARetape.a_middle_eq ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g) ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2 ReorderedAFixed.fits s m hz hb clean.cin ha]
    exact ReorderedAFixed.good_old base hc O hO s _ hf
  have middleEq := A161Low4FixedFold.cert100.middle_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g)
    A161Low4FixedFold.checked.out (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) s m zeroU offHs
  have knownEq := AKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
  have goodKnown : WReady ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
      (regValue ReorderedAFixed.src s.basis)
      (middleState (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) KnownAMidStaged.body s m) := by
    rw [knownEq, middleEq]; exact goodOriginal
  have buildFrame := ReorderedAPlain.build_triple ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src
    ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2 ReorderedAFixed.fits s.basis hz hb clean.cin s
    (m.take (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src))) ⟨ha, fun _ _ => rfl⟩
  have flag : (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
      (m.take (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src))) s).basis 4762 = false :=
    (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
  have plainNew := core_plainA s m hz hb clean.cin ha zeroOld goodKnown flag
  have midEq : run KnownAMidStaged.body (m.drop (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)))
      (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m s) =
      run A161Low4FixedFold.checked.out (m.drop (measurementCount (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)))
      (run (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m s) := by
    simpa only [middleState, run_take] using knownEq
  have ctxt := ReorderedKnownA.context_eq (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    A161Low4FixedFold.checked.out KnownAMidStaged.body (ReorderedAPlain.unbuild ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    s m AKnownMiddleResearch.measurements midEq
  have middleReplace := A161Low4FixedFold.cert100.surround_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle ReorderedAFixed.L ReorderedAFixed.g)
    A161Low4FixedFold.checked.out (ReorderedAPlain.build ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src)
    (ReorderedAPlain.unbuild ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) s m zeroU offHs
  exact ReorderedAFixed.transport _ s _ _ (plainNew.trans (ctxt.trans middleReplace)) (ReorderedAFixed.plain_frame base hc O hO s m hf)

private theorem keepA_cached_wires : wires rawFA ⊆ A109Research.domain.toFinset ∪ keepA.toFinset :=
  (ReorderedSupport.cached 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
    (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])).1

private theorem keepA_consumed_wires :
    wires (ReorderedConsumedSub.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin) ⊆
      A109Research.domain.toFinset ∪ keepA.toFinset :=
  ReorderedSupport.consumed 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    (by rw [A109Research.raw_lengths.1, A109Research.raw_lengths.2.1])
    (by rw [A109Research.raw_lengths.2.1, A109Research.raw_lengths.2.2])

theorem loopPCA_off (h : Wire) (hh : h ∈ ReorderedAFixed.hosts) (hk : h ∉ keepA) : h ∉ wires loopPCA := by
  have hA : h ∈ A109Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedAFixed.off_plain h hh).1
  rw [A109Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedAFixed.off_plain h hh).2
  rw [A109Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires A109LowEraseResearch.clear := by
    rw [StairSqLoopA.clear_wires]; intro bad
    exact A109Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ A109Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ A109Research.domain.toFinset ∪ keepA.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨A109Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCA, restA, newIA, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (SignAHeadSupport.support bad), clearOff, fun bad => out (keepA_cached_wires bad),
    A109Research.top_off h hA, A109Research.middle_fresh h hA, A109Research.preInv_off h hA,
    fun bad => out (keepA_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCA_support : wires loopPCA ⊆ A109Research.S := by
  have hh : wires SignAHead.head ⊆ A109Research.S := by
    apply Finset.Subset.trans ?_ A109Research.old_prefix_support
    rw [A109Research.oldPrefix, wires_append]
    exact Finset.subset_union_left
  have ks : A109Research.domain.toFinset ∪ keepA.toFinset ⊆ A109Research.S := by
    intro q hq; apply A109Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepA_sub q h)
  simp only [loopPCA, restA, newIA, wires_append, Finset.union_subset_iff]
  exact ⟨hh,
    ⟨⟨⟨⟨⟨⟨A109Research.clear_support, keepA_cached_wires.trans ks⟩, A109Research.endpoint_support.1⟩,
      A109Research.middle_support⟩, ⟨A109Research.endpoint_support.2.1, keepA_consumed_wires.trans ks⟩⟩,
      A109Research.clear_support⟩, A109Research.endpoint_support.2.2⟩⟩

theorem loopPCA_physical : GatePhysical loopPCA := by
  have f := ReorderedPhysical.cached 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
    (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
    (by rw [A109Research.raw_lengths.2.2]; decide)
    A109Research.raw_nd (fun q hq bad => A109Research.geometry.2.2 q (keepA_sub q hq) (A109Research.c_in q bad))
  have n := notRegister_physical A109Research.ys
  simp only [loopPCA, restA, newIA, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨SignAHeadResources.physical,
    ⟨⟨⟨⟨⟨⟨A109LowEraseResearch.physical, f.1⟩, A109Research.endpoint_physical.2.1⟩,
      AAliasesResearch.physical⟩, ⟨A109Research.endpoint_physical.2.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      A109LowEraseResearch.physical⟩, A109Research.endpoint_physical.2.2.2⟩⟩

theorem loopA_pairs_free : ∀ ab ∈ StairSqLoopA.pairs hs, ab.2 ∉ wires loopPCA := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCA_off _ (StairSqLoopA.hosts_of_hs _ (StairSqLoopA.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepA_geometry.2.2.2.2.1 _ h

theorem loopA_support : wires loopA ⊆ A109Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCA_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopA.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact A109Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopA.hosts_of_hs _ (StairSqLoopA.holes_geometry44.2.2 y hy))))))

theorem loopA_avoids_hs : ∀ q ∈ hs, q ∉ wires loopA := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free
  rw [StairSqLoopA.pairs_fst] at h; exact h q hq

theorem loopA_avoids_workTA : ∀ q ∈ workTA, q ∉ wires loopA := by
  intro q hq bad
  have sub := hostRename_support (StairSqLoopA.pairs hs) loopPCA (StairSqLoopA.pairs_nodup44 hs (List.Sublist.refl _)) loopA_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · have hm : ∀ x ∈ workTA, x ∈ ReorderedAFixed.hosts := by rw [workTA_lit, hostsAFix_fast]; decide +kernel
    exact loopPCA_off q (hm q hq) (keepA_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopA.pairs_snd] at h
    have dis : ∀ x ∈ workTA, x ∉ hs.map StairSqLoopA.hostOf := by simp only [workTA_lit, StairSqLoopA.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hsA_fast]; decide +kernel
    exact dis q hq (List.mem_toFinset.mp h)

theorem loopA_counts :
    toffoliCount loopA = toffoliCount A109SignResearch.loop + 79 ∧
    measurementCount loopA = measurementCount A109SignResearch.loop := by
  have hr := hostRename_counts (StairSqLoopA.pairs hs) loopPCA
  have rel : toffoliCount loopPCA + 33 = toffoliCount StairSqLoopA.loopNC ∧
      measurementCount loopPCA = measurementCount StairSqLoopA.loopNC := by
    have cb := ReorderedGenericCache.count_balance 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide) (by rw [A109Research.raw_lengths.2.2]; decide)
    rw [loopPCA, restA, rawFA, newIA, StairSqLoopA.loopNC, StairSqLoopA.suffixNC,
      A109Research.I, A109Research.rawI, A109Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopA.loopNC_counts
  rw [loopA, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopA_slots : Challenge.gateSlots loopA = Challenge.gateSlots A109SignResearch.loop + 231 := by
  have hr := hostRename_slots (StairSqLoopA.pairs hs) loopPCA
  have rel : Challenge.gateSlots loopPCA + 99 = Challenge.gateSlots StairSqLoopA.loopNC := by
    have sc := ReorderedSlots.cache 33 A109Research.xs A109Research.ys A109Research.cs keepA ReorderedBPrefixResearch.cin
      (by rw [A109Research.raw_lengths.1]; decide) (by rw [A109Research.raw_lengths.2.1]; decide)
      (by rw [A109Research.raw_lengths.2.2]; decide) keepA_geometry.2.1
    rw [loopPCA, restA, rawFA, newIA, StairSqLoopA.loopNC, StairSqLoopA.suffixNC,
      A109Research.I, A109Research.rawI, A109Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopA.loopNC_slots
  rw [loopA, hr]
  omega

theorem loopA_frame : A109SignResearch.DirectLoopFrame loopA := by
  have pcFrame : A109SignResearch.DirectLoopFrame loopPCA := by
    intro base hc hsum hV hP hd O hO s m hf
    have clean := ReorderedAFixed.L.squareFrame_clean ReorderedAFixed.hn base s.basis O hf hc
    have hz : ∀ u ∈ ReorderedAFixed.pad, s.basis u = false := by
      intro u hu; rcases accZ_mem ReorderedAFixed.L u ((FullPadDevelop.pad_sublist ReorderedAFixed.L).subset hu) with hu' | hu'
      · exact (regValue_zero _ _).mp clean.pad u hu'
      · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu')
    have hb : ∀ u ∈ ReorderedAFixed.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
    have ha : regValue ReorderedAFixed.acc s.basis = 0 := A161Low4Ghost.ghostAcc_zero ReorderedAFixed.L s.basis clean
    have hhead : ∀ a b : List Bool, run SignAHead.head a s = run (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) b s :=
      fun a b => ReorderedFrameUnique.program_eq ReorderedAFixed.acc s.basis 0 ((2 ^ 138 - 48 * regValue ReorderedAFixed.src s.basis) % 2 ^ 138) _ _
        (SignAHead.frame s.basis hz hb clean.cin)
        (ReorderedAHead.head_triple ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src ReorderedAFixed.lengths.1 ReorderedAFixed.lengths.2.2.2.le ReorderedAFixed.fits s.basis hz hb clean.cin)
        s a b ⟨ha, fun _ _ => rfl⟩
    have eq := SignRetape.replace SignAHead.head (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) restA s m hhead
    have hheadEq : A109Research.head = ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src := rfl
    have hcoreEq : coreA = ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src ++ restA := by
      rw [coreA, newFA, restA, hheadEq]
      have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
      exact g _ _ _ _ _ _ _ _
    have eq' : run loopPCA m s = run coreA (SignRetape.tape SignAHead.head (ReorderedAHead.head ReorderedAFixed.acc ReorderedAFixed.pad ReorderedAFixed.bank ReorderedAFixed.L.core.cin ReorderedAFixed.src) m) s := by
      rw [loopPCA, hcoreEq]; exact eq
    exact ReorderedAFixed.transport _ s _ _ eq' (coreA_frame base hc hsum hV hP hd O hO s _ hf)
  intro base hc hsum hV hP hd O hO s m hf
  have r := pcFrame base hc hsum hV hP hd O hO s m hf
  have hEq : run loopA m s = run loopPCA m s := by
    apply hostRename_run_eq (StairSqLoopA.pairs hs) loopPCA s m
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopA.holes_geometry44.2.1 y hy
      exact (hf.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact (hf.2 _ (A161Low4FixedFold.hostClean base hc hd _ (StairSqLoopA.holes_geometry44.2.2 y hy)).1).trans
        (A161Low4FixedFold.hostClean base hc hd _ (StairSqLoopA.holes_geometry44.2.2 y hy)).2
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopA.holes_geometry44.2.1 y hy
      exact (r.2.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · exact loopA_pairs_free
  rw [hEq]; exact r

theorem bodyA_wires_plain : wires bodyA ⊆ wires bodyAPlain ∪ (K0.core.pad.take 32).toFinset := by
  have sp1 := directFold_rename_support foldPairsA (negP K0) (negP_count K0) foldPairsA_geom.1 (fun ab hab => (foldPairsA_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsA (rot128F K0) (rot128F_count K0) foldPairsA_geom.1 (fun ab hab => (foldPairsA_geom.2.2.2.1 ab hab).2.2.1)
  rw [foldPairsA_geom.2.2.1] at sp1 sp2
  intro q hq
  simp only [bodyA, wires_append, Finset.mem_union] at hq
  rcases hq with (b | b | b) | b
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; right; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, wires_append, Finset.mem_union]; left; right; right; exact b)
  · exact Finset.mem_union_left _ (by simp only [bodyAPlain, A109SignResearch.directBody, wires_append, Finset.mem_union]; right; exact b)

theorem bodyA_ok : BodyAOK bodyA := by
  have s0 := A109SignResearch.direct_body_support_S loopA loopA_support
  have e0 := A109SignResearch.direct_body_eU_free_S loopA loopA_support
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; rcases Finset.mem_union.mp (bodyA_wires_plain hq) with h | h
    · exact s0 h
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsA_geom.2.2.2.2 q (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.2.1))
  · intro bad; rcases Finset.mem_union.mp (bodyA_wires_plain bad) with h | h
    · exact e0 h
    · exact (foldPairsA_geom.2.2.2.2 _ (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.1 rfl
  · intro base M hM hP hc hsum O hO hg hd s m hf
    have rawRef := A109SignResearch.direct_body_frame loopA loopA_frame base M hM hP hc hsum O hO hg hd s m hf
    have views := accA_views K0 hwK base M hM hP
    have hv1 : K0.MeasuredFoldView base (negP K0) := views (.inl (negP K0)) (by simp [accAMix])
    have hv2 : K0.MeasuredFoldView base (rot128F K0) := views (.inl (rot128F K0)) (by simp [accAMix])
    have mc1 : measurementCount dF1A = measurementCount (directFoldQTq K0 (negP K0)) := (hostRename_counts foldPairsA (directFoldQTq K0 (negP K0))).2
    have mc2 : measurementCount dF2A = measurementCount (directFoldQTq K0 (rot128F K0)) := (hostRename_counts foldPairsA (directFoldQTq K0 (rot128F K0))).2
    have eq1 : run dF1A m s = run (directFoldQTq K0 (negP K0)) m s :=
      directFold_rename_run foldPairsA (negP K0) (negP_count K0) (negP_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).1, (foldPairsA_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).2.2.1, (foldPairsA_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv1 hc O hO s m hf
    have hn := (List.nodup_cons.mp controlND).2
    have f1 := directFoldQ_frameTq K0 hwK hn base (negP K0) hv1 rfl hc (negP_length K0 hwK) rfl O hO s m hf
    have eq2 : run dF2A (m.drop (measurementCount (directFoldQTq K0 (negP K0)))) (run (directFoldQTq K0 (negP K0)) m s) =
        run (directFoldQTq K0 (rot128F K0)) (m.drop (measurementCount (directFoldQTq K0 (negP K0)))) (run (directFoldQTq K0 (negP K0)) m s) :=
      directFold_rename_run foldPairsA (rot128F K0) (rot128F_count K0) (rot128F_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).1, (foldPairsA_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsA_geom.2.2.2.1 ab hab).2.2.1, (foldPairsA_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv2 hc _ (Nat.mod_lt _ (by norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c])) _ _ f1.2
    have bodyEq : run bodyA m s = run bodyAPlain m s := by
      simp only [bodyA, bodyAPlain, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
        ControlledBorrowResearch.run_cat, measurementCount_append, mc1, mc2]
      rw [eq1, eq2]
    rw [bodyEq]; exact rawRef

theorem bodyA_avoids_workTA : ∀ q ∈ workTA, q ∉ wires bodyA := by
  intro q hq bad
  have hn := (List.nodup_cons.mp controlND).2
  have a1 := hostRename_avoids foldPairsA (directFoldQTq K0 (negP K0)) foldPairsA_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negP K0) (negP_count K0) ab.2 (by simp [directFree, (foldPairsA_geom.2.2.2.1 ab hab).2.2.1]))
  have a2 := hostRename_avoids foldPairsA (directFoldQTq K0 (rot128F K0)) foldPairsA_geom.1
    (fun ab hab => directFoldQ_free K0 hn (rot128F K0) (rot128F_count K0) ab.2 (by simp [directFree, (foldPairsA_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsA_geom.2.1] at a1 a2
  simp only [bodyA, wires_append, Finset.mem_union] at bad
  rcases bad with (b | b | b) | b
  · exact a1 q hq b
  · exact a2 q hq b
  · exact loopA_avoids_workTA q hq b
  · exact (by rw [workTA_lit, K0_eq]; decide +kernel : ∀ x ∈ workTA, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 7 K0.core.cin b))

theorem bodyA_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyA := by
  intro q hq bad
  rcases Finset.mem_union.mp (bodyA_wires_plain bad) with h | h
  · exact A109SignResearch.direct_body_holes loopA hs (fun x hx => (StairSqLoopA.holes_geometry44.2.1 x hx).1) loopA_avoids_hs q hq h
  · exact (foldPairsA_geom.2.2.2.2 q (by rw [foldPairsA_geom.2.2.1]; exact List.mem_toFinset.mp h)).1 hq

theorem bodyA_physical : GatePhysical bodyA := by
  have p0 := A109SignResearch.direct_body_physical loopA (hostRename_physical _ _ loopPCA_physical)
  simp only [A109SignResearch.directBody, A109SignResearch.directRawBody, gatePhysical_append] at p0
  simp only [bodyA, dF1A, dF2A, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, ⟨hostRename_physical _ _ p0.1.2.1, p0.1.2.2⟩⟩, p0.2⟩

theorem bodyA_counts :
    toffoliCount bodyA = toffoliCount A109SignResearch.body + 79 ∧
    measurementCount bodyA = measurementCount A109SignResearch.body := by
  have c0 := A109SignResearch.direct_body_counts loopA
  have cl := loopA_counts
  have r1 := hostRename_counts foldPairsA (directFoldQTq K0 (negP K0))
  have r2 := hostRename_counts foldPairsA (directFoldQTq K0 (rot128F K0))
  have eqT : toffoliCount bodyA = toffoliCount (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      toffoliCount_append, r1.1, r2.1]
  have eqM : measurementCount bodyA = measurementCount (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      measurementCount_append, r1.2, r2.2]
  rw [eqT, eqM]
  exact ⟨by omega, by omega⟩

theorem bodyA_slots : Challenge.gateSlots bodyA + 793 = Challenge.gateSlots A109SignResearch.body := by
  have s0 := A109SignResearch.direct_body_slots loopA
  have sl := loopA_slots
  have r1 := hostRename_slots foldPairsA (directFoldQTq K0 (negP K0))
  have r2 := hostRename_slots foldPairsA (directFoldQTq K0 (rot128F K0))
  have eqS : Challenge.gateSlots bodyA = Challenge.gateSlots (A109SignResearch.directBody loopA) := by
    simp only [bodyA, dF1A, dF2A, A109SignResearch.directBody, A109SignResearch.directRawBody, la_eq_K0,
      Challenge.gateSlots_append, r1, r2]
  rw [eqS]
  omega

theorem bodyAPlain_coarse :
    wires bodyAPlain ⊆ insert D0 (G0 :: K0.wires).toFinset :=
  A109SignResearch.direct_body_coarse_S loopA loopA_support

theorem bodyAPlain_fine :
    wires bodyAPlain ⊆ insert D0 (wires (InverseCarryDevelop.hostedADual K0
      (LowZero18Square.foldPerm K0 E0) G0)) :=
  A109SignResearch.direct_body_fine_S loopA loopA_support

end BodyA

/-! ## Branch B body (`keepB` = 19 carries, `efSwapB` = 20 swaps, avoids `workTB`, `hs`, `normFlag`) -/

section BodyB
open ControlLoan1589BFFold ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq ControlLoan1589BFFold.eAddLo ControlLoan1589BFFold.eSubK ParkCarryDevelop.program ParkCarry10Develop.rebuild

private theorem lb_eq_K0 : StairSqBodyB.LB = K0 := rfl
private theorem cb_eq_G0 : StairSqBodyB.cB = G0 := rfl

def keepB : List Wire := (B95Research.keepK.filter (fun q => !workTB.contains q)).take 19

theorem keepB_geometry : keepB.Nodup ∧ keepB.length = 19 ∧
    (∀ q ∈ keepB, q ∈ B95Research.hosts) ∧
    (∀ q ∈ workTB, q ∉ keepB) ∧
    (∀ i, i < 44 → LowAccCarryDevelop.hosts88.getD i 0 ∉ keepB) ∧
    (4761 : Wire) ∉ keepB ∧
    (∀ q ∈ keepB, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepB, keepKB_fast, workTB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepB, keepKB_fast, workTB_lit, hs_lit]; decide +kernel))
  have hr : keepB.Nodup ∧ keepB.length = 19 ∧
      (∀ q ∈ keepB, q ∈ B95Research.hosts) ∧
      (∀ q ∈ workTB, q ∉ keepB) ∧
      (∀ i, i < 44 → LowAccCarryDevelop.hosts88.getD i 0 ∉ keepB) ∧
      (4761 : Wire) ∉ keepB := by rw [keepB, keepKB_fast, hostsB95_fast, hosts88_fast, workTB_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, hall⟩

def rawFB : Program := ReorderedGenericCache.cachedAdd 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
def newFB : Program := B95Research.head ++ B95LowEraseResearch.clear ++ rawFB ++ B95Research.top
def newIB : Program := B95Research.preInv ++ ReorderedConsumedSub.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
def coreB : Program := (newFB ++ B95Research.M ++ newIB) ++ (B95LowEraseResearch.clear ++ B95Research.tail)
def restB : Program := B95LowEraseResearch.clear ++ rawFB ++ B95Research.top ++ B95Research.M ++ newIB ++ B95LowEraseResearch.clear ++ B95Research.tail
def loopPCB : Program := KnownBHeadResearch.output ++ restB
def loopB : Program := hostRename (StairSqLoopB.pairs hs) loopPCB
def foldPairsB : List (Wire × Wire) := (workTB.take 31).zip (K0.core.pad.take 31)
def dF1B : Program := hostRename foldPairsB (directFoldQTq K0 (negP K0))
def dF2B : Program := hostRename foldPairsB (directFoldQTq K0 (rot128F K0))
def efoldB : Program := hostRename efSwapB StairSquareBEFoldK.efold
def bodyB : Program :=
  StairSquareBBody.bodyG K0 dF1B dF2B loopB efoldB LocalRebuild.improved ++
    ReorderedRecordPadding.program 4 K0.core.cin

theorem foldPairsB_geom :
    (holesOf foldPairsB ++ hostsOf foldPairsB).Nodup ∧
    holesOf foldPairsB = workTB.take 31 ∧
    hostsOf foldPairsB = K0.core.pad.take 31 ∧
    (∀ ab ∈ foldPairsB, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsB, q ∉ hs ∧ q ≠ K0.core.normFlag ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsB, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsB, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsB, workTB_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsB ++ hostsOf foldPairsB).Nodup ∧
      holesOf foldPairsB = workTB.take 31 ∧
      hostsOf foldPairsB = K0.core.pad.take 31 ∧
      (∀ ab ∈ foldPairsB, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsB, q ∉ hs ∧ q ≠ K0.core.normFlag) := by
    rw [foldPairsB, workTB_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; have h := hr.2.2.2.2 q hq
    exact ⟨h.1, h.2, hK q hq, hall q hq⟩

private theorem keepB_sub (q : Wire) (hq : q ∈ keepB) : q ∈ B95Research.hosts := keepB_geometry.2.2.1 q hq

private theorem core_plainB (s : State) (m : List Bool)
    (hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ ReorderedBPrefixResearch.bank, s.basis q = false)
    (hi : s.basis ReorderedBPrefixResearch.cin = false) (ha : regValue ReorderedBPrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedBSupportResearch.hosts, s.basis q = false)
    (after : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      (regValue ReorderedBPrefixResearch.src s.basis) (middleState B95Research.oldF B95Research.oldM s m))
    (flag : (run B95Research.oldF (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false) :
    run coreB m s = run (B95Research.oldF ++ B95Research.oldM ++
      ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
  let H := regValue ReorderedBPrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 19 H (976 * H / 1024)
  have fwdM : measurementCount newFB = measurementCount B95Research.F := by
    have h := (ReorderedGenericCache.count_balance 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFB, rawFB, B95Research.F, B95Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIB = measurementCount B95Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)
    simp only [newIB, B95Research.I, B95Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((B95Research.cs.drop 4).take 19).map (run (carryPrefix (4 + 19) B95Research.xs B95Research.ys B95Research.cs ReorderedBPrefixResearch.cin) []
      (run (B95Research.head ++ B95LowEraseResearch.clear)
        ((m.take (measurementCount B95Research.F)).take (measurementCount (B95Research.head ++ B95LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount B95Research.F)).take (measurementCount (B95Research.head ++ B95LowEraseResearch.clear))
    let u := run B95Research.head m0 s
    let t := run (B95Research.head ++ B95LowEraseResearch.clear) m0 s
    have te : t = B95LowEraseResearch.erase u := B95Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 128 := by simpa only [H, ReorderedBPrefixResearch.source_length] using regValue_lt ReorderedBPrefixResearch.src s.basis
    have ready := ReorderedHeadArithmeticResearch.ready ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
      ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ B95Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact B95LowEraseResearch.bit_same _ q (B95Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ B95Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 19 H (((2 ^ 138 - 48 * H) % 2 ^ 138) / 1024) (976 * H / 1024)
      B95Research.xs B95Research.ys B95Research.cs ReorderedBPrefixResearch.cin t
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) B95Research.raw_nd
      (fun q hq => (eb q (B95Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ B95Research.cin_in).trans ready.2.1)
      ((er _ B95Research.x_in).trans ready.2.2.1)
      ((er _ B95Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 128 + 10 = 138 by decide] using ReorderedCacheArithmetic.high_add_low 128 (4 + j + 1) H (by omega) hH)
  have forward : run newFB (m.take (measurementCount B95Research.F)) s =
      scatterState keepB vs (run B95Research.F (m.take (measurementCount B95Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (B95Research.head ++ B95LowEraseResearch.clear) B95Research.top
      19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) keepB_geometry.1
      (fun q hq bad => B95Research.geometry.2.2 q (keepB_sub q hq) (by clear * - bad; simp only [B95Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => B95Research.rawF_off q (keepB_sub q hq)) (fun q hq => B95Research.top_off q (keepB_sub q hq))
      s (m.take (measurementCount B95Research.F))
      (fun q hq => B95Research.prefix_zero s _ hz hb hi ha zero q (keepB_sub q hq))
    rw [fwdVal] at h; exact h
  have mid := B95Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFB ++ B95Research.M ++ newIB) m s = run (B95Research.F ++ B95Research.M ++ B95Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent B95Research.F newFB B95Research.M B95Research.I newIB keepB vs
      fwdM (fun q hq => B95Research.middle_fresh q (keepB_sub q hq))
      (fun q hq => B95Research.I_off q (keepB_sub q hq)) keepB_geometry.1 s m
      (fun q hq => B95Research.forward_zero s _ hz hb hi ha zero q (keepB_sub q hq)) forward
    rw [mid]
    let ms := middleState B95Research.oldF B95Research.oldM s m
    let mr := m.drop (measurementCount B95Research.F + measurementCount B95Research.M)
    let t := scatterState keepB vs (B95LowEraseResearch.erase ms)
    have comm : run B95Research.preInv mr t = scatterState keepB vs (B95LowEraseResearch.erase (run B95Research.preInv mr ms)) := by
      rw [show t = scatterState keepB vs (B95LowEraseResearch.erase ms) from rfl,
        run_scatter B95Research.preInv keepB vs _ _ (fun q hq => B95Research.preInv_off q (keepB_sub q hq)),
        B95LowEraseResearch.commute B95Research.preInv mr ms (fun q hq => B95Research.preInv_off q (B95Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ B95Research.domain) : (run B95Research.preInv mr t).basis q = (run B95Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepB vs _ q (fun bad => B95Research.geometry.2.2 q (keepB_sub q bad) hq)]
      exact B95LowEraseResearch.bit_same _ q (B95Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ B95Research.domain) :
        regValue r (run B95Research.preInv mr t).basis = regValue r (run B95Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := B95Research.pre_raw_ready H ms mr after
    have saved : keepB.map t.basis = vs := scatter_saved_map keepB vs _ keepB_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepB_geometry.2.1, List.length_range])
    have same : keepB.map (run B95Research.preInv mr t).basis = keepB.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside B95Research.preInv mr t q (B95Research.preInv_off q (keepB_sub q hq)))
    simp only [newIB, B95Research.I, B95Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide)
      (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
      (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])
      B95Research.raw_nd keepB_geometry.1 keepB_geometry.2.1 (fun q hq => B95Research.geometry.2.2 q (keepB_sub q hq))
      (run B95Research.preInv mr t) _ (fun q hq => (bits q (B95Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ B95Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ B95Research.x_in).trans rr.2.2.1) ((regs _ B95Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFB ++ B95Research.M ++ newIB)
    (B95Research.F ++ B95Research.M ++ B95Research.I) (B95LowEraseResearch.clear ++ B95Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (B95Research.F ++ B95Research.M ++ B95Research.I) ++ (B95LowEraseResearch.clear ++ B95Research.tail) =
      B95Research.F ++ B95Research.M ++ (B95Research.I ++ B95LowEraseResearch.clear ++ B95Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (B95Research.plain_loop s m hz hb hi ha after flag))

private theorem keepB_cached_wires : wires rawFB ⊆ B95Research.domain.toFinset ∪ keepB.toFinset :=
  (ReorderedSupport.cached 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
    (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])).1

private theorem keepB_consumed_wires :
    wires (ReorderedConsumedSub.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin) ⊆
      B95Research.domain.toFinset ∪ keepB.toFinset :=
  ReorderedSupport.consumed 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    (by rw [B95Research.raw_lengths.1, B95Research.raw_lengths.2.1])
    (by rw [B95Research.raw_lengths.2.1, B95Research.raw_lengths.2.2])

theorem loopPCB_off (h : Wire) (hh : h ∈ ReorderedBSupportResearch.hosts) (hk : h ∉ keepB) : h ∉ wires loopPCB := by
  have hA : h ∈ B95Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedBSupportResearch.plain_free h hh).1
  rw [B95Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) := (ReorderedBSupportResearch.plain_free h hh).2
  rw [B95Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires B95LowEraseResearch.clear := by
    rw [StairSqLoopB.clear_wires]; intro bad
    exact B95Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ B95Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ B95Research.domain.toFinset ∪ keepB.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨B95Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCB, restB, newIB, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (KnownBHeadResearch.support bad), clearOff, fun bad => out (keepB_cached_wires bad),
    B95Research.top_off h hA, B95Research.middle_fresh h hA, B95Research.preInv_off h hA,
    fun bad => out (keepB_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCB_support : wires loopPCB ⊆ B95Research.S := by
  have ks : B95Research.domain.toFinset ∪ keepB.toFinset ⊆ B95Research.S := by
    intro q hq; apply B95Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepB_sub q h)
  simp only [loopPCB, restB, newIB, wires_append, Finset.union_subset_iff]
  exact ⟨KnownBHeadResearch.support.trans B95Research.endpoint_support.1,
    ⟨⟨⟨⟨⟨⟨B95Research.clear_support, keepB_cached_wires.trans ks⟩, B95Research.endpoint_support.2.1⟩,
      B95Research.middle_support⟩, ⟨B95Research.endpoint_support.2.2.1, keepB_consumed_wires.trans ks⟩⟩,
      B95Research.clear_support⟩, B95Research.endpoint_support.2.2.2⟩⟩

theorem loopPCB_physical : GatePhysical loopPCB := by
  have f := ReorderedPhysical.cached 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
    (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
    (by rw [B95Research.raw_lengths.2.2]; decide)
    B95Research.raw_nd (fun q hq bad => B95Research.geometry.2.2 q (keepB_sub q hq) (B95Research.c_in q bad))
  have n := notRegister_physical B95Research.ys
  simp only [loopPCB, restB, newIB, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨KnownBHeadResearch.physical B95Research.endpoint_physical.1,
    ⟨⟨⟨⟨⟨⟨B95LowEraseResearch.physical, f.1⟩, B95Research.endpoint_physical.2.1⟩,
      B95AliasesResearch.physical⟩, ⟨B95Research.endpoint_physical.2.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      B95LowEraseResearch.physical⟩, B95Research.endpoint_physical.2.2.2⟩⟩

theorem loopB_pairs_free : ∀ ab ∈ StairSqLoopB.pairs hs, ab.2 ∉ wires loopPCB := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCB_off _ (StairSqLoopB.hosts_of_88 _ (StairSqLoopB.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepB_geometry.2.2.2.2.1 _ h

theorem loopB_support : wires loopB ⊆ B95Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCB_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopB.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact B95Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopB.hosts_of_88 _ (StairSqLoopB.holes_geometry44.2.2 y hy))))))

theorem loopB_avoids_hs : ∀ q ∈ hs, q ∉ wires loopB := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free
  rw [StairSqLoopB.pairs_fst] at h; exact h q hq

theorem loopB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires loopB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    have park := ParkCarry10Develop.body_support StairSqBodyB.LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup StairSqBodyB.cB
    have hsup := park (FullB99OptTemp.actual_subset (loopB_support bad))
    rw [lb_eq_K0, cb_eq_G0] at hsup
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp hsup)
  · have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free bad
    rcases Finset.mem_union.mp sub with h | h
    · have hm : ∀ x ∈ workTB, x ≠ D0 → x ∈ ReorderedBSupportResearch.hosts := by rw [workTB_lit, D0_eq, hostsBSup_fast]; decide +kernel
      exact loopPCB_off q (hm q hq hD) (keepB_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
    · rw [StairSqLoopB.pairs_snd] at h
      have dis : ∀ x ∈ workTB, x ∉ hs.map StairSqLoopB.hostOf := by simp only [workTB_lit, StairSqLoopB.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hosts88_fast]; decide +kernel
      exact dis q hq (List.mem_toFinset.mp h)

theorem loopB_normFlag : K0.core.normFlag ∉ wires loopB := by
  have hM := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _)
  have hb := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.build_norm _ (List.mem_singleton_self _)
  have hu := StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.unbuild_norm _ (List.mem_singleton_self _)
  rw [B95Research.plain_split] at hb; rw [B95Research.unbuild_split] at hu
  simp only [wires_append, Finset.mem_union, not_or] at hb hu
  have clearOff : K0.core.normFlag ∉ wires B95LowEraseResearch.clear := by
    rw [StairSqLoopB.clear_wires]; intro h
    exact (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.normFlag ∉ ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire)) (List.mem_toFinset.mp h)
  have out : K0.core.normFlag ∉ B95Research.domain.toFinset ∪ keepB.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]
    exact ⟨fun h => hb.2.1 (by rw [B95Research.raw_wires]; exact List.mem_toFinset.mpr h), keepB_geometry.2.2.2.2.2.1⟩
  have pcNF : K0.core.normFlag ∉ wires loopPCB := by
    have hI := hu.1; simp only [B95Research.I, wires_append, Finset.mem_union, not_or] at hI
    simp only [loopPCB, restB, newIB, wires_append, Finset.mem_union, not_or, and_assoc]
    exact ⟨fun h => hb.1 (KnownBHeadResearch.support h), clearOff, fun h => out (keepB_cached_wires h),
      hb.2.2, hM, hI.1, fun h => out (keepB_consumed_wires h), clearOff, hu.2⟩
  intro bad
  have sub := hostRename_support (StairSqLoopB.pairs hs) loopPCB (StairSqLoopB.pairs_nodup44 hs (List.Sublist.refl _)) loopB_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · exact pcNF (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopB.pairs_snd] at h
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    have hm := StairSqLoopB.holes_geometry44.2.2 y hy; rw [hyx] at hm
    exact (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.normFlag ∉ LowAccCarryDevelop.hosts88) hm

theorem loopB_counts :
    toffoliCount loopB = toffoliCount B95Research.loop + 79 ∧
    measurementCount loopB = measurementCount B95Research.loop := by
  have hr := hostRename_counts (StairSqLoopB.pairs hs) loopPCB
  have rel : toffoliCount loopPCB + 19 = toffoliCount StairSqLoopB.loopNC ∧
      measurementCount loopPCB = measurementCount StairSqLoopB.loopNC := by
    have cb := ReorderedGenericCache.count_balance 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide) (by rw [B95Research.raw_lengths.2.2]; decide)
    rw [loopPCB, restB, rawFB, newIB, StairSqLoopB.loopNC, StairSqLoopB.restNC,
      B95Research.I, B95Research.rawI, B95Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopB.loopNC_counts
  rw [loopB, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopB_slots : Challenge.gateSlots loopB = Challenge.gateSlots B95Research.loop + 231 := by
  have hr := hostRename_slots (StairSqLoopB.pairs hs) loopPCB
  have rel : Challenge.gateSlots loopPCB + 57 = Challenge.gateSlots StairSqLoopB.loopNC := by
    have sc := ReorderedSlots.cache 19 B95Research.xs B95Research.ys B95Research.cs keepB ReorderedBPrefixResearch.cin
      (by rw [B95Research.raw_lengths.1]; decide) (by rw [B95Research.raw_lengths.2.1]; decide)
      (by rw [B95Research.raw_lengths.2.2]; decide) keepB_geometry.2.1
    rw [loopPCB, restB, rawFB, newIB, StairSqLoopB.loopNC, StairSqLoopB.restNC,
      B95Research.I, B95Research.rawI, B95Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopB.loopNC_slots
  rw [loopB, hr]
  omega

theorem loopB_frame (base : BasisState) (clean : K0.PairClean base) (hsum : base K0.core.sumCarry = false)
    (O E O' : Nat) (hE : E < 2 ^ 129)
    (mid : Triple (BState K0 base O E (4294968272 * regValue (hiReg K0) base)) (FullBTemp.middle K0 G0)
      (BState K0 base O' E (4294968272 * regValue (hiReg K0) base))) :
    Triple (BState K0 base O E 0) loopB (BState K0 base O' E 0) := by
  have pcFrame : Triple (BState K0 base O E 0) loopPCB (BState K0 base O' E 0) := by
    intro s m hsB
    obtain ⟨hzFull, hb, hi, _, _⟩ := zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O E 0 s.basis hsB
    have hz : ∀ q ∈ ReorderedBPrefixResearch.pad, s.basis q = false := fun q hq => hzFull q ((FullPadDevelop.pad_sublist K0).subset hq)
    have ha : regValue LowAccCarryDevelop.ga s.basis = 0 := LowAccCarryDevelop.ga_bstate_value base s.basis clean O E 0 hsB (by decide)
    have small : regValue ReorderedBPrefixResearch.acc s.basis = 0 := by
      rw [regValue_take_mod LowAccCarryDevelop.ga 161 (by rw [LowAccCarryDevelop.ga_length]; decide), ha]; rfl
    have headEq : run loopPCB m s = run coreB m s := by
      have cl : ∀ q ∈ KnownBHeadResearch.clean, s.basis q = false := by
        intro q hq; simp only [KnownBHeadResearch.clean, List.mem_append, List.mem_singleton] at hq
        rcases hq with ((hq | hq) | hq) | rfl
        · exact (regValue_zero _ _).mp small q hq
        · exact hz q hq
        · exact hb q hq
        · exact hi
      have hheadEq : B95Research.head = KnownBHeadResearch.original := by
        unfold B95Research.head KnownBHeadResearch.original; rfl
      have shape : coreB = KnownBHeadResearch.original ++ restB := by
        rw [coreB, newFB, restB, hheadEq]
        have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
        exact g _ _ _ _ _ _ _ _
      exact (ClearContextResearch.append_at KnownBHeadResearch.output KnownBHeadResearch.original restB s m
        KnownBHeadResearch.measurements (KnownBHeadResearch.run_eq s m cl)).trans (congrArg (fun P => run P m s) shape.symm)
    rw [headEq]
    have zero : ∀ q ∈ ReorderedBSupportResearch.hosts, s.basis q = false := by
      intro q hq; rcases List.mem_cons.mp hq with rfl | hq
      · have away := ParkCarryDevelop.sumCarry_off_regs K0 LowAccCarryDevelop.layout_nodup
        exact (hsB.2.2.2 _ away.1 away.2.1 away.2.2).trans hsum
      · exact LowAccCarryDevelop.initial_hosts_zero base s.basis clean O E hsB q hq
    have good := fun r => ReorderedBReadyResearch.original_ready base clean O E O' mid s r hsB
    have hc : ExtraCarryDomain.Clean s.basis := ⟨bstate_clean K0 LowAccCarryDevelop.layout_nodup base clean O E s.basis hsB, by change regValue (eReg K0) s.basis < 2 ^ 129; rw [hsB.2.1]; exact hE⟩
    have ready : WReady ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank
        ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src (regValue ReorderedBPrefixResearch.src s.basis)
        (middleState B95Research.oldF B95Research.oldM s m) :=
      BRelocatedReadyResearch.patched_after s m hc hz hb hi ha zero good
    have f := ReorderedAPlain.build_triple ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
      ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src
      ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits s.basis hz hb hi s
      (m.take (measurementCount B95Research.oldF)) ⟨small, fun _ _ => rfl⟩
    have flag0 := (f.2.2 4762 (by simp only [ReorderedBPrefixResearch.acc, ReorderedBPrefixResearch.pad, ReorderedBPrefixResearch.bank, ReorderedBPrefixResearch.cin, ReorderedBPrefixResearch.src, ReorderedBPrefixResearch.ga, LowAccCarryDevelop.ga, LowAccCarryDevelop.L, FullBReady.L, show Baselines.layout.dialogStreamedSquareWide = K0 from rfl, K0_eq]; decide +kernel)).trans hc.1.modFlag
    have e : B95Research.oldF = ReorderedAPlain.build ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad
        ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src := rfl
    have flag : (run B95Research.oldF (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false :=
      (congrArg (fun P => (run P (m.take (measurementCount B95Research.oldF)) s).basis 4762 = false) e).mpr flag0
    have one := core_plainB s m hz hb hi small zero ready flag
    have two : run BPatchedLoopResearch.core m s =
        run (B95Research.oldF ++ B95Research.oldM ++ ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src) m s := by
      simpa only [BPatchedLoopResearch.core, B95Research.oldF, B95Research.oldM] using
        HighCachedLoopBResearch.loop_eq ReorderedBPrefixResearch.acc ReorderedBMiddlePatchesResearch.output
          ReorderedBPrefixResearch.acc_length ReorderedBPrefixResearch.fits rfl s m hz hb hi small
          ReorderedBSupportResearch.fresh (fun q hq => (ReorderedBSupportResearch.plain_free q hq).1)
          (fun q hq => (ReorderedBSupportResearch.plain_free q hq).2) ReorderedBMiddlePatchesResearch.fresh zero ready
    rw [one.trans two.symm]
    exact BPatchedLoopResearch.core_frame base clean hsum O E O' hE mid s m hsB
  intro s m hsB
  have r := pcFrame s m hsB
  have zIn := (zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O E 0 s.basis hsB).2.2.2.1
  have zOut := (zero_regs K0 LowAccCarryDevelop.layout_nodup base clean O' E 0 (run loopPCB m s).basis r.2).2.2.2.1
  have hOut : ∀ q ∈ hs, (run loopPCB m s).basis q = false := fun q hq => zOut q (StairSqLoopB.holes_geometry44.2.1 q hq)
  have hEq : run loopB m s = run loopPCB m s := by
    apply hostRename_run_eq (StairSqLoopB.pairs hs) loopPCB s m
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact zIn y (StairSqLoopB.holes_geometry44.2.1 y hy)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact LowAccCarryDevelop.initial_hosts_zero base s.basis clean O E hsB _ (StairSqLoopB.holes_geometry44.2.2 y hy)
    · intro ab hab; obtain ⟨y, hy, he⟩ := List.mem_map.mp hab
      have h1 : ab.1 = y := by rw [← he]
      rw [h1]; exact hOut y hy
    · exact loopB_pairs_free
  rw [hEq]; exact r

private def efCheckB : List Wire :=
  [4726, 4727, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736, 4737, 4738, 4739, 4740, 4741,
   4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4756]

private theorem efold_avoids_check : ∀ q ∈ efCheckB, q ∉ wires StairSquareBEFoldK.efold := by
  have hflip : ∀ q ∈ efCheckB, q ∉ wires (ControlLoan1589BFFold.eFlip K0 G0) :=
    StairSquareBChecks.touchedAny_spec _ _
      (StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [K0_eq, G0_eq]; decide +kernel))
  have hfill : ∀ q ∈ efCheckB, q ∉ StairSquareBChecks.K2Fill.efillS K0 :=
    StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [K0_eq]; decide +kernel)
  have hsup := StairSquareBChecks.K2Fill.efill_support K0 hwK LowAccCarryDevelop.layout_nodup
  have h3 : ∀ q ∈ efCheckB,
      q ∉ (StairSquareBEFold.coreB K0).out ++ (StairSquareBEFold.coreB K0).carry ++
        [(StairSquareBEFold.coreB K0).high, (StairSquareBEFold.coreB K0).cin,
         (StairSquareBEFold.coreB K0).flag] ++ ECDSAAdd.Entrant.accReg K0 :=
    StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [K0_eq]; decide +kernel)
  intro q hq bad
  simp only [StairSquareBEFoldK.efold, StairSquareBEFold.eFoldB, StairSquareBEFold.accFoldB,
    lb_eq_K0, cb_eq_G0, wires_append, Finset.mem_union] at bad
  rcases bad with hw | ((hw | hw) | hw) | hw
  · exact hflip q hq hw
  · exact hfill q hq (List.mem_toFinset.mp (hsup.1 hw))
  · have hs := StairSquareBMapped.qprogM_support (StairSquareBEFold.coreB K0)
      (StairSquareBEFold.bitsB K0) SquareReduction.p hw
    rw [StairSquareBEFold.bitsB_wires] at hs
    exact h3 q hq (List.mem_toFinset.mp hs)
  · exact hfill q hq (List.mem_toFinset.mp (hsup.2 hw))
  · exact hflip q hq hw

/-- `efoldB` satisfies `StairSqBodyB.EFoldOK` AND avoids `workTB`, `hs`, and `normFlag`. -/
theorem efoldB_hostFree : ∀ ab ∈ efSwapB, ab.2 ∉ wires StairSquareBEFoldK.efold := fun ab hab =>
  efold_avoids_check ab.2 ((by rw [efSwapB_lit]; decide +kernel : ∀ p ∈ efSwapB, p.2 ∈ efCheckB) ab hab)

theorem efoldB_ok : StairSqBodyB.EFoldOK efoldB := by
  have baseOK := StairSqBodyB.efold_ok
  refine ⟨?_, ?_, ?_, hostRename_physical _ _ baseOK.2.2.2⟩
  · intro b clean O E hO s m hsB
    have r := baseOK.1 b clean O E hO s m hsB
    have hEq : run efoldB m s = run StairSquareBEFoldK.efold m s := by
      apply hostRename_run_eq efSwapB StairSquareBEFoldK.efold s m
      · intro ab hab
        have h1 : ab.1 ∈ LowAccCarryDevelop.hosts88 := (by rw [efSwapB_lit, hosts88_fast]; decide +kernel : ∀ x ∈ holesOf efSwapB, x ∈ LowAccCarryDevelop.hosts88) ab.1 (List.mem_map.mpr ⟨ab, hab, rfl⟩)
        exact LowAccCarryDevelop.initial_hosts_zero b s.basis clean O E hsB ab.1 h1
      · intro ab hab
        have h2 : ab.2 ∈ LowAccCarryDevelop.hosts88 := List.mem_of_mem_take (work_T_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ab hab).2.2.1
        exact LowAccCarryDevelop.initial_hosts_zero b s.basis clean O E hsB ab.2 h2
      · intro ab hab
        have h1 : ab.1 ∈ LowAccCarryDevelop.hosts88 := (by rw [efSwapB_lit, hosts88_fast]; decide +kernel : ∀ x ∈ holesOf efSwapB, x ∈ LowAccCarryDevelop.hosts88) ab.1 (List.mem_map.mpr ⟨ab, hab, rfl⟩)
        exact LowAccCarryDevelop.initial_hosts_zero b (run StairSquareBEFoldK.efold m s).basis clean _ E r.2 ab.1 h1
      · exact efoldB_hostFree
    rw [hEq]; exact r
  · intro q hq
    have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree hq
    rcases Finset.mem_union.mp sub with h | h
    · exact baseOK.2.1 (Finset.mem_sdiff.mp h).1
    · have subK : ∀ x ∈ hostsOf efSwapB, x ∈ K0.wires := by rw [efSwapB_lit, K0_eq]; decide +kernel
      rw [lb_eq_K0, cb_eq_G0]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem G0 (subK q (List.mem_toFinset.mp h)))
  · intro q hq bad
    have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
    rcases Finset.mem_union.mp sub with h | h
    · exact baseOK.2.2.1 q hq (Finset.mem_sdiff.mp h).1
    · exact (by rw [efSwapB_lit, holesA_lit]; decide +kernel : ∀ x ∈ StairSqLoopA.holes, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires efoldB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    have hsup := efoldB_ok.2.1 bad
    rw [lb_eq_K0, cb_eq_G0] at hsup
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp hsup)
  · by_cases hh : q ∈ holesOf efSwapB
    · exact hostRename_avoids efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree q hh bad
    · have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
      rcases Finset.mem_union.mp sub with h | h
      · exact efold_avoids_check q ((by rw [workTB_lit, D0_eq, efSwapB_lit]; decide +kernel : ∀ x ∈ workTB, x ≠ D0 → x ∉ holesOf efSwapB → x ∈ efCheckB) q hq hD hh) (Finset.mem_sdiff.mp h).1
      · exact (by rw [workTB_lit, efSwapB_lit]; decide +kernel : ∀ x ∈ workTB, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_avoids_hs : ∀ q ∈ hs, q ∉ wires efoldB := by
  intro q hq bad
  have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
  rcases Finset.mem_union.mp sub with h | h
  · exact StairSquareBEFoldK.efold_avoids q hq (Finset.mem_sdiff.mp h).1
  · exact (by rw [efSwapB_lit, hs_lit]; decide +kernel : ∀ x ∈ hs, x ∉ hostsOf efSwapB) q hq (List.mem_toFinset.mp h)

theorem efoldB_normFlag : K0.core.normFlag ∉ wires efoldB := by
  intro bad
  have sub := hostRename_support efSwapB StairSquareBEFoldK.efold work_T_geometry.2.2.2.2.2.2.2.1 efoldB_hostFree bad
  rcases Finset.mem_union.mp sub with h | h
  · exact StairSquareBEFoldK.efold_normFlag (Finset.mem_sdiff.mp h).1
  · exact (by rw [efSwapB_lit, K0_eq]; decide +kernel : K0.core.normFlag ∉ hostsOf efSwapB) (List.mem_toFinset.mp h)

theorem bodyB_ok : BodyBOK bodyB := by
  have hn := LowAccCarryDevelop.layout_nodup
  have hcw : G0 ∉ K0.wires := (List.nodup_cons.mp controlND).1
  have sup : wires bodyB ⊆ (G0 :: K0.wires).toFinset := by
    have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
    have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
    have direct_in_K0 (f : MeasuredSquareFold) (hc : ∀ q, f.src.count q ≤ K0.core.product.count q) :
        wires (directFoldQTq K0 f) ⊆ K0.wires.toFinset := by
      intro q hq
      have h1 := List.count_pos_iff.mpr (List.mem_toFinset.mp (directFoldQ_supportTq K0 f hq))
      have h2 := hc q
      simp only [directWires, List.count_append, List.count_cons, List.count_nil] at h1
      exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by
        simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires,
          List.count_append, List.count_cons, List.count_nil]; omega))
    have f1 : wires dF1B ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rcases Finset.mem_union.mp (sp1 hq) with h | h
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (direct_in_K0 (negP K0) (negP_count K0) (Finset.mem_sdiff.mp h).1)))
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).2.2.1)
    have f2 : wires dF2B ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rcases Finset.mem_union.mp (sp2 hq) with h | h
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (direct_in_K0 (rot128F K0) (rot128F_count K0) (Finset.mem_sdiff.mp h).1)))
      · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).2.2.1)
    have park := ParkCarry10Develop.body_support StairSqBodyB.LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup StairSqBodyB.cB
    have fl : wires loopB ⊆ (G0 :: K0.wires).toFinset := by
      rw [← lb_eq_K0, ← cb_eq_G0]
      exact loopB_support.trans (fun q hq => park (FullB99OptTemp.actual_subset hq))
    have fpad : wires (ReorderedRecordPadding.program 4 K0.core.cin) ⊆ (G0 :: K0.wires).toFinset := by
      intro q hq; rw [Finset.mem_singleton.mp (padding_wires 4 K0.core.cin hq)]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (by simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires]))
    have r0 := StairSqBodyB.bodyB_support44 hs (List.Sublist.refl _)
    simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
      lb_eq_K0, cb_eq_G0, wires_append, Finset.union_subset_iff] at r0
    simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
      wires_append, Finset.union_subset_iff]
    have heSup : wires efoldB ⊆ (G0 :: K0.wires).toFinset := by rw [← lb_eq_K0, ← cb_eq_G0]; exact efoldB_ok.2.1
    exact ⟨⟨f1, f2, ⟨r0.1.2.2.1.1, fl, r0.1.2.2.1.2.2.1, r0.1.2.2.1.2.2.2⟩, heSup, r0.1.2.2.2.2⟩, fpad⟩
  refine ⟨sup, ?_⟩
  intro base M hM hP hc hsum O hO hg hSource
  have hb : M ^ 2 < 2 ^ 256 := by simpa using square_bound M 128 hM
  have views := accA_views K0 hwK base M hM hP
  have v1 : K0.MeasuredFoldView base (negP K0) := views (.inl (negP K0)) (by simp [accAMix])
  have v2 : K0.MeasuredFoldView base (rot128F K0) := views (.inl (rot128F K0)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP K0) = M ^ 2 := by
    simp only [measuredFoldPayload, negP, pow_zero, Nat.mul_one]
    rw [K0.product_take_value hwK base (M ^ 2) hP 256 (by omega), Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F K0) = (M ^ 2 / 2 ^ 128) % 2 ^ 128 + 2 ^ 128 * (M ^ 2 % 2 ^ 128) := by
    simp only [measuredFoldPayload, rot128F, pow_zero, Nat.mul_one]
    exact K0.rotated128_value hwK base (M ^ 2) hP
  have f1 : ∀ O0, O0 < SquareReduction.p → Triple (SquareFrame K0.core.out base O0) dF1B
      (SquareFrame K0.core.out base ((M ^ 2 + (SquareReduction.p - 1 - O0)) % SquareReduction.p)) := by
    intro O0 hO0 s m hf
    have eq1 := directFold_rename_run foldPairsB (negP K0) (negP_count K0) (negP_length K0 hwK) rfl rfl
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).1, (foldPairsB_geom.2.2.2.1 ab hab).2.1⟩)
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).2.2.1, (foldPairsB_geom.2.2.2.1 ab hab).2.2.2.1⟩)
      base v1 hc O0 hO0 s m hf
    rw [dF1B, eq1]
    have h := directFoldQ_frameTq K0 hwK hn base (negP K0) v1 rfl hc (negP_length K0 hwK) rfl O0 hO0 s m hf
    rwa [pay1] at h
  have f2 : ∀ O0, O0 < SquareReduction.p → Triple (SquareFrame K0.core.out base O0) dF2B
      (SquareFrame K0.core.out base
        (((M ^ 2 / 2 ^ 128) % 2 ^ 128 + 2 ^ 128 * (M ^ 2 % 2 ^ 128) + (SquareReduction.p - 1 - O0)) % SquareReduction.p)) := by
    intro O0 hO0 s m hf
    have eq2 := directFold_rename_run foldPairsB (rot128F K0) (rot128F_count K0) (rot128F_length K0 hwK) rfl rfl
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).1, (foldPairsB_geom.2.2.2.1 ab hab).2.1⟩)
      (fun ab hab => ⟨(foldPairsB_geom.2.2.2.1 ab hab).2.2.1, (foldPairsB_geom.2.2.2.1 ab hab).2.2.2.1⟩)
      base v2 hc O0 hO0 s m hf
    rw [dF2B, eq2]
    have h := directFoldQ_frameTq K0 hwK hn base (rot128F K0) v2 rfl hc (rot128F_length K0 hwK) rfl O0 hO0 s m hf
    rwa [pay2] at h
  have raw := StairSquareBBody.frameG StairSqBodyB.LB LowAccCarryDevelop.layout_widths hn StairSqBodyB.cB LowAccCarryDevelop.control_outside
    loopB (by rw [lb_eq_K0]; exact loopB_frame)
    efoldB (fun b clean O0 E0 hO0 => efoldB_ok.1 b clean O0 E0 hO0)
    LocalRebuild.improved
    (fun b outB clean O0 E0 B0 hb old => LocalRebuildLift.transfer b outB clean O0 E0 B0 hb old)
    base M hM (by rw [lb_eq_K0]; exact hP) (by rw [lb_eq_K0]; exact hc) (by rw [lb_eq_K0]; exact hsum) O hO
    (by rw [cb_eq_G0]; exact hg) (by rw [lb_eq_K0, cb_eq_G0]; exact hSource)
    dF1B dF2B (by rw [lb_eq_K0]; exact f1) (by rw [lb_eq_K0]; exact f2)
  rw [lb_eq_K0, cb_eq_G0] at raw
  show Triple _ (StairSquareBBody.bodyG K0 dF1B dF2B loopB efoldB LocalRebuild.improved ++
    ReorderedRecordPadding.program 4 K0.core.cin) _
  apply raw.seq
  intro t r ht
  have hz : t.basis K0.core.cin = false :=
    (ht.2 K0.core.cin (K0.pairAuxAway hn _ (by simp)).2).trans hc.cin
  rw [ReorderedRecordPadding.run_zero 4 K0.core.cin t r hz]
  exact ⟨rfl, ht⟩

theorem bodyB_avoids_workTB : ∀ q ∈ workTB, q ∉ wires bodyB := by
  intro q hq bad
  by_cases hD : q = D0
  · subst hD
    exact (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (List.mem_toFinset.mp (bodyB_ok.support bad))
  have hq31 : q ∈ workTB.take 31 := (by rw [workTB_lit, D0_eq]; decide +kernel : ∀ x ∈ workTB, x ≠ D0 → x ∈ workTB.take 31) q hq hD
  have hn := LowAccCarryDevelop.layout_nodup
  have a1 := hostRename_avoids foldPairsB (directFoldQTq K0 (negP K0)) foldPairsB_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negP K0) (negP_count K0) ab.2 (by simp [directFree, (foldPairsB_geom.2.2.2.1 ab hab).2.2.1]))
  have a2 := hostRename_avoids foldPairsB (directFoldQTq K0 (rot128F K0)) foldPairsB_geom.1
    (fun ab hab => directFoldQ_free K0 hn (rot128F K0) (rot128F_count K0) ab.2 (by simp [directFree, (foldPairsB_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsB_geom.2.1] at a1 a2
  have offEAdd : ∀ x ∈ workTB, x ∉ wires (ControlLoan1589BFFold.eAddLo K0) :=
    StairSquareBChecks.touchedAny_spec _ _
      (StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [workTB_lit, K0_eq]; decide +kernel))
  have offPark : ∀ x ∈ workTB, x ∉ wires (ParkCarryDevelop.program (ControlLoan1589BFFold.eU K0) K0.core.sumCarry) :=
    StairSquareBChecks.touchedAny_spec _ _
      (StairSquareBChecks.K2Hit.touchedAny_of_mask _ _ (by rw [workTB_lit, K0_eq]; decide +kernel))
  have offESub : ∀ x ∈ workTB, x ∉ wires (ControlLoan1589BFFold.eSubK K0) := fun x hx hw =>
    StairSquareBChecks.LT48B.disj_of_maskL _ _
      (by rw [workTB_lit, show StairSquareBChecks.LB = K0 from rfl, K0_eq]; decide +kernel) x hx
      (List.mem_toFinset.mp (StairSquareBChecks.eSubK_support (by rw [show StairSquareBChecks.LB = K0 from rfl]; exact hw)))
  have offReb : ∀ x ∈ workTB, x ∉ wires LocalRebuild.improved := by
    intro x hx hw
    have hact : x ∈ wires LocalRebuild.actual := LocalRebuildResources.support hw
    rw [LocalRebuild.literal, LocalRebuild.program] at hact
    simp only [wires_append, Finset.mem_union] at hact
    rcases hact with (((h | h) | (h | h)) | ((h | h) | (h | (h | h)))) | (((h | h) | (h | h)) | ((h | h) | (h | (h | h))))
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk0 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk1 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk2 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk3 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk4 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk5 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk6 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk7 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk8 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk9 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk10 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk11 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk12 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk13 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk14 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk15 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk16 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
    · exact StairSquareBChecks.touchedAny_spec _ _ (StairSquareBChecks.K2Hit.touchedAny_of_mask LocalRebuild.chunk17 workTB (by rw [workTB_lit]; decide +kernel)) x hx h
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · exact a1 q hq31 b
  · exact a2 q hq31 b
  · exact offEAdd q hq b
  · exact loopB_avoids_workTB q hq b
  · exact offPark q hq b
  · exact offESub q hq b
  · exact efoldB_avoids_workTB q hq b
  · exact offReb q hq b
  · exact (by rw [workTB_lit, K0_eq]; decide +kernel : ∀ x ∈ workTB, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 4 K0.core.cin b))

theorem bodyB_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyB := by
  intro q hq bad
  have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have h44 := StairSqBodyB.bodyB_avoids44 hs (List.Sublist.refl _) q hq
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, wires_append, Finset.mem_union, not_or] at h44
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact h44.1.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).1 hq
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact h44.1.2.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 q (List.mem_toFinset.mp h)).1 hq
  · exact h44.1.2.2.1.1 b
  · exact loopB_avoids_hs q hq b
  · exact h44.1.2.2.1.2.2.1 b
  · exact h44.1.2.2.1.2.2.2 b
  · exact efoldB_avoids_hs q hq b
  · exact h44.1.2.2.2.2 b
  · exact h44.2 b

theorem bodyB_normFlag : K0.core.normFlag ∉ wires bodyB := by
  have sp1 := directFold_rename_support foldPairsB (negP K0) (negP_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have sp2 := directFold_rename_support foldPairsB (rot128F K0) (rot128F_count K0) foldPairsB_geom.1 (fun ab hab => (foldPairsB_geom.2.2.2.1 ab hab).2.2.1)
  have hnf := StairSqBodyB.bodyB_normFlag44 hs (List.Sublist.refl _)
    (StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _))
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, wires_append, Finset.mem_union, not_or] at hnf
  intro bad
  simp only [bodyB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, wires_append, Finset.mem_union] at bad
  rcases bad with ((b | b | (b | b | b | b) | b | b) | b)
  · rcases Finset.mem_union.mp (sp1 b) with h | h
    · exact hnf.1.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 _ (List.mem_toFinset.mp h)).2.1 rfl
  · rcases Finset.mem_union.mp (sp2 b) with h | h
    · exact hnf.1.2.1 (Finset.mem_sdiff.mp h).1
    · exact (foldPairsB_geom.2.2.2.2 _ (List.mem_toFinset.mp h)).2.1 rfl
  · exact hnf.1.2.2.1.1 b
  · exact loopB_normFlag b
  · exact hnf.1.2.2.1.2.2.1 b
  · exact hnf.1.2.2.1.2.2.2 b
  · exact efoldB_normFlag b
  · exact hnf.1.2.2.2.2 b
  · exact hnf.2 b

theorem bodyB_physical : GatePhysical bodyB := by
  have p0 := StairSqBodyB.bodyB_physical hs
  simp only [StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor,
    StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, gatePhysical_append] at p0
  simp only [bodyB, dF1B, dF2B, efoldB, StairSquareBBody.bodyG, LowAccCarryDevelop.foldFor, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, hostRename_physical _ _ p0.1.2.1,
    ⟨p0.1.2.2.1.1, hostRename_physical _ _ loopPCB_physical, p0.1.2.2.1.2.2.1, p0.1.2.2.1.2.2.2⟩,
    hostRename_physical _ _ StairSquareBEFoldK.efold_physical, p0.1.2.2.2.2⟩, p0.2⟩

theorem bodyB_counts :
    toffoliCount bodyB = toffoliCount B95PaddedResearch.body + 89 ∧
    measurementCount bodyB = measurementCount B95PaddedResearch.body := by
  have c0 := StairSqBodyB.bodyB_counts hs
  have cl_old := StairSqLoopB.loopB_counts hs
  have cl_new := loopB_counts
  have r1 := hostRename_counts foldPairsB (directFoldQTq K0 (negP K0))
  have r2 := hostRename_counts foldPairsB (directFoldQTq K0 (rot128F K0))
  have re := hostRename_counts efSwapB StairSquareBEFoldK.efold
  simp only [bodyB, dF1B, dF2B, efoldB, StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG,
    LowAccCarryDevelop.foldFor, StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, toffoliCount_append, measurementCount_append,
    r1.1, r1.2, r2.1, r2.2, re.1, re.2] at c0 ⊢
  exact ⟨by linarith only [c0.1, cl_old.1, cl_new.1], by linarith only [c0.2, cl_old.2, cl_new.2]⟩

theorem bodyB_slots : Challenge.gateSlots bodyB + 793 ≤ Challenge.gateSlots B95PaddedResearch.body := by
  have s0 := StairSqBodyB.bodyB_slots hs
  have sl_old := StairSqLoopB.loopB_slots hs
  have sl_new := loopB_slots
  have r1 := hostRename_slots foldPairsB (directFoldQTq K0 (negP K0))
  have r2 := hostRename_slots foldPairsB (directFoldQTq K0 (rot128F K0))
  have re := hostRename_slots efSwapB StairSquareBEFoldK.efold
  simp only [bodyB, dF1B, dF2B, efoldB, StairSqBodyB.bodyB, StairSqBodyB.bodyBG, StairSquareBBody.bodyG,
    LowAccCarryDevelop.foldFor, StairSqBodyB.dF1, StairSqBodyB.dF2, lb_eq_K0, Challenge.gateSlots_append, r1, r2, re] at s0 ⊢
  linarith only [s0, sl_old, sl_new]

end BodyB

/-! ## Branch C body (`keepC` = 27 carries, avoids `workTC` and `hs`) -/

section BodyC
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical directFoldQTq

private theorem lc_eq_K0 : C163Low4Middle.L = K0 := rfl

def keepC : List Wire := C105Research.keepK.filter (fun q => !workTC.contains q)

theorem keepC_geometry : keepC.Nodup ∧ keepC.length = 27 ∧
    (∀ q ∈ keepC, q ∈ C105Research.hosts) ∧
    (∀ q ∈ workTC, q ∉ keepC) ∧
    (∀ i, i < 44 → C163Low4Middle.hs.getD i 0 ∉ keepC) ∧
    (∀ q ∈ keepC, q ∈ allowedWires) := by
  have hall : ∀ q ∈ keepC, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [keepC, keepKC_fast, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [keepC, keepKC_fast, workTC_lit, hs_lit]; decide +kernel))
  have hr : keepC.Nodup ∧ keepC.length = 27 ∧
      (∀ q ∈ keepC, q ∈ C105Research.hosts) ∧
      (∀ q ∈ workTC, q ∉ keepC) ∧
      (∀ i, i < 44 → C163Low4Middle.hs.getD i 0 ∉ keepC) := by
    rw [keepC, keepKC_fast, hostsC105_fast, hsC_fast, workTC_lit]; decide +kernel
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, hall⟩

def rawFC : Program := ReorderedGenericCache.cachedAdd 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
def newFC : Program := C105Research.head ++ C105LowEraseResearch.clear ++ rawFC ++ C105Research.top
def newIC : Program := C105Research.preInv ++ ReorderedConsumedSub.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
def coreC : Program := (newFC ++ C105Research.M ++ newIC) ++ (C105LowEraseResearch.clear ++ C105Research.tail)
def restC : Program := C105LowEraseResearch.clear ++ rawFC ++ C105Research.top ++ C105Research.M ++ newIC ++ C105LowEraseResearch.clear ++ C105Research.tail
def loopPCC : Program := SignCHead.head ++ restC
def loopC : Program := hostRename (StairSqLoopC.pairs hs) loopPCC
def foldPairsC : List (Wire × Wire) := workTC.zip (K0.core.pad.take 34)
def dFC : Program := hostRename foldPairsC (directFoldQTq K0 (negRot K0))
def bodyC : Program := (dFC ++ loopC) ++ ReorderedRecordPadding.program 7 K0.core.cin
def bodyCPlain : Program := C105SignResearch.directBody loopC

theorem foldPairsC_geom :
    (holesOf foldPairsC ++ hostsOf foldPairsC).Nodup ∧
    holesOf foldPairsC = workTC ∧
    hostsOf foldPairsC = K0.core.pad.take 34 ∧
    (∀ ab ∈ foldPairsC, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out ∧ ab.2 ∈ allowedWires) ∧
    (∀ q ∈ hostsOf foldPairsC, q ∉ hs ∧ q ∈ K0.wires ∧ q ∈ allowedWires) := by
  have hall : ∀ q ∈ hostsOf foldPairsC, q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq, hs_lit]; decide +kernel))
  have hK : ∀ q ∈ hostsOf foldPairsC, q ∈ K0.wires :=
    StairSquareBChecks.LT48B.sub_of_maskL _ _ (by rw [foldPairsC, workTC_lit, K0_eq]; decide +kernel)
  have hr : (holesOf foldPairsC ++ hostsOf foldPairsC).Nodup ∧
      holesOf foldPairsC = workTC ∧
      hostsOf foldPairsC = K0.core.pad.take 34 ∧
      (∀ ab ∈ foldPairsC, ab.1 ∈ K0.core.work ∧ ab.1 ∉ K0.core.out ∧ ab.2 ∈ K0.core.pad ∧ ab.2 ∉ K0.core.out) ∧
      (∀ q ∈ hostsOf foldPairsC, q ∉ hs) := by rw [foldPairsC, workTC_lit, K0_eq, hs_lit]; decide +kernel
  refine ⟨hr.1, hr.2.1, hr.2.2.1, ?_, ?_⟩
  · intro ab hab; have h := hr.2.2.2.1 ab hab
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hall ab.2 (List.mem_map.mpr ⟨ab, hab, rfl⟩)⟩
  · intro q hq; exact ⟨hr.2.2.2.2 q hq, hK q hq, hall q hq⟩

private theorem keepC_sub (q : Wire) (hq : q ∈ keepC) : q ∈ C105Research.hosts := keepC_geometry.2.2.1 q hq

private theorem core_plainC (s : State) (m : List Bool)
    (hz : ∀ q ∈ C105PrefixResearch.pad, s.basis q = false) (hb : ∀ q ∈ C105PrefixResearch.bank, s.basis q = false)
    (hi : s.basis C105PrefixResearch.cin = false) (ha : regValue C105PrefixResearch.acc s.basis = 0)
    (zero : ∀ q ∈ ReorderedCFixed.hosts, s.basis q = false)
    (after : WReady C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src
      (regValue C105PrefixResearch.src s.basis) (middleState C105Research.oldF C105Research.oldM s m))
    (flag : (run C105Research.oldF (m.take (measurementCount C105Research.oldF)) s).basis 4762 = false) :
    run coreC m s = run (C105Research.oldF ++ C105Research.oldM ++
      ReorderedCPlain.unbuild C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) m s := by
  let H := regValue C105PrefixResearch.src s.basis
  let vs := ReorderedCacheBits.values 4 27 H (976 * H / 1024)
  have keepSubK (q : Wire) (hq : q ∈ keepC) : q ∈ C105Research.keepK := (List.mem_filter.mp hq).1
  have fwdM : measurementCount newFC = measurementCount C105Research.F := by
    have h := (ReorderedGenericCache.count_balance 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)).2.1
    simp only [newFC, rawFC, C105Research.F, C105Research.rawF, measurementCount_append]; rw [h]
  have invM : measurementCount newIC = measurementCount C105Research.I := by
    have h := ReorderedConsumedSub.measurement_eq 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)
    simp only [newIC, C105Research.I, C105Research.rawI, measurementCount_append]; rw [h]
  have fwdVal : (((C105Research.cs.drop 4).take 27).map (run (carryPrefix (4 + 27) C105Research.xs C105Research.ys C105Research.cs C105PrefixResearch.cin) []
      (run (C105Research.head ++ C105LowEraseResearch.clear)
        ((m.take (measurementCount C105Research.F)).take (measurementCount (C105Research.head ++ C105LowEraseResearch.clear))) s)).basis) = vs := by
    let m0 := (m.take (measurementCount C105Research.F)).take (measurementCount (C105Research.head ++ C105LowEraseResearch.clear))
    let u := run C105Research.head m0 s
    let t := run (C105Research.head ++ C105LowEraseResearch.clear) m0 s
    have te : t = C105LowEraseResearch.erase u := C105Research.prefix_erased s m0 hz hb hi ha
    have hH : H < 2 ^ 130 := by simpa only [H, C105PrefixResearch.source_length] using regValue_lt C105PrefixResearch.src s.basis
    have ready := CHeadArithmeticResearch.ready C105PrefixResearch.acc C105PrefixResearch.pad C105PrefixResearch.bank
      C105PrefixResearch.cin C105PrefixResearch.src C105PrefixResearch.acc_length C105PrefixResearch.source_length C105PrefixResearch.fits s m0 hz hb hi ha
    have eb (q : Wire) (hq : q ∈ C105Research.domain) : t.basis q = u.basis q := by
      rw [te]; exact C105LowEraseResearch.bit_same _ q (C105Research.domain_away_low q hq)
    have er (r : List Wire) (sub : ∀ q ∈ r, q ∈ C105Research.domain) : regValue r t.basis = regValue r u.basis :=
      regValue_congr _ _ _ (fun q hq => eb q (sub q hq))
    exact ReorderedCacheBits.forward_values 4 27 H (((2 ^ 140 - 48 * H) % 2 ^ 140) / 1024) (976 * H / 1024)
      C105Research.xs C105Research.ys C105Research.cs C105PrefixResearch.cin t
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) C105Research.raw_nd
      (fun q hq => (eb q (C105Research.c_in q hq)).trans (ready.1 q hq))
      ((eb _ C105Research.cin_in).trans ready.2.1)
      ((er _ C105Research.x_in).trans ready.2.2.1)
      ((er _ C105Research.y_in).trans ready.2.2.2)
      (fun j hj => by simpa only [show 130 + 10 = 140 by decide] using ReorderedCacheArithmetic.high_add_low 130 (4 + j + 1) H (by omega) hH)
  have forward : run newFC (m.take (measurementCount C105Research.F)) s =
      scatterState keepC vs (run C105Research.F (m.take (measurementCount C105Research.F)) s) := by
    have h := CacheBetweenFrameResearch.forward (C105Research.head ++ C105LowEraseResearch.clear) C105Research.top
      27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) keepC_geometry.1
      (fun q hq bad => C105Research.geometry.2.2 q (keepC_sub q hq) (by clear * - bad; simp only [C105Research.domain, List.mem_cons, List.mem_append] at bad ⊢; tauto))
      (fun q hq => C105Research.rawF_off q (keepC_sub q hq)) (fun q hq => C105Research.top_off q (keepC_sub q hq))
      s (m.take (measurementCount C105Research.F))
      (fun q hq => C105Research.prefix_zeroK s _ hz hb hi ha zero q (keepSubK q hq))
    rw [fwdVal] at h; exact h
  have mid := C105Research.middle_erased s m hz hb hi ha after flag
  have cacheEq : run (newFC ++ C105Research.M ++ newIC) m s = run (C105Research.F ++ C105Research.M ++ C105Research.I) m s := by
    apply CacheFromCleanForwardResearch.equivalent C105Research.F newFC C105Research.M C105Research.I newIC keepC vs
      fwdM (fun q hq => C105Research.middle_fresh q (keepC_sub q hq))
      (fun q hq => C105Research.I_off q (keepC_sub q hq)) keepC_geometry.1 s m
      (fun q hq => C105Research.forward_zeroK s _ hz hb hi ha zero q (keepSubK q hq)) forward
    rw [mid]
    let ms := middleState C105Research.oldF C105Research.oldM s m
    let mr := m.drop (measurementCount C105Research.F + measurementCount C105Research.M)
    let t := scatterState keepC vs (C105LowEraseResearch.erase ms)
    have comm : run C105Research.preInv mr t = scatterState keepC vs (C105LowEraseResearch.erase (run C105Research.preInv mr ms)) := by
      rw [show t = scatterState keepC vs (C105LowEraseResearch.erase ms) from rfl,
        run_scatter C105Research.preInv keepC vs _ _ (fun q hq => C105Research.preInv_off q (keepC_sub q hq)),
        C105LowEraseResearch.commute C105Research.preInv mr ms (fun q hq => C105Research.preInv_off q (C105Research.low_hosts q hq))]
    have bits (q : Wire) (hq : q ∈ C105Research.domain) : (run C105Research.preInv mr t).basis q = (run C105Research.preInv mr ms).basis q := by
      rw [comm, scatter_outside keepC vs _ q (fun bad => C105Research.geometry.2.2 q (keepC_sub q bad) hq)]
      exact C105LowEraseResearch.bit_same _ q (C105Research.domain_away_low q hq)
    have regs (r : List Wire) (sub : ∀ q ∈ r, q ∈ C105Research.domain) :
        regValue r (run C105Research.preInv mr t).basis = regValue r (run C105Research.preInv mr ms).basis :=
      regValue_congr _ _ _ (fun q hq => bits q (sub q hq))
    have rr := C105Research.pre_raw_ready H ms mr after
    have saved : keepC.map t.basis = vs := scatter_saved_map keepC vs _ keepC_geometry.1
      (by simp only [vs, ReorderedCacheBits.values, List.length_map, keepC_geometry.2.1, List.length_range])
    have same : keepC.map (run C105Research.preInv mr t).basis = keepC.map t.basis :=
      List.map_congr_left (fun q hq => run_preserves_outside C105Research.preInv mr t q (C105Research.preInv_off q (keepC_sub q hq)))
    simp only [newIC, C105Research.I, C105Research.rawI, ControlledBorrowResearch.run_cat]
    exact ReorderedConsumedSub.frame 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide)
      (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
      (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])
      C105Research.raw_nd keepC_geometry.1 keepC_geometry.2.1 (fun q hq => C105Research.geometry.2.2 q (keepC_sub q hq))
      (run C105Research.preInv mr t) _ (fun q hq => (bits q (C105Research.c_in q hq)).trans (rr.1 q hq))
      ((bits _ C105Research.cin_in).trans rr.2.1) H (976 * H / 1024)
      ((regs _ C105Research.x_in).trans rr.2.2.1) ((regs _ C105Research.y_in).trans rr.2.2.2) (same.trans saved)
  have eq := ClearContextResearch.append_at (newFC ++ C105Research.M ++ newIC)
    (C105Research.F ++ C105Research.M ++ C105Research.I) (C105LowEraseResearch.clear ++ C105Research.tail) s m
    (by simp only [measurementCount_append, fwdM, invM]) cacheEq
  have shape : (C105Research.F ++ C105Research.M ++ C105Research.I) ++ (C105LowEraseResearch.clear ++ C105Research.tail) =
      C105Research.F ++ C105Research.M ++ (C105Research.I ++ C105LowEraseResearch.clear ++ C105Research.tail) := by
    have g (A B C D E : Program) : (A ++ B ++ C) ++ (D ++ E) = A ++ B ++ (C ++ D ++ E) := by simp only [List.append_assoc]
    exact g _ _ _ _ _
  exact eq.trans ((congrArg (fun P => run P m s) shape).trans (C105Research.plain_loop s m hz hb hi ha after flag))

private theorem coreC_frame (base : BasisState) (hc : C163Low4Middle.L.PairClean base)
    (hp : base C163Low4Middle.p = false) (hd : base C163Low4Middle.d = false) (O : Nat) (hO : O < SquareReduction.p) :
    Triple (SquareFrame C163Low4Middle.L.core.out base O) coreC
      (SquareFrame C163Low4Middle.L.core.out base
        (((if base C163Low4Middle.g then C163Low4Facts.Klow - C163Fold.payload C163Low4Middle.L base
           else C163Fold.payload C163Low4Middle.L base) + (SquareReduction.p - 1 - O)) % SquareReduction.p)) := by
  intro s m hf
  have len := C163Low4Middle.lengths; have fit := C163Low4Middle.fits
  have clean := C163Low4Middle.L.squareFrame_clean C163Low4Middle.hn base s.basis O hf hc
  have hz : ∀ u ∈ C163Low4Middle.pad, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
  have hb : ∀ u ∈ C163Low4Middle.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue C163Low4Middle.ga s.basis = 0 := C163Low4Ghost.ghostAcc_zero C163Low4Middle.L s.basis clean
  have zeroU : ∀ u ∈ C163Low4Middle.hs, s.basis u = false := StairSqLoopC.hs_zero base hc hd O s hf
  have zeroOld : ∀ u ∈ ReorderedCFixed.hosts, s.basis u = false := by
    have qz : s.basis C163Low4Middle.q = false := (regValue_zero _ _).mp clean.work C163Low4Middle.q (by decide)
    have rz : s.basis C163Low4Middle.r = false := (regValue_zero _ _).mp clean.work C163Low4Middle.r (by decide)
    have pz : s.basis C163Low4Middle.p = false := (hf.2 C163Low4Middle.p (by decide)).trans hp
    intro u hu; simp only [ReorderedCFixed.hosts, List.mem_cons] at hu
    rcases hu with rfl | rfl | rfl | hu; exact qz; exact rz; exact pz; exact zeroU u hu
  have offHs : ∀ u ∈ C163Low4Middle.hs, u ∉ wires (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) :=
    fun u hu => (ReorderedCFixed.off_plain u (StairSqLoopC.hosts_of_hs u hu)).1
  have goodOld := fun record => C163Low4Middle.good base hc O hO s record hf
  have goodSpecial : WReady C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      (regValue C163Low4Middle.src s.basis)
      (middleState (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) C163Low4Middle.specialChecked.out s m) := by
    rw [ReorderedRetape.c_middle_eq C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      C163Low4Middle.specialChecked.out len.1 len.2.2.2 fit s m hz hb clean.cin ha]
    exact goodOld _
  have middleEq := C163Low4Middle.bank_cert.middle_eq C163Low4Middle.hs C163Low4Middle.specialChecked.out C163Low4Middle.bankChecked.out
    (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) s m zeroU offHs
  have knownEq := CKKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
  have goodKnown : WReady C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
      (regValue C163Low4Middle.src s.basis)
      (middleState (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) KnownCMidStaged.body s m) := by
    rw [knownEq, middleEq]; exact goodSpecial
  have buildFrame := ReorderedCPlain.build_triple C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src
    len.1 len.2.2.2 fit s.basis hz hb clean.cin s
    (m.take (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))) ⟨ha, fun _ _ => rfl⟩
  have flag : (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
      (m.take (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))) s).basis 4762 = false :=
    (buildFrame.2.2 4762 (by simp only [C163Low4Middle.ga, C163Low4Middle.pad, C163Low4Middle.bank, C163Low4Middle.src, C163Low4Middle.L, C163Middle.L, show Baselines.layout.dialogStreamedSquareWide = K0 from rfl, K0_eq]; decide +kernel)).trans clean.modFlag
  have plainNew := core_plainC s m hz hb clean.cin ha zeroOld goodKnown flag
  have midEq : run KnownCMidStaged.body (m.drop (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)))
      (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m s) =
      run C163Low4Middle.bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)))
      (run (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m s) := by
    simpa only [middleState, run_take] using knownEq
  have ctxt := ReorderedKnownA.context_eq (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    C163Low4Middle.bankChecked.out KnownCMidStaged.body (ReorderedCPlain.unbuild C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    s m CKKnownMiddleResearch.measurements midEq
  have middleReplace := C163Low4Middle.bank_cert.surround_eq C163Low4Middle.hs C163Low4Middle.specialChecked.out C163Low4Middle.bankChecked.out
    (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)
    (ReorderedCPlain.unbuild C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) s m zeroU offHs
  have plainEq := ReorderedRetape.c_loop_eq C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src C163Low4Middle.specialChecked.out
    len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
  let record := ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src))
    (measurementCount (ReorderedCPlain.build C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src)) m
  have oldFrame := C163Low4Middle.frame base hc hp hd O hO s record hf
  rw [C163Low4Middle.eq_plain base hc hp hd O hO s record hf] at oldFrame
  exact ReorderedCFixed.transport _ s _ _ (plainNew.trans (ctxt.trans (middleReplace.trans plainEq))) oldFrame

private theorem keepC_cached_wires : wires rawFC ⊆ C105Research.domain.toFinset ∪ keepC.toFinset :=
  (ReorderedSupport.cached 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
    (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])).1

private theorem keepC_consumed_wires :
    wires (ReorderedConsumedSub.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin) ⊆
      C105Research.domain.toFinset ∪ keepC.toFinset :=
  ReorderedSupport.consumed 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    (by rw [C105Research.raw_lengths.1, C105Research.raw_lengths.2.1])
    (by rw [C105Research.raw_lengths.2.1, C105Research.raw_lengths.2.2])

theorem loopPCC_off (h : Wire) (hh : h ∈ ReorderedCFixed.hosts) (hk : h ∉ keepC) : h ∉ wires loopPCC := by
  have hA : h ∈ C105Research.hosts := List.mem_append.mpr (Or.inl hh)
  have hb : h ∉ wires (ReorderedCPlain.build C105PrefixResearch.acc C105PrefixResearch.pad
      C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) := (ReorderedCFixed.off_plain h hh).1
  rw [C105Research.plain_split] at hb
  simp only [wires_append, Finset.mem_union, not_or] at hb
  have ht : h ∉ wires (ReorderedCPlain.unbuild C105PrefixResearch.acc C105PrefixResearch.pad
      C105PrefixResearch.bank C105PrefixResearch.cin C105PrefixResearch.src) := (ReorderedCFixed.off_plain h hh).2
  rw [C105Research.unbuild_split] at ht
  simp only [wires_append, Finset.mem_union, not_or] at ht
  have clearOff : h ∉ wires C105LowEraseResearch.clear := by
    rw [StairSqLoopC.clear_wires]; intro bad
    exact C105Research.old_away h hh ((by decide : ([4243, 4505, 4244, 4506, 4245, 4507] : List Wire) ⊆ C105Research.ports) (List.mem_toFinset.mp bad))
  have out : h ∉ C105Research.domain.toFinset ∪ keepC.toFinset := by
    simp only [Finset.mem_union, List.mem_toFinset, not_or]; exact ⟨C105Research.geometry.2.2 h hA, hk⟩
  simp only [loopPCC, restC, newIC, wires_append, Finset.mem_union, not_or, and_assoc]
  exact ⟨fun bad => hb.1 (SignCHeadSupport.support bad), clearOff, fun bad => out (keepC_cached_wires bad),
    C105Research.top_off h hA, C105Research.middle_fresh h hA, C105Research.preInv_off h hA,
    fun bad => out (keepC_consumed_wires bad), clearOff, ht.2⟩

theorem loopPCC_support : wires loopPCC ⊆ C105Research.S := by
  have hh : wires SignCHead.head ⊆ C105Research.S := by
    apply Finset.Subset.trans ?_ C105Research.old_prefix_support
    rw [C105Research.oldPrefix, wires_append]
    exact Finset.subset_union_left
  have ks : C105Research.domain.toFinset ∪ keepC.toFinset ⊆ C105Research.S := by
    intro q hq; apply C105Research.raw_domain_in
    simp only [Finset.mem_union, List.mem_toFinset] at hq ⊢
    rcases hq with h | h; exact Or.inl h; exact Or.inr (keepC_sub q h)
  simp only [loopPCC, restC, newIC, wires_append, Finset.union_subset_iff]
  exact ⟨hh,
    ⟨⟨⟨⟨⟨⟨C105Research.clear_support, keepC_cached_wires.trans ks⟩, C105Research.endpoint_support.1⟩,
      C105Research.middle_support⟩, ⟨C105Research.endpoint_support.2.1, keepC_consumed_wires.trans ks⟩⟩,
      C105Research.clear_support⟩, C105Research.endpoint_support.2.2⟩⟩

theorem loopPCC_physical : GatePhysical loopPCC := by
  have f := ReorderedPhysical.cached 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
    (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
    (by rw [C105Research.raw_lengths.2.2]; decide)
    C105Research.raw_nd (fun q hq bad => C105Research.geometry.2.2 q (keepC_sub q hq) (C105Research.c_in q bad))
  have n := notRegister_physical C105Research.ys
  simp only [loopPCC, restC, newIC, ReorderedConsumedSub.consumed, gatePhysical_append]
  exact ⟨SignCHeadResources.physical,
    ⟨⟨⟨⟨⟨⟨C105LowEraseResearch.physical, f.1⟩, C105Research.endpoint_physical.1⟩,
      CKAliasesResearch.physical⟩, ⟨C105Research.endpoint_physical.2.1, ⟨⟨n, f.2⟩, n⟩⟩⟩,
      C105LowEraseResearch.physical⟩, C105Research.endpoint_physical.2.2⟩⟩

theorem loopC_pairs_free : ∀ ab ∈ StairSqLoopC.pairs hs, ab.2 ∉ wires loopPCC := by
  intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
  apply loopPCC_off _ (StairSqLoopC.hosts_of_hs _ (StairSqLoopC.holes_geometry44.2.2 y hy))
  have h := List.idxOf_lt_length_of_mem hy; rw [StairSqLoopA.hostDomain_length44] at h
  exact keepC_geometry.2.2.2.2.1 _ h

theorem loopC_support : wires loopC ⊆ C105Research.S := by
  intro q hq
  have sub := hostRename_support (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free hq
  rcases Finset.mem_union.mp sub with h | h
  · exact loopPCC_support (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopC.pairs_snd] at h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact C105Research.raw_domain_in (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_append.mpr (Or.inl (StairSqLoopC.hosts_of_hs _ (StairSqLoopC.holes_geometry44.2.2 y hy))))))

theorem loopC_avoids_hs : ∀ q ∈ hs, q ∉ wires loopC := by
  intro q hq
  have h := hostRename_avoids (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free
  rw [StairSqLoopC.pairs_fst] at h; exact h q hq

theorem loopC_avoids_workTC : ∀ q ∈ workTC, q ∉ wires loopC := by
  intro q hq bad
  have sub := hostRename_support (StairSqLoopC.pairs hs) loopPCC (StairSqLoopC.pairs_nodup44 hs (List.Sublist.refl _)) loopC_pairs_free bad
  rcases Finset.mem_union.mp sub with h | h
  · have hm : ∀ x ∈ workTC, x ∈ ReorderedCFixed.hosts := by rw [workTC_lit, hostsCFix_fast]; decide +kernel
    exact loopPCC_off q (hm q hq) (keepC_geometry.2.2.2.1 q hq) (Finset.mem_sdiff.mp h).1
  · rw [StairSqLoopC.pairs_snd] at h
    have dis : ∀ x ∈ workTC, x ∉ hs.map StairSqLoopC.hostOf := by simp only [workTC_lit, StairSqLoopC.hostOf, show StairSqLoopA.hostDomain = hs from rfl, hs_lit, hsC_fast]; decide +kernel
    exact dis q hq (List.mem_toFinset.mp h)

theorem loopC_counts :
    toffoliCount loopC = toffoliCount C105SignResearch.loop + 81 ∧
    measurementCount loopC = measurementCount C105SignResearch.loop := by
  have hr := hostRename_counts (StairSqLoopC.pairs hs) loopPCC
  have rel : toffoliCount loopPCC + 27 = toffoliCount StairSqLoopC.loopNC ∧
      measurementCount loopPCC = measurementCount StairSqLoopC.loopNC := by
    have cb := ReorderedGenericCache.count_balance 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide) (by rw [C105Research.raw_lengths.2.2]; decide)
    rw [loopPCC, restC, rawFC, newIC, StairSqLoopC.loopNC, StairSqLoopC.suffixNC,
      C105Research.I, C105Research.rawI, C105Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [toffoliCount_append, measurementCount_append]
    exact ⟨by omega, by omega⟩
  have nc := StairSqLoopC.loopNC_counts
  rw [loopC, hr.1, hr.2]
  exact ⟨by omega, by omega⟩

theorem loopC_slots : Challenge.gateSlots loopC = Challenge.gateSlots C105SignResearch.loop + 237 := by
  have hr := hostRename_slots (StairSqLoopC.pairs hs) loopPCC
  have rel : Challenge.gateSlots loopPCC + 81 = Challenge.gateSlots StairSqLoopC.loopNC := by
    have sc := ReorderedSlots.cache 27 C105Research.xs C105Research.ys C105Research.cs keepC C105PrefixResearch.cin
      (by rw [C105Research.raw_lengths.1]; decide) (by rw [C105Research.raw_lengths.2.1]; decide)
      (by rw [C105Research.raw_lengths.2.2]; decide) keepC_geometry.2.1
    rw [loopPCC, restC, rawFC, newIC, StairSqLoopC.loopNC, StairSqLoopC.suffixNC,
      C105Research.I, C105Research.rawI, C105Research.rawF, ReorderedConsumedSub.consumed, ReorderedConsumedSub.plain]
    simp only [Challenge.gateSlots_append]
    omega
  have nc := StairSqLoopC.loopNC_slots
  rw [loopC, hr]
  omega

theorem loopC_frame : C105SignResearch.DirectLoopFrame loopC := by
  have pcFrame : C105SignResearch.DirectLoopFrame loopPCC := by
    intro base hc hp hd O hO s m hf
    have clean := C163Low4Middle.L.squareFrame_clean C163Low4Middle.hn base s.basis O hf hc
    have hz : ∀ u ∈ C163Low4Middle.pad, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
    have hb : ∀ u ∈ C163Low4Middle.bank, s.basis u = false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
    have ha : regValue C163Low4Middle.ga s.basis = 0 := C163Low4Ghost.ghostAcc_zero C163Low4Middle.L s.basis clean
    have hhead : ∀ a b : List Bool, run SignCHead.head a s = run (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) b s :=
      fun a b => ReorderedFrameUnique.program_eq C163Low4Middle.ga s.basis 0 ((2 ^ 140 - 48 * regValue C163Low4Middle.src s.basis) % 2 ^ 140) _ _
        (SignCHead.frame s.basis hz hb clean.cin)
        (ReorderedCHead.head_triple C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src C163Low4Middle.lengths.1 C163Low4Middle.lengths.2.2.2.le C163Low4Middle.fits s.basis hz hb clean.cin)
        s a b ⟨ha, fun _ _ => rfl⟩
    have eq := SignRetape.replace SignCHead.head (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) restC s m hhead
    have hheadEq : C105Research.head = ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src := rfl
    have hcoreEq : coreC = ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src ++ restC := by
      rw [coreC, newFC, restC, hheadEq]
      have g (A B C D E F G H : Program) : (((A ++ B ++ C ++ D) ++ E ++ F) ++ (G ++ H)) = A ++ (B ++ C ++ D ++ E ++ F ++ G ++ H) := by simp only [List.append_assoc]
      exact g _ _ _ _ _ _ _ _
    have eq' : run loopPCC m s = run coreC (SignRetape.tape SignCHead.head (ReorderedCHead.head C163Low4Middle.ga C163Low4Middle.pad C163Low4Middle.bank C163Low4Middle.L.core.cin C163Low4Middle.src) m) s := by
      rw [loopPCC, hcoreEq]; exact eq
    exact ReorderedCFixed.transport _ s _ _ eq' (coreC_frame base hc hp hd O hO s _ hf)
  intro base hc hp hd O hO s m hf
  have r := pcFrame base hc hp hd O hO s m hf
  have hEq : run loopC m s = run loopPCC m s := by
    apply hostRename_run_eq (StairSqLoopC.pairs hs) loopPCC s m
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopC.holes_geometry44.2.1 y hy
      exact (hf.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      exact StairSqLoopC.hs_zero base hc hd O s hf _ (StairSqLoopC.holes_geometry44.2.2 y hy)
    · intro ab hab; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hab
      have hg := StairSqLoopC.holes_geometry44.2.1 y hy
      exact (r.2.2 y hg.2).trans ((regValue_zero _ _).mp hc.pad y hg.1)
    · exact loopC_pairs_free
  rw [hEq]; exact r

theorem bodyC_wires_plain : wires bodyC ⊆ wires bodyCPlain ∪ (K0.core.pad.take 34).toFinset := by
  have sp := directFold_rename_support foldPairsC (negRot K0) (negRot_count K0) foldPairsC_geom.1 (fun ab hab => (foldPairsC_geom.2.2.2.1 ab hab).2.2.1)
  rw [foldPairsC_geom.2.2.1] at sp
  intro q hq
  simp only [bodyC, wires_append, Finset.mem_union] at hq
  rcases hq with (b | b) | b
  · rcases Finset.mem_union.mp (sp b) with h | h
    · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, wires_append, Finset.mem_union]; left; left; exact (Finset.mem_sdiff.mp h).1)
    · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, wires_append, Finset.mem_union]; left; right; exact b)
  · exact Finset.mem_union_left _ (by simp only [bodyCPlain, C105SignResearch.directBody, wires_append, Finset.mem_union]; right; exact b)

theorem bodyC_ok : BodyCOK bodyC := by
  have s0 : wires bodyCPlain ⊆ insert D0 (G0 :: K0.wires).toFinset := by
    have h := C105SignResearch.direct_body_coarse_S loopC loopC_support
    rw [lc_eq_K0] at h
    exact h
  refine ⟨?_, ?_⟩
  · intro q hq; rcases Finset.mem_union.mp (bodyC_wires_plain hq) with h | h
    · exact s0 h
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (foldPairsC_geom.2.2.2.2 q (by rw [foldPairsC_geom.2.2.1]; exact List.mem_toFinset.mp h)).2.1))
  · intro base M hP hc hg hd O hO s m hf
    have rawRef := C105SignResearch.direct_body_frame loopC loopC_frame base M hP hc hg hd O hO s m hf
    have views := accC_views K0 hwK base M hP
    have hv : K0.MeasuredFoldView base (negRot K0) := views (.inl (negRot K0)) (by simp [accCMix])
    have mc : measurementCount dFC = measurementCount (directFoldQTq K0 (negRot K0)) := (hostRename_counts foldPairsC (directFoldQTq K0 (negRot K0))).2
    have eq1 : run dFC m s = run (directFoldQTq K0 (negRot K0)) m s :=
      directFold_rename_run foldPairsC (negRot K0) (negRot_count K0) (negRot_length K0 hwK) rfl rfl
        (fun ab hab => ⟨(foldPairsC_geom.2.2.2.1 ab hab).1, (foldPairsC_geom.2.2.2.1 ab hab).2.1⟩)
        (fun ab hab => ⟨(foldPairsC_geom.2.2.2.1 ab hab).2.2.1, (foldPairsC_geom.2.2.2.1 ab hab).2.2.2.1⟩)
        base hv hc O hO s m hf
    have bodyEq : run bodyC m s = run bodyCPlain m s := by
      simp only [bodyC, bodyCPlain, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
        ControlledBorrowResearch.run_cat, measurementCount_append, mc]
      rw [eq1]
    rw [bodyEq]; exact rawRef

theorem bodyC_avoids_workTC : ∀ q ∈ workTC, q ∉ wires bodyC := by
  intro q hq bad
  have hn := (List.nodup_cons.mp controlND).2
  have a1 := hostRename_avoids foldPairsC (directFoldQTq K0 (negRot K0)) foldPairsC_geom.1
    (fun ab hab => directFoldQ_free K0 hn (negRot K0) (negRot_count K0) ab.2 (by simp [directFree, (foldPairsC_geom.2.2.2.1 ab hab).2.2.1]))
  rw [foldPairsC_geom.2.1] at a1
  simp only [bodyC, wires_append, Finset.mem_union] at bad
  rcases bad with (b | b) | b
  · exact a1 q hq b
  · exact loopC_avoids_workTC q hq b
  · exact (by rw [workTC_lit, K0_eq]; decide +kernel : ∀ x ∈ workTC, x ≠ K0.core.cin) q hq (Finset.mem_singleton.mp (padding_wires 7 K0.core.cin b))

theorem bodyC_avoids_hs : ∀ q ∈ hs, q ∉ wires bodyC := by
  intro q hq bad
  rcases Finset.mem_union.mp (bodyC_wires_plain bad) with h | h
  · exact C105SignResearch.direct_body_holes loopC hs (fun x hx => (StairSqLoopC.holes_geometry44.2.1 x hx).1) loopC_avoids_hs q hq h
  · exact (foldPairsC_geom.2.2.2.2 q (by rw [foldPairsC_geom.2.2.1]; exact List.mem_toFinset.mp h)).1 hq

theorem bodyC_physical : GatePhysical bodyC := by
  have p0 := C105SignResearch.direct_body_physical loopC (hostRename_physical _ _ loopPCC_physical)
  simp only [C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, gatePhysical_append] at p0
  simp only [bodyC, dFC, gatePhysical_append]
  exact ⟨⟨hostRename_physical _ _ p0.1.1, p0.1.2⟩, p0.2⟩

theorem bodyC_counts :
    toffoliCount bodyC = toffoliCount C105SignResearch.body + 81 ∧
    measurementCount bodyC = measurementCount C105SignResearch.body := by
  have c0 := C105SignResearch.direct_body_counts loopC
  have cl := loopC_counts
  have r1 := hostRename_counts foldPairsC (directFoldQTq K0 (negRot K0))
  have eqT : toffoliCount bodyC = toffoliCount (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      toffoliCount_append, r1.1]
  have eqM : measurementCount bodyC = measurementCount (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      measurementCount_append, r1.2]
  rw [eqT, eqM]
  exact ⟨by omega, by omega⟩

theorem bodyC_slots : Challenge.gateSlots bodyC + 275 = Challenge.gateSlots C105SignResearch.body := by
  have s0 := C105SignResearch.direct_body_slots loopC
  have sl := loopC_slots
  have r1 := hostRename_slots foldPairsC (directFoldQTq K0 (negRot K0))
  have eqS : Challenge.gateSlots bodyC = Challenge.gateSlots (C105SignResearch.directBody loopC) := by
    simp only [bodyC, dFC, C105SignResearch.directBody, C105SignResearch.directRawBody, C163Low4Body.directBodyProgram, lc_eq_K0,
      Challenge.gateSlots_append, r1]
  rw [eqS]
  omega

theorem bodyCPlain_fine :
    wires bodyCPlain ⊆ insert C163Low4Middle.d
      (wires (OwnDiagAll12Square.bodyCKTq C163Low4Middle.L C163Low4Middle.g)) :=
  C105SignResearch.direct_body_fine_S loopC loopC_support

end BodyC

/-! ## Branch wrappers (`brC`, `brB`, `brA`) and top-level assembly -/

section Branches
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots GatePhysical LocalRebuild.improved directFoldQTq

/-- Generic parked-copy split-65 wrapper around any `SplitCfg` and body. -/
def withSplitPark (c : SplitCfg) (keepBits : Nat) (parkHosts : List Wire) (body : Program) : Program :=
  copyRegister (some G0) c.src c.bank ++
  c.make ++
  eraseMask G0 (c.src.take keepBits) (c.bank.take keepBits) ++
  ParkCopy.dummies parkHosts ++
  ParkCopy.move (c.bank.drop keepBits) parkHosts ++
  renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body) ++
  CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits) ++
  ParkCopy.move parkHosts (c.bank.drop keepBits) ++
  c.clear ++
  eraseMask G0 c.src c.bank

def brC : Program :=
  OwnDiagAll12Square.gPrep K0 ++
  withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC ++
  OwnDiagAll12Square.gClear K0

def brB : Program :=
  withSplitPark cfgB 119 (ParkCopy.hosts E0) bodyB

def brA : Program :=
  withSplitPark cfgA 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA

private theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s) = s := by
  apply State.extensionality
  · rfl
  · funext q; simp [pullState]

private theorem pull_swap_fix (a b : Wire) (s : State) (h : s.basis a = s.basis b) :
    pullState (Equiv.swap a b) s = s := by
  apply State.extensionality
  · rfl
  · funext q
    simp only [pullState, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1; exact h.symm
    · subst h2; exact h
    · rfl

private theorem swap_run_eq (a b : Wire) (P : Program) (s : State) (m : List Bool)
    (h0 : s.basis a = s.basis b) (h1 : (run P m s).basis a = (run P m s).basis b) :
    run (renameProgram (Equiv.swap a b) P) m s = run P m s := by
  have hr := ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective P m s
  rw [pull_swap_fix a b s h0] at hr
  have h2 := congrArg (pullState (Equiv.swap a b)) hr
  rw [pull_swap_invol, pull_swap_fix a b (run P m s) h1] at h2
  exact h2

private theorem state_eq_of_out (u v : State) (hp : u.phase = v.phase)
    (ho : regValue K0.core.out u.basis = regValue K0.core.out v.basis)
    (hf : ∀ q, q ∉ K0.core.out → u.basis q = v.basis q) : u = v := by
  apply State.extensionality _ _ hp
  funext q
  by_cases hq : q ∈ K0.core.out
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have h1 := RawClearCarryProbe.register_bit K0.core.out i u.basis hi
    have h2 := RawClearCarryProbe.register_bit K0.core.out i v.basis hi
    have hg : K0.core.out.getD i 0 = K0.core.out[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg] at h1 h2
    rw [h1, h2, ho]
  · exact hf q hq

private theorem even_bit0_false (r : List Wire) (b : BasisState) (k : Nat)
    (hr : 0 < r.length) (hv : regValue r b = 2 * k) : b (r.getD 0 0) = false := by
  have hb := RawClearCarryProbe.register_bit r 0 b hr
  rw [hv] at hb
  simpa using hb

private theorem hi_bit_false (r : List Wire) (b : BasisState) (i : Nat)
    (hi : i < r.length) (hlt : regValue r b < 2 ^ i) : b (r.getD i 0) = false := by
  have hb := RawClearCarryProbe.register_bit r i b hi
  have hdiv : regValue r b / 2 ^ i = 0 := Nat.div_eq_of_lt hlt
  rw [hdiv] at hb
  simpa using hb

/-- Core correctness theorem for `withSplitPark` when `body` avoids `E0` and `c.workT`. -/
private theorem withSplitPark_correct (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (V : Nat)
    (hkLen : keepBits + parkHosts.length = c.n)
    (hkPos : 0 < keepBits)
    (hsrcLen : c.src.length = c.n)
    (hParkNd : parkHosts.Nodup)
    (hParkIn : ∀ h ∈ parkHosts, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0)
    (hParkDisBank : ∀ h ∈ parkHosts, h ∉ c.bank)
    (hParkDisSrc : ∀ h ∈ parkHosts, h ∉ c.src)
    (hParkDisDst : ∀ h ∈ parkHosts, h ∉ c.dst)
    (hParkDisOut : ∀ h ∈ parkHosts, h ∉ K0.core.out)
    (hParkDisG0 : G0 ∉ parkHosts)
    (hParkDisSw : ∀ h ∈ parkHosts, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478)
    (hSrcDis : (G0 :: c.src ++ c.bank).Nodup)
    (hE0DisBank : ∀ q ∈ E0, q ∉ c.bank)
    (hWorkTSub : ∀ q ∈ c.workT, q ∈ K0.core.work ∨ q = D0)
    (hBodyDisE0 : ∀ q ∈ E0, q ∉ wires body)
    (hBodyDisWorkT : ∀ q ∈ c.workT, q ∉ wires body)
    (hBodyDisEU : ControlLoan1589BFFold.eU K0 ∈ parkHosts → ControlLoan1589BFFold.eU K0 ∉ wires body)
    (hLiveSub : ∀ q ∈ c.liveT, q ∈ E0 ∨ q ∈ c.workT)
    (hLiveDisBank : ∀ q ∈ c.liveT, q ∉ c.bank)
    (hLiveDisSrc : ∀ q ∈ c.liveT, q ∉ c.src)
    (hLiveDisOut : ∀ q ∈ c.liveT, q ∉ K0.core.out)
    (hScSub : ∀ q ∈ c.cleanScratch, q ∈ K0.foldPad ∨ q ∈ K0.core.work)
    (hScDisBank : ∀ q ∈ c.cleanScratch, q ∉ c.bank)
    (hScDisSrc : ∀ q ∈ c.cleanScratch, q ∉ c.src)
    (hScDisOut : ∀ q ∈ c.cleanScratch, q ∉ K0.core.out)
    (hScDisPark : ∀ q ∈ c.cleanScratch, q ∉ parkHosts)
    (hDstDisBank : ∀ q ∈ c.dst, q ∉ c.bank)
    (hDstDisSrc : ∀ q ∈ c.dst, q ∉ c.src)
    (hDstDisOut : ∀ q ∈ c.dst, q ∉ K0.core.out)
    (hBankDisOut : ∀ q ∈ c.bank, q ∉ K0.core.out)
    (hSrcDisOut : ∀ q ∈ c.src, q ∉ K0.core.out)
    (hG0Out : G0 ∉ c.bank ∧ G0 ∉ c.dst ∧ G0 ∉ c.liveT ∧ G0 ∉ c.cleanScratch ∧ G0 ∉ K0.core.out)
    (hCacheEq : LowZero18Square.cacheWire K0 c.dst = c.dst.headD 0)
    (hParkZeroAfterMake : ∀ s0 : State, ∀ m0 : List Bool,
      regValue c.dst s0.basis = 0 → regValue c.liveT s0.basis = 0 →
      regValue c.cleanScratch s0.basis = 0 → s0.basis K0.core.cin = false →
      (ControlLoan1589BFFold.eU K0 ∈ parkHosts → s0.basis (ControlLoan1589BFFold.eU K0) = false) →
      (∀ q ∈ E0, s0.basis q = false) →
      (∀ h ∈ parkHosts, (run c.make m0 s0).basis h = false) ∧
      (run c.make m0 s0).basis 5093 = false ∧ (run c.make m0 s0).basis 5478 = false)
    (s : State) (records : List Bool) (hc : K0.PairClean s.basis)
    (hd0 : regValue c.dst s.basis = 0) (he0 : regValue E0 s.basis = 0)
    (hd0_bit : s.basis D0 = false)
    (heu0 : ControlLoan1589BFFold.eU K0 ∈ parkHosts → s.basis (ControlLoan1589BFFold.eU K0) = false)
    (callback : ∀ t : State, ∀ m : List Bool,
      regValue c.dst t.basis = (if s.basis G0 then regValue c.src s.basis else 0) ^ 2 →
      (∀ q, q ∉ c.dst → t.basis q = s.basis q) →
      (run body m t).phase = t.phase ∧ regValue K0.core.out (run body m t).basis = V ∧
      ∀ q, q ∉ K0.core.out → (run body m t).basis q = t.basis q) :
    (run (withSplitPark c keepBits parkHosts body) records s).phase = s.phase ∧
    regValue K0.core.out (run (withSplitPark c keepBits parkHosts body) records s).basis = V ∧
    ∀ q, q ∉ K0.core.out → (run (withSplitPark c keepBits parkHosts body) records s).basis q = s.basis q := by
  have hbankLen : c.bank.length = c.n := v.bankLen
  have hsrc_bank : c.src.length = c.bank.length := by omega
  have hkeepLe : keepBits ≤ c.n := by omega
  have hE0_all : ∀ q ∈ E0, s.basis q = false := (regValue_zero _ _).mp he0
  have hWork_all : ∀ q ∈ K0.core.work, s.basis q = false := (regValue_zero _ _).mp hc.work
  have hPad_all : ∀ q ∈ K0.foldPad, s.basis q = false := (regValue_zero _ _).mp hc.pad
  have hSc0_s : regValue c.cleanScratch s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (hScSub q hq).elim (hPad_all q) (hWork_all q))
  have hLive0_s : regValue c.liveT s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (hLiveSub q hq).elim (hE0_all q) (fun hw => (hWorkTSub q hw).elim (hWork_all q) (fun h => h ▸ hd0_bit)))
  have hSwMem : (4834 : Wire) ∈ K0.foldPad ∧ (4875 : Wire) ∈ K0.foldPad ∧
      (4834 : Wire) ∉ K0.core.out ∧ (5093 : Wire) ∉ K0.core.out ∧
      (4875 : Wire) ∉ K0.core.out ∧ (5478 : Wire) ∉ K0.core.out ∧
      (4834 : Wire) ∉ allowedWires ∧ (4875 : Wire) ∉ allowedWires :=
    have h6 : (4834 : Wire) ∈ K0.foldPad ∧ (4875 : Wire) ∈ K0.foldPad ∧
        (4834 : Wire) ∉ K0.core.out ∧ (5093 : Wire) ∉ K0.core.out ∧
        (4875 : Wire) ∉ K0.core.out ∧ (5478 : Wire) ∉ K0.core.out := by rw [K0_eq]; decide +kernel
    ⟨h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1, h6.2.2.2.2.2, not_mem_allowedWires_4834, not_mem_allowedWires_4875⟩
  have h4834_0 : s.basis 4834 = false := hPad_all 4834 hSwMem.1
  have h4875_0 : s.basis 4875 = false := hPad_all 4875 hSwMem.2.1
  have h4834_notReal : (4834 : Wire) ∉ c.realAll := fun h => hSwMem.2.2.2.2.2.2.1 (v.realAllowed _ h)
  have h4875_notReal : (4875 : Wire) ∉ c.realAll := fun h => hSwMem.2.2.2.2.2.2.2 (v.realAllowed _ h)
  have h5093_notBank : (5093 : Wire) ∉ c.bank := hE0DisBank 5093 (by rw [E0_eq]; decide +kernel)
  have h5478_notBank : (5478 : Wire) ∉ c.bank := hE0DisBank 5478 (by rw [E0_eq]; decide +kernel)
  have hCin_notBank : K0.core.cin ∉ c.bank :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notDst : K0.core.cin ∉ c.dst :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notLive : K0.core.cin ∉ c.liveT :=
    kdis v.realNd (r := [K0.core.cin]) (fun q => by clear * - c q; rw [realAll_count]; simp only [SplitCfg.liveT, List.count_append, List.count_cons, List.count_nil]; omega) _ (by simp)
  have hCin_notPark : K0.core.cin ∉ parkHosts := fun hp =>
    (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel : K0.core.cin ∉ E0 ∧ K0.core.cin ≠ ControlLoan1589BFFold.eU K0) |>
      fun h => (hParkIn _ hp).elim h.1 h.2
  have hCin_notOut : K0.core.cin ∉ K0.core.out := by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hParkDisReal : ∀ h ∈ parkHosts, h ∉ c.dst ∧ h ∉ c.bank := fun h hh => ⟨hParkDisDst h hh, hParkDisBank h hh⟩
  let P := if s.basis G0 then regValue c.src s.basis else 0
  let pA := copyRegister (some G0) c.src c.bank
  let pM := c.make
  let pE1 := eraseMask G0 (c.src.take keepBits) (c.bank.take keepBits)
  let pD := ParkCopy.dummies parkHosts
  let pMI := ParkCopy.move (c.bank.drop keepBits) parkHosts
  let pB := renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)
  let pC1 := CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits)
  let pMO := ParkCopy.move parkHosts (c.bank.drop keepBits)
  let pCL := c.clear
  let pE := eraseMask G0 c.src c.bank
  obtain ⟨r9, mE, eE⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO ++ pCL) pE records s
  obtain ⟨r8, mCL, eCL⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO) pCL r9 s
  obtain ⟨r7, mMO, eMO⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1) pMO r8 s
  obtain ⟨r6, mC1, eC1⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB) pC1 r7 s
  obtain ⟨r5, mB, eB⟩ := kseq (pA ++ pM ++ pE1 ++ pD ++ pMI) pB r6 s
  obtain ⟨r4, mMI, eMI⟩ := kseq (pA ++ pM ++ pE1 ++ pD) pMI r5 s
  obtain ⟨r3, mD, eD⟩ := kseq (pA ++ pM ++ pE1) pD r4 s
  obtain ⟨r2, mE1, eE1⟩ := kseq (pA ++ pM) pE1 r3 s
  obtain ⟨mA, mM, eM⟩ := kseq pA pM r2 s
  rw [show withSplitPark c keepBits parkHosts body = pA ++ pM ++ pE1 ++ pD ++ pMI ++ pB ++ pC1 ++ pMO ++ pCL ++ pE from rfl,
    eE, eCL, eMO, eC1, eB, eMI, eD, eE1, eM]
  -- 1. pA: copy controlled src into bank
  have hndSB : (c.src ++ c.bank).Nodup := (List.nodup_cons.mp hSrcDis).2
  have hG0B : ∀ x ∈ some G0, x ∉ c.bank := fun x hx => by
    cases Option.some.inj hx; exact hG0Out.1
  have hBank0_s : regValue c.bank s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => hWork_all q (List.mem_of_mem_take (List.mem_of_mem_take hq)))
  have stA := copyRegister_correct (some G0) c.src c.bank hsrc_bank hndSB hG0B s mA
  generalize hsA : run pA mA s = sA at stA ⊢
  have sA_bank : regValue c.bank sA.basis = P := by
    have h := stA.2.2
    rw [hBank0_s, Nat.zero_xor] at h
    simpa [P] using h
  have sA_out (q : Wire) (hb : q ∉ c.bank) : sA.basis q = s.basis q := stA.2.1 q hb
  have hTakeA : regValue (c.bank.take keepBits) sA.basis =
      if s.basis G0 = true then regValue (c.src.take keepBits) s.basis else 0 := by
    have eA := regValue_append (c.bank.take keepBits) (c.bank.drop keepBits) sA.basis
    rw [List.take_append_drop, sA_bank] at eA
    have eS := regValue_append (c.src.take keepBits) (c.src.drop keepBits) s.basis
    rw [List.take_append_drop] at eS
    have hlenT : (c.bank.take keepBits).length = keepBits := by simp [hbankLen, hkeepLe]
    have hlenS : (c.src.take keepBits).length = keepBits := by simp [hsrcLen, hkeepLe]
    have hltA : regValue (c.bank.take keepBits) sA.basis < 2 ^ keepBits := by
      simpa [hlenT] using regValue_lt (c.bank.take keepBits) sA.basis
    have hltS : regValue (c.src.take keepBits) s.basis < 2 ^ keepBits := by
      simpa [hlenS] using regValue_lt (c.src.take keepBits) s.basis
    cases hg : s.basis G0
    · simp only [P, hg, Bool.false_eq_true, if_false] at eA ⊢
      omega
    · simp only [P, hg, if_true] at eA ⊢
      rw [hlenT] at eA; rw [hlenS] at eS
      have m1 : regValue (c.bank.take keepBits) sA.basis = regValue c.src s.basis % 2 ^ keepBits := by
        rw [eA, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltA]
      have m2 : regValue (c.src.take keepBits) s.basis = regValue c.src s.basis % 2 ^ keepBits := by
        rw [eS, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hltS]
      exact m1.trans m2.symm
  -- 2. pM: c.make computes dst = P^2 and liveT
  have sA_dst0 : regValue c.dst sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hDstDisBank q hq))).trans hd0
  have sA_live0 : regValue c.liveT sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hLiveDisBank q hq))).trans hLive0_s
  have sA_sc0 : regValue c.cleanScratch sA.basis = 0 := (regValue_congr _ _ s.basis (fun q hq => sA_out q (hScDisBank q hq))).trans hSc0_s
  have sA_cin0 : sA.basis K0.core.cin = false := (sA_out _ hCin_notBank).trans hc.cin
  have stM := cfg_make_correct c v sA mM sA_dst0 sA_live0 sA_sc0 sA_cin0
  have hZeros := hParkZeroAfterMake sA mM sA_dst0 sA_live0 sA_sc0 sA_cin0
    (fun hm => (sA_out _ (hParkDisBank _ hm)).trans (heu0 hm))
    (fun q hq => (sA_out q (hE0DisBank q hq)).trans (hE0_all q hq))
  generalize hsM : run pM mM sA = sM at stM hZeros ⊢
  have sM_dst : regValue c.dst sM.basis = P ^ 2 := by rw [stM.2.1, sA_bank]
  have sM_out (q : Wire) (hd : q ∉ c.dst) (hl : q ∉ c.liveT) : sM.basis q = sA.basis q := stM.2.2.2.2.2.2 q hd hl
  have hSrcDisBank : ∀ q ∈ c.src, q ∉ c.bank := fun q hq hb => (List.nodup_append.mp hndSB).2.2 q hq q hb rfl
  -- 3. pE1: erase bank.take keepBits
  have hndMask : (G0 :: c.src.take keepBits ++ c.bank.take keepBits).Nodup :=
    list_nodup_of_count_le hSrcDis (fun q => by
      have a := (List.take_sublist keepBits c.src).count_le q
      have b := (List.take_sublist keepBits c.bank).count_le q
      simp only [List.count_cons, List.count_append]; omega)
  have stE1 := eraseMask_correct G0 (c.src.take keepBits) (c.bank.take keepBits)
    (by simp [hsrcLen, hbankLen]) hndMask sM mE1 (by
      have e1 : regValue (c.bank.take keepBits) sM.basis = regValue (c.bank.take keepBits) sA.basis :=
        regValue_congr _ _ _ (fun q hq => sM_out q (fun h => hDstDisBank _ h (List.mem_of_mem_take hq))
          (fun h => hLiveDisBank _ h (List.mem_of_mem_take hq)))
      have e2 : sM.basis G0 = s.basis G0 := (sM_out _ hG0Out.2.1 hG0Out.2.2.1).trans (sA_out _ hG0Out.1)
      have e3 : regValue (c.src.take keepBits) sM.basis = regValue (c.src.take keepBits) s.basis :=
        regValue_congr _ _ _ (fun q hq => (sM_out q (fun h => hDstDisSrc _ h (List.mem_of_mem_take hq))
          (fun h => hLiveDisSrc _ h (List.mem_of_mem_take hq))).trans (sA_out q (hSrcDisBank _ (List.mem_of_mem_take hq))))
      rw [e1, e2, e3]; exact hTakeA)
  generalize hsE1 : run pE1 mE1 sM = sE1 at stE1 ⊢
  have sE1_park0 : ∀ h ∈ parkHosts, sE1.basis h = false := fun h hh =>
    (stE1.2.1 h (fun hb => hParkDisBank h hh (List.mem_of_mem_take hb))).trans (hZeros.1 h hh)
  -- 4. pD: dummies on zero parkHosts (no-op on state!)
  have stD : run pD mD sE1 = sE1 := ParkCopy.dummies_run parkHosts sE1 mD sE1_park0
  rw [stD]
  -- 5. pMI: move bank.drop keepBits into parkHosts
  have hDropLen : (c.bank.drop keepBits).length = parkHosts.length := by simp [hbankLen]; omega
  have hBankNd : c.bank.Nodup := (List.nodup_append.mp hndSB).2.1
  have hndMP : (c.bank.drop keepBits ++ parkHosts).Nodup :=
    List.nodup_append.mpr ⟨hBankNd.sublist (List.drop_sublist _ _), hParkNd,
      fun q hq r hr heq => hParkDisBank r hr (heq ▸ List.mem_of_mem_drop hq)⟩
  have stMI := ParkCopy.move_correct (c.bank.drop keepBits) parkHosts hDropLen hndMP sE1 mMI
    ((regValue_zero _ _).mpr sE1_park0)
  generalize hsMI : run pMI mMI sE1 = sMI at stMI ⊢
  -- Helper: track sMI vs s outside dst ∪ liveT ∪ parkHosts
  have hBankZero_MI : regValue c.bank sMI.basis = 0 := by
    rw [← List.take_append_drop keepBits c.bank, regValue_append]
    have h1 : regValue (c.bank.take keepBits) sMI.basis = 0 := by
      rw [regValue_congr _ _ sE1.basis (fun q hq => by
        have hnD : q ∉ c.bank.drop keepBits := by
          have := hBankNd; rw [← List.take_append_drop keepBits c.bank] at this
          exact fun hd => (List.nodup_append.mp this).2.2 q hq q hd rfl
        exact stMI.2.1 q hnD (fun hp => hParkDisBank q hp (List.mem_of_mem_take hq)))]
      exact stE1.2.2
    rw [h1, stMI.2.2.2]; simp
  have sMI_eq_s (q : Wire) (hd : q ∉ c.dst) (hl : q ∉ c.liveT) (hp : q ∉ parkHosts) :
      sMI.basis q = s.basis q := by
    by_cases hb : q ∈ c.bank
    · exact ((regValue_zero _ _).mp hBankZero_MI q hb).trans ((regValue_zero _ _).mp hBank0_s q hb).symm
    · have h1 := stMI.2.1 q (fun h => hb (List.mem_of_mem_drop h)) hp
      have h2 := stE1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      exact h1.trans (h2.trans ((sM_out q hd hl).trans (sA_out q hb)))
  have sMI_eq_sM_dst (q : Wire) (hd : q ∈ c.dst) : sMI.basis q = sM.basis q := by
    have hnb : q ∉ c.bank := fun hb => hDstDisBank q hd hb
    have hnp : q ∉ parkHosts := fun hp => hParkDisDst q hp hd
    exact (stMI.2.1 q (fun h => hnb (List.mem_of_mem_drop h)) hnp).trans
      (stE1.2.1 q (fun h => hnb (List.mem_of_mem_take h)))
  -- 6. pB: renameProgram foldPerm (bodySwap body) = body on sMI
  have sMI_4834 : sMI.basis 4834 = false :=
    (sMI_eq_s 4834 (fun h => h4834_notReal (by simp [SplitCfg.realAll, h]))
      (fun h => h4834_notReal (by clear * - h; simp only [SplitCfg.realAll, SplitCfg.liveT, List.mem_cons, List.mem_append] at h ⊢; tauto))
      (fun h => (hParkDisSw _ h).1 rfl)).trans h4834_0
  have sMI_4875 : sMI.basis 4875 = false :=
    (sMI_eq_s 4875 (fun h => h4875_notReal (by simp [SplitCfg.realAll, h]))
      (fun h => h4875_notReal (by clear * - h; simp only [SplitCfg.realAll, SplitCfg.liveT, List.mem_cons, List.mem_append] at h ⊢; tauto))
      (fun h => (hParkDisSw _ h).2.2.1 rfl)).trans h4875_0
  have sMI_5093 : sMI.basis 5093 = false :=
    ((stMI.2.1 5093 (fun h => h5093_notBank (List.mem_of_mem_drop h)) (fun h => (hParkDisSw _ h).2.1 rfl)).trans
      (stE1.2.1 5093 (fun h => h5093_notBank (List.mem_of_mem_take h)))).trans hZeros.2.1
  have sMI_5478 : sMI.basis 5478 = false :=
    ((stMI.2.1 5478 (fun h => h5478_notBank (List.mem_of_mem_drop h)) (fun h => (hParkDisSw _ h).2.2.2 rfl)).trans
      (stE1.2.1 5478 (fun h => h5478_notBank (List.mem_of_mem_take h)))).trans hZeros.2.2
  -- Build clean reference state t for callback
  let t : State := { phase := sMI.phase, basis := fun q => if q ∈ c.dst then sM.basis q else s.basis q }
  have t_dst : regValue c.dst t.basis = P ^ 2 := by
    rw [regValue_congr c.dst t.basis sM.basis (fun q hq => by simp [t, hq]), sM_dst]
  have cb := callback t mB t_dst (fun q hq => by simp [t, hq])
  have body_dis_live : ∀ q ∈ wires body, q ∉ c.liveT := fun q hq hl =>
    (hLiveSub q hl).elim (fun h => hBodyDisE0 q h hq) (fun h => hBodyDisWorkT q h hq)
  have body_dis_park : ∀ q ∈ wires body, q ∉ parkHosts := fun q hq hp =>
    (hParkIn q hp).elim (fun h => hBodyDisE0 q h hq) (fun h => hBodyDisEU (h ▸ hp) (h ▸ hq))
  have locB := ECDSAAdd.run_measured_locality body (wires body) (Finset.Subset.refl _) sMI t mB rfl
    (fun q hq => by
      by_cases hd : q ∈ c.dst
      · simp [t, hd]; exact sMI_eq_sM_dst q hd
      · simp [t, hd]; exact sMI_eq_s q hd (body_dis_live q hq) (body_dis_park q hq))
  have runBody_phase : (run body mB sMI).phase = sMI.phase := locB.1.trans cb.1
  have runBody_out : regValue K0.core.out (run body mB sMI).basis = V := by
    rw [regValue_congr K0.core.out (run body mB sMI).basis (run body mB t).basis (fun q hq => by
      by_cases hw : q ∈ wires body
      · exact locB.2 q hw
      · rw [run_preserves_outside body mB sMI q hw, run_preserves_outside body mB t q hw]
        have hnd : q ∉ c.dst := fun h => hDstDisOut q h hq
        simp only [t, hnd, if_false]
        exact sMI_eq_s q hnd (fun h => hLiveDisOut q h hq) (fun h => hParkDisOut q h hq))]
    exact cb.2.1
  have runBody_keep (q : Wire) (ho : q ∉ K0.core.out) : (run body mB sMI).basis q = sMI.basis q := by
    by_cases hw : q ∈ wires body
    · rw [locB.2 q hw, cb.2.2 q ho]
      by_cases hd : q ∈ c.dst
      · simp [t, hd]; exact (sMI_eq_sM_dst q hd).symm
      · simp [t, hd]; exact (sMI_eq_s q hd (body_dis_live q hw) (body_dis_park q hw)).symm
    · exact run_preserves_outside body mB sMI q hw
  have hFoldPerm : LowZero18Square.foldPerm K0 E0 = Equiv.swap 4834 5093 := by
    ext x; rw [StairSquareSites.LT48K.foldPerm_eq, Equiv.swap_apply_def]; rfl
  have hSqSwap : R2SqEp760.sqSwap K0 E0 = Equiv.swap 4875 5478 := by
    ext x; rw [StairSquareSites.LT48K.sqSwap_eq, Equiv.swap_apply_def]; rfl
  have eqSq : run (R2SqEp760.bodySwap K0 E0 body) mB sMI = run body mB sMI := by
    rw [R2SqEp760.bodySwap, hSqSwap]
    exact swap_run_eq 4875 5478 body sMI mB (sMI_4875.trans sMI_5478.symm)
      ((runBody_keep 4875 hSwMem.2.2.2.2.1).trans (sMI_4875.trans (sMI_5478.symm.trans (runBody_keep 5478 hSwMem.2.2.2.2.2.1).symm)))
  have eqPB : run pB mB sMI = run body mB sMI := by
    change run (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) mB sMI = _
    rw [hFoldPerm]
    refine (swap_run_eq 4834 5093 (R2SqEp760.bodySwap K0 E0 body) sMI mB
      (sMI_4834.trans sMI_5093.symm) ?_).trans eqSq
    rw [eqSq, runBody_keep 4834 hSwMem.2.2.1, runBody_keep 5093 hSwMem.2.2.2.1, sMI_4834, sMI_5093]
  generalize hsB : run pB mB sMI = sB at eqPB ⊢
  have sB_phase : sB.phase = sMI.phase := by rw [eqPB]; exact runBody_phase
  have sB_out : regValue K0.core.out sB.basis = V := by rw [eqPB]; exact runBody_out
  have sB_keep (q : Wire) (ho : q ∉ K0.core.out) : sB.basis q = sMI.basis q := by rw [eqPB]; exact runBody_keep q ho
  -- 7. pC1: CachedSquareCopy restores bank.take keepBits
  have sB_dst : regValue c.dst sB.basis = P ^ 2 := by
    rw [regValue_congr c.dst sB.basis sM.basis (fun q hq => (sB_keep q (hDstDisOut q hq)).trans (sMI_eq_sM_dst q hq)), sM_dst]
  have sB_G0 : sB.basis G0 = s.basis G0 :=
    (sB_keep G0 hG0Out.2.2.2.2).trans (sMI_eq_s G0 hG0Out.2.1 hG0Out.2.2.1 hParkDisG0)
  have sB_src : regValue c.src sB.basis = regValue c.src s.basis :=
    regValue_congr c.src sB.basis s.basis (fun q hq =>
      (sB_keep q (hSrcDisOut q hq)).trans
      (sMI_eq_s q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq) (fun h => hParkDisSrc _ h hq)))
  have hCached : sB.basis (LowZero18Square.cacheWire K0 c.dst) =
      (sB.basis G0 && sB.basis ((c.src.take keepBits).headD 0)) := by
    rw [hCacheEq, ParkCopy.headD_take c.src keepBits hkPos]
    have hsq := CachedSquareCopy.square_head c.src c.dst G0 sB (by omega) (by rw [v.dstLen]; omega)
      (by rw [sB_dst, sB_G0, sB_src])
    exact hsq
  have eqC1 : run pC1 mC1 sB = run (copyRegister (some G0) (c.src.take keepBits) (c.bank.take keepBits)) mC1 sB :=
    CachedSquareCopy.run_eq G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits) sB mC1 hCached
  have hndSB_k : (c.src.take keepBits ++ c.bank.take keepBits).Nodup := (List.nodup_cons.mp hndMask).2
  have hG0B_k : ∀ x ∈ some G0, x ∉ c.bank.take keepBits := fun x hx hb => hG0B x hx (List.mem_of_mem_take hb)
  have stC1 := copyRegister_correct (some G0) (c.src.take keepBits) (c.bank.take keepBits)
    (by simp [hsrcLen, hbankLen]) hndSB_k hG0B_k sB mC1
  rw [← eqC1] at stC1
  generalize hsC1 : run pC1 mC1 sB = sC1 at stC1 ⊢
  have sB_bk0 : regValue (c.bank.take keepBits) sB.basis = 0 := by
    rw [regValue_congr _ _ sMI.basis (fun q hq => sB_keep q (hBankDisOut q (List.mem_of_mem_take hq)))]
    exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hBankZero_MI q (List.mem_of_mem_take hq))
  have sC1_bk : regValue (c.bank.take keepBits) sC1.basis = regValue (c.bank.take keepBits) sA.basis := by
    have h := stC1.2.2
    rw [sB_bk0, Nat.zero_xor] at h
    have hsrc_k : regValue (c.src.take keepBits) sB.basis = regValue (c.src.take keepBits) s.basis :=
      regValue_congr _ _ s.basis (fun q hq =>
        (sB_keep q (hSrcDisOut q (List.mem_of_mem_take hq))).trans
        (sMI_eq_s q (fun h' => hDstDisSrc _ h' (List.mem_of_mem_take hq))
          (fun h' => hLiveDisSrc _ h' (List.mem_of_mem_take hq))
          (fun h' => hParkDisSrc _ h' (List.mem_of_mem_take hq))))
    rw [h]; simp only [copyValue, sB_G0, hsrc_k]; exact hTakeA.symm
  -- 8. pMO: move parkHosts back into bank.drop keepBits
  have hndPM : (parkHosts ++ c.bank.drop keepBits).Nodup := (List.perm_append_comm.nodup_iff).mp hndMP
  have hDropNotTake : ∀ q ∈ c.bank.drop keepBits, q ∉ c.bank.take keepBits := by
    intro q hd ht
    have := hBankNd; rw [← List.take_append_drop keepBits c.bank] at this
    exact (List.nodup_append.mp this).2.2 q ht q hd rfl
  have sC1_drop0 : regValue (c.bank.drop keepBits) sC1.basis = 0 :=
    (regValue_congr _ _ sMI.basis (fun q hq =>
      (stC1.2.1 q (hDropNotTake q hq)).trans (sB_keep q (hBankDisOut q (List.mem_of_mem_drop hq))))).trans stMI.2.2.2
  have stMO := ParkCopy.move_correct parkHosts (c.bank.drop keepBits) hDropLen.symm hndPM sC1 mMO sC1_drop0
  generalize hsMO : run pMO mMO sC1 = sMO at stMO ⊢
  -- Key state invariants on sMO before c.clear!
  have sMO_eq_sM_of_not_out (q : Wire) (ho : q ∉ K0.core.out) (hb : q ∉ c.bank) : sMO.basis q = sM.basis q := by
    by_cases hp : q ∈ parkHosts
    · have h0_mo : sMO.basis q = false := (regValue_zero _ _).mp stMO.2.2.2 q hp
      have h0_m : sM.basis q = false := hZeros.1 q hp
      exact h0_mo.trans h0_m.symm
    · have h1 := stMO.2.1 q hp (fun h => hb (List.mem_of_mem_drop h))
      have h2 := stC1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      have h3 := sB_keep q ho
      have h4 := stMI.2.1 q (fun h => hb (List.mem_of_mem_drop h)) hp
      have h5 := stE1.2.1 q (fun h => hb (List.mem_of_mem_take h))
      exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have sMO_bank : regValue c.bank sMO.basis = P := by
    rw [← List.take_append_drop keepBits c.bank, regValue_append]
    have h1 : regValue (c.bank.take keepBits) sMO.basis = regValue (c.bank.take keepBits) sA.basis := by
      rw [regValue_congr _ _ sC1.basis (fun q hq =>
        stMO.2.1 q (fun hp => hParkDisBank q hp (List.mem_of_mem_take hq)) (fun hd => hDropNotTake q hd hq)), sC1_bk]
    have h2 : regValue (c.bank.drop keepBits) sMO.basis = regValue (c.bank.drop keepBits) sA.basis := by
      rw [stMO.2.2.1]
      rw [regValue_congr parkHosts sC1.basis sMI.basis (fun q hq =>
        (stC1.2.1 q (fun ht => hParkDisBank q hq (List.mem_of_mem_take ht))).trans (sB_keep q (hParkDisOut q hq)))]
      rw [stMI.2.2.1]
      exact regValue_congr _ _ sA.basis (fun q hq =>
        (stE1.2.1 q (hDropNotTake q hq)).trans
          (sM_out q (fun h => hDstDisBank _ h (List.mem_of_mem_drop hq))
            (fun h => hLiveDisBank _ h (List.mem_of_mem_drop hq))))
    rw [h1, h2, ← regValue_append, List.take_append_drop, sA_bank]
  have sMO_bank_bit (q : Wire) (hq : q ∈ c.bank) : sMO.basis q = sA.basis q := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have b1 := RawClearCarryProbe.register_bit c.bank i sMO.basis hi
    have b2 := RawClearCarryProbe.register_bit c.bank i sA.basis hi
    have hg : c.bank.getD i 0 = c.bank[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg] at b1 b2; rw [b1, b2, sMO_bank, sA_bank]
  have sMO_lo : regValue c.R.lo sMO.basis = regValue c.R.lo sA.basis :=
    regValue_congr _ _ _ (fun q hq => sMO_bank_bit q (List.mem_of_mem_take hq))
  have sMO_hi : regValue c.R.hi sMO.basis = regValue c.R.hi sA.basis :=
    regValue_congr _ _ _ (fun q hq => sMO_bank_bit q (List.mem_of_mem_drop hq))
  have sMO_dst : regValue c.dst sMO.basis = (regValue c.bank sMO.basis) ^ 2 := by
    rw [regValue_congr c.dst sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q (hDstDisOut q hq) (hDstDisBank q hq)),
      sM_dst, sMO_bank]
  have sMO_T : regValue c.T sMO.basis = 2 * regValue c.R.lo sMO.basis * regValue c.R.hi sMO.basis := by
    rw [regValue_congr c.T sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.1, sMO_lo, sMO_hi]
  have sMO_T1 : regValue c.T1 sMO.basis = 2 * (regValue c.R.lo sMO.basis % 2 ^ 32) * (regValue c.R.lo sMO.basis / 2 ^ 32) := by
    rw [regValue_congr c.T1 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.1, sMO_lo]
  have sMO_T2 : regValue c.T2 sMO.basis = 2 * (regValue c.R.hi sMO.basis % 2 ^ c.Q2.h) * (regValue c.R.hi sMO.basis / 2 ^ c.Q2.h) := by
    rw [regValue_congr c.T2 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.2.1, sMO_hi]
  have sMO_T5 : regValue c.T5 sMO.basis = 2 * ((regValue c.R.lo sMO.basis + regValue c.R.hi sMO.basis) % 2 ^ 33) *
      ((regValue c.R.lo sMO.basis + regValue c.R.hi sMO.basis) / 2 ^ 33) := by
    rw [regValue_congr c.T5 sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q
      (hLiveDisOut q (by simp [SplitCfg.liveT, hq])) (hLiveDisBank q (by simp [SplitCfg.liveT, hq]))),
      stM.2.2.2.2.2.1, sMO_lo, sMO_hi]
  have sMO_sc0 : regValue c.cleanScratch sMO.basis = 0 := by
    rw [regValue_congr c.cleanScratch sMO.basis sM.basis (fun q hq => sMO_eq_sM_of_not_out q (hScDisOut q hq) (hScDisBank q hq))]
    refine (regValue_congr c.cleanScratch sM.basis sA.basis (fun q hq => sM_out q
      (kdis v.realNd (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.cleanScratch, List.count_cons, List.count_append, List.count_nil]; omega) q hq)
      (kdis v.realNd (fun x => by clear * - c x; rw [realAll_count]; simp only [SplitCfg.cleanScratch, SplitCfg.liveT, List.count_cons, List.count_append, List.count_nil]; omega) q hq))).trans sA_sc0
  have sMO_cin0 : sMO.basis K0.core.cin = false :=
    (sMO_eq_sM_of_not_out K0.core.cin hCin_notOut hCin_notBank).trans
      ((sM_out K0.core.cin hCin_notDst hCin_notLive).trans sA_cin0)
  -- 9. pCL: c.clear uncomputes dst and liveT to 0
  have stCL := cfg_clear_correct c v sMO mCL sMO_dst sMO_T sMO_T1 sMO_T2 sMO_T5 sMO_sc0 sMO_cin0
  generalize hsCL : run pCL mCL sMO = sCL at stCL ⊢
  -- 10. pE: eraseMask erases bank back to 0
  have stE := eraseMask_correct G0 c.src c.bank hsrc_bank hSrcDis sCL mE (by
    have e1 : regValue c.bank sCL.basis = P :=
      (regValue_congr c.bank sCL.basis sMO.basis (fun q hq =>
        stCL.2.2.2 q (fun h => hDstDisBank _ h hq) (fun h => hLiveDisBank _ h hq))).trans sMO_bank
    have e2 : sCL.basis G0 = s.basis G0 :=
      (stCL.2.2.2 G0 hG0Out.2.1 hG0Out.2.2.1).trans
        ((sMO_eq_sM_of_not_out G0 hG0Out.2.2.2.2 hG0Out.1).trans
          ((sM_out G0 hG0Out.2.1 hG0Out.2.2.1).trans (sA_out G0 hG0Out.1)))
    have e3 : regValue c.src sCL.basis = regValue c.src s.basis :=
      regValue_congr c.src sCL.basis s.basis (fun q hq =>
        (stCL.2.2.2 q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq)).trans
          ((sMO_eq_sM_of_not_out q (hSrcDisOut q hq) (hSrcDisBank q hq)).trans
            ((sM_out q (fun h => hDstDisSrc _ h hq) (fun h => hLiveDisSrc _ h hq)).trans
              (sA_out q (hSrcDisBank q hq)))))
    rw [e1, e2, e3])
  generalize hsE : run pE mE sCL = sE at stE ⊢
  refine ⟨?_, ?_, ?_⟩
  · exact stE.1.trans (stCL.1.trans (stMO.1.trans (stC1.1.trans (sB_phase.trans
      (stMI.1.trans (stE1.1.trans (stM.1.trans stA.1)))))))
  · rw [regValue_congr K0.core.out sE.basis sB.basis (fun q hq =>
      (stE.2.1 q (fun h => hBankDisOut q h hq)).trans
      ((stCL.2.2.2 q (fun h => hDstDisOut q h hq) (fun h => hLiveDisOut q h hq)).trans
      ((stMO.2.1 q (fun h => hParkDisOut q h hq) (fun h => hBankDisOut q (List.mem_of_mem_drop h) hq)).trans
       (stC1.2.1 q (fun h => hBankDisOut q (List.mem_of_mem_take h) hq)))))]
    exact sB_out
  · intro q ho
    by_cases hb : q ∈ c.bank
    · exact ((regValue_zero _ _).mp stE.2.2 q hb).trans ((regValue_zero _ _).mp hBank0_s q hb).symm
    · rw [stE.2.1 q hb]
      by_cases hd : q ∈ c.dst
      · exact ((regValue_zero _ _).mp stCL.2.1 q hd).trans ((regValue_zero _ _).mp hd0 q hd).symm
      · by_cases hl : q ∈ c.liveT
        · exact ((regValue_zero _ _).mp stCL.2.2.1 q hl).trans ((regValue_zero _ _).mp hLive0_s q hl).symm
        · exact (stCL.2.2.2 q hd hl).trans ((sMO_eq_sM_of_not_out q ho hb).trans ((sM_out q hd hl).trans (sA_out q hb)))

/-! ### Zero-bit proofs for parked hosts and swap hosts after `make` -/

private theorem getD_take {α : Type} (l : List α) (n i : Nat) (d : α) (hi : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

private theorem getD_drop {α : Type} (l : List α) (k i : Nat) (d : α) :
    (l.drop k).getD i d = l.getD (k + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem cfg128_zeros (c : SplitCfg) (v : CfgValid c) (hn : c.n = 128)
    (hT5_0 : c.T5.getD 0 0 = E0.getD 231 0)
    (hT5_66 : c.T5.getD 66 0 = E0.getD 298 0)
    (hT5_67 : c.T5.getD 67 0 = E0.getD 299 0)
    (hT_eq : c.T = E0.take 130) (hT1_eq : c.T1 = (E0.drop 132).take 66) (hT2_eq : c.T2 = (E0.drop 232).take 66)
    (parkHosts : List Wire)
    (hParkSub : ∀ h ∈ parkHosts, h ∈ ParkCopy.hosts E0 ∨ h = ControlLoan1589BFFold.eU K0)
    (h130_not : E0.getD 130 0 ∉ c.dst ∧ E0.getD 130 0 ∉ c.liveT)
    (h131_not : E0.getD 131 0 ∉ c.dst ∧ E0.getD 131 0 ∉ c.liveT)
    (heU_not : ControlLoan1589BFFold.eU K0 ∉ c.dst ∧ ControlLoan1589BFFold.eU K0 ∉ c.liveT)
    (s0 : State) (m0 : List Bool)
    (hd0 : regValue c.dst s0.basis = 0) (hT0 : regValue c.liveT s0.basis = 0)
    (hSc0 : regValue c.cleanScratch s0.basis = 0) (hi0 : s0.basis K0.core.cin = false)
    (heu0 : ControlLoan1589BFFold.eU K0 ∈ parkHosts → s0.basis (ControlLoan1589BFFold.eU K0) = false)
    (he0 : ∀ q ∈ E0, s0.basis q = false) :
    (∀ h ∈ parkHosts, (run c.make m0 s0).basis h = false) ∧
    (run c.make m0 s0).basis 5093 = false ∧ (run c.make m0 s0).basis 5478 = false := by
  have st := cfg_make_correct c v s0 m0 hd0 hT0 hSc0 hi0
  set u := run c.make m0 s0
  set a := regValue c.R.lo s0.basis
  set b := regValue c.R.hi s0.basis
  have haLt : a < 2 ^ 64 := by
    have : c.R.lo.length = 64 := by simp [KRegs.lo, SplitCfg.R, v.bankLen, hn]
    simpa [this] using regValue_lt c.R.lo s0.basis
  have hbLt : b < 2 ^ 64 := by
    have : c.R.hi.length = 64 := by simp [KRegs.hi, SplitCfg.R, v.bankLen, hn]
    simpa [this] using regValue_lt c.R.hi s0.basis
  have hQ2h : c.Q2.h = 32 := by simp [SplitCfg.Q2, hn]
  have hElen : E0.length = 300 := by rw [E0_eq]; decide +kernel
  have h5093 : E0.getD 0 0 = 5093 := by rw [E0_eq]; decide +kernel
  have h5478 : E0.getD 130 0 = 5478 := by rw [E0_eq]; decide +kernel
  have bT0 : u.basis (E0.getD 0 0) = false := by
    have e : c.T.getD 0 0 = E0.getD 0 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact even_bit0_false c.T u.basis (a * b) (by rw [v.tLen, hn]; decide) (by rw [st.2.2.1]; ring)
  have bT129 : u.basis (E0.getD 129 0) = false := by
    have e : c.T.getD 129 0 = E0.getD 129 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; refine hi_bit_false c.T u.basis 129 (by rw [v.tLen, hn]; decide) ?_
    rw [st.2.2.1, Nat.mul_assoc]; have : a * b < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' haLt hbLt; omega
  have bT130 : u.basis (E0.getD 130 0) = false :=
    (st.2.2.2.2.2.2 _ h130_not.1 h130_not.2).trans (he0 _ (DiagSq.getD_in E0 130 (by omega)))
  have bT131 : u.basis (E0.getD 131 0) = false :=
    (st.2.2.2.2.2.2 _ h131_not.1 h131_not.2).trans (he0 _ (DiagSq.getD_in E0 131 (by omega)))
  have bT1_0 : u.basis (E0.getD 132 0) = false := by
    have e : c.T1.getD 0 0 = E0.getD 132 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false c.T1 u.basis ((a % 2 ^ 32) * (a / 2 ^ 32)) (by rw [v.t1Len]; decide) (by rw [st.2.2.2.1]; ring)
  have bT1_65 : u.basis (E0.getD 197 0) = false := by
    have e : c.T1.getD 65 0 = E0.getD 197 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false c.T1 u.basis 65 (by rw [v.t1Len]; decide) ?_
    rw [st.2.2.2.1, Nat.mul_assoc]
    have h1 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : a / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (a % 2 ^ 32) * (a / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT2_0 : u.basis (E0.getD 232 0) = false := by
    have e : c.T2.getD 0 0 = E0.getD 232 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false c.T2 u.basis ((b % 2 ^ c.Q2.h) * (b / 2 ^ c.Q2.h))
      (by have := v.t2Len; simp [hn] at this; omega) (by rw [st.2.2.2.2.1]; ring)
  have bT2_65 : u.basis (E0.getD 297 0) = false := by
    have e : c.T2.getD 65 0 = E0.getD 297 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false c.T2 u.basis 65 (by have := v.t2Len; simp [hn] at this; omega) ?_
    rw [st.2.2.2.2.1, hQ2h, Nat.mul_assoc]
    have h1 : b % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : b / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (b % 2 ^ 32) * (b / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT5_0 : u.basis (E0.getD 231 0) = false := by
    rw [← hT5_0]; exact even_bit0_false c.T5 u.basis (((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33))
      (by rw [v.t5Len]; decide) (by rw [st.2.2.2.2.2.1]; ring)
  have bT5_lt : regValue c.T5 u.basis < 2 ^ 66 := by
    rw [st.2.2.2.2.2.1, Nat.mul_assoc]
    have h1 : (a + b) % 2 ^ 33 < 2 ^ 33 := Nat.mod_lt _ (by decide)
    have h2 : (a + b) / 2 ^ 33 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : ((a + b) % 2 ^ 33) * ((a + b) / 2 ^ 33) < 2 ^ 33 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT5_66 : u.basis (E0.getD 298 0) = false := by
    rw [← hT5_66]; exact hi_bit_false c.T5 u.basis 66 (by rw [v.t5Len]; decide) bT5_lt
  have bT5_67 : u.basis (E0.getD 299 0) = false := by
    rw [← hT5_67]; exact hi_bit_false c.T5 u.basis 67 (by rw [v.t5Len]; decide) (by omega)
  refine ⟨?_, by rwa [← h5093], by rwa [← h5478]⟩
  intro h hh
  rcases hParkSub h hh with hp | rfl
  · simp only [ParkCopy.hosts, ParkCopy.hostIdx, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [bT129, bT131, bT1_0, bT1_65, bT5_0, bT2_0, bT2_65, bT5_66, bT5_67]
  · exact (st.2.2.2.2.2.2 _ heU_not.1 heU_not.2).trans (heu0 hh)

private theorem cfgC_zeros (s0 : State) (m0 : List Bool)
    (hd0 : regValue cfgC.dst s0.basis = 0) (hT0 : regValue cfgC.liveT s0.basis = 0)
    (hSc0 : regValue cfgC.cleanScratch s0.basis = 0) (hi0 : s0.basis K0.core.cin = false)
    (_ : ControlLoan1589BFFold.eU K0 ∈ ParkCopyS.hostsS E0 → s0.basis (ControlLoan1589BFFold.eU K0) = false)
    (_ : ∀ q ∈ E0, s0.basis q = false) :
    (∀ h ∈ ParkCopyS.hostsS E0, (run cfgC.make m0 s0).basis h = false) ∧
    (run cfgC.make m0 s0).basis 5093 = false ∧ (run cfgC.make m0 s0).basis 5478 = false := by
  have st := cfg_make_correct cfgC cfgC_valid s0 m0 hd0 hT0 hSc0 hi0
  set u := run cfgC.make m0 s0
  set a := regValue cfgC.R.lo s0.basis
  set b := regValue cfgC.R.hi s0.basis
  have hbl : cfgC.bank.length = 129 := cfgC_valid.bankLen
  have ht2 : cfgC.T2.length = 68 := cfgC_valid.t2Len
  have haLt : a < 2 ^ 64 := by
    have : cfgC.R.lo.length = 64 := by simp only [KRegs.lo, SplitCfg.R, List.length_take, hbl]; decide
    simpa [this] using regValue_lt cfgC.R.lo s0.basis
  have hbLt : b < 2 ^ 65 := by
    have : cfgC.R.hi.length = 65 := by simp only [KRegs.hi, SplitCfg.R, List.length_drop, hbl]
    simpa [this] using regValue_lt cfgC.R.hi s0.basis
  have hQ2h : cfgC.Q2.h = 33 := by simp [SplitCfg.Q2, cfgC]
  have hT_eq : cfgC.T = E0.take 132 := by simp [SplitCfg.T, cfgC]
  have hT1_eq : cfgC.T1 = (E0.drop 132).take 66 := rfl
  have hT2_eq : cfgC.T2 = (E0.drop 232).take 68 := rfl
  have h5093 : E0.getD 0 0 = 5093 := by rw [E0_eq]; decide +kernel
  have h5478 : E0.getD 130 0 = 5478 := by rw [E0_eq]; decide +kernel
  have bT0 : u.basis (E0.getD 0 0) = false := by
    have e : cfgC.T.getD 0 0 = E0.getD 0 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact even_bit0_false cfgC.T u.basis (a * b) (by rw [cfgC_valid.tLen]; decide) (by rw [st.2.2.1]; ring)
  have hT_lt : regValue cfgC.T u.basis < 2 ^ 130 := by
    rw [st.2.2.1, Nat.mul_assoc]; have : a * b < 2 ^ 64 * 2 ^ 65 := Nat.mul_lt_mul'' haLt hbLt; omega
  have bT130 : u.basis (E0.getD 130 0) = false := by
    have e : cfgC.T.getD 130 0 = E0.getD 130 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact hi_bit_false cfgC.T u.basis 130 (by rw [cfgC_valid.tLen]; decide) hT_lt
  have bT131 : u.basis (E0.getD 131 0) = false := by
    have e : cfgC.T.getD 131 0 = E0.getD 131 0 := by rw [hT_eq, getD_take _ _ _ _ (by decide)]
    rw [← e]; exact hi_bit_false cfgC.T u.basis 131 (by rw [cfgC_valid.tLen]; decide) (by omega)
  have bT1_0 : u.basis (E0.getD 132 0) = false := by
    have e : cfgC.T1.getD 0 0 = E0.getD 132 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false cfgC.T1 u.basis ((a % 2 ^ 32) * (a / 2 ^ 32)) (by rw [cfgC_valid.t1Len]; decide) (by rw [st.2.2.2.1]; ring)
  have bT1_65 : u.basis (E0.getD 197 0) = false := by
    have e : cfgC.T1.getD 65 0 = E0.getD 197 0 := by rw [hT1_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false cfgC.T1 u.basis 65 (by rw [cfgC_valid.t1Len]; decide) ?_
    rw [st.2.2.2.1, Nat.mul_assoc]
    have h1 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : a / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (a % 2 ^ 32) * (a / 2 ^ 32) < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  have bT2_0 : u.basis (E0.getD 232 0) = false := by
    have e : cfgC.T2.getD 0 0 = E0.getD 232 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; exact even_bit0_false cfgC.T2 u.basis ((b % 2 ^ cfgC.Q2.h) * (b / 2 ^ cfgC.Q2.h))
      (by omega) (by rw [st.2.2.2.2.1]; ring)
  have bT2_67 : u.basis (E0.getD 299 0) = false := by
    have e : cfgC.T2.getD 67 0 = E0.getD 299 0 := by rw [hT2_eq, getD_take _ _ _ _ (by decide), getD_drop]
    rw [← e]; refine hi_bit_false cfgC.T2 u.basis 67 (by omega) ?_
    rw [st.2.2.2.2.1, hQ2h, Nat.mul_assoc]
    have h1 : b % 2 ^ 33 < 2 ^ 33 := Nat.mod_lt _ (by decide)
    have h2 : b / 2 ^ 33 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    have : (b % 2 ^ 33) * (b / 2 ^ 33) < 2 ^ 33 * 2 ^ 32 := Nat.mul_lt_mul'' h1 h2; omega
  refine ⟨?_, by rwa [← h5093], by rwa [← h5478]⟩
  intro h hh
  simp only [ParkCopyS.hostsS, ParkCopyS.hostIdxS, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  exacts [bT131, bT1_0, bT1_65, bT2_0, bT2_67]

/-! ### Branch equivalences (`brC`, `brB`, `brA`) and `coreOK` -/

private theorem mask_union_mem (A B C : List Nat)
    (h : A.all (fun q => (StairSquareBChecks.LT48B.maskL B).testBit q || (StairSquareBChecks.LT48B.maskL C).testBit q) = true) :
    ∀ q ∈ A, q ∈ B ∨ q ∈ C := by
  intro q hq
  have t := List.all_eq_true.mp h q hq
  simp only [Bool.or_eq_true, StairSquareBChecks.LT48B.testBit_maskL, decide_eq_true_eq] at t
  exact t

private theorem cfgA_geom :
    118 + (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).length = cfgA.n ∧
    cfgA.src.length = cfgA.n ∧
    (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).Nodup ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∉ cfgA.bank ∧ h ∉ cfgA.src ∧ h ∉ cfgA.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ∧
    (G0 :: cfgA.src ++ cfgA.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgA.bank) ∧
    (∀ q ∈ cfgA.workT, q ∈ K0.core.work) ∧
    (∀ q ∈ cfgA.liveT, (q ∈ E0 ∨ q ∈ cfgA.workT) ∧ q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) ∧
    (∀ q ∈ cfgA.dst, q ∉ cfgA.bank ∧ q ∉ cfgA.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgA.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgA.bank ∧ G0 ∉ cfgA.dst ∧ G0 ∉ cfgA.liveT ∧ G0 ∉ cfgA.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgA.dst = cfgA.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgA.dst ∧ E0.getD 130 0 ∉ cfgA.liveT ∧ E0.getD 131 0 ∉ cfgA.dst ∧ E0.getD 131 0 ∉ cfgA.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgA.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgA.liveT) ∧
    (cfgA.T5.getD 0 0 = E0.getD 231 0 ∧ cfgA.T5.getD 66 0 = E0.getD 298 0 ∧ cfgA.T5.getD 67 0 = E0.getD 299 0) := by
  have hS : 118 + (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).length = cfgA.n ∧
      cfgA.src.length = cfgA.n ∧ (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)).Nodup ∧
      (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
      (∀ h ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
      G0 ∉ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ∧
      (G0 ∉ cfgA.bank ∧ G0 ∉ cfgA.dst ∧ G0 ∉ cfgA.liveT ∧ G0 ∉ cfgA.cleanScratch ∧ G0 ∉ K0.core.out) ∧
      LowZero18Square.cacheWire K0 cfgA.dst = cfgA.dst.headD 0 ∧
      (E0.getD 130 0 ∉ cfgA.dst ∧ E0.getD 130 0 ∉ cfgA.liveT ∧ E0.getD 131 0 ∉ cfgA.dst ∧ E0.getD 131 0 ∉ cfgA.liveT ∧
        ControlLoan1589BFFold.eU K0 ∉ cfgA.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgA.liveT) ∧
      (cfgA.T5.getD 0 0 = E0.getD 231 0 ∧ cfgA.T5.getD 66 0 = E0.getD 298 0 ∧ cfgA.T5.getD 67 0 = E0.getD 299 0) := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hnd : (G0 :: cfgA.src ++ cfgA.bank).Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPB := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPS := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPD := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) cfgA.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPO := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hEB := StairSquareBChecks.LT48B.disj_of_maskL E0 cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hWW := StairSquareBChecks.LT48B.sub_of_maskL cfgA.workT K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLU := mask_union_mem cfgA.liveT E0 cfgA.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLB := StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLS := StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSU := mask_union_mem cfgA.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSB := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSS := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSP := StairSquareBChecks.LT48B.disj_of_maskL cfgA.cleanScratch (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDB := StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst cfgA.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDS := StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst cfgA.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hBO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSrO := StairSquareBChecks.LT48B.disj_of_maskL cfgA.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2⟩

private theorem cfgB_geom :
    119 + (ParkCopy.hosts E0).length = cfgB.n ∧
    cfgB.src.length = cfgB.n ∧
    (ParkCopy.hosts E0).Nodup ∧
    (∀ h ∈ ParkCopy.hosts E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopy.hosts E0, h ∉ cfgB.bank ∧ h ∉ cfgB.src ∧ h ∉ cfgB.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopy.hosts E0 ∧
    (G0 :: cfgB.src ++ cfgB.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgB.bank) ∧
    (∀ q ∈ cfgB.workT, q ∈ K0.core.work ∨ q = D0) ∧
    (∀ q ∈ cfgB.liveT, (q ∈ E0 ∨ q ∈ cfgB.workT) ∧ q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopy.hosts E0) ∧
    (∀ q ∈ cfgB.dst, q ∉ cfgB.bank ∧ q ∉ cfgB.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgB.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgB.bank ∧ G0 ∉ cfgB.dst ∧ G0 ∉ cfgB.liveT ∧ G0 ∉ cfgB.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgB.dst = cfgB.dst.headD 0 ∧
    (E0.getD 130 0 ∉ cfgB.dst ∧ E0.getD 130 0 ∉ cfgB.liveT ∧ E0.getD 131 0 ∉ cfgB.dst ∧ E0.getD 131 0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ cfgB.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgB.liveT ∧
      ControlLoan1589BFFold.eU K0 ∉ ParkCopy.hosts E0) ∧
    (cfgB.T5.getD 0 0 = E0.getD 231 0 ∧ cfgB.T5.getD 66 0 = E0.getD 298 0 ∧ cfgB.T5.getD 67 0 = E0.getD 299 0) := by
  have hS : 119 + (ParkCopy.hosts E0).length = cfgB.n ∧
      cfgB.src.length = cfgB.n ∧ (ParkCopy.hosts E0).Nodup ∧
      (∀ h ∈ ParkCopy.hosts E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
      (∀ h ∈ ParkCopy.hosts E0, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
      G0 ∉ ParkCopy.hosts E0 ∧
      (G0 ∉ cfgB.bank ∧ G0 ∉ cfgB.dst ∧ G0 ∉ cfgB.liveT ∧ G0 ∉ cfgB.cleanScratch ∧ G0 ∉ K0.core.out) ∧
      LowZero18Square.cacheWire K0 cfgB.dst = cfgB.dst.headD 0 ∧
      (E0.getD 130 0 ∉ cfgB.dst ∧ E0.getD 130 0 ∉ cfgB.liveT ∧ E0.getD 131 0 ∉ cfgB.dst ∧ E0.getD 131 0 ∉ cfgB.liveT ∧
        ControlLoan1589BFFold.eU K0 ∉ cfgB.dst ∧ ControlLoan1589BFFold.eU K0 ∉ cfgB.liveT ∧
        ControlLoan1589BFFold.eU K0 ∉ ParkCopy.hosts E0) ∧
      (cfgB.T5.getD 0 0 = E0.getD 231 0 ∧ cfgB.T5.getD 66 0 = E0.getD 298 0 ∧ cfgB.T5.getD 67 0 = E0.getD 299 0) := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hnd : (G0 :: cfgB.src ++ cfgB.bank).Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPB := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPS := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPD := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) cfgB.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPO := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopy.hosts E0) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hEB := StairSquareBChecks.LT48B.disj_of_maskL E0 cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hWW : ∀ q ∈ cfgB.workT, q ∈ K0.core.work ∨ q = D0 := by
    have h := mask_union_mem cfgB.workT K0.core.work [D0] (by simp only [cfgB_fast, workTB_lit, K0_eq, D0_eq]; decide +kernel)
    intro q hq; exact (h q hq).imp_right List.mem_singleton.mp
  have hLU := mask_union_mem cfgB.liveT E0 cfgB.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLB := StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLS := StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSU := mask_union_mem cfgB.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSB := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSS := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSP := StairSquareBChecks.LT48B.disj_of_maskL cfgB.cleanScratch (ParkCopy.hosts E0) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDB := StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst cfgB.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDS := StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst cfgB.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hBO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSrO := StairSquareBChecks.LT48B.disj_of_maskL cfgB.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2⟩

private theorem cfgC_geom :
    124 + (ParkCopyS.hostsS E0).length = cfgC.n ∧
    cfgC.src.length = cfgC.n ∧
    (ParkCopyS.hostsS E0).Nodup ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
    (∀ h ∈ ParkCopyS.hostsS E0, h ∉ cfgC.bank ∧ h ∉ cfgC.src ∧ h ∉ cfgC.dst ∧
      h ∉ K0.core.out ∧ h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
    G0 ∉ ParkCopyS.hostsS E0 ∧
    (G0 :: cfgC.src ++ cfgC.bank).Nodup ∧
    (∀ q ∈ E0, q ∉ cfgC.bank) ∧
    (∀ q ∈ cfgC.workT, q ∈ K0.core.work) ∧
    (∀ q ∈ cfgC.liveT, (q ∈ E0 ∨ q ∈ cfgC.workT) ∧ q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.cleanScratch, (q ∈ K0.foldPad ∨ q ∈ K0.core.work) ∧ q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧
      q ∉ K0.core.out ∧ q ∉ ParkCopyS.hostsS E0) ∧
    (∀ q ∈ cfgC.dst, q ∉ cfgC.bank ∧ q ∉ cfgC.src ∧ q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.bank, q ∉ K0.core.out) ∧
    (∀ q ∈ cfgC.src, q ∉ K0.core.out) ∧
    (G0 ∉ cfgC.bank ∧ G0 ∉ cfgC.dst ∧ G0 ∉ cfgC.liveT ∧ G0 ∉ cfgC.cleanScratch ∧ G0 ∉ K0.core.out) ∧
    LowZero18Square.cacheWire K0 cfgC.dst = cfgC.dst.headD 0 ∧
    ControlLoan1589BFFold.eU K0 ∉ ParkCopyS.hostsS E0 := by
  have hS : 124 + (ParkCopyS.hostsS E0).length = cfgC.n ∧
      cfgC.src.length = cfgC.n ∧ (ParkCopyS.hostsS E0).Nodup ∧
      (∀ h ∈ ParkCopyS.hostsS E0, h ∈ E0 ∨ h = ControlLoan1589BFFold.eU K0) ∧
      (∀ h ∈ ParkCopyS.hostsS E0, h ≠ 4834 ∧ h ≠ 5093 ∧ h ≠ 4875 ∧ h ≠ 5478) ∧
      G0 ∉ ParkCopyS.hostsS E0 ∧
      (G0 ∉ cfgC.bank ∧ G0 ∉ cfgC.dst ∧ G0 ∉ cfgC.liveT ∧ G0 ∉ cfgC.cleanScratch ∧ G0 ∉ K0.core.out) ∧
      LowZero18Square.cacheWire K0 cfgC.dst = cfgC.dst.headD 0 ∧
      ControlLoan1589BFFold.eU K0 ∉ ParkCopyS.hostsS E0 := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  have hnd : (G0 :: cfgC.src ++ cfgC.bank).Nodup :=
    PeakNodup.nodup_of_mask _ (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPB := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPS := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPD := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) cfgC.dst (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hPO := StairSquareBChecks.LT48B.disj_of_maskL (ParkCopyS.hostsS E0) K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hEB := StairSquareBChecks.LT48B.disj_of_maskL E0 cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hWW := StairSquareBChecks.LT48B.sub_of_maskL cfgC.workT K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLU := mask_union_mem cfgC.liveT E0 cfgC.workT (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLB := StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLS := StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hLO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.liveT K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSU := mask_union_mem cfgC.cleanScratch K0.foldPad K0.core.work (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSB := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSS := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSP := StairSquareBChecks.LT48B.disj_of_maskL cfgC.cleanScratch (ParkCopyS.hostsS E0) (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDB := StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst cfgC.bank (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDS := StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst cfgC.src (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hDO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.dst K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hBO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.bank K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  have hSrO := StairSquareBChecks.LT48B.disj_of_maskL cfgC.src K0.core.out (by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel)
  exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1,
    fun h hh => ⟨hPB h hh, hPS h hh, hPD h hh, hPO h hh, hS.2.2.2.2.1 h hh⟩,
    hS.2.2.2.2.2.1, hnd, hEB, hWW,
    fun q hq => ⟨hLU q hq, hLB q hq, hLS q hq, hLO q hq⟩,
    fun q hq => ⟨hSU q hq, hSB q hq, hSS q hq, hSO q hq, hSP q hq⟩,
    fun q hq => ⟨hDB q hq, hDS q hq, hDO q hq⟩, hBO, hSrO,
    hS.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2⟩

private theorem e0_dis_bodyA : ∀ q ∈ E0, q ∉ wires bodyA := fun q hq hw => by
  have hs := bodyA_ok.support hw
  rcases Finset.mem_insert.mp hs with rfl | hmem
  · exact (by rw [E0_eq, D0_eq]; decide +kernel : D0 ∉ E0) hq
  · exact hext.away q hq (List.mem_toFinset.mp hmem)

private theorem e0_dis_bodyB : ∀ q ∈ E0, q ∉ wires bodyB := fun q hq hw =>
  hext.away q hq (List.mem_toFinset.mp (bodyB_ok.support hw))

private theorem e0_dis_bodyC : ∀ q ∈ E0, q ∉ wires bodyC := fun q hq hw => by
  have hs := bodyC_ok.support hw
  rcases Finset.mem_insert.mp hs with rfl | hmem
  · exact (by rw [E0_eq, D0_eq]; decide +kernel : D0 ∉ E0) hq
  · exact hext.away q hq (List.mem_toFinset.mp hmem)

private theorem eU_zero_of_prod0 (b : BasisState) (hp0 : regValue K0.core.product b = 0) :
    b (ControlLoan1589BFFold.eU K0) = false := by
  have hm : ControlLoan1589BFFold.eU K0 ∈ K0.core.product := by simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  exact (regValue_zero _ _).mp hp0 _ hm

private theorem prod_eq_of_take256 (b : BasisState) (hp256 : b (K0.core.product.getD 256 0) = false)
    (hp257 : b (K0.core.product.getD 257 0) = false) :
    regValue K0.core.product b = regValue (K0.core.product.take 256) b := by
  have hl : K0.core.product.length = 258 := hwK.core.product
  have hdrop : K0.core.product.drop 256 = [K0.core.product.getD 256 0, K0.core.product.getD 257 0] := by
    apply List.ext_getElem (by simp [hl])
    intro i hi1 hi2
    have hi : i = 0 ∨ i = 1 := by simp [hl] at hi1; omega
    rcases hi with rfl | rfl <;> simp [List.getD_eq_getElem?_getD, hl]
  have h0 : regValue [K0.core.product.getD 256 0, K0.core.product.getD 257 0] b = 0 := by
    simp only [regValue, List.foldr_cons, List.foldr_nil, hp256, hp257]; rfl
  conv_lhs => rw [← List.take_append_drop 256 K0.core.product, regValue_append, hdrop, h0]
  simp

theorem brA_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brA m t = run (recBrA bodyA) m t := by
  have g := cfgA_geom
  have h128 : regValue K0.core.low t.basis < 2 ^ 128 := by
    simpa [K0.core.low_length hwK.core] using regValue_lt K0.core.low t.basis
  let M := if t.basis G0 then regValue K0.core.low t.basis else 0
  let O := regValue K0.core.out t.basis
  let V := A161Low4Offsets.resAFlow (M ^ 2) O (t.basis G0)
  have hMlt : M < 2 ^ 128 := by dsimp only [M]; split_ifs <;> omega
  have hRec := A161Low4Branch.swapped_correct K0 hwK E0 G0 controlND
    (regValue K0.core.low t.basis) O pre.outLt t m rfl rfl pre.prod0 pre.clean pre.sum0 hext pre.ext0
    D0 (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (B3CarryPort.pool1540_facts L0 hw0 hn0).2.1 pre.d0
    bodyA bodyA_ok.support bodyA_ok.eUfree bodyA_ok.frame
  have hNew := withSplitPark_correct cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyA bodyA_avoids_workTA (fun _ => bodyA_ok.eUfree)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun s0 m0 hd0 hT0 hSc0 hi0 heu0 he0 =>
      cfg128_zeros cfgA cfgA_valid rfl g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        (by simp [SplitCfg.T, cfgA, List.take_take]) rfl rfl _
        (fun h hh => by simp only [ParkCopy10.hosts10, List.mem_append, List.mem_singleton] at hh; exact hh)
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2⟩
        s0 m0 hd0 hT0 hSc0 hi0 heu0 he0)
    t m pre.clean
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp pre.prod0 q (List.mem_of_mem_take hq)))
    pre.ext0 pre.d0 (fun _ => eU_zero_of_prod0 t.basis pre.prod0)
    (fun t' m' hdst hkeep => by
      have h256_dis : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
          K0.core.cin, K0.core.normFlag, K0.core.modFlag, K0.core.product.getD 256 0, K0.core.product.getD 257 0,
          K0.core.sumCarry, D0, G0], q ∉ cfgA.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgA_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have h256_in : K0.core.product.getD 256 0 ∈ K0.core.product ∧ K0.core.product.getD 257 0 ∈ K0.core.product :=
        ⟨DiagSq.getD_in _ 256 (by rw [hwK.core.product]; decide), DiagSq.getD_in _ 257 (by rw [hwK.core.product]; decide)⟩
      have hprod : regValue K0.core.product t'.basis = M ^ 2 := by
        rw [prod_eq_of_take256 t'.basis
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.1))
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.2))]
        exact hdst
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.work,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.productHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.outHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.workHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.cin,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.normFlag,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := hkeep G0 (h256_dis _ (by simp))
      have hout : regValue K0.core.out t'.basis = O :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))
      have hfr := bodyA_ok.frame t'.basis M hMlt hprod hpc ((hkeep _ (h256_dis _ (by simp))).trans pre.sum0) O pre.outLt
        (fun hg => by rw [hG] at hg; simp [M, hg]) ((hkeep _ (h256_dis _ (by simp))).trans pre.d0)
        t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, O, recBrA, A161Low4Branch.branch] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

theorem brB_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brB m t = run (recBrB bodyB) m t := by
  have g := cfgB_geom
  have h128 : regValue K0.core.high t.basis < 2 ^ 128 := by
    simpa [K0.core.high_length hwK.core] using regValue_lt K0.core.high t.basis
  let M := if t.basis G0 then regValue K0.core.high t.basis else 0
  let O := regValue K0.core.out t.basis
  let V := ControlLoan1589BFFold.resBF (M ^ 2) O (t.basis G0)
  have hMlt : M < 2 ^ 128 := by dsimp only [M]; split_ifs <;> omega
  have hRec := StairSquareAssembly.recBrB_correct bodyB bodyB_ok (regValue K0.core.high t.basis) O
    pre.outLt t m rfl rfl pre.prod0 pre.clean pre.sum0 pre.ext0
  have hNew := withSplitPark_correct cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.1 e0_dis_bodyB bodyB_avoids_workTB
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (fun s0 m0 hd0 hT0 hSc0 hi0 heu0 he0 =>
      cfg128_zeros cfgB cfgB_valid rfl g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        (by simp [SplitCfg.T, cfgB, List.take_take]) rfl rfl _ (fun _ hh => Or.inl hh)
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1⟩
        ⟨g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1, g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1⟩
        s0 m0 hd0 hT0 hSc0 hi0 heu0 he0)
    t m pre.clean
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp pre.prod0 q (List.mem_of_mem_take hq)))
    pre.ext0 pre.d0 (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2)
    (fun t' m' hdst hkeep => by
      have h256_dis : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
          K0.core.cin, K0.core.normFlag, K0.core.modFlag, K0.core.product.getD 256 0, K0.core.product.getD 257 0,
          K0.core.sumCarry, G0], q ∉ cfgB.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgB_fast, K0_eq, G0_eq]; decide +kernel)
      have h256_in : K0.core.product.getD 256 0 ∈ K0.core.product ∧ K0.core.product.getD 257 0 ∈ K0.core.product :=
        ⟨DiagSq.getD_in _ 256 (by rw [hwK.core.product]; decide), DiagSq.getD_in _ 257 (by rw [hwK.core.product]; decide)⟩
      have hprod : regValue K0.core.product t'.basis = M ^ 2 := by
        rw [prod_eq_of_take256 t'.basis
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.1))
          ((hkeep _ (h256_dis _ (by simp))).trans ((regValue_zero _ _).mp pre.prod0 _ h256_in.2))]
        exact hdst
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (h256_dis q (by simp [hq])))).trans pre.clean.work,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.productHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.outHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.workHigh,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.cin,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.normFlag,
        (hkeep _ (h256_dis _ (by simp))).trans pre.clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := hkeep G0 (h256_dis _ (by simp))
      have hout : regValue K0.core.out t'.basis = O :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))
      have hhi : regValue K0.core.high t'.basis = regValue K0.core.high t.basis :=
        regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.1 hq))
      have hg0 : t'.basis G0 = false → M = 0 := fun hg => by rw [hG] at hg; simp [M, hg]
      have hfr := bodyB_ok.frame t'.basis M hMlt hprod hpc ((hkeep _ (h256_dis _ (by simp))).trans pre.sum0) O pre.outLt
        hg0 (by rw [hG, hhi]) t' m' ⟨hout, fun _ _ => rfl⟩
      rw [ControlLoan1589BFFold.bO4_eq M O (t'.basis G0) hMlt hg0 pre.outLt, hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, O] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

theorem brC_run_eq (t : State) (m : List Bool) (pre : BranchPre t) :
    run brC m t = run (recBrC bodyC) m t := by
  have g := cfgC_geom
  have nd := (List.nodup_cons.mp controlND).2
  have dis := K0.measured_sum_disjoint nd
  have ctrlAway : G0 ∉ K0.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp controlND G0
    have pos := List.count_pos_iff.mpr bad
    have sumBound := K0.measured_sum_count G0
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, List.count_append, List.count_cons,
      List.count_nil, beq_self_eq_true, if_true] at h sumBound
    omega
  set A := regValue K0.core.low t.basis
  set B := regValue K0.core.sum t.basis
  set O := regValue K0.core.out t.basis
  have hLowLt : A < 2 ^ 128 := by
    simpa [A, K0.core.low_length hwK.core] using regValue_lt K0.core.low t.basis
  have hSumEq : B = regValue K0.core.high t.basis := by
    simp [B, CuccaroStreamedSquareLayout.sum, regValue_append, regValue, pre.sum0]
  have hHiLt : regValue K0.core.high t.basis < 2 ^ 128 := by
    simpa [K0.core.high_length hwK.core] using regValue_lt K0.core.high t.basis
  have hSumBd : A + B < 2 ^ 129 := by rw [hSumEq]; omega
  let midNew := withSplitPark cfgC 124 (ParkCopyS.hostsS E0) bodyC
  obtain ⟨r1, mC, eC⟩ := kseq (OwnDiagAll12Square.gPrep K0 ++ midNew) (OwnDiagAll12Square.gClear K0) m t
  obtain ⟨mP, mM, eM⟩ := kseq (OwnDiagAll12Square.gPrep K0) midNew r1 t
  have hbrC : run brC m t = run (OwnDiagAll12Square.gClear K0) mC (run midNew mM (run (OwnDiagAll12Square.gPrep K0) mP t)) := by
    change run ((OwnDiagAll12Square.gPrep K0 ++ midNew) ++ OwnDiagAll12Square.gClear K0) m t = _
    rw [eC, eM]
  have hprep := OwnDiagAll12Square.gPrep_frame K0 hwK nd t.basis A B rfl hSumBd
    (PairClean.corePad K0 t.basis pre.clean) pre.clean.cin pre.clean.work t mP ⟨rfl, fun _ _ => rfl⟩
  generalize hu : run (OwnDiagAll12Square.gPrep K0) mP t = u at hbrC hprep ⊢
  have u_prod0 : regValue K0.core.product u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans pre.prod0
  have u_out : regValue K0.core.out u.basis = O :=
    regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))
  have u_ctrl : u.basis G0 = t.basis G0 := hprep.2.2 G0 ctrlAway
  have u_clean : K0.PairClean u.basis := by
    have keep (q : Wire) (hq : q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh,
        K0.core.workHigh, K0.core.cin, K0.core.normFlag, K0.core.modFlag]) : u.basis q = t.basis q :=
      hprep.2.2 q (K0.measured_sum_aux_away nd q hq)
    exact ⟨(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.pad,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans pre.clean.work,
      (keep _ (by simp)).trans pre.clean.productHigh, (keep _ (by simp)).trans pre.clean.outHigh,
      (keep _ (by simp)).trans pre.clean.workHigh, (keep _ (by simp)).trans pre.clean.cin,
      (keep _ (by simp)).trans pre.clean.normFlag, (keep _ (by simp)).trans pre.clean.modFlag⟩
  have u_ext0 : regValue E0 u.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => hprep.2.2 q (fun bad => hext.away q hq (OwnDiagAll12Square.sum_in K0 G0 q bad)))).trans pre.ext0
  have u_d0 : u.basis D0 = false :=
    (hprep.2.2 D0 (fun bad => (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (OwnDiagAll12Square.sum_in K0 G0 D0 bad))).trans pre.d0
  let M := if t.basis G0 then A + B else 0
  let V := C163Low4Offsets.resCFlow (t.basis G0) (M ^ 2) O
  have hM_eq : (if u.basis G0 = true then regValue cfgC.src u.basis else 0) = M := by
    change (if u.basis G0 = true then regValue K0.core.sum u.basis else 0) = M
    rw [u_ctrl, hprep.2.1]
  have used := withSplitPark_correct cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC V
    g.1 (by decide) g.2.1 g.2.2.1 g.2.2.2.1
    (fun h hh => (g.2.2.2.2.1 h hh).1) (fun h hh => (g.2.2.2.2.1 h hh).2.1)
    (fun h hh => (g.2.2.2.2.1 h hh).2.2.1) (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.1)
    g.2.2.2.2.2.1 (fun h hh => (g.2.2.2.2.1 h hh).2.2.2.2) g.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.1
    (fun q hq => Or.inl (g.2.2.2.2.2.2.2.2.1 q hq)) e0_dis_bodyC bodyC_avoids_workTC
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2.2.2)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).1) (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.1)
    (fun q hq => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hq).2.2) g.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    cfgC_zeros u mM u_clean u_prod0 u_ext0 u_d0
    (fun hm => absurd hm g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (fun t' m' hdst hkeep => by
      have haux : ∀ q ∈ K0.foldPad ++ K0.core.work ++ [K0.core.productHigh, K0.core.outHigh, K0.core.workHigh,
            K0.core.cin, K0.core.normFlag, K0.core.modFlag, D0, G0], q ∉ cfgC.dst :=
        StairSquareBChecks.LT48B.disj_of_maskL _ _ (by rw [cfgC_fast, K0_eq, D0_eq, G0_eq]; decide +kernel)
      have hpc : K0.PairClean t'.basis := ⟨
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.pad,
        (regValue_congr _ _ _ (fun q hq => hkeep q (haux q (by simp [hq])))).trans u_clean.work,
        (hkeep _ (haux _ (by simp))).trans u_clean.productHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.outHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.workHigh,
        (hkeep _ (haux _ (by simp))).trans u_clean.cin,
        (hkeep _ (haux _ (by simp))).trans u_clean.normFlag,
        (hkeep _ (haux _ (by simp))).trans u_clean.modFlag⟩
      have hG : t'.basis G0 = t.basis G0 := (hkeep G0 (haux _ (by simp))).trans u_ctrl
      have hout : regValue K0.core.out t'.basis = O :=
        (regValue_congr _ _ _ (fun q hq => hkeep q (fun hd => (g.2.2.2.2.2.2.2.2.2.2.2.1 q hd).2.2 hq))).trans u_out
      have hdstM : regValue K0.core.product t'.basis = M ^ 2 := by rw [← hM_eq]; exact hdst
      have hfr := bodyC_ok.frame t'.basis M hdstM hpc (fun hg => by rw [hG] at hg; simp [M, hg])
        ((hkeep _ (haux _ (by simp))).trans u_d0) O pre.outLt t' m' ⟨hout, fun _ _ => rfl⟩
      rw [hG] at hfr
      exact ⟨hfr.1, hfr.2.1, hfr.2.2⟩)
  change (run midNew mM u).phase = u.phase ∧ regValue K0.core.out (run midNew mM u).basis = V ∧
    ∀ q, q ∉ K0.core.out → (run midNew mM u).basis q = u.basis q at used
  generalize hv : run midNew mM u = v at hbrC used ⊢
  let restoreBase : BasisState := fun q => if q ∈ K0.core.out then v.basis q else t.basis q
  have lowOutAway (q : Wire) (hq : q ∈ K0.core.low) : q ∉ K0.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires, List.count_append, List.count_cons, List.count_nil] at h
    omega
  have lowRestore : regValue K0.core.low restoreBase = A :=
    regValue_congr _ _ _ (fun q hq => by simp [restoreBase, lowOutAway q hq])
  have padRestore : regValue K0.core.pad restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad, hq])).2
      simp [restoreBase, away])).trans (PairClean.corePad K0 t.basis pre.clean)
  have cinRestore : restoreBase K0.core.cin = false := by
    have away := (K0.pairAuxAway nd K0.core.cin (by simp)).2
    simp [restoreBase, away, pre.clean.cin]
  have workRestore : regValue K0.core.work restoreBase = 0 :=
    (regValue_congr _ _ _ (fun q hq => by
      have away := (K0.pairAuxAway nd q (by simp [hq])).2
      simp [restoreBase, away])).trans pre.clean.work
  have clearPre : SquareFrame K0.core.sum restoreBase (A + B) v.basis := by
    refine ⟨(regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans hprep.2.1, ?_⟩
    intro q hq
    by_cases outSite : q ∈ K0.core.out
    · simp [restoreBase, outSite]
    · simp only [restoreBase, if_neg outSite]
      exact (used.2.2 q outSite).trans (hprep.2.2 q hq)
  have cleared := OwnDiagAll12Square.gClear_frame K0 hwK nd restoreBase A B lowRestore hSumBd padRestore cinRestore workRestore v mC clearPre
  generalize hout : run (OwnDiagAll12Square.gClear K0) mC v = out at hbrC cleared ⊢
  have hNew : out.phase = t.phase ∧ regValue K0.core.out out.basis = V ∧ ∀ q, q ∉ K0.core.out → out.basis q = t.basis q := by
    refine ⟨cleared.1.trans (used.1.trans hprep.1), ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => by
        have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
        simpa [restoreBase, hq] using same)).trans used.2.1
    · intro q hq
      by_cases sumSite : q ∈ K0.core.sum
      · exact (regValue_eq_iff K0.core.sum out.basis t.basis).mp cleared.2.1 q sumSite
      · have same := cleared.2.2 q sumSite
        simpa [restoreBase, hq] using same
  have hRec := SumSavedCBranch.branch_correct K0 hwK E0 G0 controlND A B O pre.outLt t m rfl rfl hSumBd rfl
    pre.prod0 pre.clean hext pre.ext0 D0 (B3CarryPort.pool1540_facts L0 hw0 hn0).1 (B3CarryPort.pool1540_facts L0 hw0 hn0).2.1
    pre.d0 bodyC bodyC_ok.support bodyC_ok.frame
  rw [hbrC]
  exact state_eq_of_out _ _ (hNew.1.trans hRec.1.symm)
    (by simpa [V, M, recBrC] using hNew.2.1.trans hRec.2.1.symm)
    (fun q hq => (hNew.2.2 q hq).trans (hRec.2.2 q hq).symm)

/-- Top-level core correctness of the split-65 concrete square core. -/
theorem coreOK : CoreOK L0 (coreN brC brB brA) :=
  coreN_coreOK bodyA bodyB bodyC brC brB brA bodyA_ok bodyB_ok bodyC_ok brC_run_eq brB_run_eq brA_run_eq

/-! ### Exact Toffoli, measurement, and gate-slot counts -/

theorem brA_counts :
    toffoliCount brA + 293 = toffoliCount (recBrA A109SignResearch.body) ∧
    measurementCount brA + 197 = measurementCount (recBrA A109SignResearch.body) := by
  have hk := cfg_counts_H cfgA cfgA_valid rfl K0.core.low (K0.core.product.take 256)
    (K0.core.low_length hwK.core) (by rw [List.length_take, hwK.core.product]; decide)
  have hb := bodyA_counts
  have hc := InnerLinearCopy.copy_counts118 G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.low.take 118) ((K0.inputBank.take K0.core.low.length).take 118)
    (by simp [K0.core.low_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.low_length hwK.core])
  have hbl : K0.core.low.length = 128 := K0.core.low_length hwK.core
  dsimp only at hk
  simp only [brA, withSplitPark, recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10,
    ParkCopy10.pA, ParkCopy10.pM, ParkCopy10.pE1, ParkCopy10.pD, ParkCopy10.pMI, ParkCopy10.pB,
    ParkCopy10.pC1, ParkCopy10.pMO, ParkCopy10.pCL, ParkCopy10.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgA, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hc ⊢
  exact ⟨by clear * - hk hb hc; omega, by clear * - hk hb hc; omega⟩

theorem brB_counts :
    toffoliCount brB + 283 = toffoliCount (recBrB B95PaddedResearch.body) ∧
    measurementCount brB + 197 = measurementCount (recBrB B95PaddedResearch.body) := by
  have hk := cfg_counts_H cfgB cfgB_valid rfl K0.core.high (K0.core.product.take 256)
    (K0.core.high_length hwK.core) (by rw [List.length_take, hwK.core.product]; decide)
  have hb := bodyB_counts
  have hc := InnerLinearCopy.copy_counts G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.high.take 119) ((K0.inputBank.take K0.core.high.length).take 119)
    (by simp [K0.core.high_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.high_length hwK.core])
  have hbl : K0.core.high.length = 128 := K0.core.high_length hwK.core
  dsimp only at hk
  simp only [brB, withSplitPark, recBrB, ParkCopy.withLowK2P,
    ParkCopy.pA, ParkCopy.pM, ParkCopy.pE1, ParkCopy.pD, ParkCopy.pMI, ParkCopy.pB,
    ParkCopy.pC1, ParkCopy.pMO, ParkCopy.pCL, ParkCopy.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgB, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hc ⊢
  exact ⟨by clear * - hk hb hc; omega, by clear * - hk hb hc; omega⟩

theorem brC_counts :
    toffoliCount brC + 289 = toffoliCount (recBrC C105SignResearch.body) ∧
    measurementCount brC + 195 = measurementCount (recBrC C105SignResearch.body) := by
  have hk := cfg_counts_S cfgC cfgC_valid rfl K0.core.sum K0.core.product
    (K0.core.sum_length hwK.core) hwK.core.product
  have hb := bodyC_counts
  have srcCount (q : Wire) : K0.core.sum.count q ≤ (K0.core.y ++ [K0.core.sumCarry]).count q := by
    have h1 := (List.take_sublist 128 (K0.core.y.drop 128)).count_le q
    have h2 := (List.drop_sublist 128 K0.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum, CuccaroStreamedSquareLayout.high, List.count_append] at h1 ⊢; omega
  have hall := LowZero18LowK.kg_nodup K0 G0 controlND E0 K0.core.sum K0.core.product srcCount (fun _ => le_rfl) hext.nodup hext.away
  have sp := LowZero18LowK.kg_spec K0 hwK E0 K0.core.sum K0.core.product
    (by rw [K0.core.sum_length hwK.core]; decide) (by rw [K0.core.sum_length hwK.core])
    (by rw [K0.core.sum_length hwK.core, hwK.core.product]) hext.len hall
  have hcl := SumSavedSquare.clear_counts K0 hwK E0 K0.core.sum K0.core.product hext.len (K0.core.sum_length hwK.core) sp hall
  have hbl : K0.core.sum.length = 129 := K0.core.sum_length hwK.core
  dsimp only at hk
  simp only [brC, withSplitPark, recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, SumSavedPark.pCL,
    ParkCopyS.pA, ParkCopyS.pM, ParkCopyS.pE1, ParkCopyS.pD, ParkCopyS.pMI, ParkCopyS.pB,
    ParkCopyS.pC1, ParkCopyS.pMO, ParkCopyS.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgC, hbl, toffoliCount_append, measurementCount_append,
    renameProgram_counts] at hk hcl ⊢
  exact ⟨by clear * - hk hb hcl; omega, by clear * - hk hb hcl; omega⟩

theorem square_counts (k : Fp) :
    toffoliCount (squareN brC brB brA k) + 865 = toffoliCount (A161Generic.squareEntry L0 k) ∧
    measurementCount (squareN brC brB brA k) + 589 = measurementCount (A161Generic.squareEntry L0 k) := by
  have cA := brA_counts; have cB := brB_counts; have cC := brC_counts
  have e1 : toffoliCount (StairSquareEntryR.entryRH (k - (C163Low4Offsets.delta : Fp))) =
        toffoliCount (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) ∧
      measurementCount (StairSquareEntryR.entryRH (k - (C163Low4Offsets.delta : Fp))) =
        measurementCount (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) :=
    StairSquareEntryR.entryRH_counts _
  rw [recordSquare_eq, SumSavedB95Square.program, StairSquareAssembly.fastCore_eq, StairSquareFinal.branchBF760_rec]
  simp only [squareN, placedN, coreN, SquareCarryLoan719BF.place,
    toffoliCount_append, measurementCount_append, renameProgram_counts]
  exact ⟨by clear * - cA cB cC e1; omega, by clear * - cA cB cC e1; omega⟩

theorem brA_slots_le :
    Challenge.gateSlots brA ≤ Challenge.gateSlots (recBrA A109SignResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgA cfgA_valid
  have hb := bodyA_slots
  have hc := InnerLinearCopy.copy_slots118 G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.low.take 118) ((K0.inputBank.take K0.core.low.length).take 118)
    (by simp [K0.core.low_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.low_length hwK.core])
  have hbl : K0.core.low.length = 128 := K0.core.low_length hwK.core
  simp only [brA, withSplitPark, recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10,
    ParkCopy10.pA, ParkCopy10.pM, ParkCopy10.pE1, ParkCopy10.pD, ParkCopy10.pMI, ParkCopy10.pB,
    ParkCopy10.pC1, ParkCopy10.pMO, ParkCopy10.pCL, ParkCopy10.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgA, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk hc ⊢
  clear * - hk hb hc; omega

theorem brB_slots_le :
    Challenge.gateSlots brB ≤ Challenge.gateSlots (recBrB B95PaddedResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgB cfgB_valid
  have hb := bodyB_slots
  have hc := InnerLinearCopy.copy_slots G0 (LowZero18Square.cacheWire K0 (K0.core.product.take 256))
    (E0.getD 198 0) (E0.getD 199 0) (E0.getD 233 0)
    (K0.core.high.take 119) ((K0.inputBank.take K0.core.high.length).take 119)
    (by simp [K0.core.high_length hwK.core]) (by simp [(K0.measured_bank_widths hwK).1, K0.core.high_length hwK.core])
  have hbl : K0.core.high.length = 128 := K0.core.high_length hwK.core
  simp only [brB, withSplitPark, recBrB, ParkCopy.withLowK2P,
    ParkCopy.pA, ParkCopy.pM, ParkCopy.pE1, ParkCopy.pD, ParkCopy.pMI, ParkCopy.pB,
    ParkCopy.pC1, ParkCopy.pMO, ParkCopy.pCL, ParkCopy.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgB, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk hc ⊢
  clear * - hk hb hc; omega

theorem brC_slots_le :
    Challenge.gateSlots brC ≤ Challenge.gateSlots (recBrC C105SignResearch.body) + 1830000 := by
  have hk := cfg_slots_bound cfgC cfgC_valid
  have hb := bodyC_slots
  have hbl : K0.core.sum.length = 129 := K0.core.sum_length hwK.core
  simp only [brC, withSplitPark, recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, SumSavedPark.pCL,
    ParkCopyS.pA, ParkCopyS.pM, ParkCopyS.pE1, ParkCopyS.pD, ParkCopyS.pMI, ParkCopyS.pB,
    ParkCopyS.pC1, ParkCopyS.pMO, ParkCopyS.pE, R2SqEp760.bodySwap,
    SplitCfg.bank, cfgC, hbl, Challenge.gateSlots_append, Baselines.rename_gateSlots] at hk ⊢
  clear * - hk hb; omega

theorem square_slots_le (k : Fp) :
    Challenge.gateSlots (squareN brC brB brA k) ≤ Challenge.gateSlots (A161Generic.squareEntry L0 k) + 5490000 := by
  have sA := brA_slots_le; have sB := brB_slots_le; have sC := brC_slots_le
  have e := squareN_slots brC brB brA k
  have r : Challenge.gateSlots (A161Generic.squareEntry L0 k) =
      Challenge.gateSlots (recBrC C105SignResearch.body) + Challenge.gateSlots (recBrB B95PaddedResearch.body) +
        Challenge.gateSlots (recBrA A109SignResearch.body) +
        Challenge.gateSlots (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) := by
    rw [recordSquare_eq, SumSavedB95Square.program, StairSquareAssembly.fastCore_eq, StairSquareFinal.branchBF760_rec]
    simp only [SquareCarryLoan719BF.place, Challenge.gateSlots_append, Baselines.rename_gateSlots]
  rw [e, r]; clear * - sA sB sC; omega

/-! ### Physicality, wire support, and hole avoidance -/

private theorem dummies_physical (hs : List Wire) : GatePhysical (ParkCopy.dummies hs) := by
  rw [GatePhysical]
  intro x hx
  simp only [ParkCopy.dummies, List.mem_map] at hx
  rcases hx with ⟨a, _, rfl⟩
  simp [RecordedQuantum.PhysicalInstr]

private theorem dummies_wires (hs : List Wire) : wires (ParkCopy.dummies hs) ⊆ hs.toFinset := by
  induction hs with
  | nil => simp [ParkCopy.dummies, wires]
  | cons a hs ih =>
    intro q hq
    rw [ParkCopy.dummies, List.map_cons, wires] at hq
    rcases Finset.mem_union.mp hq with h | h
    · simp [Instr.wires, ECDSAAdd.correctionWires] at h; simp [h]
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (ih h)))

private theorem move_physical (a b : List Wire) (hnd : (a ++ b).Nodup) :
    GatePhysical (ParkCopy.move a b) := by
  have hnd' : (b ++ a).Nodup := (List.perm_append_comm.nodup_iff).mp hnd
  simp only [ParkCopy.move, gatePhysical_append]
  exact ⟨copyRegister_physical none a b hnd (by simp), copyRegister_physical none b a hnd' (by simp)⟩

private theorem move_wires (a b : List Wire) : wires (ParkCopy.move a b) ⊆ (a ++ b).toFinset := by
  intro q hq
  simp only [ParkCopy.move, wires_append, Finset.mem_union] at hq
  rcases hq with h | h
  · have := copyRegister_wires_subset none a b h
    simpa [Option.toList_none] using this
  · have := copyRegister_wires_subset none b a h
    simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at this ⊢
    exact this.symm

private theorem withSplitPark_physical (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (hbody : GatePhysical body)
    (hkLen : keepBits + parkHosts.length = c.n) (hkPos : 0 < keepBits) (hsrcLen : c.src.length = c.n)
    (hParkNd : parkHosts.Nodup) (hParkDisBank : ∀ h ∈ parkHosts, h ∉ c.bank)
    (hSrcDis : (G0 :: c.src ++ c.bank).Nodup)
    (hCacheNotBank : LowZero18Square.cacheWire K0 c.dst ∉ c.bank) :
    GatePhysical (withSplitPark c keepBits parkHosts body) := by
  have hbankLen : c.bank.length = c.n := v.bankLen
  have hndSB : (c.src ++ c.bank).Nodup := (List.nodup_cons.mp hSrcDis).2
  have hG0B : ∀ x ∈ some G0, x ∉ c.bank := fun x hx => by
    cases Option.some.inj hx; exact fun hb => (List.nodup_cons.mp hSrcDis).1 (List.mem_append_right _ hb)
  have hndMask : (G0 :: c.src.take keepBits ++ c.bank.take keepBits).Nodup :=
    list_nodup_of_count_le hSrcDis (fun q => by
      have a := (List.take_sublist keepBits c.src).count_le q
      have b := (List.take_sublist keepBits c.bank).count_le q
      simp only [List.count_cons, List.count_append]; omega)
  have hndMP : (c.bank.drop keepBits ++ parkHosts).Nodup :=
    List.nodup_append.mpr ⟨((List.nodup_append.mp hndSB).2.1).sublist (List.drop_sublist _ _), hParkNd,
      fun q hq r hr heq => hParkDisBank r hr (heq ▸ List.mem_of_mem_drop hq)⟩
  have hndPM : (parkHosts ++ c.bank.drop keepBits).Nodup := (List.perm_append_comm.nodup_iff).mp hndMP
  have hcfg := cfg_physical c v
  have hHeadIn : (c.bank.take keepBits).headD 0 ∈ c.bank := by
    rw [ParkCopy.headD_take c.bank keepBits hkPos]
    have hpos : 0 < c.bank.length := by omega
    have h0 : c.bank.headD 0 = c.bank.getD 0 0 := by cases c.bank <;> simp
    rw [h0]; exact DiagSq.getD_in c.bank 0 hpos
  have hC1 : GatePhysical (CachedSquareCopy.copy G0 (LowZero18Square.cacheWire K0 c.dst)
      (c.src.take keepBits) (c.bank.take keepBits)) :=
    CachedSquareCopy.physical G0 (LowZero18Square.cacheWire K0 c.dst) (c.src.take keepBits) (c.bank.take keepBits)
      (fun heq => hCacheNotBank (heq ▸ hHeadIn))
      (copyRegister_physical (some G0) (c.src.take keepBits) (c.bank.take keepBits)
        (List.nodup_cons.mp hndMask).2 (fun x hx hb => hG0B x hx (List.mem_of_mem_take hb)))
  have hB : GatePhysical (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) :=
    gatePhysical_rename _ (LowZero18Square.foldPerm K0 E0).injective _
      (gatePhysical_rename _ (R2SqEp760.sqSwap K0 E0).injective _ hbody)
  simp only [withSplitPark, gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨copyRegister_physical (some G0) c.src c.bank hndSB hG0B,
    hcfg.1⟩, eraseMask_physical G0 _ _⟩,
    dummies_physical parkHosts⟩, move_physical _ _ hndMP⟩, hB⟩, hC1⟩,
    move_physical _ _ hndPM⟩, hcfg.2⟩, eraseMask_physical G0 c.src c.bank⟩

theorem brA_physical : GatePhysical brA :=
  withSplitPark_physical cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA bodyA_physical
    cfgA_geom.1 (by decide) cfgA_geom.2.1 cfgA_geom.2.2.1 (fun h hh => (cfgA_geom.2.2.2.2.1 h hh).1)
    cfgA_geom.2.2.2.2.2.2.1 (by simp only [cfgA_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)

theorem brB_physical : GatePhysical brB :=
  withSplitPark_physical cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB bodyB_physical
    cfgB_geom.1 (by decide) cfgB_geom.2.1 cfgB_geom.2.2.1 (fun h hh => (cfgB_geom.2.2.2.2.1 h hh).1)
    cfgB_geom.2.2.2.2.2.2.1 (by simp only [cfgB_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)

theorem brC_physical : GatePhysical brC := by
  have hr := StairSquareFinal.record_branches_physical.1
  simp only [recBrC, SumSavedCBranch.branch, gatePhysical_append] at hr
  simp only [brC, gatePhysical_append]
  exact ⟨⟨hr.1.1, withSplitPark_physical cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC bodyC_physical
    cfgC_geom.1 (by decide) cfgC_geom.2.1 cfgC_geom.2.2.1 (fun h hh => (cfgC_geom.2.2.2.2.1 h hh).1)
    cfgC_geom.2.2.2.2.2.2.1 (by simp only [cfgC_fast, SplitCfg.bank_fast, K0_eq]; decide +kernel)⟩, hr.2⟩

theorem square_physical (k : Fp) : GatePhysical (squareN brC brB brA k) :=
  squareN_physical brC brB brA k brC_physical brB_physical brA_physical

private theorem withSplitPark_support_aux (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program)
    (hSrcAllowed : ∀ q ∈ c.src, q ∈ allowedWires)
    (hParkAllowed : ∀ q ∈ parkHosts, q ∈ allowedWires)
    (hCacheAllowed : LowZero18Square.cacheWire K0 c.dst ∈ allowedWires) :
    wires (withSplitPark c keepBits parkHosts body) ⊆
      wires (renameProgram (LowZero18Square.foldPerm K0 E0) (R2SqEp760.bodySwap K0 E0 body)) ∪ allowedWires.toFinset := by
  have hG0A : G0 ∈ allowedWires :=
    sub_allowedWires [G0] (fun q hq => by simp [List.mem_singleton.mp hq])
      (fun q hq => by rw [List.mem_singleton.mp hq, G0_eq, hs_lit]; decide +kernel) G0 (by simp)
  have hReal : c.realAll.toFinset ⊆ allowedWires.toFinset := fun q hq =>
    List.mem_toFinset.mpr (v.realAllowed q (List.mem_toFinset.mp hq))
  have hBankA : ∀ q ∈ c.bank, q ∈ allowedWires := fun q hq => v.realAllowed q (by simp [SplitCfg.realAll, hq])
  have hcfg := cfg_support c v
  intro q hq
  simp only [withSplitPark, wires_append, Finset.mem_union] at hq
  rcases hq with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := copyRegister_wires_subset (some G0) c.src c.bank h
    simp only [Option.toList_some, List.singleton_append, List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q w
    · exact hBankA q w
  · exact Finset.mem_union_right _ (hReal (hcfg.1 h))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := eraseMask_wires_subset G0 (c.src.take keepBits) (c.bank.take keepBits) h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q (List.mem_of_mem_take w)
    · exact hBankA q (List.mem_of_mem_take w)
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (hParkAllowed q (List.mem_toFinset.mp (dummies_wires _ h))))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := move_wires (c.bank.drop keepBits) parkHosts h
    simp only [List.mem_toFinset, List.mem_append] at w
    rcases w with w | w
    · exact hBankA q (List.mem_of_mem_drop w)
    · exact hParkAllowed q w
  · exact Finset.mem_union_left _ h
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := CachedSquareCopy.wires_subset G0 (LowZero18Square.cacheWire K0 c.dst)
      (c.src.take keepBits) (c.bank.take keepBits) h
    rcases Finset.mem_union.mp w with wc | hc
    · have w2 := copyRegister_wires_subset (some G0) (c.src.take keepBits) (c.bank.take keepBits) wc
      simp only [Option.toList_some, List.singleton_append, List.cons_append, List.mem_toFinset, List.mem_cons, List.mem_append, List.not_mem_nil, false_or] at w2
      rcases w2 with rfl | w2 | w2
      · exact hG0A
      · exact hSrcAllowed q (List.mem_of_mem_take w2)
      · exact hBankA q (List.mem_of_mem_take w2)
    · rw [Finset.mem_singleton.mp hc]; exact hCacheAllowed
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := move_wires parkHosts (c.bank.drop keepBits) h
    simp only [List.mem_toFinset, List.mem_append] at w
    rcases w with w | w
    · exact hParkAllowed q w
    · exact hBankA q (List.mem_of_mem_drop w)
  · exact Finset.mem_union_right _ (hReal (hcfg.2 h))
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
    have w := eraseMask_wires_subset G0 c.src c.bank h
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at w
    rcases w with rfl | w | w
    · exact hG0A
    · exact hSrcAllowed q w
    · exact hBankA q w

private theorem rename_wires_pad (f : Wire → Wire) {P Q : Program} (L : List Wire)
    (h : wires P ⊆ wires Q ∪ L.toFinset)
    (hf : ∀ x ∈ L, f x = x) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) ∪ L.toFinset := by
  intro q hq
  rw [renameProgram_support, Finset.mem_image] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  rcases Finset.mem_union.mp (h hx) with hQ | hL
  · exact Finset.mem_union_left _ (by rw [renameProgram_support]; exact Finset.mem_image_of_mem f hQ)
  · rw [hf x (List.mem_toFinset.mp hL)]; exact Finset.mem_union_right _ hL

private theorem perm_fixes_allowed :
    (∀ x ∈ K0.core.pad.take 34, LowZero18Square.foldPerm K0 E0 x = x) ∧
    (∀ x ∈ K0.core.pad.take 34, R2SqEp760.sqSwap K0 E0 x = x) ∧
    (∀ q ∈ K0.core.pad.take 34, q ∈ allowedWires) ∧
    (∀ q ∈ cfgA.src, q ∈ allowedWires) ∧ (∀ q ∈ cfgB.src, q ∈ allowedWires) ∧ (∀ q ∈ cfgC.src, q ∈ allowedWires) ∧
    (∀ q ∈ ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0), q ∈ allowedWires) ∧
    (∀ q ∈ ParkCopy.hosts E0, q ∈ allowedWires) ∧ (∀ q ∈ ParkCopyS.hostsS E0, q ∈ allowedWires) ∧
    LowZero18Square.cacheWire K0 cfgA.dst ∈ allowedWires ∧
    LowZero18Square.cacheWire K0 cfgB.dst ∈ allowedWires ∧
    LowZero18Square.cacheWire K0 cfgC.dst ∈ allowedWires := by
  have h1 : ∀ x ∈ K0.core.pad.take 34, StairSquareSites.LT48K.swF 4834 5093 x = x := by
    rw [K0_eq]; decide +kernel
  have h2 : ∀ x ∈ K0.core.pad.take 34, StairSquareSites.LT48K.swF 4875 5478 x = x := by
    rw [K0_eq]; decide +kernel
  have hAll : ∀ q ∈ K0.core.pad.take 34 ++ cfgA.src ++ cfgB.src ++ cfgC.src ++
      ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0) ++ ParkCopy.hosts E0 ++ ParkCopyS.hostsS E0 ++
      [LowZero18Square.cacheWire K0 cfgA.dst, LowZero18Square.cacheWire K0 cfgB.dst,
        LowZero18Square.cacheWire K0 cfgC.dst], q ∈ allowedWires :=
    sub_allowedWires _
      (StairSquareBChecks.LT48B.sub_of_maskL _ _ (by
        simp only [cfgA_fast, cfgB_fast, cfgC_fast, K0_eq, E0_eq, G0_eq, D0_eq]; decide +kernel))
      (StairSquareBChecks.LT48B.disj_of_maskL _ _ (by
        simp only [cfgA_fast, cfgB_fast, cfgC_fast, K0_eq, E0_eq, hs_lit]; decide +kernel))
  refine ⟨fun x hx => by rw [StairSquareSites.LT48K.foldPerm_eq]; exact h1 x hx,
    fun x hx => by rw [StairSquareSites.LT48K.sqSwap_eq]; exact h2 x hx,
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]), fun q hq => hAll q (by simp [hq]),
    fun q hq => hAll q (by simp [hq]),
    hAll _ (by simp), hAll _ (by simp), hAll _ (by simp)⟩

theorem brA_support : wires brA ⊆ wires (recBrA bodyAPlain) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA
    pa.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.1
  have hbody : wires bodyA ⊆ wires bodyAPlain ∪ (K0.core.pad.take 34).toFinset := by
    intro q hq
    rcases Finset.mem_union.mp (bodyA_wires_plain hq) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_of_mem_take (by
        have : K0.core.pad.take 32 = (K0.core.pad.take 34).take 32 := by simp [List.take_take]
        rw [← this]; exact List.mem_toFinset.mp h)))
  have hB1 := rename_wires_pad (R2SqEp760.sqSwap K0 E0) (K0.core.pad.take 34) hbody pa.2.1
  have hB2 := rename_wires_pad (LowZero18Square.foldPerm K0 E0) (K0.core.pad.take 34) hB1 pa.1
  intro q hq
  rcases Finset.mem_union.mp (hbase hq) with h | h
  · rcases Finset.mem_union.mp (hB2 h) with hP | hA
    · refine Finset.mem_union_left _ ?_
      simp only [recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10, ParkCopy10.pB, R2SqEp760.bodySwap,
        wires_append, Finset.mem_union]
      left; left; left; left; right; exact hP
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (pa.2.2.1 q (List.mem_toFinset.mp hA)))
  · exact Finset.mem_union_right _ h

theorem brB_support : wires brB ⊆ wires (recBrB bodyB) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB
    pa.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.2.1
  intro q hq
  rcases Finset.mem_union.mp (hbase hq) with h | h
  · refine Finset.mem_union_left _ ?_
    simp only [recBrB, ParkCopy.withLowK2P, ParkCopy.pB, R2SqEp760.bodySwap, wires_append, Finset.mem_union]
    left; left; left; left; right; exact h
  · exact Finset.mem_union_right _ h

theorem brC_support : wires brC ⊆ wires (recBrC bodyCPlain) ∪ allowedWires.toFinset := by
  have pa := perm_fixes_allowed
  have hbase := withSplitPark_support_aux cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC
    pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.2.2.2.2
  have hB1 := rename_wires_pad (R2SqEp760.sqSwap K0 E0) (K0.core.pad.take 34) bodyC_wires_plain pa.2.1
  have hB2 := rename_wires_pad (LowZero18Square.foldPerm K0 E0) (K0.core.pad.take 34) hB1 pa.1
  intro q hq
  simp only [brC, wires_append, Finset.mem_union] at hq
  rcases hq with (h | h) | h
  · refine Finset.mem_union_left _ ?_
    simp only [recBrC, SumSavedCBranch.branch, wires_append, Finset.mem_union]; left; left; exact h
  · rcases Finset.mem_union.mp (hbase h) with hb | ha
    · rcases Finset.mem_union.mp (hB2 hb) with hP | hA
      · refine Finset.mem_union_left _ ?_
        simp only [recBrC, SumSavedCBranch.branch, SumSavedPark.withLowK2S, ParkCopyS.pB, R2SqEp760.bodySwap,
          wires_append, Finset.mem_union]
        left; right; left; left; left; left; right; exact hP
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr (pa.2.2.1 q (List.mem_toFinset.mp hA)))
    · exact Finset.mem_union_right _ ha
  · refine Finset.mem_union_left _ ?_
    simp only [recBrC, SumSavedCBranch.branch, wires_append, Finset.mem_union]; right; exact h

private theorem hs_not_allowed : ∀ q ∈ hs, q ∉ allowedWires := fun q hq ha => by
  rw [allowedWires, List.mem_filter] at ha
  have h := ha.2
  simp [hq] at h

private theorem hs_fix_perms : ∀ q ∈ hs, LowZero18Square.foldPerm K0 E0 q = q ∧ R2SqEp760.sqSwap K0 E0 q = q := by
  have h1 : ∀ q ∈ hs, StairSquareSites.LT48K.swF 4834 5093 q = q ∧ StairSquareSites.LT48K.swF 4875 5478 q = q := by rw [hs_lit]; decide +kernel
  intro q hq; rw [StairSquareSites.LT48K.foldPerm_eq, StairSquareSites.LT48K.sqSwap_eq]; exact h1 q hq

private theorem withSplitPark_avoids (c : SplitCfg) (v : CfgValid c) (keepBits : Nat) (parkHosts : List Wire)
    (body : Program) (hba : ∀ q ∈ hs, q ∉ wires body)
    (hSrcAllowed : ∀ q ∈ c.src, q ∈ allowedWires)
    (hParkAllowed : ∀ q ∈ parkHosts, q ∈ allowedWires)
    (hCacheAllowed : LowZero18Square.cacheWire K0 c.dst ∈ allowedWires) :
    ∀ q ∈ hs, q ∉ wires (withSplitPark c keepBits parkHosts body) := by
  have hsup := withSplitPark_support_aux c v keepBits parkHosts body hSrcAllowed hParkAllowed hCacheAllowed
  intro q hq hw
  rcases Finset.mem_union.mp (hsup hw) with hB | hA
  · rw [R2SqEp760.bodySwap, renameProgram_support, renameProgram_support, Finset.mem_image] at hB
    obtain ⟨y, hy, hyq⟩ := hB
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hfix := hs_fix_perms q hq
    have hx1 : R2SqEp760.sqSwap K0 E0 x = q := (LowZero18Square.foldPerm K0 E0).injective (hyq.trans hfix.1.symm)
    have hx2 : x = q := (R2SqEp760.sqSwap K0 E0).injective (hx1.trans hfix.2.symm)
    exact hba q hq (hx2 ▸ hx)
  · exact hs_not_allowed q hq (List.mem_toFinset.mp hA)

theorem brA_avoids : ∀ q ∈ hs, q ∉ wires brA :=
  withSplitPark_avoids cfgA cfgA_valid 118 (ParkCopy10.hosts10 E0 (ControlLoan1589BFFold.eU K0)) bodyA
    bodyA_avoids_hs perm_fixes_allowed.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.1

theorem brB_avoids : ∀ q ∈ hs, q ∉ wires brB :=
  withSplitPark_avoids cfgB cfgB_valid 119 (ParkCopy.hosts E0) bodyB
    bodyB_avoids_hs perm_fixes_allowed.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.2.1

theorem brC_avoids : ∀ q ∈ hs, q ∉ wires brC := by
  have hmid := withSplitPark_avoids cfgC cfgC_valid 124 (ParkCopyS.hostsS E0) bodyC
    bodyC_avoids_hs perm_fixes_allowed.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.1 perm_fixes_allowed.2.2.2.2.2.2.2.2.2.2.2
  have sl := OwnDiagAll12Square.sum_lengths K0 hwK
  have hgp := addInPlace_wires (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (by omega) (by omega)
  have hgc := subInPlace_wires (OwnDiagAll12Square.sumSrc K0) K0.core.sum (OwnDiagAll12Square.sumBank K0) K0.core.cin
    (by omega) (by omega)
  have hnot : ∀ q ∈ hs, q ∉ K0.core.cin :: ((OwnDiagAll12Square.sumSrc K0 ++ K0.core.sum) ++ OwnDiagAll12Square.sumBank K0) := by
    simp only [cfgA_fast, cfgB_fast, cfgC_fast, SplitCfg.bank_fast, SplitCfg.S_fast, SplitCfg.T_fast, SplitCfg.liveT_fast, SplitCfg.realAll_fast, SplitCfg.cleanScratch_fast, SplitCfg.R_fast, SplitCfg.R8_fast, SplitCfg.Q1_fast, SplitCfg.Q2_fast, SplitCfg.Q5_fast, workTA_lit, workTB_lit, workTC_lit, efSwapB_lit, K0_eq, E0_eq, G0_eq, D0_eq, allowedWires_eq, holesA_lit, hs_lit, hosts88_fast, hostsBSup_fast, hostsB95_fast, keepKB_fast, hsC_fast, hostsCFix_fast, hostsC105_fast, keepKC_fast]; decide +kernel
  intro q hq hw
  simp only [brC, wires_append, Finset.mem_union] at hw
  rcases hw with (h | h) | h
  · rw [OwnDiagAll12Square.gPrep, hgp, List.mem_toFinset] at h; exact hnot q hq h
  · exact hmid q hq h
  · rw [OwnDiagAll12Square.gClear, hgc, List.mem_toFinset] at h; exact hnot q hq h

end Branches

end ECDSAAdd.Entrant.SplitLeafSquare
end
