import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Submission.Entrant.CRT
import ECDSAAdd.Submission.Entrant.OddField
import ECDSAAdd.Framework.RecordedPaths
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Submission.Entrant.MainP1
import ECDSAAdd.Submission.Entrant.Mixed20D
import ECDSAAdd.Submission.Entrant.MainM

section

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts
open Arithmetic MappedCompressed Stair44Resources StairConcreteAssembly StairArchiveInactive
open StairArchiveRelease StairArchiveNativeCut StairArchiveTen StairArchiveGates
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount measurementCount StairGroups.packet
  StairArchiveInactive.packet fieldHook

/-- The smallest-rail sign relocated into the last B87 rest letter. -/
def signHost : Wire := base 510

def signPayload : List Wire := (List.range' 1 84).flatMap pkSitesOf

def prefixDataPorts : List Nat := [0, 1, 2, 3, 4, 6, 7, 8]
def prefixEncodedPorts : List Nat := prefixDataPorts.drop 1

def prefixExpand (n : Nat) : Nat :=
  prefixEncodedPorts.zipIdx.foldl
    (fun acc p => if n.testBit p.2 then acc + 2 ^ p.1 else acc) 0

def prefixParityValue (n : Nat) : Bool :=
  let d := MeasuredCodec5.bitRun FourScratchPrefix.invV (prefixExpand n)
  TraceParity5.parity (prefixDataPorts.map d.testBit)

def prefixLoanSites : List Wire :=
  [tagPort 86, tagPort 7, tagPort 8, tagPort 9, tagPort 10, tagPort 87,
    tagPort 11, tagPort 12, tagPort 13, tagPort 88, tagPort 89, tagPort 90]

def prefixLoanPort (i : Nat) : Wire := prefixLoanSites[i]?.getD i

def xorIntoSign (xs : List Wire) : Program := xs.map fun q => .CX q signHost

def prefixParity : Program :=
  renameProgram prefixLoanPort FourScratchPrefix.invV ++
    xorIntoSign (prefixDataPorts.map prefixLoanPort) ++
    renameProgram prefixLoanPort FourScratchPrefix.clearV

def signBracket : Program := prefixParity ++ xorIntoSign signPayload

def spk (d : Bool) (k : Nat) : Program :=
  renameProgram (Equiv.swap (base 720) signHost) (rpk d k)

def sfirst (j : Nat) (rev : Bool) := spk (!rev) (if rev then j + 1 else j)
def ssecond (j : Nat) (rev : Bool) := spk (!rev) (if rev then j else j + 1)

def sten (j : Nat) (rev : Bool) :=
  fieldHook j (enter rev) ++ (sfirst j rev ++ (fieldHook j (shift rev) ++
    (ssecond j rev ++ fieldHook j (leave rev))))


/-- Fully decoded packet `k`, hosted like `opk` with its half-window carry on the archive tag,
    for every packet of the field group. -/
def gpk (d : Bool) (k : Nat) : Program :=
  renameProgram rawSwap (StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (RouteA.Rolling1588.rawPacket d k)))

/-- The fully decoded packet with its carry on the relocated sign site. -/
def epk (d : Bool) (k : Nat) : Program :=
  renameProgram (Equiv.swap (base 720) signHost) (gpk d k)

/-- A native leg of fully decoded packets with the carry on the sign site. -/
def egroup (d : Bool) (j n : Nat) : Program := PacketSequence.program d (epk d) j n

theorem gpk_hosted (d : Bool) (k : Nat) :
    gpk d k=renameProgram (fun q => rawSwap (StairArchiveInactive.host (OB5.sig 511 q)))
      (RouteA.Rolling1588.rawPacket d k) := by
  rw [gpk,StairArchiveInactive.hosts_eq,renameProgram_comp,renameProgram_comp]
  rfl

section
attribute [local irreducible] wires renameProgram opk
theorem gpk_sub (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) :
    wires (gpk d k)⊆insert (base 720) (wires (opk d k)) := by
  rw [gpk_hosted d k,renameProgram_support]
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have sub := RouteA.Rolling1588.rawPacket_wires d k (by omega) hp
  rw [← oddPk_regular d k lo hi] at sub
  rcases Finset.mem_insert.mp sub with e|member
  · subst e
    apply Finset.mem_insert.mpr
    left
    simp only [host_760,rawSwap,Equiv.swap_apply_left]
  · apply Finset.mem_insert_of_mem
    have hw : StairArchiveInactive.host (OB5.sig 511 p)∈wires (opk d k) := by
      rw [opk_hosted,renameProgram_support]; exact Finset.mem_image_of_mem _ member
    have fix : rawSwap (StairArchiveInactive.host (OB5.sig 511 p))=StairArchiveInactive.host (OB5.sig 511 p) :=
      Equiv.swap_apply_of_ne_of_ne (fun e => opk_avoid760 d k lo hi (e ▸ hw))
        (fun e => opk_avoid720 d k lo hi (e ▸ hw))
    simpa only [fix] using hw

end

theorem gpk_measure (c : Cost) (d : Bool) (k : Nat) (h1 : 1≤k) (h2 : k≤84) :
    c.measure (gpk d k)+(c.measure Rolling1588.d3short+c.measure Rolling1588.e3short)=c.measure (opk d k) := by
  have raw := RouteA.Rolling1588.rawPacket_measure_regular c d k
  have o : c.measure (opk d k)=c.measure (oddPk d k) := by
    simp only [opk,StairArchiveInactive.hosts_eq,c.rename]
  rw [o,oddPk_regular d k h1 h2,c.rename]
  rw [gpk,c.rename,StairArchiveInactive.hosts_eq,c.rename,c.rename]
  omega

theorem epk_measure (c : Cost) (d : Bool) (k : Nat) (h1 : 1≤k) (h2 : k≤84) :
    c.measure (epk d k)+(c.measure Rolling1588.d3short+c.measure Rolling1588.e3short)=c.measure (opk d k) := by
  rw [epk,c.rename]
  exact gpk_measure c d k h1 h2

theorem egroup_measure (c : Cost) (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    c.measure (egroup d j n)+n*(c.measure Rolling1588.d3short+c.measure Rolling1588.e3short)=
      c.measure (ogroup d j n) := by
  unfold egroup ogroup
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,Nat.zero_mul,Nat.add_zero]
  | succ n ih =>
    have head := epk_measure c d j lo (by omega)
    have tail := ih (j+1) (by omega) (by omega)
    rw [Nat.succ_mul]
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true,c.append] <;> omega


def group84SignBody (d : Bool) : Program :=
  ordered d (sten 10 (!d)) (ordered d (rgroup d 12 1) (ordered d (sten 13 (!d)) (ordered d (rgroup d 15 1) (ordered d (sten 16 (!d)) (ordered d (rgroup d 18 1) (ordered d (sten 19 (!d)) (ordered d (rgroup d 21 1) (ordered d (sten 22 (!d)) (ordered d (rgroup d 24 1) (ordered d (sten 25 (!d)) (ordered d (rgroup d 27 1) (ordered d (sten 28 (!d)) (ordered d (rgroup d 30 1) (ordered d (sten 31 (!d)) (ordered d (rgroup d 33 2) (ordered d (sten 35 (!d)) (ordered d (rgroup d 37 2) (ordered d (sten 39 (!d)) (ordered d (rgroup d 41 2) (ordered d (sten 43 (!d)) (ordered d (rgroup d 45 2) (ordered d (sten 47 (!d)) (ordered d (rgroup d 49 2) (ordered d (sten 51 (!d)) (ordered d (rgroup d 53 2) (ordered d (sten 55 (!d)) (ordered d (rgroup d 57 2) (ordered d (sten 59 (!d)) (ordered d (rgroup d 61 2) (ordered d (sten 63 (!d)) (ordered d (rgroup d 65 2) (ordered d (sten 67 (!d)) (ordered d (rgroup d 69 1) (ordered d (sten 70 (!d)) (ordered d (rgroup d 72 1) (ordered d (sten 73 (!d)) (ordered d (rgroup d 75 1) (ordered d (sten 76 (!d)) (ordered d (rgroup d 78 1) (ordered d (sten 79 (!d)) (ordered d (rgroup d 81 1) (ordered d (sten 82 (!d)) ((rgroup d 84 1))))))))))))))))))))))))))))))))))))))))))))

def group84Sign (d : Bool) : Program :=
  signBracket ++ ordered d (egroup d 1 9)
    (packTag ++ renameProgram tagSwap (group84SignBody d) ++ unpackTag) ++ signBracket


namespace SignCounts

attribute [local irreducible] opk

theorem signBracket_t : toffoliCount signBracket = 13 := by decide +kernel
theorem signBracket_m : measurementCount signBracket = 11 := by decide +kernel
theorem signBracket_slots : Challenge.gateSlots signBracket = 1447 := by decide +kernel

theorem sten_measure (c : Stair44Resources.Cost) (d : Bool) (j : Nat)
    (lo : 10 ≤ j) (hi : j ≤ 83) :
    c.measure (sten j (!d)) +
        2 * (c.measure Rolling1588.d3short + c.measure Rolling1588.e3short) =
      c.measure (oten j (!d)) := by
  have a := rpk_measure c d j lo (by omega)
  have b := rpk_measure c d (j + 1) (by omega) (by omega)
  cases d <;>
    simp only [sten, oten, sfirst, ssecond, ofirst, osecond, spk, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, c.append, c.rename] <;> omega

theorem signBody_measure (c : Stair44Resources.Cost) (d : Bool) :
    c.measure (group84SignBody d) +
        44 * (c.measure Rolling1588.d3short + c.measure Rolling1588.e3short) =
      c.measure (group84Body d) := by
  have h10 := sten_measure c d 10 (by decide) (by decide)
  have h13 := sten_measure c d 13 (by decide) (by decide)
  have h16 := sten_measure c d 16 (by decide) (by decide)
  have h19 := sten_measure c d 19 (by decide) (by decide)
  have h22 := sten_measure c d 22 (by decide) (by decide)
  have h25 := sten_measure c d 25 (by decide) (by decide)
  have h28 := sten_measure c d 28 (by decide) (by decide)
  have h31 := sten_measure c d 31 (by decide) (by decide)
  have h35 := sten_measure c d 35 (by decide) (by decide)
  have h39 := sten_measure c d 39 (by decide) (by decide)
  have h43 := sten_measure c d 43 (by decide) (by decide)
  have h47 := sten_measure c d 47 (by decide) (by decide)
  have h51 := sten_measure c d 51 (by decide) (by decide)
  have h55 := sten_measure c d 55 (by decide) (by decide)
  have h59 := sten_measure c d 59 (by decide) (by decide)
  have h63 := sten_measure c d 63 (by decide) (by decide)
  have h67 := sten_measure c d 67 (by decide) (by decide)
  have h70 := sten_measure c d 70 (by decide) (by decide)
  have h73 := sten_measure c d 73 (by decide) (by decide)
  have h76 := sten_measure c d 76 (by decide) (by decide)
  have h79 := sten_measure c d 79 (by decide) (by decide)
  have h82 := sten_measure c d 82 (by decide) (by decide)
  simp only [group84SignBody, group84Body, ord]
  omega

theorem group_delta (d : Bool) :
    toffoliCount (group84Sign d) + 239 = toffoliCount (group84 d) ∧
    measurementCount (group84Sign d) + 31 = measurementCount (group84 d) ∧
    Challenge.gateSlots (group84Sign d) + 8925 = Challenge.gateSlots (group84 d) := by
  have et := egroup_measure Stair44Resources.tc d 1 9 (by decide) (by decide)
  have em := egroup_measure Stair44Resources.mc d 1 9 (by decide) (by decide)
  have es := egroup_measure Stair44Resources.slots d 1 9 (by decide) (by decide)
  change toffoliCount _ + 9 * (toffoliCount _ + toffoliCount _) = toffoliCount _ at et
  change measurementCount _ + 9 * (measurementCount _ + measurementCount _) = measurementCount _ at em
  change Challenge.gateSlots _ + 9 * (Challenge.gateSlots _ + Challenge.gateSlots _) =
    Challenge.gateSlots _ at es
  have ht := signBody_measure Stair44Resources.tc d
  have hm := signBody_measure Stair44Resources.mc d
  have hs := signBody_measure Stair44Resources.slots d
  have hc := RouteA.Rolling1588.codec_short_counts
  change toffoliCount _ + 44 * (toffoliCount _ + toffoliCount _) = toffoliCount _ at ht
  change measurementCount _ + 44 * (measurementCount _ + measurementCount _) = measurementCount _ at hm
  change Challenge.gateSlots _ + 44 * (Challenge.gateSlots _ + Challenge.gateSlots _) =
    Challenge.gateSlots _ at hs
  cases d <;> simp only [group84Sign, group84, ordered, Bool.false_eq_true, if_false, if_true,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append,
    Baselines.rename_gateSlots, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2,
    signBracket_t, signBracket_m, signBracket_slots] <;> omega

end SignCounts


end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts





section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [45,406); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 29 ++
    Shadow20.MergeCut.forward d ++ Rolling1588TickGap.forward d 421 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 421 tail ++
    Shadow20.MergeCut.reverse d ++ Rolling1588.reverse d 16 29) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

private theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (Shadow20.MergeCut.forward d)+f=c.measure (Rolling1588TickGap.forward d 45 376))
    (hr : c.measure (Shadow20.MergeCut.reverse d)+r=c.measure (Rolling1588.reverse d 45 376)) :
    c.measure (forward d tail)+f=c.measure (Stair44WalkRun.forward d (405+tail)) ∧
    c.measure (backward d tail)+r=c.measure (Stair44WalkRun.backward d (405+tail)) := by
  have a := StairRestSupport.forward_append d 29 16 (376+tail)
  have b := StairRestSupport.forward_append d 376 45 tail
  have x := StairRestSupport.reverse_append d 29 16 (376+tail)
  have y := StairRestSupport.reverse_append d 376 45 tail
  change Rolling1588TickGap.forward d 16 (29+(376+tail)) =
    Rolling1588TickGap.forward d 16 29 ++ Rolling1588TickGap.forward d 45 (376+tail) at a
  change Rolling1588.reverse d 16 (29+(376+tail)) =
    Rolling1588.reverse d 45 (376+tail) ++ Rolling1588.reverse d 16 29 at x
  rw [b] at a
  rw [y] at x
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,forward,backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

attribute [local irreducible] Shadow20.MergeCut.forward Shadow20.MergeCut.reverse Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 39828 else 39828)=
      toffoliCount (Stair44WalkRun.forward d (405+tail)) ∧
    toffoliCount (backward d tail)+(if d then 39979 else 39957)=
      toffoliCount (Stair44WalkRun.backward d (405+tail)) ∧
    measurementCount (forward d tail)+(if d then 17960 else 17938)=measurementCount (Stair44WalkRun.forward d (405+tail)) ∧
    measurementCount (backward d tail)+(if d then 17730 else 17708)=measurementCount (Stair44WalkRun.backward d (405+tail)) := by
  have sf := StockWindowCosts420.stock420from45 d
  have mcw := Shadow20.MergeCut.mixed_counts d
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at mcw ⊢
    have t := walk tc false tail 39828 39957 (subEq 39828 mcw.1 sf.1 (by omega)) (subEq 39957 mcw.2.1 sf.2.2.1 (by omega))
    have mv := walk mc false tail 17938 17708 (subEq 17938 mcw.2.2.1 sf.2.1 (by omega)) (subEq 17708 mcw.2.2.2 sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,mv⟩
  · simp only [↓reduceIte] at mcw ⊢
    have t := walk tc true tail 39828 39979 (subEq 39828 mcw.1 sf.1 (by omega)) (subEq 39979 mcw.2.1 sf.2.2.1 (by omega))
    have mv := walk mc true tail 17960 17730 (subEq 17960 mcw.2.2.1 sf.2.1 (by omega)) (subEq 17730 mcw.2.2.2 sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,mv⟩

/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 39828 else 39828)=f) (hr : (if d then 39979 else 39957)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+(if d then 17960 else 17938)=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+(if d then 17730 else 17708)=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact exactWalks d tail

theorem instMeasurements (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 17960 else 17938)=f) (hr : (if d then 17730 else 17708)=r) :
    mc.measure (forward d tail)+f=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+r=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact ⟨(exactWalks d tail).2.2.1, (exactWalks d tail).2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowWalkCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

def entryTailPrefix (p : StairSchedule.StairPrimitives)
     : Program :=
  WindowFieldCosts.group84Sign true ++
    StairSchedule.forwardSegment p 87 62 425 450 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 5 ++
    StairSchedule.forwardSegment p 62 47 450 465 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 3 ++
    StairSchedule.forwardSegment p 47 32 465 480 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 3 ++
    StairSchedule.forwardSegment p 32 22 480 490 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 2 ++
    StairSchedule.forwardSegment p 22 12 490 500 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 2 ++ StairSchedule.forwardLast p

def exitHeadSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.reverseLast p ++
    PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1 ++
    PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1 ++
    PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2 ++
    PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2 ++
    PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4 ++
    WindowFieldCosts.group84Sign false

/-- Odd-word half-cell on `base 760` used for cells 2, 3, 4 of `placedFirstPacketOdd`. -/
def oddFirstHalf (divide : Bool) : Program :=
  P1Life.half (base 760) divide base (base 2409)

theorem oddFirstHalf_physical (divide : Bool) : GatePhysical (oddFirstHalf divide) :=
  (P1Life.half_resources (base 760) divide base (base 2409)
    Rolling1588Lifetime.half_ports_nodup RouteA.Rolling1588.route_retired_member).1

theorem oddFirstHalf_support (divide : Bool) :
    JointOdd1588.OddHalfSupport (oddFirstHalf divide) := by
  intro q hq
  have hsub := (P1Life.half_resources (base 760) divide base (base 2409)
    Rolling1588Lifetime.half_ports_nodup RouteA.Rolling1588.route_retired_member).2 hq
  have hne := (Finset.mem_erase.mp hsub).1
  have hmem := Finset.mem_of_mem_erase hsub
  rw [P1Life.junction_footprint_ports, List.mem_toFinset] at hmem
  have hindices : q ∈ (2409 :: 768 :: 1797 :: 1027 ::
      (List.range' 2056 256 ++ List.range' 770 256 ++ (List.range' 512 253 ++ [1540]))).map base := by
    simpa only [List.map_cons, List.map_append, List.map_nil, wireBlock] using hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hindices
  have h760 : i ≠ 760 := fun e => hne (congrArg base e)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hi
  have inside : i = 2409 ∨ i ∈ Q6EndpointCell.ids := by
    simp only [Q6EndpointCell.ids, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
    omega
  refine ⟨?_, ?_⟩
  · rw [StairFirstPacketKernel.LT48T.env]
    rcases inside with rfl | hi
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro hit
    simp only [StairFirstPacketKernel.LT48T.bad, List.mem_cons, List.not_mem_nil, or_false,
      base_injective.eq_iff] at hit
    omega

theorem oddFirstHalf_slots_le (divide : Bool) :
    Challenge.gateSlots (oddFirstHalf divide) ≤ Challenge.gateSlots (R2Life760.half760 divide) := by
  have h1 := RouteA.slot_half (base 760) divide base (base 2409)
  have h2 := RouteA.slot_record_half divide
  cases divide <;> simp only [oddFirstHalf, Bool.false_eq_true, if_false, if_true] at h1 h2 ⊢ <;> omega

theorem fpSup_bounds (w : Wire) (h : StairWireCheck.fpSup w = true) :
    (16 ≤ w ∧ w < 2330) ∨ w = 2425 := by
  unfold StairWireCheck.fpSup at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Wire] at *
  omega

private theorem rebindMany_slots_eq (roles hosts : List Wire) (P : Program) :
    Challenge.gateSlots (StairLoan.rebindMany roles hosts P) = Challenge.gateSlots P := by
  induction roles generalizing hosts with
  | nil => rfl
  | cons r roles ih =>
    cases hosts with
    | nil => rfl
    | cons h hosts => simp only [StairLoan.rebindMany, Baselines.rename_gateSlots, ih]

def entryLowPrefix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
      (JointOdd1588.placedFirstPacketOdd oddFirstHalf true) ++
    FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (entryTailPrefix p) ++
    FourScratchWindow.unprefix

def exitLowSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (exitHeadSuffix p) ++
    FourScratchWindow.unprefix ++
    StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
      (JointOdd1588.placedFirstPacketOdd oddFirstHalf false)

def entryFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.fieldRename (entryLowPrefix p) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowSuffix p)

/-- The division field's tail prefix with the five packet-cut odd rows. -/
def entryTailPrefixCut : Program :=
  WindowFieldCosts.group84Sign true ++
    (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4 ++
    (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2 ++
    (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2 ++
    (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1 ++
    (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1 ++ StairSchedule.forwardLast checkpointPrimitives)))))

def entryLowPrefixCut : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
      (JointOdd1588.placedFirstPacketOdd oddFirstHalf true) ++
    FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow entryTailPrefixCut ++
    FourScratchWindow.unprefix

def entryFieldHostedCut : Program :=
  StairSchedule.fieldRename entryLowPrefixCut ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

theorem field_delta_tc_div (n : Nat)
    (h : tc.measure (WindowFieldCosts.group84Sign true)=tc.measure (WindowFieldCosts.group true 1 84)+n) :
    tc.measure (entryFieldHosted checkpointPrimitives)+616 =
      tc.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 13 85 5 (by decide) (by decide)).1
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 22 90 3 (by decide) (by decide)).1
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 30 93 3 (by decide) (by decide)).1
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 36 96 2 (by decide) (by decide)).1
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 41 98 2 (by decide) (by decide)).1
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 43 100 2 (by decide) (by decide)).1
  have hc := OddFullPass.HalfConvertOdd.canon760OddLoan_counts.1
  have hcn := StairBoundaryLoan.canon760Loan_counts.1
  have hcb : toffoliCount R2SqEp760.canon760 = 254 := by
    rw [StairBoundaryLoan.canon760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).2.2.1
  have hde := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_counts.1
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf true
    (P1Life.half_counts (base 760) true base (base 2409)).1
    (P1Life.half_counts (base 760) true base (base 2409)).2).1
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf true)).1
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (Rolling1588.placedFirstPacket true)).1
  rw [show tc.measure=toffoliCount from rfl] at h ⊢
  simp only [if_true,WindowFieldCosts.group,entryFieldHosted,entryLowPrefix,entryTailPrefix,
    OddFullPass.P1LifeLoan.entryLowSuffixOdd,OddFullPass.P1LifeLoan.entryTailSuffixOdd,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.entryLowPrefix,
    StairHostsSchedule.entryTailPrefix,StairHostsSchedule.entryLowSuffix,
    StairHostsSchedule.entryTailSuffix,StairConcrete.bestLoans_divEndpoint,
    StairConcrete.bestLoans,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,toffoliCount_append] at *
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_tc_mul (n : Nat)
    (h : tc.measure (WindowFieldCosts.group84Sign false)=tc.measure (WindowFieldCosts.group false 1 84)+n) :
    tc.measure (exitFieldHosted checkpointPrimitives)+729 =
      tc.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 13 85 5 (by decide) (by decide)).1
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 22 90 3 (by decide) (by decide)).1
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 30 93 3 (by decide) (by decide)).1
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 36 96 2 (by decide) (by decide)).1
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 41 98 2 (by decide) (by decide)).1
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 43 100 2 (by decide) (by decide)).1
  have hct := OddFullPass.HalfConvertOdd.center760OddLoan_counts.1
  have hctn := StairBoundaryLoan.center760Loan_counts.1
  have hctb : toffoliCount R2SqEp760.center760 = 254 := by
    rw [StairBoundaryLoan.center760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).1
  have hme := OddFullPass.InverseTailCOdd.endPacket760OddLoan44_counts.1
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf false
    (P1Life.half_counts (base 760) false base (base 2409)).1
    (P1Life.half_counts (base 760) false base (base 2409)).2).1
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf false)).1
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (Rolling1588.placedFirstPacket false)).1
  have cr0 := PackCutOddExit.cutRow0_counts.1
  have cr1 := PackCutOddExit.cutRow1_counts.1
  have cr2 := PackCutOddExit.cutRow2_counts.1
  have cr3 := PackCutOddExit.cutRow3_counts.1
  have cr4 := PackCutOddExit.cutRow4_counts.1
  rw [show tc.measure=toffoliCount from rfl] at h ⊢
  simp only [WindowFieldCosts.group,exitFieldHosted,exitLowSuffix,exitHeadSuffix,
    OddFullPass.P1LifeLoan.exitLowPrefixOdd,OddFullPass.P1LifeLoan.exitHeadPrefixOdd,
    StairHostsSchedule.exitFieldHosted,StairHostsSchedule.exitLowSuffix,
    StairHostsSchedule.exitHeadSuffix,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.exitHeadPrefix,StairHostsSchedule.hostedEndpoint,
    StairSchedule.placedEndPacket,StairConcrete.bestLoans,StairConcrete.endPacket,
    Bool.false_eq_true,if_false,if_true,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,toffoliCount_append] at *
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_mc_div (n : Nat)
    (h : mc.measure (WindowFieldCosts.group84Sign true)=mc.measure (WindowFieldCosts.group true 1 84)+n) :
    mc.measure (entryFieldHosted checkpointPrimitives)+1381 =
      mc.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 13 85 5 (by decide) (by decide)).2
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 22 90 3 (by decide) (by decide)).2
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 30 93 3 (by decide) (by decide)).2
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 36 96 2 (by decide) (by decide)).2
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 41 98 2 (by decide) (by decide)).2
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 43 100 2 (by decide) (by decide)).2
  have hc := OddFullPass.HalfConvertOdd.canon760OddLoan_counts.2
  have hcn := StairBoundaryLoan.canon760Loan_counts.2
  have hcb : measurementCount R2SqEp760.canon760 = 254 := by
    rw [StairBoundaryLoan.canon760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).2.2.2
  have hde := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_counts.2
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf true
    (P1Life.half_counts (base 760) true base (base 2409)).1
    (P1Life.half_counts (base 760) true base (base 2409)).2).2
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf true)).2
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (Rolling1588.placedFirstPacket true)).2
  rw [show mc.measure=measurementCount from rfl] at h ⊢
  simp only [WindowFieldCosts.group,entryFieldHosted,entryLowPrefix,entryTailPrefix,
    OddFullPass.P1LifeLoan.entryLowSuffixOdd,OddFullPass.P1LifeLoan.entryTailSuffixOdd,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.entryLowPrefix,
    StairHostsSchedule.entryTailPrefix,StairHostsSchedule.entryLowSuffix,
    StairHostsSchedule.entryTailSuffix,StairConcrete.bestLoans_divEndpoint,
    StairConcrete.bestLoans,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,measurementCount_append] at *
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_mc_mul (n : Nat)
    (h : mc.measure (WindowFieldCosts.group84Sign false)=mc.measure (WindowFieldCosts.group false 1 84)+n) :
    mc.measure (exitFieldHosted checkpointPrimitives)+1707 =
      mc.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 13 85 5 (by decide) (by decide)).2
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 22 90 3 (by decide) (by decide)).2
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 30 93 3 (by decide) (by decide)).2
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 36 96 2 (by decide) (by decide)).2
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 41 98 2 (by decide) (by decide)).2
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 43 100 2 (by decide) (by decide)).2
  have hct := OddFullPass.HalfConvertOdd.center760OddLoan_counts.2
  have hctn := StairBoundaryLoan.center760Loan_counts.2
  have hctb : measurementCount R2SqEp760.center760 = 254 := by
    rw [StairBoundaryLoan.center760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).2.1
  have hme := OddFullPass.InverseTailCOdd.endPacket760OddLoan44_counts.2
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf false
    (P1Life.half_counts (base 760) false base (base 2409)).1
    (P1Life.half_counts (base 760) false base (base 2409)).2).2
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf false)).2
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (Rolling1588.placedFirstPacket false)).2
  have cr0 := PackCutOddExit.cutRow0_counts.2
  have cr1 := PackCutOddExit.cutRow1_counts.2
  have cr2 := PackCutOddExit.cutRow2_counts.2
  have cr3 := PackCutOddExit.cutRow3_counts.2
  have cr4 := PackCutOddExit.cutRow4_counts.2
  rw [show mc.measure=measurementCount from rfl] at h ⊢
  simp only [WindowFieldCosts.group,exitFieldHosted,exitLowSuffix,exitHeadSuffix,
    OddFullPass.P1LifeLoan.exitLowPrefixOdd,OddFullPass.P1LifeLoan.exitHeadPrefixOdd,
    StairHostsSchedule.exitFieldHosted,StairHostsSchedule.exitLowSuffix,
    StairHostsSchedule.exitHeadSuffix,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.exitHeadPrefix,StairHostsSchedule.hostedEndpoint,
    StairSchedule.placedEndPacket,StairConcrete.bestLoans,StairConcrete.endPacket,
    Bool.false_eq_true,if_false,if_true,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,measurementCount_append] at *
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_slots (d : Bool) (n : Nat)
    (h : slots.measure (WindowFieldCosts.group84Sign d)=slots.measure (WindowFieldCosts.group d 1 84)+n) :
    (if d then slots.measure (entryFieldHosted checkpointPrimitives)
     else slots.measure (exitFieldHosted checkpointPrimitives)) ≤
    (if d then slots.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
     else slots.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan))+n+
      (if d then 12660 else 12920) := by
  have g13 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 13 85 5 (by decide) (by decide)
  have g22 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 22 90 3 (by decide) (by decide)
  have g30 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 30 93 3 (by decide) (by decide)
  have g36 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 36 96 2 (by decide) (by decide)
  have g41 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 41 98 2 (by decide) (by decide)
  have g43 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 43 100 2 (by decide) (by decide)
  have hc := OddFullPass.HalfConvertOdd.canon760OddLoan_slots_le
  have hct := OddFullPass.HalfConvertOdd.center760OddLoan_slots_le
  have hde := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_slots_le
  have hme := OddFullPass.InverseTailCOdd.endPacket760OddLoan44_slots_le
  have hfp := JointOdd1588.placedFirstPacketOdd_slots_le oddFirstHalf d (oddFirstHalf_slots_le d)
  have hrNew := rebindMany_slots_eq StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf d)
  have hrOld := rebindMany_slots_eq StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (Rolling1588.placedFirstPacket d)
  have cs0 := PackCutOddExit.cutRow0_slots
  have cs1 := PackCutOddExit.cutRow1_slots
  have cs2 := PackCutOddExit.cutRow2_slots
  have cs3 := PackCutOddExit.cutRow3_slots
  have cs4 := PackCutOddExit.cutRow4_slots
  rw [show slots.measure=Challenge.gateSlots from rfl] at h ⊢
  cases d <;> simp only [Bool.false_eq_true,if_true,if_false,WindowFieldCosts.group,
    entryFieldHosted,exitFieldHosted,entryLowPrefix,exitLowSuffix,
    entryTailPrefix,exitHeadSuffix,OddFullPass.P1LifeLoan.entryLowSuffixOdd,
    OddFullPass.P1LifeLoan.exitLowPrefixOdd,OddFullPass.P1LifeLoan.entryTailSuffixOdd,
    OddFullPass.P1LifeLoan.exitHeadPrefixOdd,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.exitFieldHosted,
    StairHostsSchedule.entryLowPrefix,StairHostsSchedule.exitLowSuffix,
    StairHostsSchedule.entryTailPrefix,StairHostsSchedule.exitHeadSuffix,
    StairHostsSchedule.entryLowSuffix,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.entryTailSuffix,StairHostsSchedule.exitHeadPrefix,
    StairHostsSchedule.hostedEndpoint,StairSchedule.placedEndPacket,
    StairConcrete.bestLoans_divEndpoint,StairConcrete.bestLoans,StairConcrete.endPacket,
    StairSchedule.fieldRename,StairSchedule.parityRename,
    Baselines.rename_gateSlots,Challenge.gateSlots_append] at * <;> (norm_num only at g13 g22 g30 g36 g41 g43; omega)

open Stair44Outer

def divide : Program :=
  phasePlace (WindowWalkCosts.forward true 4) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace entryFieldHostedCut ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 85) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 84) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 4) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

def generic (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (EntryFuseOdd.entryYAllOdd layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (EntryFuseOdd.exitYAllOdd layout cy)

def borrowGeneric (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (generic cx cy))

def finite (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGeneric cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def program (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finite (.some hc) cx cy)

theorem tailPrefix_rows : entryTailPrefix checkpointPrimitives = WindowFieldCosts.group84Sign true ++
      ((StairSchedule.forwardSegment checkpointPrimitives 87 62 425 450 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 (4 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 62 47 450 465 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 (2 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 47 32 465 480 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 (2 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 32 22 480 490 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 (1 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 22 12 490 500 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 (1 + 1)) ++
        StairSchedule.forwardLast checkpointPrimitives))))) := by
  simp only [entryTailPrefix, List.append_assoc]

theorem tail_sublist : entryTailPrefixCut.Sublist (entryTailPrefix checkpointPrimitives) := by
  rw [tailPrefix_rows]
  unfold entryTailPrefixCut
  exact (List.Sublist.refl _).append ((PackCutOdd.row_subOdd 87 62 425 450 14 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp1_1542).append
    ((PackCutOdd.row_subOdd 62 47 450 465 23 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp2_1542).append
    ((PackCutOdd.row_subOdd 47 32 465 480 31 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp3_1542).append
    ((PackCutOdd.row_subOdd 32 22 480 490 37 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp4_1542).append
    ((PackCutOdd.row_subOdd 22 12 490 500 42 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp5_1542).append
    (List.Sublist.refl _))))))

theorem low_sublist : entryLowPrefixCut.Sublist (entryLowPrefix checkpointPrimitives) := by
  unfold entryLowPrefixCut entryLowPrefix
  exact ((List.Sublist.refl _).append (PackCutSub.rename_sub _ tail_sublist)).append (List.Sublist.refl _)

theorem field_sublist : entryFieldHostedCut.Sublist (entryFieldHosted checkpointPrimitives) := by
  have f : (StairSchedule.fieldRename entryLowPrefixCut).Sublist
      (StairSchedule.fieldRename (entryLowPrefix checkpointPrimitives)) :=
    PackCutSub.rename_sub _ (PackCutSub.rename_sub _ low_sublist)
  unfold entryFieldHostedCut entryFieldHosted
  exact ((((f.append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append
    (List.Sublist.refl _)).append (List.Sublist.refl _)

/-- One cut odd row costs the placed `ep` and `dp` less, for every additive renaming-invariant cost. -/
theorem rowOdd_cost (c : Cost) (B N s f d first cc : Nat)
    (h1 : s + 1 ≤ 5 * first + 5) (h2 : 5 * first + 5 + 1 ≤ f)
    (h5 : 5 * first + 5 ≠ 5) (hdue : History5.packDue (5 * first + 5) = true) (hf0 : first ≠ 0)
    (hdp : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
        (OddFullPass.P1LifeLoan.hostPlan1542.group true d first (cc + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) =
      renameProgram (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
        Rolling1588.dp) :
    c.measure (StairSchedule.forwardSegment checkpointPrimitives B N s f ++
        OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true d first (cc + 1)) =
      c.measure (PackCutOdd.cutRowOdd B N s f d first cc) + (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  obtain ⟨X, M, Y, ho, hc⟩ := PackCutOdd.row_shapeOdd B N s f d first cc h1 h2 h5 hdue hf0 hdp
  rw [ho, hc]
  simp only [c.append, c.rename]
  omega

theorem rows_cost (c : Cost) :
    c.measure (entryTailPrefix checkpointPrimitives) =
      c.measure entryTailPrefixCut + 5 * (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  have r1 := rowOdd_cost c 87 62 425 450 14 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp1_1542
  have r2 := rowOdd_cost c 62 47 450 465 23 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp2_1542
  have r3 := rowOdd_cost c 47 32 465 480 31 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp3_1542
  have r4 := rowOdd_cost c 32 22 480 490 37 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp4_1542
  have r5 := rowOdd_cost c 22 12 490 500 42 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp5_1542
  rw [tailPrefix_rows]
  simp only [entryTailPrefixCut, c.append] at r1 r2 r3 r4 r5 ⊢
  omega

theorem field_cut (c : Cost) :
    c.measure (entryFieldHosted checkpointPrimitives) =
      c.measure entryFieldHostedCut + 5 * (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  have hr := rows_cost c
  simp only [entryFieldHosted, entryFieldHostedCut, entryLowPrefix, entryLowPrefixCut,
    StairSchedule.fieldRename, StairSchedule.parityRename, c.rename, c.append]
  omega

theorem kernels (c : Cost) (gainF gainR tailSave fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 4)+gainF=c.measure (Stair44WalkRun.forward true 409))
    (dR : c.measure (WindowWalkCosts.backward false 85)+gainR=c.measure (Stair44WalkRun.backward false 490))
    (h : c.measure (entryFieldHosted checkpointPrimitives)+tailSave=
      c.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+fieldExtra) :
    c.measure divide+gainF+gainR+tailSave+5 * (c.measure Rolling1588.ep + c.measure Rolling1588.dp)=
      c.measure Stair44Outer.divide+fieldExtra := by
  have hc := field_cut c
  simp only [divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

theorem kernelsM (c : Cost) (k gainF gainR tailSave fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 84)+gainF=c.measure (Stair44WalkRun.forward false 489))
    (mR : c.measure (WindowWalkCosts.backward true 4)+gainR=c.measure (Stair44WalkRun.backward true 409))
    (h : c.measure (exitFieldHosted checkpointPrimitives)+tailSave=
      c.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+fieldExtra) :
    c.measure (multiply k)+gainF+gainR+tailSave=c.measure (Stair44Outer.multiply k)+fieldExtra := by
  simp only [multiply,Stair44Outer.multiply,phasePlace,kernelPlace,c.append,c.rename,Stair44PointMap.switchX]
  omega

theorem finite_delta (c : Cost) (C : Point) (cx cy : Fp) (gain : Nat)
    (hEn : c.measure (EntryFuseOdd.entryYAllOdd layout (-cy)) = c.measure (ParityUniform.entryYAll layout (-cy)))
    (hEx : c.measure (EntryFuseOdd.exitYAllOdd layout cy) = c.measure (ParityUniform.exitYAll layout cy))
    (h : c.measure divide+c.measure (multiply cx.val)+gain =
      c.measure Stair44Outer.divide+c.measure (Stair44Outer.multiply cx.val)) :
    c.measure (finite C cx cy)+gain=c.measure (Stair44Outer.finite C cx cy) := by
  simp only [finite,Stair44Outer.finite,borrowGeneric,Stair44Outer.borrowGeneric,
    generic,Stair44Outer.generic,Stair44PointMap.encodeY,c.append,c.rename,hEn,hEx]
  omega

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts



section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

section
attribute [local irreducible] WindowFieldCosts.group84Sign WindowFieldCosts.group84
  WindowFieldCosts.group toffoliCount measurementCount

private theorem fieldCountScalar (stock signed field total saving extra : Nat)
    (before : stock = field + total) (after : signed + saving = stock)
    (offset : total = saving + extra) : signed = field + extra := by omega

private theorem fieldCountTransport (c : Cost) (f : Program → Nat) (measure_eq : c.measure = f)
    (stock signed field : Program) (total saving extra : Nat)
    (before : f stock = f field + total) (after : f signed + saving = f stock)
    (offset : total = saving + extra) : c.measure signed = c.measure field + extra :=
  Eq.mpr (congrArg (fun measure : Program → Nat => measure signed = measure field + extra) measure_eq)
    (fieldCountScalar (f stock) (f signed) (f field) total saving extra before after offset)

private theorem fieldTcDiv :
    tc.measure (WindowFieldCosts.group84Sign true)=tc.measure (WindowFieldCosts.group true 1 84)+827 :=
  fieldCountTransport tc toffoliCount rfl
    (WindowFieldCosts.group84 true) (WindowFieldCosts.group84Sign true) (WindowFieldCosts.group true 1 84)
    1066 239 827 WindowFieldCosts.group_cost_div.1
    (WindowFieldCosts.SignCounts.group_delta true).1 rfl
private theorem fieldMcDiv :
    mc.measure (WindowFieldCosts.group84Sign true)=mc.measure (WindowFieldCosts.group true 1 84)+657 :=
  fieldCountTransport mc measurementCount rfl
    (WindowFieldCosts.group84 true) (WindowFieldCosts.group84Sign true) (WindowFieldCosts.group true 1 84)
    688 31 657 WindowFieldCosts.group_cost_div.2
    (WindowFieldCosts.SignCounts.group_delta true).2.1 rfl
private theorem fieldTcMul :
    tc.measure (WindowFieldCosts.group84Sign false)=tc.measure (WindowFieldCosts.group false 1 84)+739 :=
  fieldCountTransport tc toffoliCount rfl
    (WindowFieldCosts.group84 false) (WindowFieldCosts.group84Sign false) (WindowFieldCosts.group false 1 84)
    978 239 739 WindowFieldCosts.group_cost_mul.1
    (WindowFieldCosts.SignCounts.group_delta false).1 rfl
private theorem fieldMcMul :
    mc.measure (WindowFieldCosts.group84Sign false)=mc.measure (WindowFieldCosts.group false 1 84)+547 :=
  fieldCountTransport mc measurementCount rfl
    (WindowFieldCosts.group84 false) (WindowFieldCosts.group84Sign false) (WindowFieldCosts.group false 1 84)
    578 31 547 WindowFieldCosts.group_cost_mul.2
    (WindowFieldCosts.SignCounts.group_delta false).2.1 rfl

end

private theorem pair_delta2 {a b x y g h i j t1 t2 f1 f2 r : Nat}
    (l : a+g+h+t1=x+f1) (rr : b+i+j+t2=y+f2) (v : g+h+t1+i+j+t2=r+f1+f2) : a+b+r=x+y := by omega
attribute [local irreducible] Stair44Outer.divide Stair44Outer.multiply divide multiply
  finite Stair44Outer.finite WindowWalkCosts.forward WindowWalkCosts.backward
  WindowFieldCosts.group84Sign WindowFieldCosts.group Stair44WalkRun.forward Stair44WalkRun.backward
  toffoliCount measurementCount

theorem tc_div : tc.measure divide+39828+39957+681=tc.measure Stair44Outer.divide+827 := by
  have k := kernels tc 39828 39957 616 827 (WindowWalkCosts.inst true 4 409 39828 39979 rfl rfl rfl).1
    (WindowWalkCosts.inst false 85 490 39828 39957 rfl rfl rfl).2.1 (field_delta_tc_div 827 fieldTcDiv)
  have e : tc.measure Rolling1588.ep + tc.measure Rolling1588.dp = 13 := by
    show toffoliCount Rolling1588.ep + toffoliCount Rolling1588.dp = 13
    rw [PackCutCounts.tc_ep, PackCutCounts.tc_dp]
  omega

theorem tc_mul (k : Nat) : tc.measure (multiply k)+39828+39979+729=tc.measure (Stair44Outer.multiply k)+739 :=
  kernelsM tc k 39828 39979 729 739 (WindowWalkCosts.inst false 84 489 39828 39957 rfl rfl rfl).1
    (WindowWalkCosts.inst true 4 409 39828 39979 rfl rfl rfl).2.1 (field_delta_tc_mul 739 fieldTcMul)

theorem mc_div : mc.measure divide+17960+17708+1406=mc.measure Stair44Outer.divide+657 := by
  have k := kernels mc 17960 17708 1381 657 (WindowWalkCosts.instMeasurements true 4 409 17960 17730 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements false 85 490 17938 17708 rfl rfl rfl).2 (field_delta_mc_div 657 fieldMcDiv)
  have e : mc.measure Rolling1588.ep + mc.measure Rolling1588.dp = 5 := by
    show measurementCount Rolling1588.ep + measurementCount Rolling1588.dp = 5
    exact PackCutCounts.mc_epdp
  omega

theorem mc_mul (k : Nat) : mc.measure (multiply k)+17938+17730+1707=mc.measure (Stair44Outer.multiply k)+547 :=
  kernelsM mc k 17938 17730 1707 547 (WindowWalkCosts.instMeasurements false 84 489 17938 17708 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements true 4 409 17960 17730 rfl rfl rfl).2 (field_delta_mc_mul 547 fieldMcMul)

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+159436=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+73245=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 159436
      (OddOuterBridge.entryYAllOdd_tc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_tc_eq layout layout_widths cy)
      (pair_delta2 tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 73245
      (OddOuterBridge.entryYAllOdd_mc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_mc_eq layout layout_widths cy)
      (pair_delta2 mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2008161 ∧
    measurementCount (program C) ≤ 1446339 := by
  have h := Stair44Resources.totals C
  cases C with
  | zero => change toffoliCount [] ≤ _ ∧ measurementCount [] ≤ _; simp [toffoliCount,measurementCount]
  | @some cx cy hc =>
    have d := deltas (.some hc) cx cy
    simp only [program,Stair44Outer.program,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2] at h ⊢
    exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts


section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open ArchiveFieldScratch StairArchiveRelease StairArchiveNativeCut StairArchiveTen

def reserved : List Wire := StairPhysicalInventory.physicalHoles
theorem subset {q : Wire} (h : q∈reserved) : q∈StairPhysicalInventory.physicalHoles := h

theorem weaken {P : Program} {f : Wire → Wire} (h : PieceOK StairPhysicalInventory.physicalHoles f P) :
    PieceOK reserved f P := h

theorem app {a b : Program} {f : Wire → Wire} {hs : List Wire} :
    PieceOK hs f (a++b) ↔ PieceOK hs f a ∧ PieceOK hs f b := by
  refine ⟨fun h => ⟨?_,?_⟩,fun h => h.1.append h.2⟩ <;>
    constructor <;> intro q hq
  · exact h.1 q (wires_append a b ▸ Finset.mem_union_left _ hq)
  · exact h.2 q (wires_append a b ▸ Finset.mem_union_left _ hq)
  · exact h.1 q (wires_append a b ▸ Finset.mem_union_right _ hq)
  · exact h.2 q (wires_append a b ▸ Finset.mem_union_right _ hq)

theorem ren {a : Program} {f g : Wire → Wire} {hs : List Wire} :
    PieceOK hs f (renameProgram g a) ↔ PieceOK hs (fun q => f (g q)) a := by
  refine ⟨fun h => ⟨?_,?_⟩,PieceOK.rename⟩ <;> intro x hx
  · exact h.1 (g x) (renameProgram_support g a ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  · exact h.2 (g x) (renameProgram_support g a ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩)

private theorem singleton_ok {q : Wire} (h : Stair44OuterSites.fit q=true) :
    q∈StairHoleSupport.recordArena ∧ q∉StairHoleSupport.oldHoles ∧ q∉reserved := by
  let P : Program := [.X q]
  have inv : PieceOK StairPhysicalInventory.physicalHoles id P := Stair44OuterSites.fits
    (fun x hx => by
      have eq : x=q := by simpa [P,wires,Instr.wires] using hx
      exact eq ▸ h)
  have here : q∈wires P := by simp [P,wires,Instr.wires]
  exact ⟨(inv.1 q here).1,(inv.1 q here).2,(weaken inv).2 q here⟩

private theorem tagOK : 4835∈StairHoleSupport.recordArena ∧ 4835∉StairHoleSupport.oldHoles ∧
    4835∉Stair44FieldSites.holes := by
  rw [StairPhysicalLayout.recordArena_eq,StairPhysicalLayout.oldHoles_eq]
  decide +kernel

private theorem addresses (j : Nat) (hj : j∈List.range' 1 83) (q : Wire) (hq : q∈layout j) :
    Stair44OuterSites.fit q=true ∨ q=4835 := by
  have p := List.all_eq_true.mp packets_exact j hj
  dsimp only [packetOK,Id.run,pure] at p
  simp only [Bool.and_eq_true] at p
  simp only [layout,transient_exact,List.mem_append,List.mem_cons] at hq
  rcases hq with a | a | a
  · have z := List.all_eq_true.mp p.2 q a
    simp only [Bool.and_eq_true] at z
    exact Or.inl z.1
  · exact Or.inr a
  · exact Or.inl (List.all_eq_true.mp permanent_exact.2 q a)

theorem hook43 (j : Nat) (hj : j∈List.range' 1 83) (op : Stage) :
    PieceOK Stair44FieldSites.holes TP (fieldHook j op) := by
  rw [fieldHook,ren]
  have cover (x : Wire) (hx : x∈wires (program op)) :
      TP (fieldPort j x)∈StairHoleSupport.recordArena ∧
      TP (fieldPort j x)∉StairHoleSupport.oldHoles ∧ TP (fieldPort j x)∉Stair44FieldSites.holes := by
    have lt := Finset.mem_range.mp (sub op hx)
    have sl := (layout_frame j hj).2
    have small : x < (layout j).length := sl ▸ lt
    have member : port j x ∈ layout j := by
      simp only [port,List.getElem?_eq_getElem small,Option.getD_some,List.getElem_mem]
    change StairOuterPlacement.outerPlace _ ∈ _ ∧ _ ∧ _
    simp only [show TP=StairOuterPlacement.outerPlace from rfl,StairPlaceFast.outerPlace_eqB,placed_port j hj x lt]
    rcases addresses j hj _ member with p|e
    · have sok := singleton_ok p
      exact ⟨sok.1, sok.2.1, fun h => sok.2.2 (Stair44FieldSites.hsub _ h)⟩
    · rw [e]; exact tagOK
  exact ⟨fun x hx => ⟨(cover x hx).1,(cover x hx).2.1⟩,fun x hx => (cover x hx).2.2⟩

theorem width {P : Program} (h : PieceOK reserved id P) : Challenge.qubits P ≤ 1542 := by
  have listOK := StairCertificate.holeList_of_physical_sub reserved
    (by rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat]; decide +kernel) (fun _ hx => subset hx)
  have hq := StairCertificate.qubits_le_holes reserved listOK P (holePlacement_of_ok h)
  have hlen : reserved.length = 44 := by rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat]; decide +kernel
  omega
end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

attribute [local irreducible] wires domain

theorem forwardMixed_domain (d : Bool) : Covered (Shadow20.MergeCut.forward d) := by
  intro q h
  rw [domain_eq]
  exact (Shadow20.MergeCut.covered d).1 q h
theorem reverseMixed_domain (d : Bool) : Covered (Shadow20.MergeCut.reverse d) := by
  intro q h
  rw [domain_eq]
  exact Shadow20.MergeCut.rcovered d q h

theorem forwardMixed_fits (d : Bool) : ∀ q ∈ wires (Shadow20.MergeCut.forward d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (forwardMixed_domain d q h)

theorem reverseMixed_fits (d : Bool) : ∀ q ∈ wires (Shadow20.MergeCut.reverse d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (reverseMixed_domain d q h)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44Resources Stair44Outer
open StairConcreteAssembly WindowWalkCosts WindowFold Partial
set_option maxHeartbeats 1400000
set_option maxRecDepth 14000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount gateSlots measurementCount wires renameProgram
  Rolling1588TickGap.forward Rolling1588.reverse Shadow20.MergeCut.forward Shadow20.MergeCut.reverse

theorem walk (c : Cost) (d : Bool) (tail f r n : Nat) (hn : 405+tail=n)
    (hf : c.measure (Shadow20.MergeCut.forward d) ≤ f) (hr : c.measure (Shadow20.MergeCut.reverse d) ≤ r) :
    c.measure (WindowWalkCosts.forward d tail) ≤ c.measure (Stair44WalkRun.forward d n)+f ∧
    c.measure (WindowWalkCosts.backward d tail) ≤ c.measure (Stair44WalkRun.backward d n)+r := by
  subst n
  have a := StairRestSupport.forward_append d 29 16 (376+tail)
  have b := StairRestSupport.forward_append d 376 45 tail
  have x := StairRestSupport.reverse_append d 29 16 (376+tail)
  have y := StairRestSupport.reverse_append d 376 45 tail
  change Rolling1588TickGap.forward d 16 (29+(376+tail)) =
    Rolling1588TickGap.forward d 16 29 ++ Rolling1588TickGap.forward d 45 (376+tail) at a
  change Rolling1588.reverse d 16 (29+(376+tail)) =
    Rolling1588.reverse d 45 (376+tail) ++ Rolling1588.reverse d 16 29 at x
  rw [b] at a
  rw [y] at x
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,WindowWalkCosts.forward,WindowWalkCosts.backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

private theorem kernels (gainF gainR fieldExtra : Nat)
    (dF : slots.measure (WindowWalkCosts.forward true 4) ≤ slots.measure (Stair44WalkRun.forward true 409)+gainF)
    (dR : slots.measure (WindowWalkCosts.backward false 85) ≤ slots.measure (Stair44WalkRun.backward false 490)+gainR)
    (g : slots.measure (WindowFieldCosts.group84Sign true)=slots.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    slots.measure WindowCallerCosts.divide ≤ slots.measure Stair44Outer.divide+gainF+gainR+fieldExtra+12660 := by
  have h := WindowCallerCosts.field_delta_slots true _ g
  have hc := WindowCallerCosts.field_cut slots
  simp only [if_true] at h
  simp only [WindowCallerCosts.divide,Stair44Outer.divide,phasePlace,kernelPlace,
    Stair44Resources.slots.append,Stair44Resources.slots.rename]
  omega

private theorem kernelsM (k gainF gainR fieldExtra : Nat)
    (mF : slots.measure (WindowWalkCosts.forward false 84) ≤ slots.measure (Stair44WalkRun.forward false 489)+gainF)
    (mR : slots.measure (WindowWalkCosts.backward true 4) ≤ slots.measure (Stair44WalkRun.backward true 409)+gainR)
    (g : slots.measure (WindowFieldCosts.group84Sign false)=slots.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
    slots.measure (WindowCallerCosts.multiply k) ≤ slots.measure (Stair44Outer.multiply k)+gainF+gainR+fieldExtra+12920 := by
  have h := WindowCallerCosts.field_delta_slots false _ g
  simp only [Bool.false_eq_true,if_false] at h
  simp only [WindowCallerCosts.multiply,Stair44Outer.multiply,phasePlace,kernelPlace,
    Stair44Resources.slots.append,Stair44Resources.slots.rename,Stair44PointMap.switchX]
  omega

private theorem finite_upper (C : Point) (cx cy : Fp) (gain : Nat)
    (h : slots.measure WindowCallerCosts.divide+slots.measure (WindowCallerCosts.multiply cx.val)+7144 ≤
      slots.measure Stair44Outer.divide+slots.measure (Stair44Outer.multiply cx.val)+gain) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤ slots.measure (Stair44Outer.finite C cx cy)+gain := by
  have hy := OddOuterBridge.outerY_slots_delta cy
  rw [show slots.measure=Challenge.gateSlots from rfl] at h ⊢
  simp only [WindowCallerCosts.finite,Stair44Outer.finite,WindowCallerCosts.borrowGeneric,Stair44Outer.borrowGeneric,
    WindowCallerCosts.generic,Stair44Outer.generic,Challenge.gateSlots_append,Baselines.rename_gateSlots] at *
  omega



private theorem route20_slots (j : Fin 9) (i n : Nat) :
    gateSlots (Shadow20.routed20 j i n) ≤ 5000 * n ∧
    gateSlots (Shadow20.unrouted20 j i n) ≤ 5000 * n := by
  induction n generalizing i with
  | zero =>
    simp only [Shadow20.routed20, Shadow20.unrouted20, gateSlots_nil, Nat.mul_zero, Nat.le_refl, and_self]
  | succ n ih =>
    have tail := ih (i + 1)
    have t := WindowSlots.tick (Shadow20.shape20 j) i
    have u := WindowSlots7.untickR_slots (Shadow20.shape20 j) i
    simp only [Shadow20.routed20, Shadow20.unrouted20, gateSlots_append, rename_gateSlots, Nat.mul_succ]
    exact ⟨by omega, by omega⟩

private theorem sum_flatten_slots (ps : List Program) :
    gateSlots ps.flatten = (ps.map gateSlots).sum := by
  induction ps with
  | nil => simp only [List.flatten_nil, gateSlots_nil, List.map_nil, List.sum_nil]
  | cons p ps ih => simp only [List.flatten_cons, gateSlots_append, List.map_cons, List.sum_cons, ih]

private theorem sum_flatMap_slots_le {α : Type} (f : α → List Program) (b : α → Nat) (xs : List α)
    (h : ∀ x ∈ xs, ((f x).map gateSlots).sum ≤ b x) :
    ((xs.flatMap f).map gateSlots).sum ≤ (xs.map b).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

private def b15SF (j : Fin 26) : Nat :=
  35 + 5000 + 168 + 15988 + 70000 +
  (6 * CRTBarrel.adjustWidth (start j) + 5 * Shadow7.liveW (start j) + 10 * Shadow7.lowsP (start j) + 646 +
    3 * Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) false)

private def b15SR (j : Fin 26) : Nat :=
  36 + 5000 + 166 + 12262 + 70098 +
  (6 * CRTBarrel.adjustWidth (start j) + 5 * Shadow7.liveW (start j) + 11 * Shadow7.lowsP (start j) + 616 +
    3 * Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) true)

private def b20SF (j : Fin 9) : Nat :=
  let s := Shadow20.start20 j
  35 + 5000 + (if j.val = 0 then 168 else 336) + 15988 + 95000 +
  (6 * Shadow20.TrimHigh.adjustWidth s + 5 * Shadow20.liveW20 s + 10 * Shadow20.lowsP20 s + 851 +
    3 * Shadow20.nextWp20 s + Shadow20.barrel20Slots s false)

private def b20SR (j : Fin 9) : Nat :=
  let s := Shadow20.start20 j
  36 + 5000 + (if j.val = 0 then 166 else 332) + 12262 + 95000 +
  (6 * Shadow20.TrimHigh.adjustWidth s + 5 * Shadow20.liveW20 s + 11 * Shadow20.lowsP20 s + 811 +
    3 * Shadow20.nextWp20 s + Shadow20.barrel20Slots s true)

private theorem packW_slots_le (d : Bool) (s t : Nat) (hd : WindowParams.dueTick t = true) :
    gateSlots (Shadow20.MixedWindow.packW d s t) ≤ 168 ∧
    gateSlots (Shadow20.MixedWindow.unpackW d s t) ≤ 166 := by
  have h1 := WindowParams7.slots_le.pack d s t
  have h2 := WindowParams7.slots_le.unpack d s t
  simp only [Pieces.map, Shadow7.params, ofParts, WindowParams7.slotsV, hd, ↓reduceIte] at h1 h2
  change gateSlots (Shadow20.MixedWindow.packW d s t) ≤ _ at h1
  change gateSlots (Shadow20.MixedWindow.unpackW d s t) ≤ _ at h2
  cases d <;> simp only [if_true, if_false, Bool.false_eq_true] at h1 h2 <;> exact ⟨by omega, by omega⟩

private theorem arch15_slots_le (j : Fin 26) (d : Bool) :
    gateSlots (Shadow7.archiveLoadP j d) ≤ 15988 ∧
    gateSlots (Shadow7.archiveRestoreP j d) ≤ 12262 := by
  have h1 := WindowParams7.slots_le.load j d
  have h2 := WindowParams7.slots_le.restore j d
  simp only [Pieces.map, Shadow7.params, ofParts, WindowParams7.slotsV] at h1 h2
  cases d <;> simp only [if_true, if_false, Bool.false_eq_true] at h1 h2 <;> exact ⟨by omega, by omega⟩

private theorem arch20_slots_le (j : Fin 9) (d : Bool) :
    gateSlots (Shadow20.archiveLoadP20 j d) ≤ 15988 ∧
    gateSlots (Shadow20.archiveRestoreP20 j d) ≤ 12262 := by
  have h := Shadow20.archive20_counts j d
  have h1 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.1
  have h2 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.2.2.2.1
  have a := arch15_slots_le WindowParams.first d
  exact ⟨by omega, by omega⟩

private theorem arch150_slots_le (d : Bool) :
    gateSlots (Shadow20.archiveLoad150To20 d) ≤ 15988 ∧
    gateSlots (Shadow20.archiveRestore150To20 d) ≤ 12262 := by
  obtain ⟨_, _, l3, _, _, l6⟩ := moves_counts 165 (Shadow20.e0P20 165 + 6)
  obtain ⟨_, _, m3, _, _, m6⟩ := moves240_counts
  have hL : gateSlots (Shadow20.archiveLoad150To20 d) = gateSlots (archiveLoad240 d) := by
    simp only [Shadow20.archiveLoad150To20, archiveLoad240, gateSlots_append, rename_gateSlots, l3, m3]
  have hR : gateSlots (Shadow20.archiveRestore150To20 d) = gateSlots (archiveRestore240 d) := by
    simp only [Shadow20.archiveRestore150To20, archiveRestore240, gateSlots_append, rename_gateSlots, l6, m6]
  have h1 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.1
  have h2 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.2.2.2.1
  have a := arch15_slots_le WindowParams.first d
  exact ⟨by omega, by omega⟩

private theorem exit420_slots_le (d : Bool) :
    gateSlots (Shadow7.exitLoadP 420 d) ≤ 15988 ∧
    gateSlots (Shadow7.exitRestoreP 420 d) ≤ 12262 := by
  have h1 := WindowParams7.slots_le.exitLoad 420 d
  have h2 := WindowParams7.slots_le.exitRestore 420 d
  simp only [Pieces.map, Shadow7.params, ofParts, WindowParams7.slotsV] at h1 h2
  cases d <;> simp only [if_true, if_false, Bool.false_eq_true] at h1 h2 <;> exact ⟨by omega, by omega⟩

private theorem mixed_slot_sum_vals :
    ((22 * Shadow7.wpP 45 - 9) + (35 + (5000 + (168 + (70000 +
      ((6 * CRTBarrel.adjustWidth 45 + 5 * Shadow7.liveW 45 + 10 * Shadow7.lowsP 45 + 641 + 3 * Shadow7.wpP 60 + CRTBarrel.barrelSlots 45 false) + 0)))))) +
    (Shadow20.MixedWindow.prefixPairs.map fun p => b15SF p.2).sum +
    (35 + (5000 + (168 + (15988 + (70000 + (11679 + 0)))))) +
    ((List.finRange 9).map b20SF).sum +
    (35 + (5000 + (168 + (168 + (15988 + (70000 +
      ((6 * CRTBarrel.adjustWidth 345 + 5 * Shadow7.liveW 345 + 10 * Shadow7.lowsP 345 + 641 + 3 * Shadow7.wpP 360 + CRTBarrel.barrelSlots 345 false) + 0))))))) +
    (Shadow20.MixedWindow.suffixPairs.map fun p => b15SF p.2).sum +
    (9 + ((21 * Shadow7.wpP 420 - 7) + (6004 + (168 + (15988 + 0))))) ≤ 2698994 ∧
    (12262 + (166 + (6001 + ((22 * Shadow7.wpP 420 - 9) + (9 + 0))))) +
    (Shadow20.MixedWindow.suffixPairs.reverse.map fun p => b15SR p.2).sum +
    ((6 * CRTBarrel.adjustWidth 345 + 5 * Shadow7.liveW 345 + 11 * Shadow7.lowsP 345 + 611 + 3 * Shadow7.wpP 360 + CRTBarrel.barrelSlots 345 true) +
      (70098 + (12262 + (166 + (166 + (5000 + (36 + 0))))))) +
    ((List.finRange 9).reverse.map b20SR).sum +
    (11697 + (70098 + (12262 + (166 + (5000 + (36 + 0)))))) +
    (Shadow20.MixedWindow.prefixPairs.reverse.map fun p => b15SR p.2).sum +
    ((6 * CRTBarrel.adjustWidth 45 + 5 * Shadow7.liveW 45 + 11 * Shadow7.lowsP 45 + 611 + 3 * Shadow7.wpP 60 + CRTBarrel.barrelSlots 45 true) +
      (70098 + (166 + (5000 + (36 + ((21 * Shadow7.wpP 45 - 7) + 0)))))) ≤ 2598694 := by
  decide +kernel

private theorem tick420_slots_le :
    gateSlots (Shadow20.MixedWindow.tickW 420) ≤ 6004 ∧
    gateSlots (Shadow20.MixedWindow.recvW 420) ≤ 6001 := by
  unfold Shadow20.MixedWindow.tickW Shadow20.MixedWindow.recvW
  rw [rename_gateSlots, rename_gateSlots,
    StairSlotsLib.tick_slots_formula base 420 (by decide) (by decide) base_pool_nodup,
    StairSlotsLib.receiverTick_slots_formula base 420 (by decide) (by decide) base_pool_nodup]
  decide +kernel

private theorem b15F_slots_le (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24)
    (hd : WindowParams.dueTick (start j - 10) = true) :
    ((Shadow20.MixedWindow.block15F d i j).map gateSlots).sum ≤ b15SF j := by
  have e := (Shadow7.enter_counts j).2.2.2.2.1
  have r0 := (WindowSlots7.route j 0 1).1
  have r1 := (WindowSlots7.route j 1 14).1
  have pk := (packW_slots_le d (start j) (start j - 10) hd).1
  have ar := (arch15_slots_le i d).1
  have lv := (CRTWindow.leave_metrics j (Nat.zero_le _) hj).2.2.2.2.1
  simp only [Shadow20.MixedWindow.block15F, b15SF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem sel14_slots (j : Fin 26) : gateSlots (TickCut.Tail.selected j 1 14) ≤ 70098 := by
  have c := (TickCut.Tail.tail_counts j).2.2
  have r := (WindowSlots7.route j 1 14).2
  rw [TickCut.Tail.selected, if_pos (show (1:Nat) = 1 ∧ (14:Nat) = 14 from ⟨rfl, rfl⟩)]
  omega

private theorem b15R_slots_le (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24)
    (hd : WindowParams.dueTick (start j - 10) = true) :
    ((Shadow20.MixedWindow.block15R d i j).map gateSlots).sum ≤ b15SR j := by
  have e := (Shadow7.enter_counts j).2.2.2.2.2
  have r0 := (WindowSlots7.route j 0 1).2
  have r1 := sel14_slots j
  have pk := (packW_slots_le d (start j) (start j - 10) hd).2
  have ar := (arch15_slots_le i d).2
  have lv := (CRTWindow.leave_metrics j (Nat.zero_le _) hj).2.2.2.2.2
  simp only [Shadow20.MixedWindow.block15R, b15SR, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem b20F_slots_le (d : Bool) (j : Fin 9) :
    ((Shadow20.MixedWindow.block20F d j).map gateSlots).sum ≤ b20SF j := by
  have e := (Shadow20.enter20_counts j).2.2.2.2.1
  have r0 := (route20_slots j 0 1).1
  have r1 := (route20_slots j 1 19).1
  have lv := (Shadow20.leave20Red_counts j).2.2.2.2.1
  by_cases h0 : j.val = 0
  · have pk := (packW_slots_le d 165 155 (by decide)).1
    have ar := (arch150_slots_le d).1
    simp only [Shadow20.MixedWindow.block20F, b20SF, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · have hd1 : WindowParams.dueTick (Shadow20.start20 j - 15) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 15) = true := by decide +kernel
      exact h j h0
    have hd2 : WindowParams.dueTick (Shadow20.start20 j - 10) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 10) = true := by decide +kernel
      exact h j h0
    have pk1 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 15) hd1).1
    have pk2 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 10) hd2).1
    have ar := (arch20_slots_le ⟨j.val - 1, by omega⟩ d).1
    simp only [Shadow20.MixedWindow.block20F, b20SF, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

private theorem b20R_slots_le (d : Bool) (j : Fin 9) :
    ((Shadow20.MixedWindow.block20R d j).map gateSlots).sum ≤ b20SR j := by
  have e := (Shadow20.enter20_counts j).2.2.2.2.2
  have r0 := (route20_slots j 0 1).2
  have r1 := (route20_slots j 1 19).2
  have lv := (Shadow20.leave20Red_counts j).2.2.2.2.2
  by_cases h0 : j.val = 0
  · have pk := (packW_slots_le d 165 155 (by decide)).2
    have ar := (arch150_slots_le d).2
    simp only [Shadow20.MixedWindow.block20R, b20SR, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · have hd1 : WindowParams.dueTick (Shadow20.start20 j - 15) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 15) = true := by decide +kernel
      exact h j h0
    have hd2 : WindowParams.dueTick (Shadow20.start20 j - 10) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 10) = true := by decide +kernel
      exact h j h0
    have pk1 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 15) hd1).2
    have pk2 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 10) hd2).2
    have ar := (arch20_slots_le ⟨j.val - 1, by omega⟩ d).2
    simp only [Shadow20.MixedWindow.block20R, b20SR, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

private theorem sum_map_append7 (m : Program → Nat) (a b c d e f g : List Program) :
    ((a ++ b ++ c ++ d ++ e ++ f ++ g).map m).sum =
      (a.map m).sum + (b.map m).sum + (c.map m).sum + (d.map m).sum + (e.map m).sum + (f.map m).sum + (g.map m).sum := by
  simp only [List.map_append, List.sum_append]

private theorem sum_map5 (m : Program → Nat) (a b c d e : Program) :
    ([a, b, c, d, e].map m).sum = m a + (m b + (m c + (m d + (m e + 0)))) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

private theorem sum_map6 (m : Program → Nat) (a b c d e f : Program) :
    ([a, b, c, d, e, f].map m).sum = m a + (m b + (m c + (m d + (m e + (m f + 0))))) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

private theorem sum_map7 (m : Program → Nat) (a b c d e f g : Program) :
    ([a, b, c, d, e, f, g].map m).sum = m a + (m b + (m c + (m d + (m e + (m f + (m g + 0)))))) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP
  Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP Shadow7.routed Shadow7.unrouted
  Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.exitLoadP Shadow7.exitRestoreP
  CRTBarrel.leave CRTBarrel.unleave Shadow20.enterP20 Shadow20.enterInvP20 Shadow20.leaveP20 Shadow20.leaveInvP20 Shadow20.leaveP20Red Shadow20.leaveInvP20Red
  Shadow20.routed20 Shadow20.unrouted20 Shadow20.archiveLoadP20 Shadow20.archiveRestoreP20
  Shadow20.leave150To20 Shadow20.leaveInv150To20 Shadow20.leave150To20Red Shadow20.leaveInv150To20Red Shadow20.archiveLoad150To20 Shadow20.archiveRestore150To20
  Shadow20.MixedWindow.packW Shadow20.MixedWindow.unpackW Shadow20.MixedWindow.tickW Shadow20.MixedWindow.recvW
  Shadow20.MixedWindow.block15F Shadow20.MixedWindow.block15R Shadow20.MixedWindow.block20F Shadow20.MixedWindow.block20R in
private theorem mixed_slots_F (d : Bool) :
    gateSlots (Shadow20.MixedWindow.forwardMixed d) ≤ 2698994 := by
  have hp15 : ∀ p ∈ Shadow20.MixedWindow.prefixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hs15 : ∀ p ∈ Shadow20.MixedWindow.suffixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hprF := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15F d p.1 p.2) (fun p => b15SF p.2) Shadow20.MixedWindow.prefixPairs (fun p hp => by have h := hp15 p hp; exact b15F_slots_le d p.1 p.2 h.1 h.2)
  have hsuF := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15F d p.1 p.2) (fun p => b15SF p.2) Shadow20.MixedWindow.suffixPairs (fun p hp => by have h := hs15 p hp; exact b15F_slots_le d p.1 p.2 h.1 h.2)
  have h20F := sum_flatMap_slots_le (Shadow20.MixedWindow.block20F d) b20SF (List.finRange 9) (fun j _ => b20F_slots_le d j)
  have p45 := (Shadow7.portal_counts 45 (by decide)).2.2.2.2.1
  have p420 := (Shadow7.portal_counts 420 (by decide)).2.2.2.2.2
  have pk420 := (Shadow7.park_counts 420).2.2.2.2.1
  have t420 := tick420_slots_le.1
  have exF := (exit420_slots_le d).1
  have e0 := (Shadow7.enter_counts Shadow20.MixedWindow.j0).2.2.2.2.1
  have r0a : gateSlots (Shadow7.routed Shadow20.MixedWindow.j0 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j0 0 1).1
  have r0b : gateSlots (Shadow7.routed Shadow20.MixedWindow.j0 1 14) ≤ 70000 := by
    simpa only [show 5000 * 14 = 70000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j0 1 14).1
  have l0 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j0 (by decide) (by decide)).2.2.2.2.1
  have e7 := (Shadow7.enter_counts Shadow20.MixedWindow.j7).2.2.2.2.1
  have r7a : gateSlots (Shadow7.routed Shadow20.MixedWindow.j7 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j7 0 1).1
  have r7b : gateSlots (Shadow7.routed Shadow20.MixedWindow.j7 1 14) ≤ 70000 := by
    simpa only [show 5000 * 14 = 70000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j7 1 14).1
  have a6 := (arch15_slots_le Shadow20.MixedWindow.j6 d).1
  have l7 := Shadow20.leave150To20Red_counts.2.2.2.2.1
  have e20 := (Shadow7.enter_counts Shadow20.MixedWindow.j20).2.2.2.2.1
  have r20a : gateSlots (Shadow7.routed Shadow20.MixedWindow.j20 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j20 0 1).1
  have r20b : gateSlots (Shadow7.routed Shadow20.MixedWindow.j20 1 14) ≤ 70000 := by
    simpa only [show 5000 * 14 = 70000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j20 1 14).1
  have a8 := (arch20_slots_le Shadow20.MixedWindow.k8 d).1
  have l20 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j20 (by decide) (by decide)).2.2.2.2.1
  have pk45 := (packW_slots_le d 45 45 (by decide)).1
  have pk140 := (packW_slots_le d 150 140 (by decide)).1
  have pk330 := (packW_slots_le d 345 330 (by decide)).1
  have pk335 := (packW_slots_le d 345 335 (by decide)).1
  have pk410 := (packW_slots_le d 420 410 (by decide)).1
  have mv := mixed_slot_sum_vals.1
  rw [show start Shadow20.MixedWindow.j0 = 45 from rfl, show (45 : Nat) + 15 = 60 from rfl] at l0
  rw [show start Shadow20.MixedWindow.j20 = 345 from rfl, show (345 : Nat) + 15 = 360 from rfl] at l20
  have hdef : Shadow20.MixedWindow.forwardMixed d = (Shadow20.MixedWindow.forwardL d).flatten := by
    unfold Shadow20.MixedWindow.forwardMixed; rfl
  rw [hdef, sum_flatten_slots, Shadow20.MixedWindow.forwardL, sum_map_append7, sum_map6, sum_map6, sum_map7, sum_map5]
  rw [p45, e0, l0, e7, l7, e20, l20, pk420, p420]
  refine Nat.le_trans ?_ mv
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add r0a (Nat.add_le_add pk45 (Nat.add_le_add r0b (Nat.le_refl _)))) _) _)
              hprF)
            (Nat.add_le_add_left (Nat.add_le_add r7a (Nat.add_le_add pk140 (Nat.add_le_add a6 (Nat.add_le_add r7b (Nat.le_refl _))))) _))
          h20F)
        (Nat.add_le_add_left (Nat.add_le_add r20a (Nat.add_le_add pk330 (Nat.add_le_add pk335 (Nat.add_le_add a8 (Nat.add_le_add r20b (Nat.le_refl _)))))) _))
      hsuF)
    (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add t420 (Nat.add_le_add pk410 (Nat.add_le_add exF (Nat.le_refl _)))) _) _)

attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP
  Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP Shadow7.routed Shadow7.unrouted
  Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.exitLoadP Shadow7.exitRestoreP
  CRTBarrel.leave CRTBarrel.unleave Shadow20.enterP20 Shadow20.enterInvP20 Shadow20.leaveP20 Shadow20.leaveInvP20 Shadow20.leaveP20Red Shadow20.leaveInvP20Red
  Shadow20.routed20 Shadow20.unrouted20 Shadow20.archiveLoadP20 Shadow20.archiveRestoreP20
  Shadow20.leave150To20 Shadow20.leaveInv150To20 Shadow20.leave150To20Red Shadow20.leaveInv150To20Red Shadow20.archiveLoad150To20 Shadow20.archiveRestore150To20
  Shadow20.MixedWindow.packW Shadow20.MixedWindow.unpackW Shadow20.MixedWindow.tickW Shadow20.MixedWindow.recvW
  Shadow20.MixedWindow.block15F Shadow20.MixedWindow.block15R Shadow20.MixedWindow.block20F Shadow20.MixedWindow.block20R in
private theorem mixed_slots_R (d : Bool) :
    gateSlots (Shadow20.MixedWindow.reverseMixed d) ≤ 2598694 := by
  have hp15 : ∀ p ∈ Shadow20.MixedWindow.prefixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hs15 : ∀ p ∈ Shadow20.MixedWindow.suffixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hprR := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15R d p.1 p.2) (fun p => b15SR p.2) Shadow20.MixedWindow.prefixPairs.reverse (fun p hp => by have h := hp15 p (List.mem_reverse.mp hp); exact b15R_slots_le d p.1 p.2 h.1 h.2)
  have hsuR := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15R d p.1 p.2) (fun p => b15SR p.2) Shadow20.MixedWindow.suffixPairs.reverse (fun p hp => by have h := hs15 p (List.mem_reverse.mp hp); exact b15R_slots_le d p.1 p.2 h.1 h.2)
  have h20R := sum_flatMap_slots_le (Shadow20.MixedWindow.block20R d) b20SR (List.finRange 9).reverse (fun j _ => b20R_slots_le d j)
  have p45 := (Shadow7.portal_counts 45 (by decide)).2.2.2.2.2
  have p420 := (Shadow7.portal_counts 420 (by decide)).2.2.2.2.1
  have pk420 := (Shadow7.park_counts 420).2.2.2.2.2
  have t420 := tick420_slots_le.2
  have exR := (exit420_slots_le d).2
  have e0 := (Shadow7.enter_counts Shadow20.MixedWindow.j0).2.2.2.2.2
  have r0a : gateSlots (Shadow7.unrouted Shadow20.MixedWindow.j0 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j0 0 1).2
  have r0b : gateSlots (TickCut.Tail.selected Shadow20.MixedWindow.j0 1 14) ≤ 70098 := sel14_slots _
  have l0 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j0 (by decide) (by decide)).2.2.2.2.2
  have e7 := (Shadow7.enter_counts Shadow20.MixedWindow.j7).2.2.2.2.2
  have r7a : gateSlots (Shadow7.unrouted Shadow20.MixedWindow.j7 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j7 0 1).2
  have r7b : gateSlots (TickCut.Tail.selected Shadow20.MixedWindow.j7 1 14) ≤ 70098 := sel14_slots _
  have a6 := (arch15_slots_le Shadow20.MixedWindow.j6 d).2
  have l7 := Shadow20.leave150To20Red_counts.2.2.2.2.2
  have e20 := (Shadow7.enter_counts Shadow20.MixedWindow.j20).2.2.2.2.2
  have r20a : gateSlots (Shadow7.unrouted Shadow20.MixedWindow.j20 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j20 0 1).2
  have r20b : gateSlots (TickCut.Tail.selected Shadow20.MixedWindow.j20 1 14) ≤ 70098 := sel14_slots _
  have a8 := (arch20_slots_le Shadow20.MixedWindow.k8 d).2
  have l20 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j20 (by decide) (by decide)).2.2.2.2.2
  have pk45 := (packW_slots_le d 45 45 (by decide)).2
  have pk140 := (packW_slots_le d 150 140 (by decide)).2
  have pk330 := (packW_slots_le d 345 330 (by decide)).2
  have pk335 := (packW_slots_le d 345 335 (by decide)).2
  have pk410 := (packW_slots_le d 420 410 (by decide)).2
  have mv := mixed_slot_sum_vals.2
  rw [show start Shadow20.MixedWindow.j0 = 45 from rfl, show (45 : Nat) + 15 = 60 from rfl] at l0
  rw [show start Shadow20.MixedWindow.j20 = 345 from rfl, show (345 : Nat) + 15 = 360 from rfl] at l20
  have hdef : Shadow20.MixedWindow.reverseMixed d = (Shadow20.MixedWindow.reverseL d).flatten := by
    unfold Shadow20.MixedWindow.reverseMixed; rfl
  rw [hdef, sum_flatten_slots, Shadow20.MixedWindow.reverseL, sum_map_append7, sum_map5, sum_map7, sum_map6, sum_map6]
  rw [p45, e0, l0, e7, l7, e20, l20, pk420, p420]
  refine Nat.le_trans ?_ mv
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add exR (Nat.add_le_add pk410 (Nat.add_le_add t420 (Nat.le_refl _))))
              hsuR)
            (Nat.add_le_add_left (Nat.add_le_add r20b (Nat.add_le_add a8 (Nat.add_le_add pk335 (Nat.add_le_add pk330 (Nat.add_le_add r20a (Nat.le_refl _)))))) _))
          h20R)
        (Nat.add_le_add_left (Nat.add_le_add r7b (Nat.add_le_add a6 (Nat.add_le_add pk140 (Nat.add_le_add r7a (Nat.le_refl _))))) _))
      hprR)
    (Nat.add_le_add_left (Nat.add_le_add r0b (Nat.add_le_add pk45 (Nat.add_le_add r0a (Nat.le_refl _)))) _)

private theorem mixed_slots (d : Bool) :
    gateSlots (Shadow20.MixedWindow.forwardMixed d) ≤ 2698994 ∧
    gateSlots (Shadow20.MixedWindow.reverseMixed d) ≤ 2598694 :=
  ⟨mixed_slots_F d, mixed_slots_R d⟩

private theorem casts {P : Program} {n : Nat} (h : gateSlots P ≤ n) : slots.measure P ≤ n := h
private theorem groupCap (d : Bool) (n : Nat)
    (hn : 22*(if d then 5322 else 6122)+881=n+(if d then 30118 else 27598)) :
    slots.measure (WindowFieldCosts.group84Sign d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  have offset : (if d then 21193 else 18673) + 8925 =
      (if d then 30118 else 27598) := by cases d <;> decide
  have transport (stock signed field : Nat)
      (before : stock + (if d then 21193 else 18673) =
        field + 22 * (if d then 5322 else 6122) + 881)
      (after : signed + 8925 = stock) : signed = field + n := by omega
  exact transport (slots.measure (WindowFieldCosts.group84 d))
    (slots.measure (WindowFieldCosts.group84Sign d))
    (slots.measure (WindowFieldCosts.group d 1 84)) (WindowFieldCosts.group_slots d)
    (WindowFieldCosts.SignCounts.group_delta d).2.2
theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+2698994+2599891+94760+12660 :=
  Nat.le_trans (kernels 2698994 2599891 87847
    (walk slots true 4 2698994 2599891 409 rfl (casts ((Shadow20.MergeCut.slots_le true).1.trans (mixed_slots true).1)) (casts ((Shadow20.MergeCut.rslots_le true).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le true).2.trans (mixed_slots true).2) 1197)))).1
    (walk slots false 85 2698994 2599891 490 rfl (casts ((Shadow20.MergeCut.slots_le false).1.trans (mixed_slots false).1)) (casts ((Shadow20.MergeCut.rslots_le false).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le false).2.trans (mixed_slots false).2) 1197)))).2
    (groupCap true 87847 rfl)) (by omega)

theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+2698994+2599891+114880+12920 :=
  Nat.le_trans (kernelsM k 2698994 2599891 107967
    (walk slots false 84 2698994 2599891 489 rfl (casts ((Shadow20.MergeCut.slots_le false).1.trans (mixed_slots false).1)) (casts ((Shadow20.MergeCut.rslots_le false).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le false).2.trans (mixed_slots false).2) 1197)))).1
    (walk slots true 4 2698994 2599891 409 rfl (casts ((Shadow20.MergeCut.slots_le true).1.trans (mixed_slots true).1)) (casts ((Shadow20.MergeCut.rslots_le true).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le true).2.trans (mixed_slots true).2) 1197)))).2
    (groupCap false 107967 rfl)) (by omega)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+2698994+2599891+94760+12660)
    (hm : b ≤ y+2698994+2599891+114880+12920) : a+b+7144 ≤ x+y+10840134 := by omega

theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+10840134 :=
  finite_upper C cx cy 10840134 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 67191214 := by
  have h := Stair44Resources.slotBound C
  cases C with
  | zero => change gateSlots [] ≤ _; simp [gateSlots]
  | @some cx cy hc =>
    have f := cap (.some hc) cx cy
    rw [show slots.measure=gateSlots from rfl] at f
    simp only [WindowCallerCosts.program,Stair44Outer.program,rename_gateSlots] at h ⊢
    omega
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open StairRestSupport StairPhysicalV3 ArchiveFieldScratch StairArchiveRelease StairArchiveGates Baselines
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet


theorem app {p q : Program} : Sound (p++q) ↔ Sound p ∧ Sound q :=
  ⟨fun h => ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩,
    fun h => sound_append h.1 h.2⟩

theorem emitted (op : Stage) : GatePhysical (StairArchiveRelease.program op) := by
  cases op
  exacts [ReducedWindowArchives.enter0_counts.1,ReducedWindowArchives.switch0_counts.1,ReducedWindowArchives.leave0_counts.1,
    ReducedWindowArchives.enter1_counts.1,ReducedWindowArchives.switch1_counts.1,ReducedWindowArchives.leave1_counts.1]

theorem hook (j : Nat) (hj : j∈[10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (op : Stage) :
    Sound (fieldHook j op) := by
  have span : j∈List.range' 1 83 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; apply List.mem_range'_1.mpr; omega
  have chk : (fieldSites j).all (fun q => decide (InDom q))=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  refine ⟨gatePhysical_rename_support _ _ (fun a ha b hb eq => field_inj j span a (sub op ha) b (sub op hb) eq) (emitted op),?_⟩
  intro q hq
  rw [fieldHook,renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  have len : (fieldSites j).length=121 := by
    have hh := (layout_frame j span).2
    rwa [←field_layout,List.length_map] at hh
  have lt : x < (fieldSites j).length := len ▸ (Finset.mem_range.mp (sub op hx))
  apply of_decide_eq_true (List.all_eq_true.mp chk _ ?_)
  simp only [fieldPort,List.getElem?_eq_getElem lt,Option.getD_some,List.getElem_mem]

private theorem distributed_ok (d : Bool) (j n : Nat) :
    Sound (distributed d j n) ↔
    ∀ (i : Nat), j ≤ i → i < j+n → Sound (packet d i) := by
  induction n generalizing j with
  | zero =>
    change Sound [] ↔ _
    exact ⟨fun _ i lo hi => False.elim (by omega),fun _ => ⟨by simp [GatePhysical],fun _ h => by simp [wires] at h⟩⟩
  | succ n ih =>
    change Sound (if d then packet d j ++ distributed d (j+1) n
      else distributed d (j+1) n ++ packet d j) ↔ _
    have both : (Sound (packet d j) ∧ Sound (distributed d (j+1) n)) ↔
        ∀ (i : Nat), j ≤ i → i < j+(n+1) → Sound (packet d i) := by
      rw [ih]
      refine ⟨fun h i l u => ?_,fun h => ⟨h j (by omega) (by omega),?_⟩⟩
      · by_cases e : j=i
        · exact e ▸ h.1
        · exact h.2 i (by omega) (by omega)
      · exact fun i l u => h i (by omega) (by omega)
    cases d <;> simp only [Bool.false_eq_true,if_false,if_true,app]
    · exact and_comm.trans both
    · exact both

theorem whole (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → Sound (packet d i) := by
  apply (distributed_ok d 1 84).mp
  rw [←distribute]
  exact sound_hostedGroup StairOpenWiring.half760 hostSlots_v3 d 0 1 84 (by decide) (by decide) (by decide) (by decide)

/-- oddten: the field group's own packets are sound (record footprint, odd packets physical). -/
private theorem ot_opk_sound (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) : Sound (opk d k) := by
  by_cases big : 84<k
  · rw [WindowFieldCosts.ot_opk_std d k big]; exact whole d k lo (by omega)
  · refine ⟨?_,good_of_subset (WindowFieldCosts.ot_opk_sub d k) (whole d k lo (by omega)).good⟩
    simp only [opk,StairArchiveInactive.hosts_eq]
    exact gatePhysical_rename _ (Equiv.injective _) _
      (gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _ (WindowFieldCosts.oddPk_physical d k lo (by omega)))

private theorem ot_ogroup_sound (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) : Sound (ogroup d j n) := by
  unfold ogroup
  induction n generalizing j with
  | zero =>
    show Sound []
    exact ⟨by simp [GatePhysical],fun _ h => by simp [wires] at h⟩
  | succ n ih =>
    have head := ot_opk_sound d j lo (by omega)
    have tail := ih (j+1) (by omega) (by omega)
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true]
    · exact sound_append tail head
    · exact sound_append head tail

/-- the fully decoded field-body packets are sound (regular footprint plus the archive tag). -/
private theorem ot_rpk_sound (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) : Sound (rpk d k) := by
  by_cases big : 10≤k
  · refine ⟨?_,?_⟩
    · rw [WindowFieldCosts.rpk_hosted d k big hi]
      exact gatePhysical_rename _ (rawSwap.injective.comp (StairArchiveInactive.host.injective.comp
        (OB5.sig_injective 511 (by decide)))) _ (RouteA.Rolling1588.rawPacket_physical d k (by omega))
    · intro q hq
      rcases Finset.mem_insert.mp (WindowFieldCosts.rpk_sub d k hq) with e|m
      · subst e
        decide
      · exact (ot_opk_sound d k lo hi).good q m
  · rw [WindowFieldCosts.rpk_low d k (by omega)]
    exact ot_opk_sound d k lo hi

private theorem ot_rgroup_sound (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) : Sound (rgroup d j n) := by
  unfold rgroup
  induction n generalizing j with
  | zero =>
    show Sound []
    exact ⟨by simp [GatePhysical],fun _ h => by simp [wires] at h⟩
  | succ n ih =>
    have head := ot_rpk_sound d j lo (by omega)
    have tail := ih (j+1) (by omega) (by omega)
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true]
    · exact sound_append tail head
    · exact sound_append head tail

private theorem ot_pair (d : Bool) (j : Nat) (pick : j∈[10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (lo : 1≤j) (hi : j≤83) :
    Sound (oten j (!d)) := by
  have here := ot_opk_sound d j lo (by omega)
  have next := ot_opk_sound d (j+1) (by omega) (by omega)
  have firstOK : Sound (ofirst j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (osecond j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))

private theorem tagSites_inDom : tagSites.all (fun q => decide (InDom q)) = true := by decide +kernel

theorem packTag_sound : Sound packTag := by
  refine ⟨gatePhysical_rename_support _ _
    (fun a ha b hb eq => tagPort_inj a (Finset.mem_range.mpr (TagPack1542.packTagProg_wires_lt a ha))
      b (Finset.mem_range.mpr (TagPack1542.packTagProg_wires_lt b hb)) eq)
    TagPack1542.packTagProg_physical, ?_⟩
  intro q hq
  rw [packTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.packTagProg_wires_lt x hx
  apply of_decide_eq_true (List.all_eq_true.mp tagSites_inDom _ ?_)
  simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]

theorem unpackTag_sound : Sound unpackTag := by
  refine ⟨gatePhysical_rename_support _ _
    (fun a ha b hb eq => tagPort_inj a (Finset.mem_range.mpr (TagPack1542.unpackTagProg_wires_lt a ha))
      b (Finset.mem_range.mpr (TagPack1542.unpackTagProg_wires_lt b hb)) eq)
    TagPack1542.unpackTagProg_physical, ?_⟩
  intro q hq
  rw [unpackTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.unpackTagProg_wires_lt x hx
  apply of_decide_eq_true (List.all_eq_true.mp tagSites_inDom _ ?_)
  simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]

theorem tagSwap_inDom (q : Wire) (hq : InDom q) : InDom (tagSwap q) :=
  indom_swap _ _ (by decide) (by decide) q hq

theorem group84Body_ok (d : Bool) : Sound (group84Body d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  have c43 := ord (ot_pair d 82 (by decide) (by decide) (by decide)) (ot_rgroup_sound d 84 1 (by decide) (by decide))
  have c42 := ord (ot_rgroup_sound d 81 1 (by decide) (by decide)) c43
  have c41 := ord (ot_pair d 79 (by decide) (by decide) (by decide)) c42
  have c40 := ord (ot_rgroup_sound d 78 1 (by decide) (by decide)) c41
  have c39 := ord (ot_pair d 76 (by decide) (by decide) (by decide)) c40
  have c38 := ord (ot_rgroup_sound d 75 1 (by decide) (by decide)) c39
  have c37 := ord (ot_pair d 73 (by decide) (by decide) (by decide)) c38
  have c36 := ord (ot_rgroup_sound d 72 1 (by decide) (by decide)) c37
  have c35 := ord (ot_pair d 70 (by decide) (by decide) (by decide)) c36
  have c34 := ord (ot_rgroup_sound d 69 1 (by decide) (by decide)) c35
  have c33 := ord (ot_pair d 67 (by decide) (by decide) (by decide)) c34
  have c32 := ord (ot_rgroup_sound d 65 2 (by decide) (by decide)) c33
  have c31 := ord (ot_pair d 63 (by decide) (by decide) (by decide)) c32
  have c30 := ord (ot_rgroup_sound d 61 2 (by decide) (by decide)) c31
  have c29 := ord (ot_pair d 59 (by decide) (by decide) (by decide)) c30
  have c28 := ord (ot_rgroup_sound d 57 2 (by decide) (by decide)) c29
  have c27 := ord (ot_pair d 55 (by decide) (by decide) (by decide)) c28
  have c26 := ord (ot_rgroup_sound d 53 2 (by decide) (by decide)) c27
  have c25 := ord (ot_pair d 51 (by decide) (by decide) (by decide)) c26
  have c24 := ord (ot_rgroup_sound d 49 2 (by decide) (by decide)) c25
  have c23 := ord (ot_pair d 47 (by decide) (by decide) (by decide)) c24
  have c22 := ord (ot_rgroup_sound d 45 2 (by decide) (by decide)) c23
  have c21 := ord (ot_pair d 43 (by decide) (by decide) (by decide)) c22
  have c20 := ord (ot_rgroup_sound d 41 2 (by decide) (by decide)) c21
  have c19 := ord (ot_pair d 39 (by decide) (by decide) (by decide)) c20
  have c18 := ord (ot_rgroup_sound d 37 2 (by decide) (by decide)) c19
  have c17 := ord (ot_pair d 35 (by decide) (by decide) (by decide)) c18
  have c16 := ord (ot_rgroup_sound d 33 2 (by decide) (by decide)) c17
  have c15 := ord (ot_pair d 31 (by decide) (by decide) (by decide)) c16
  have c14 := ord (ot_rgroup_sound d 30 1 (by decide) (by decide)) c15
  have c13 := ord (ot_pair d 28 (by decide) (by decide) (by decide)) c14
  have c12 := ord (ot_rgroup_sound d 27 1 (by decide) (by decide)) c13
  have c11 := ord (ot_pair d 25 (by decide) (by decide) (by decide)) c12
  have c10 := ord (ot_rgroup_sound d 24 1 (by decide) (by decide)) c11
  have c9 := ord (ot_pair d 22 (by decide) (by decide) (by decide)) c10
  have c8 := ord (ot_rgroup_sound d 21 1 (by decide) (by decide)) c9
  have c7 := ord (ot_pair d 19 (by decide) (by decide) (by decide)) c8
  have c6 := ord (ot_rgroup_sound d 18 1 (by decide) (by decide)) c7
  have c5 := ord (ot_pair d 16 (by decide) (by decide) (by decide)) c6
  have c4 := ord (ot_rgroup_sound d 15 1 (by decide) (by decide)) c5
  have c3 := ord (ot_pair d 13 (by decide) (by decide) (by decide)) c4
  have c2 := ord (ot_rgroup_sound d 12 1 (by decide) (by decide)) c3
  exact ord (ot_pair d 10 (by decide) (by decide) (by decide)) c2

theorem group84_ok (d : Bool) : Sound (group84 d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  have hbody : Sound (renameProgram tagSwap (group84Body d)) :=
    sound_rename tagSwap tagSwap.injective tagSwap_inDom (group84Body_ok d)
  exact ord (ot_ogroup_sound d 1 9 (by decide) (by decide))
    (sound_append (sound_append packTag_sound hbody) unpackTag_sound)

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet

private theorem distributed_ok43 (d : Bool) (j n : Nat) :
    PieceOK Stair44FieldSites.holes TP (distributed d j n) ↔
    ∀ (i : Nat), j ≤ i → i < j+n → PieceOK Stair44FieldSites.holes TP (packet d i) := by
  induction n generalizing j with
  | zero =>
    change PieceOK _ _ [] ↔ _
    exact ⟨fun _ i lo hi => False.elim (by omega),fun _ => pieceOK_nil _ _⟩
  | succ n ih =>
    change PieceOK _ _ (if d then packet d j ++ distributed d (j+1) n
      else distributed d (j+1) n ++ packet d j) ↔ _
    have both : (PieceOK Stair44FieldSites.holes TP (packet d j) ∧ PieceOK Stair44FieldSites.holes TP (distributed d (j+1) n)) ↔
        ∀ (i : Nat), j ≤ i → i < j+(n+1) → PieceOK Stair44FieldSites.holes TP (packet d i) := by
      rw [ih]
      refine ⟨fun h i l u => ?_,fun h => ⟨h j (by omega) (by omega),?_⟩⟩
      · by_cases e : j=i
        · exact e ▸ h.1
        · exact h.2 i (by omega) (by omega)
      · exact fun i l u => h i (by omega) (by omega)
    cases d <;> simp only [Bool.false_eq_true,if_false,if_true,app]
    · exact and_comm.trans both
    · exact both

theorem whole43 (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → PieceOK Stair44FieldSites.holes TP (packet d i) := by
  apply (distributed_ok43 d 1 84).mp
  rw [←distribute]
  exact Stair44Groups.hostedGroup44 d 0 1 84 (by decide)

theorem ordinary43 (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK Stair44FieldSites.holes TP (group d j n) := by
  rw [group,distribute,distributed_ok43]
  exact fun i l u => whole43 d i (by omega) (by omega)

theorem pair43 (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) :
    PieceOK Stair44FieldSites.holes TP (ten j (!d)) := by
  have jmem : j∈List.range' 1 83 := List.mem_range'_1.mpr ⟨lo,by omega⟩
  have here := whole43 d j lo (by omega)
  have next := whole43 d (j+1) (by omega) (by omega)
  have firstOK : PieceOK Stair44FieldSites.holes TP (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : PieceOK Stair44FieldSites.holes TP (second j (!d)) := by cases d <;> first | exact here | exact next
  exact (hook43 j jmem _).append (firstOK.append ((hook43 j jmem _).append (lastOK.append (hook43 j jmem _))))


-- oddten:begin SITES
private theorem ot_ogroup_piece43 (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK Stair44FieldSites.holes TP (ogroup d j n) := by
  have hrec := ordinary43 d j n lo hi
  exact ⟨fun x hx => hrec.1 x (WindowFieldCosts.ot_ogroup_sub d j n hx),
    fun x hx => hrec.2 x (WindowFieldCosts.ot_ogroup_sub d j n hx)⟩

private theorem ot_oten_piece43 (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) :
    PieceOK Stair44FieldSites.holes TP (oten j (!d)) := by
  have hrec := pair43 d j lo hi
  exact ⟨fun x hx => hrec.1 x (WindowFieldCosts.ot_oten_sub j (!d) hx),
    fun x hx => hrec.2 x (WindowFieldCosts.ot_oten_sub j (!d) hx)⟩

private theorem tag720_piece : TP (base 720)∈StairHoleSupport.recordArena ∧
    TP (base 720)∉StairHoleSupport.oldHoles ∧ TP (base 720)∉Stair44FieldSites.holes := by
  have e : TP (base 720)=4835 := by
    change StairOuterPlacement.outerPlace _=_
    rw [StairPlaceFast.outerPlace_eqB]
    decide +kernel
  rw [e]
  exact tagOK

private theorem ot_rgroup_piece43 (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK Stair44FieldSites.holes TP (rgroup d j n) := by
  have hrec := ot_ogroup_piece43 d j n lo hi
  refine ⟨fun x hx => ?_,fun x hx => ?_⟩
  · rcases Finset.mem_insert.mp (WindowFieldCosts.rgroup_sub d j n hx) with e|m
    · subst e
      exact ⟨tag720_piece.1,tag720_piece.2.1⟩
    · exact hrec.1 x m
  · rcases Finset.mem_insert.mp (WindowFieldCosts.rgroup_sub d j n hx) with e|m
    · subst e
      exact tag720_piece.2.2
    · exact hrec.2 x m

private theorem tagSites_fit :
    tagSites.all (fun q => Stair44OuterSites.fit (StairPlaceFast.outerPlaceB q)) = true := by
  decide +kernel

theorem packTag_ok : PieceOK reserved TP packTag := by
  apply Stair44OuterSites.fits
  intro q hq
  rw [packTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.packTagProg_wires_lt x hx
  have hmem : tagPort x ∈ tagSites := by
    simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  change Stair44OuterSites.fit (StairOuterPlacement.outerPlace (tagPort x)) = true
  rw [StairPlaceFast.outerPlace_eqB]
  exact List.all_eq_true.mp tagSites_fit _ hmem

theorem unpackTag_ok : PieceOK reserved TP unpackTag := by
  apply Stair44OuterSites.fits
  intro q hq
  rw [unpackTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.unpackTagProg_wires_lt x hx
  have hmem : tagPort x ∈ tagSites := by
    simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  change Stair44OuterSites.fit (StairOuterPlacement.outerPlace (tagPort x)) = true
  rw [StairPlaceFast.outerPlace_eqB]
  exact List.all_eq_true.mp tagSites_fit _ hmem

private theorem sLetter435_fit :
    Stair44OuterSites.fit (StairPlaceFast.outerPlaceB (StairPhysicalLayout.sLetter 435)) = true := by
  decide +kernel

private theorem packet_avoids_wire (w : Wire)
    (hchk : (List.range' 1 84).all (fun k => !(StairArchiveInactive.cover k).contains (StairArchiveInactive.preimage k w)) = true)
    (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    w ∉ wires (packet d k) := by
  intro hw
  have yes := StairArchiveInactive.original d k (by omega) hw
  have no := List.all_eq_true.mp hchk k (List.mem_range'_1.mpr ⟨lo, by omega⟩)
  simp [yes] at no

/-- Off the placement's zero region, the archive preimage of a wire does not depend on the packet. -/
theorem preimage_const (k : Nat) (hk : k < 102) (q : Wire)
    (h16 : 16 ≤ OB5.sig 511 (StairArchiveInactive.host.symm q))
    (hw : ¬ Placement5.workRegion (OB5.sig 511 (StairArchiveInactive.host.symm q) - 16))
    (hh : ¬ Placement5.holeRegion (OB5.sig 511 (StairArchiveInactive.host.symm q) - 16)) :
    StairArchiveInactive.preimage k q = OB5.sig 511 (StairArchiveInactive.host.symm q) := by
  unfold StairArchiveInactive.preimage
  generalize OB5.sig 511 (StairArchiveInactive.host.symm q) = x at h16 hw hh ⊢
  apply (Equiv.symm_apply_eq (shifted (Placement5.pi k))).mpr
  have hx : x = base (x - 16) := by simp only [base, Wire] at *; omega
  rw [hx, shifted_base, Placement5.pi_outside k _ hk (fun h => h.elim hw hh)]

/-- Both archive-tag wires at once (also reused by `WindowFieldView.tagged`): their preimages are
packet-independent (`preimage_const`), so the kernel evaluates each preimage once. -/
theorem opk_both_chk : (List.range' 1 84).all (fun k =>
    !(StairArchiveInactive.cover k).contains (StairArchiveInactive.preimage k (base 720)) &&
    !(StairArchiveInactive.cover k).contains
      (StairArchiveInactive.preimage k (StairPhysicalLayout.sLetter 435))) = true := by
  have c := (by decide +kernel :
    (let x := OB5.sig 511 (StairArchiveInactive.host.symm (base 720))
     let y := OB5.sig 511 (StairArchiveInactive.host.symm (StairPhysicalLayout.sLetter 435))
     let fc := [base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base
     decide (16 ≤ x) && !decide (Placement5.workRegion (x - 16)) && !decide (Placement5.holeRegion (x - 16)) &&
     decide (16 ≤ y) && !decide (Placement5.workRegion (y - 16)) && !decide (Placement5.holeRegion (y - 16)) &&
     !fc.contains x && !fc.contains y &&
     (List.range' 1 84).all (fun k => (List.finRange 10).all (fun j =>
       History5.historyMap base (5 * k) j != x && History5.historyMap base (5 * k) j != y))) = true)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at c
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hx16, hxw⟩, hxh⟩, hy16⟩, hyw⟩, hyh⟩, hfx⟩, hfy⟩, hall⟩ := c
  have key : ∀ k z, ([base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base).contains z = false →
      (∀ j ∈ List.finRange 10, History5.historyMap base (5 * k) j ≠ z) →
      (!(StairArchiveInactive.cover k).contains z) = true := by
    intro k z hf hj
    simp only [Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hc
    have hm := List.contains_iff_mem.mp hc
    simp only [StairArchiveInactive.cover, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact Bool.noConfusion (hf.symm.trans (List.contains_iff_mem.mpr (List.mem_append_left _ hm)))
    · exact Bool.noConfusion (hf.symm.trans (List.contains_iff_mem.mpr (List.mem_append_right _ hm)))
    · obtain ⟨j, hjm, hje⟩ := List.mem_map.mp hm
      exact hj j hjm hje
  rw [List.all_eq_true] at hall ⊢
  intro k hk
  have hk' := List.mem_range'_1.mp hk
  have hh := List.all_eq_true.mp (hall k hk)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
  rw [preimage_const k (by omega) _ hx16 hxw hxh, preimage_const k (by omega) _ hy16 hyw hyh,
    Bool.and_eq_true]
  exact ⟨key k _ hfx (fun j hj => (hh j hj).1), key k _ hfy (fun j hj => (hh j hj).2)⟩

private theorem opk_avoids_720 (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    base 720 ∉ wires (opk d k) :=
  fun hw => packet_avoids_wire (base 720)
    (List.all_eq_true.mpr fun j hj => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp opk_both_chk j hj)).1)
    d k lo hi (WindowFieldCosts.ot_opk_sub d k hw)

private theorem opk_avoids_435 (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    StairPhysicalLayout.sLetter 435 ∉ wires (opk d k) :=
  fun hw => packet_avoids_wire (StairPhysicalLayout.sLetter 435)
    (List.all_eq_true.mpr fun j hj => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp opk_both_chk j hj)).2)
    d k lo hi (WindowFieldCosts.ot_opk_sub d k hw)

private theorem ogroup_avoids_wire (w : Wire)
    (hpk : ∀ k, 1 ≤ k → k ≤ 84 → w ∉ wires (opk d k))
    (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    w ∉ wires (ogroup d j n) := by
  unfold ogroup
  induction n generalizing j with
  | zero => intro h; simp [PacketSequence.program, wires] at h
  | succ n ih =>
    intro h
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      wires_append, Finset.mem_union] at h
    · rcases h with h1 | h2
      · exact ih (j + 1) (by omega) (by omega) h1
      · exact hpk j lo (by omega) h2
    · rcases h with h1 | h2
      · exact hpk j lo (by omega) h1
      · exact ih (j + 1) (by omega) (by omega) h2

private theorem fieldHook_avoids_435_chk :
    WindowBankCheck.banks.all (fun j =>
      (StairArchiveRelease.fieldSites j).all (fun q => q != StairPhysicalLayout.sLetter 435)) = true := by
  decide +kernel

private theorem fieldHook_avoids_435 (j : Nat)
    (hj : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (op : StairArchiveRelease.Stage) :
    StairPhysicalLayout.sLetter 435 ∉ wires (StairArchiveRelease.fieldHook j op) := by
  have hchk : (StairArchiveRelease.fieldSites j).all (fun q => q != StairPhysicalLayout.sLetter 435) = true :=
    List.all_eq_true.mp fieldHook_avoids_435_chk j hj
  have hspan : j ∈ List.range' 1 83 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    apply List.mem_range'_1.mpr; omega
  intro hw
  rw [StairArchiveRelease.fieldHook, renameProgram_support] at hw
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hw
  have len : (StairArchiveRelease.fieldSites j).length = 121 := by
    have hh := (ArchiveFieldScratch.layout_frame j hspan).2
    rwa [← StairArchiveRelease.field_layout, List.length_map] at hh
  have lt : x < (StairArchiveRelease.fieldSites j).length :=
    len ▸ (Finset.mem_range.mp (StairArchiveRelease.sub op hx))
  have hmem : StairArchiveRelease.fieldPort j x ∈ StairArchiveRelease.fieldSites j := by
    simp only [StairArchiveRelease.fieldPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  have hne := List.all_eq_true.mp hchk _ hmem
  rw [hxeq] at hne
  simp at hne

private theorem oten_avoids_435 (d : Bool) (j : Nat)
    (hj : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (lo : 1 ≤ j) (hi : j ≤ 83) :
    StairPhysicalLayout.sLetter 435 ∉ wires (oten j (!d)) := by
  intro h
  simp only [oten, wires_append, Finset.mem_union] at h
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact fieldHook_avoids_435 j hj _ h1
  · cases d <;> simp only [ofirst, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h2
    · exact opk_avoids_435 false (j + 1) (by omega) (by omega) h2
    · exact opk_avoids_435 true j lo (by omega) h2
  · exact fieldHook_avoids_435 j hj _ h3
  · cases d <;> simp only [osecond, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h4
    · exact opk_avoids_435 false j lo (by omega) h4
    · exact opk_avoids_435 true (j + 1) (by omega) (by omega) h4
  · exact fieldHook_avoids_435 j hj _ h5

private theorem group84Body_ok43_and_avoids435 (d : Bool) :
    PieceOK Stair44FieldSites.holes TP (group84Body d) ∧
    StairPhysicalLayout.sLetter 435 ∉ wires (group84Body d) := by
  have ord {a b : Program}
      (ha : PieceOK Stair44FieldSites.holes TP a ∧ StairPhysicalLayout.sLetter 435 ∉ wires a)
      (hb : PieceOK Stair44FieldSites.holes TP b ∧ StairPhysicalLayout.sLetter 435 ∉ wires b) :
      PieceOK Stair44FieldSites.holes TP (ordered d a b) ∧ StairPhysicalLayout.sLetter 435 ∉ wires (ordered d a b) := by
    cases d <;> simp only [ordered, if_true, if_false, Bool.false_eq_true, wires_append, Finset.mem_union]
    · exact ⟨hb.1.append ha.1, fun h => h.elim hb.2 ha.2⟩
    · exact ⟨ha.1.append hb.1, fun h => h.elim ha.2 hb.2⟩
  have ot (j : Nat) (hj : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (lo : 1 ≤ j) (hi : j ≤ 83) :
      PieceOK Stair44FieldSites.holes TP (oten j (!d)) ∧ StairPhysicalLayout.sLetter 435 ∉ wires (oten j (!d)) :=
    ⟨ot_oten_piece43 d j lo hi, oten_avoids_435 d j hj lo hi⟩
  have og (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
      PieceOK Stair44FieldSites.holes TP (rgroup d j n) ∧ StairPhysicalLayout.sLetter 435 ∉ wires (rgroup d j n) :=
    ⟨ot_rgroup_piece43 d j n lo hi, rgroup_avoids d (StairPhysicalLayout.sLetter 435) j n (by decide +kernel)
      (ogroup_avoids_wire (StairPhysicalLayout.sLetter 435) (opk_avoids_435 d) j n lo hi)⟩
  have c43 := ord (ot 82 (by decide) (by decide) (by decide)) (og 84 1 (by decide) (by decide))
  have c42 := ord (og 81 1 (by decide) (by decide)) c43
  have c41 := ord (ot 79 (by decide) (by decide) (by decide)) c42
  have c40 := ord (og 78 1 (by decide) (by decide)) c41
  have c39 := ord (ot 76 (by decide) (by decide) (by decide)) c40
  have c38 := ord (og 75 1 (by decide) (by decide)) c39
  have c37 := ord (ot 73 (by decide) (by decide) (by decide)) c38
  have c36 := ord (og 72 1 (by decide) (by decide)) c37
  have c35 := ord (ot 70 (by decide) (by decide) (by decide)) c36
  have c34 := ord (og 69 1 (by decide) (by decide)) c35
  have c33 := ord (ot 67 (by decide) (by decide) (by decide)) c34
  have c32 := ord (og 65 2 (by decide) (by decide)) c33
  have c31 := ord (ot 63 (by decide) (by decide) (by decide)) c32
  have c30 := ord (og 61 2 (by decide) (by decide)) c31
  have c29 := ord (ot 59 (by decide) (by decide) (by decide)) c30
  have c28 := ord (og 57 2 (by decide) (by decide)) c29
  have c27 := ord (ot 55 (by decide) (by decide) (by decide)) c28
  have c26 := ord (og 53 2 (by decide) (by decide)) c27
  have c25 := ord (ot 51 (by decide) (by decide) (by decide)) c26
  have c24 := ord (og 49 2 (by decide) (by decide)) c25
  have c23 := ord (ot 47 (by decide) (by decide) (by decide)) c24
  have c22 := ord (og 45 2 (by decide) (by decide)) c23
  have c21 := ord (ot 43 (by decide) (by decide) (by decide)) c22
  have c20 := ord (og 41 2 (by decide) (by decide)) c21
  have c19 := ord (ot 39 (by decide) (by decide) (by decide)) c20
  have c18 := ord (og 37 2 (by decide) (by decide)) c19
  have c17 := ord (ot 35 (by decide) (by decide) (by decide)) c18
  have c16 := ord (og 33 2 (by decide) (by decide)) c17
  have c15 := ord (ot 31 (by decide) (by decide) (by decide)) c16
  have c14 := ord (og 30 1 (by decide) (by decide)) c15
  have c13 := ord (ot 28 (by decide) (by decide) (by decide)) c14
  have c12 := ord (og 27 1 (by decide) (by decide)) c13
  have c11 := ord (ot 25 (by decide) (by decide) (by decide)) c12
  have c10 := ord (og 24 1 (by decide) (by decide)) c11
  have c9 := ord (ot 22 (by decide) (by decide) (by decide)) c10
  have c8 := ord (og 21 1 (by decide) (by decide)) c9
  have c7 := ord (ot 19 (by decide) (by decide) (by decide)) c8
  have c6 := ord (og 18 1 (by decide) (by decide)) c7
  have c5 := ord (ot 16 (by decide) (by decide) (by decide)) c6
  have c4 := ord (og 15 1 (by decide) (by decide)) c5
  have c3 := ord (ot 13 (by decide) (by decide) (by decide)) c4
  have c2 := ord (og 12 1 (by decide) (by decide)) c3
  exact ord (ot 10 (by decide) (by decide) (by decide)) c2

private theorem newHolesNat_sub_43_or_4835 :
    StairPhysicalLayout.newHolesNat.all (fun v => decide (v ∈ Stair44FieldSites.holes) || (v == 4835)) = true := by
  decide +kernel

private theorem sw_in_range {a b z lo hi : Nat}
    (h : lo ≤ StairPlaceFast.sw a b z ∧ StairPlaceFast.sw a b z ≤ hi)
    (ha : ¬(lo ≤ a ∧ a ≤ hi)) (hb : ¬(lo ≤ b ∧ b ≤ hi)) :
    StairPlaceFast.sw a b z = z := by
  unfold StairPlaceFast.sw at h ⊢
  by_cases h1 : z = a
  · rw [if_pos h1] at h; omega
  · by_cases h2 : z = b
    · rw [if_neg h1, if_pos h2] at h; omega
    · rw [if_neg h1, if_neg h2]

private theorem metaN_not_4835_4839 (j : Nat) :
    ¬(4835 ≤ StairPlaceFast.metaN j ∧ StairPlaceFast.metaN j ≤ 4839) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => decide
  | j + 12 => unfold StairPlaceFast.metaN; simp

private theorem pwN_window (i : Nat)
    (h : 4835 ≤ StairPlaceFast.pwN i ∧ StairPlaceFast.pwN i ≤ 4839) :
    720 ≤ i ∧ i ≤ 724 ∧ StairPlaceFast.pwN i = 4115 + i := by
  unfold StairPlaceFast.pwN at h ⊢
  by_cases h1 : i < 2314
  · rw [if_pos h1] at h ⊢
    by_cases h2 : 770 ≤ i ∧ i < 1026
    · rw [if_pos h2] at h; omega
    · rw [if_neg h2] at h ⊢
      by_cases h3 : 2056 ≤ i ∧ i < 2312
      · rw [if_pos h3] at h; omega
      · rw [if_neg h3] at h ⊢
        by_cases h4 : 1026 ≤ i <;> by_cases h5 : 2312 ≤ i
        · rw [if_pos h4, if_pos h5] at h; omega
        · rw [if_pos h4, if_neg h5] at h; omega
        · rw [if_neg h4, if_pos h5] at h; omega
        · rw [if_neg h4, if_neg h5] at h ⊢; omega
  · rw [if_neg h1] at h
    exact (metaN_not_4835_4839 (i - 2400) h).elim

private theorem outerPlace_in_4835_4839 (x : Wire)
    (h : 4835 ≤ StairOuterPlacement.outerPlace x ∧ StairOuterPlacement.outerPlace x ≤ 4839) :
    x = StairOuterPlacement.outerPlace x - 4835 + 736 := by
  rw [StairPlaceFast.outerPlace_eqN] at h ⊢
  unfold StairPlaceFast.outerPlaceN StairPlaceFast.kernelPlaceN at h ⊢
  have s1 := sw_in_range h (by omega) (by omega); rw [s1] at h ⊢
  have s2 := sw_in_range h (by omega) (by omega); rw [s2] at h ⊢
  have s3 := sw_in_range h (by omega) (by omega); rw [s3] at h ⊢
  have s4 := sw_in_range h (by omega) (by omega); rw [s4] at h ⊢
  have s5 := sw_in_range h (by omega) (by omega); rw [s5] at h ⊢
  have s6 := sw_in_range h (by omega) (by omega); rw [s6] at h ⊢
  have s7 := sw_in_range h (by omega) (by omega); rw [s7] at h ⊢
  have hpw := pwN_window (StairPlaceFast.sw 785 1813 (StairPlaceFast.fieldPlaceN x) - 16) h
  rw [hpw.2.2]
  have hfp : 736 ≤ StairPlaceFast.sw 785 1813 (StairPlaceFast.fieldPlaceN x) ∧
      StairPlaceFast.sw 785 1813 (StairPlaceFast.fieldPlaceN x) ≤ 740 := by omega
  have hsw0 := sw_in_range hfp (by omega) (by omega)
  rw [hsw0] at hfp ⊢
  unfold StairPlaceFast.fieldPlaceN at hfp ⊢
  have hsw1 := sw_in_range hfp (by omega) (by omega); rw [hsw1] at hfp ⊢
  have hsw2 := sw_in_range hfp (by omega) (by omega); rw [hsw2] at hfp ⊢
  have hsw3 := sw_in_range hfp (by omega) (by omega); rw [hsw3] at hfp ⊢
  have hsw4 := sw_in_range hfp (by omega) (by omega); rw [hsw4] at hfp ⊢
  dsimp only [Wire] at *
  omega

private theorem upgrade44_of_avoids_720 {P : Program}
    (h43 : PieceOK Stair44FieldSites.holes TP P)
    (hdom : ∀ x ∈ wires P, x < 2428)
    (h720 : base 720 ∉ wires P) :
    PieceOK reserved TP P := by
  have _ := hdom
  refine ⟨h43.1, fun x hx bad => ?_⟩
  rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat] at bad
  have hmem := List.all_eq_true.mp newHolesNat_sub_43_or_4835 (TP x) bad
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hmem
  rcases hmem with h43b | h4835
  · exact h43.2 x hx h43b
  · have h1 : x = base 720 := by
      have h4835' : StairOuterPlacement.outerPlace x = 4835 := h4835
      have hxeq := outerPlace_in_4835_4839 x ⟨Nat.le_of_eq h4835'.symm, Nat.le_trans (Nat.le_of_eq h4835') (by decide)⟩
      dsimp only [base, Wire] at *
      omega
    exact h720 (h1 ▸ hx)

private theorem lt_2428_of_inDom {x : Wire} (h : StairRestSupport.InDom x) : x < 2428 := by
  unfold StairRestSupport.InDom StairRestSupport.InDomN at h
  dsimp only [Wire] at *
  omega

theorem group84_ok (d : Bool) : PieceOK reserved TP (group84 d) := by
  have ord {a b : Program} (ha : PieceOK reserved TP a) (hb : PieceOK reserved TP b) :
      PieceOK reserved TP (ordered d a b) := by cases d <;> first | exact ha.append hb | exact hb.append ha
  have h19 : PieceOK reserved TP (ogroup d 1 9) :=
    upgrade44_of_avoids_720 (ot_ogroup_piece43 d 1 9 (by decide) (by decide))
      (fun x hx => lt_2428_of_inDom ((WindowPhysical.ot_ogroup_sound d 1 9 (by decide) (by decide)).good x hx))
      (ogroup_avoids_wire (base 720) (opk_avoids_720 d) 1 9 (by decide) (by decide))
  have ⟨hb43, hb435⟩ := group84Body_ok43_and_avoids435 d
  have h435_ok : TP (StairPhysicalLayout.sLetter 435) ∈ StairHoleSupport.recordArena ∧
      TP (StairPhysicalLayout.sLetter 435) ∉ StairHoleSupport.oldHoles ∧
      TP (StairPhysicalLayout.sLetter 435) ∉ reserved := by
    have hf := sLetter435_fit
    rw [← StairPlaceFast.outerPlace_eqB] at hf
    exact singleton_ok hf
  have hbody : PieceOK reserved TP (renameProgram tagSwap (group84Body d)) := by
    rw [ren]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · dsimp only
      by_cases hx720 : x = base 720
      · subst hx720
        have heq : tagSwap (base 720) = StairPhysicalLayout.sLetter 435 := Equiv.swap_apply_left _ _
        rw [heq]
        exact ⟨h435_ok.1, h435_ok.2.1⟩
      · have hx435 : x ≠ StairPhysicalLayout.sLetter 435 := fun h => hb435 (h ▸ hx)
        rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hx720 hx435]
        exact hb43.1 x hx
    · dsimp only
      by_cases hx720 : x = base 720
      · subst hx720
        have heq : tagSwap (base 720) = StairPhysicalLayout.sLetter 435 := Equiv.swap_apply_left _ _
        rw [heq]
        exact h435_ok.2.2
      · have hx435 : x ≠ StairPhysicalLayout.sLetter 435 := fun h => hb435 (h ▸ hx)
        rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hx720 hx435]
        intro bad
        rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat] at bad
        have hmem := List.all_eq_true.mp newHolesNat_sub_43_or_4835 (TP x) bad
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hmem
        rcases hmem with h43b | h4835
        · exact hb43.2 x hx h43b
        · have h1 : x = base 720 := by
            have h4835' : StairOuterPlacement.outerPlace x = 4835 := h4835
            have hxeq := outerPlace_in_4835_4839 x ⟨Nat.le_of_eq h4835'.symm, Nat.le_trans (Nat.le_of_eq h4835') (by decide)⟩
            dsimp only [base, Wire] at *
            omega
          exact hx720 h1
  exact ord h19 ((packTag_ok.append hbody).append unpackTag_ok)

end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

open Arithmetic MappedCompressed StairArchiveInactive StairArchiveRelease RecordedQuantum
open StairArchiveNativeCut StairArchiveTen
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires run opk rpk fieldHook

theorem signHost_ne_tag : signHost ≠ base 720 := by decide +kernel

theorem packet_avoids_sign (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    signHost ∉ wires (packet d k) := by
  intro used
  have pre_eq : preimage k signHost = signHost := by
    rw [WindowSites.preimage_const k (by omega) signHost (by decide +kernel)
      (by decide +kernel) (by decide +kernel)]
    decide +kernel
  have admissible := StairArchiveInactive.original d k (by omega) used
  rw [pre_eq] at admissible
  have check : (List.range' 1 84).all (fun j => !(cover j).contains signHost) = true := by
    decide +kernel
  have out := List.all_eq_true.mp check k (List.mem_range'_1.mpr ⟨lo, by omega⟩)
  simp [admissible] at out

theorem opk_avoids_sign (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    signHost ∉ wires (opk d k) :=
  fun used => packet_avoids_sign d k lo hi (ot_opk_sub d k used)

theorem spk_sub (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    wires (spk d k) ⊆ insert signHost (wires (opk d k)) := by
  rw [spk, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (rpk_sub d k hw) with h | h
  · subst w
    rw [Equiv.swap_apply_left]
    exact Finset.mem_insert_self _ _
  · have ht : w ≠ base 720 := fun he => opk_avoid720 d k lo hi (he ▸ h)
    have hs : w ≠ signHost := fun he => opk_avoids_sign d k lo hi (he ▸ h)
    rw [Equiv.swap_apply_of_ne_of_ne ht hs]
    exact Finset.mem_insert_of_mem h

theorem spk_physical (d : Bool) (k : Nat) (lo : 10 ≤ k) (hi : k ≤ 84) :
    GatePhysical (spk d k) := by
  rw [spk, rpk_hosted d k lo hi]
  exact gatePhysical_rename _ (Equiv.swap _ _).injective _
    (gatePhysical_rename _ (rawSwap.injective.comp
      (StairArchiveInactive.host.injective.comp (OB5.sig_injective 511 (by decide)))) _
      (RouteA.Rolling1588.rawPacket_physical d k (by omega)))

section
attribute [local irreducible] gpk

theorem epk_sub (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    wires (epk d k) ⊆ insert signHost (wires (opk d k)) := by
  rw [epk, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (gpk_sub d k lo hi hw) with h | h
  · subst w
    rw [Equiv.swap_apply_left]
    exact Finset.mem_insert_self _ _
  · have ht : w ≠ base 720 := fun he => opk_avoid720 d k lo hi (he ▸ h)
    have hs : w ≠ signHost := fun he => opk_avoids_sign d k lo hi (he ▸ h)
    rw [Equiv.swap_apply_of_ne_of_ne ht hs]
    exact Finset.mem_insert_of_mem h

theorem epk_physical (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    GatePhysical (epk d k) := by
  rw [epk, gpk_hosted d k]
  exact gatePhysical_rename _ (Equiv.swap _ _).injective _
    (gatePhysical_rename _ (rawSwap.injective.comp
      (StairArchiveInactive.host.injective.comp (OB5.sig_injective 511 (by decide)))) _
      (RouteA.Rolling1588.rawPacket_physical d k (by omega)))

theorem egroup_sub (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    wires (egroup d j n) ⊆ insert signHost (wires (ogroup d j n)) := by
  unfold egroup ogroup
  induction n generalizing j with
  | zero =>
    intro q hq
    simp [PacketSequence.program, wires] at hq
  | succ n ih =>
    have head := epk_sub d j lo (by omega)
    have tail := ih (j + 1) (by omega) (by omega)
    intro q hq
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      wires_append, Finset.mem_union, Finset.mem_insert] at hq ⊢
    · rcases hq with h | h
      · have := Finset.mem_insert.mp (tail h); tauto
      · have := Finset.mem_insert.mp (head h); tauto
    · rcases hq with h | h
      · have := Finset.mem_insert.mp (head h); tauto
      · have := Finset.mem_insert.mp (tail h); tauto

theorem egroup_physical (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    GatePhysical (egroup d j n) := by
  unfold egroup
  induction n generalizing j with
  | zero => simp [PacketSequence.program, GatePhysical]
  | succ n ih =>
    have head := epk_physical d j lo (by omega)
    have tail := ih (j + 1) (by omega) (by omega)
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      gatePhysical_append]
    · exact ⟨tail, head⟩
    · exact ⟨head, tail⟩

end

theorem hook_avoids_sign (j : Nat) (hj : j ∈ WindowBankCheck.banks) (op : Stage) :
    signHost ∉ wires (fieldHook j op) := by
  intro used
  rw [fieldHook, renameProgram_support] at used
  obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp used
  have inRange : j ∈ List.range' 1 83 := by
    simp only [WindowBankCheck.banks, List.mem_cons, List.not_mem_nil, or_false] at hj
    exact List.mem_range'_1.mpr (by omega)
  have len : (fieldSites j).length = 121 := by
    have h := (ArchiveFieldScratch.layout_frame j inRange).2
    rwa [← field_layout, List.length_map] at h
  have lt : i < (fieldSites j).length := len ▸ Finset.mem_range.mp (StairArchiveRelease.sub op hi)
  have hmem : fieldPort j i ∈ fieldSites j := by
    simp only [fieldPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  have check : WindowBankCheck.banks.all
      (fun b => !(fieldSites b).contains signHost) = true := by decide +kernel
  have out := List.all_eq_true.mp check j hj
  rw [eq] at hmem
  simp [hmem] at out

private theorem xorIntoSign_sub (xs : List Wire) :
    wires (xorIntoSign xs) ⊆ insert signHost xs.toFinset := by
  induction xs with
  | nil => simp [xorIntoSign, wires]
  | cons x xs ih =>
    intro q hq
    rw [xorIntoSign, List.map_cons, wires] at hq
    rcases Finset.mem_union.mp hq with h | h
    · simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at h
      simp only [List.toFinset_cons, Finset.mem_insert]
      exact h.elim (fun he => Or.inr (Or.inl he)) Or.inl
    · exact (Finset.mem_insert.mp (ih h)).elim
        (fun he => Finset.mem_insert.mpr (Or.inl he))
        (fun hu => Finset.mem_insert_of_mem
          (List.mem_toFinset.mpr (List.mem_cons_of_mem x (List.mem_toFinset.mp hu))))

theorem prefixLoanPort_mem (i : Nat) (hi : i < 12) : prefixLoanPort i ∈ tagSites := by
  have h : ∀ k : Fin 12, prefixLoanPort k ∈ tagSites := by decide +kernel
  exact h ⟨i, hi⟩

theorem signBracket_sub :
    wires signBracket ⊆ insert signHost (tagSites.toFinset ∪ signPayload.toFinset) := by
  have renSub (P : Program) (hp : wires P ⊆ Finset.range 12) :
      wires (renameProgram prefixLoanPort P) ⊆ tagSites.toFinset := by
    intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact List.mem_toFinset.mpr (prefixLoanPort_mem i (Finset.mem_range.mp (hp hi)))
  have px : (prefixDataPorts.map prefixLoanPort).toFinset ⊆ tagSites.toFinset := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have hlt : ∀ n ∈ prefixDataPorts, n < 12 := by decide +kernel
    exact List.mem_toFinset.mpr (prefixLoanPort_mem i (hlt i hi))
  intro q hq
  simp only [signBracket, prefixParity, wires_append, Finset.mem_union] at hq
  simp only [Finset.mem_insert, Finset.mem_union]
  rcases hq with ((a | b) | c) | d
  · exact Or.inr (Or.inl (renSub _ FourScratchPrefix.support.2.2 a))
  · exact (Finset.mem_insert.mp (xorIntoSign_sub _ b)).elim Or.inl (fun h => Or.inr (Or.inl (px h)))
  · exact Or.inr (Or.inl (renSub _ FourScratchPrefix.support.2.1 c))
  · exact (Finset.mem_insert.mp (xorIntoSign_sub _ d)).elim Or.inl (fun h => Or.inr (Or.inr h))

private def signPayloadBand (q : Wire) : Prop :=
  (21 ≤ q ∧ q < 441) ∨ (1049 ≤ q ∧ q < 1301) ∨ (1645 ≤ q ∧ q < 1813)

private theorem sign_rebinder_fix : ∀ (rs hs : List Wire) (x : Wire), x ∉ rs → x ∉ hs →
    StairArchiveInactive.rebinder rs hs x = x
  | r :: rs, h :: hs, x, hr, hh => by
    simp only [List.mem_cons, not_or] at hr hh
    simp only [StairArchiveInactive.rebinder, Equiv.trans_apply]
    rw [sign_rebinder_fix rs hs x hr.2 hh.2]
    exact Equiv.swap_apply_of_ne_of_ne hr.1 hh.1
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl

private theorem signPayload_raw_band (k : Nat) (hk : k ∈ List.range' 1 84) (i : Fin 8) :
    signPayloadBand (OB5.sig 511 (History5.historyMap base (5 * k) (NewHistory5.payloadPort i))) := by
  have hk' := List.mem_range'_1.mp hk
  have hi := (NewHistory5.payloadPort i).isLt
  unfold OB5.sig History5.historyMap History5.historyId signPayloadBand
  simp only [MappedCompressed.base, Wire]
  split_ifs <;> omega

private theorem signPayload_host_fix (k : Nat) (hk : k ∈ List.range' 1 84) (i : Fin 8) :
    let x := OB5.sig 511 (History5.historyMap base (5 * k) (NewHistory5.payloadPort i))
    StairArchiveInactive.host x = x := by
  let x := OB5.sig 511 (History5.historyMap base (5 * k) (NewHistory5.payloadPort i))
  have bound : signPayloadBand x := signPayload_raw_band k hk i
  have roles : x ∉ StairSchedule.exclusiveRoles := by
    intro h
    simp only [StairWireCheck.exclusiveRoles_eq_nat, StairWireCheck.exclusiveNat,
      List.mem_append, List.mem_range'_1] at h
    unfold signPayloadBand at bound
    dsimp only [Wire] at *
    omega
  have hosts : x ∉ StairPhysicalLayout.hosts 87 := by
    intro h
    have hostBounds : StairWireCheck.hosts87Nat.all (fun w => decide (1561 ≤ w ∧ w ≤ 1633)) = true := by
      decide +kernel
    rw [StairWireCheck.hosts87_eq_nat] at h
    have hh := of_decide_eq_true (List.all_eq_true.mp hostBounds x h)
    unfold signPayloadBand at bound
    dsimp only [Wire] at *
    omega
  exact sign_rebinder_fix _ _ x roles hosts

theorem signPayload_band (q : Wire) (hq : q ∈ signPayload) : signPayloadBand q := by
  change q ∈ (List.range' 1 84).flatMap pkSitesOf at hq
  obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
  simp only [pkSitesOf, List.mem_map] at hq
  obtain ⟨i, _, rfl⟩ := hq
  have fixed := signPayload_host_fix k hk i
  dsimp only at fixed
  rw [fixed]
  exact signPayload_raw_band k hk i

theorem signPayload_hosted_shape :
    signPayload = (List.range' 8 672).map (fun i =>
      StairArchiveInactive.host (OB5.sig 511 (NewHistory5.payloadWire base i))) := by
  let blocks := (List.range' 1 84).flatMap (fun k => (List.finRange 8).map (fun i => 8*k+i.val))
  have indices : blocks = List.range' 8 672 := by decide +kernel
  rw [← indices]
  dsimp only [blocks]
  rw [List.map_flatMap]
  simp only [signPayload, List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro k _
  simp only [pkSitesOf, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [NewHistory5.payloadWire_packet base k i.val i.isLt]

theorem signPayload_unhosted_shape :
    signPayload = (List.range' 8 672).map (fun i => OB5.sig 511 (NewHistory5.payloadWire base i)) := by
  rw [signPayload_hosted_shape]
  apply List.map_congr_left
  intro n hn
  have span := List.mem_range'_1.mp hn
  have packet : n / 8 ∈ List.range' 1 84 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
  exact signPayload_host_fix (n / 8) packet ⟨n % 8, Nat.mod_lt _ (by decide)⟩

theorem signPayload_range :
    signPayload.all (fun q => decide (16 ≤ q ∧ q < 2330)) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have h := signPayload_band q hq
  unfold signPayloadBand at h
  apply decide_eq_true_eq.mpr
  dsimp only [Wire] at *
  omega

theorem sten_sub (j : Nat) (lo : 1 ≤ j) (hi : j ≤ 83) (rev : Bool) :
    wires (sten j rev) ⊆ insert signHost (wires (oten j rev)) := by
  have hfirst : wires (sfirst j rev) ⊆ insert signHost (wires (ofirst j rev)) := by
    unfold sfirst ofirst
    exact spk_sub _ _ (by split <;> omega) (by split <;> omega)
  have hsecond : wires (ssecond j rev) ⊆ insert signHost (wires (osecond j rev)) := by
    unfold ssecond osecond
    exact spk_sub _ _ (by split <;> omega) (by split <;> omega)
  intro q hq
  simp only [sten, oten, wires_append, Finset.mem_union, Finset.mem_insert] at hq ⊢
  rcases hq with a | b | c | d | e
  · tauto
  · have := Finset.mem_insert.mp (hfirst b); tauto
  · tauto
  · have := Finset.mem_insert.mp (hsecond d); tauto
  · tauto

private theorem ordered_wires (d : Bool) (A B : Program) :
    wires (ordered d A B) = wires A ∪ wires B := by
  cases d <;> simp [ordered, Finset.union_comm]

private def signBodyRows : List (Nat × Nat) :=
  WindowBankCheck.banks.zip WindowBankCheck.banks.tail

private abbrev signBodyRowOK (r : Nat × Nat) : Prop :=
  r.1 ∈ WindowBankCheck.banks ∧ 10 ≤ r.1 ∧ r.1 ≤ 83 ∧
    1 ≤ r.1 + 2 ∧ r.1 + 2 + (r.2 - (r.1 + 2)) ≤ 85

private theorem signBodyRows_ok : ∀ r ∈ signBodyRows, signBodyRowOK r := by decide +kernel

private def signBodyFold (d : Bool) (pair : Nat → Program) : List (Nat × Nat) → Program
  | [] => ordered d (pair 82) (rgroup d 84 1)
  | r :: rs => ordered d (pair r.1)
      (ordered d (rgroup d (r.1 + 2) (r.2 - (r.1 + 2))) (signBodyFold d pair rs))

section
attribute [local irreducible] ordered sten oten rgroup

theorem signBody_rel (d : Bool) (R : Program → Program → Prop)
    (join : ∀ {A A' B B'}, R A A' → R B B' → R (ordered d A B) (ordered d A' B'))
    (pair : ∀ j ∈ WindowBankCheck.banks, 10 ≤ j → j ≤ 83 → R (sten j (!d)) (oten j (!d)))
    (native : ∀ j n, 1 ≤ j → j + n ≤ 85 → R (rgroup d j n) (rgroup d j n)) :
    R (group84SignBody d) (group84Body d) := by
  have assemble : ∀ xs : List (Nat × Nat), (∀ r ∈ xs, signBodyRowOK r) →
      R (signBodyFold d (fun j => sten j (!d)) xs) (signBodyFold d (fun j => oten j (!d)) xs) := by
    intro xs
    induction xs with
    | nil =>
      intro _
      exact join (pair 82 (by decide) (by decide) (by decide)) (native 84 1 (by decide) (by decide))
    | cons r rs ih =>
      intro valid
      have h := valid r List.mem_cons_self
      have tail := ih (fun q hq => valid q (List.mem_cons_of_mem r hq))
      exact join (pair r.1 h.1 h.2.1 h.2.2.1)
        (join (native (r.1 + 2) (r.2 - (r.1 + 2)) h.2.2.2.1 h.2.2.2.2) tail)
  change R (signBodyFold d (fun j => sten j (!d)) signBodyRows)
    (signBodyFold d (fun j => oten j (!d)) signBodyRows)
  exact assemble signBodyRows signBodyRows_ok
end

theorem signBody_sub (d : Bool) :
    wires (group84SignBody d) ⊆ insert signHost (wires (group84Body d)) := by
  have step {A A' B B' : Program}
      (a : wires A' ⊆ insert signHost (wires A))
      (b : wires B' ⊆ insert signHost (wires B)) :
      wires (ordered d A' B') ⊆ insert signHost (wires (ordered d A B)) := by
    rw [ordered_wires, ordered_wires]
    intro q hq
    simp only [Finset.mem_union, Finset.mem_insert] at hq ⊢
    rcases hq with hl | hr
    · have := Finset.mem_insert.mp (a hl); tauto
    · have := Finset.mem_insert.mp (b hr); tauto
  exact signBody_rel d (fun A B => wires A ⊆ insert signHost (wires B))
    (fun a b => step a b) (fun j _ lo hi => sten_sub j (by omega) hi (!d))
    (fun _ _ _ _ => Finset.subset_insert _ _)

theorem tagSwap_signHost : tagSwap signHost = signHost := by decide +kernel

private theorem rename_sign_sub (f : Wire → Wire) (hf : f signHost = signHost)
    (P Q : Program) (h : wires P ⊆ insert signHost (wires Q)) :
    wires (renameProgram f P) ⊆ insert signHost (wires (renameProgram f Q)) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (h hi) with pin | old
  · subst i
    rw [hf]
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    rw [renameProgram_support]
    exact Finset.mem_image_of_mem _ old

private theorem signBracketed_sub (d : Bool)
    (bracket early first pack old body unpack : Program) (tag payload : Finset Wire)
    (hBracket : wires bracket ⊆ insert signHost (tag ∪ payload))
    (hEarly : wires first ⊆ insert signHost (wires early))
    (hBody : wires body ⊆ insert signHost (wires old)) :
    wires (bracket ++ ordered d first (pack ++ body ++ unpack) ++ bracket) ⊆
      insert signHost ((wires (ordered d early (pack ++ old ++ unpack)) ∪ tag) ∪ payload) := by
  intro q used
  simp only [wires_append, ordered_wires, Finset.mem_union, Finset.mem_insert] at used ⊢
  rcases used with (left | (bare | ((packed | newBody) | unpacked))) | right
  · have hit := Finset.mem_insert.mp (hBracket left)
    simp only [Finset.mem_union] at hit
    tauto
  · have hit := Finset.mem_insert.mp (hEarly bare)
    tauto
  · tauto
  · have hit := Finset.mem_insert.mp (hBody newBody)
    tauto
  · tauto
  · have hit := Finset.mem_insert.mp (hBracket right)
    simp only [Finset.mem_union] at hit
    tauto

theorem group84Sign_sub (d : Bool) :
    wires (group84Sign d) ⊆ insert signHost
      ((wires (group84 d) ∪ tagSites.toFinset) ∪ signPayload.toFinset) :=
  signBracketed_sub d signBracket (ogroup d 1 9) (egroup d 1 9) packTag
    (renameProgram tagSwap (group84Body d)) (renameProgram tagSwap (group84SignBody d)) unpackTag
    tagSites.toFinset signPayload.toFinset signBracket_sub
    (egroup_sub d 1 9 (by decide) (by decide))
    (rename_sign_sub tagSwap tagSwap_signHost _ _ (signBody_sub d))

end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical

open Arithmetic MappedCompressed RecordedQuantum StairPhysicalV3 StairRestSupport
open StairArchiveRelease StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires group84SignBody group84Body rgroup

private def signPhysicalBool : Instr → Bool
  | .X _ => true
  | .CX c t => decide (c ≠ t)
  | .CCX a b t => decide (a ≠ t ∧ b ≠ t)
  | .measureX _ _ _ => true

theorem signBracket_physical : GatePhysical signBracket := by
  have check : signBracket.all signPhysicalBool = true := by decide +kernel
  intro i hi
  have h := List.all_eq_true.mp check i hi
  cases i <;> simp_all [signPhysicalBool, PhysicalInstr, ProperGate]

private theorem sten_physical (d : Bool) (j : Nat) (lo : 10 ≤ j) (hi : j ≤ 83)
    (pick : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) :
    GatePhysical (sten j (!d)) := by
  have firstOK : GatePhysical (sfirst j (!d)) := by
    unfold sfirst
    exact spk_physical _ _ (by split <;> omega) (by split <;> omega)
  have lastOK : GatePhysical (ssecond j (!d)) := by
    unfold ssecond
    exact spk_physical _ _ (by split <;> omega) (by split <;> omega)
  simp only [sten, gatePhysical_append]
  exact ⟨(hook j pick _).1, firstOK, (hook j pick _).1, lastOK, (hook j pick _).1⟩

private theorem signBody_physical (d : Bool) : GatePhysical (group84SignBody d) := by
  have ord {A B : Program} (a : GatePhysical A) (b : GatePhysical B) :
      GatePhysical (ordered d A B) := by cases d <;> simp [ordered, gatePhysical_append, a, b]
  exact signBody_rel d (fun A _ => GatePhysical A)
    (fun a b => ord a b) (fun j pick lo hi => sten_physical d j lo hi pick)
    (fun j n lo hi => (ot_rgroup_sound d j n lo hi).1)

theorem group84Sign_ok (d : Bool) : Sound (group84Sign d) := by
  refine ⟨?_, ?_⟩
  · have hbody := gatePhysical_rename _ tagSwap.injective _ (signBody_physical d)
    have hnl := egroup_physical d 1 9 (by decide) (by decide)
    have hp := packTag_sound.1
    have hu := unpackTag_sound.1
    cases d <;> simp only [group84Sign, ordered, Bool.false_eq_true, if_false, if_true,
      gatePhysical_append, hbody, hp, hu, hnl, signBracket_physical, and_self]
  · intro q hq
    rcases Finset.mem_insert.mp (group84Sign_sub d hq) with eq | mem
    · subst q; decide +kernel
    · rcases Finset.mem_union.mp mem with left | payload
      · rcases Finset.mem_union.mp left with old | tag
        · exact (group84_ok d).2 q old
        · exact of_decide_eq_true (List.all_eq_true.mp tagSites_inDom q (List.mem_toFinset.mp tag))
      · exact Or.inl (of_decide_eq_true
          (List.all_eq_true.mp signPayload_range q (List.mem_toFinset.mp payload)))

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

namespace ECDSAAdd.Entrant.StairPacket.WindowSites

open Arithmetic MappedCompressed StairConcreteAssembly StairSiteAvoidance
open WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires group84Sign group84

private theorem signPayload_fit (q : Wire) (hq : q ∈ signPayload) :
    Stair44OuterSites.fit (StairPlaceFast.outerPlaceB q) = true := by
  have band := signPayload_band q hq
  change (21 ≤ q ∧ q < 441) ∨ (1049 ≤ q ∧ q < 1301) ∨ (1645 ≤ q ∧ q < 1813) at band
  dsimp only [Wire] at *
  have good : StairSiteEasy.good39B (StairPlaceFast.outerPlaceB q) = true := by
    rcases band with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact StairSiteEasy.kbTP1 q (by omega) (by omega)
    · exact StairSiteEasy.kbTP5 q (by omega) hi
    · rcases Nat.lt_or_ge q 1672 with h | h
      · exact StairSiteEasy.kbTP7 q (by omega) h
      · rcases Nat.lt_or_ge q 1673 with h' | h'
        · have e : (q : Nat) = 1672 := Nat.le_antisymm (Nat.le_of_lt_succ h') h
          subst q
          decide +kernel
        · rcases Nat.lt_or_ge q 1812 with h'' | h''
          · exact StairSiteEasy.kbTP8 q h' h''
          · have e : (q : Nat) = 1812 := Nat.le_antisymm (Nat.le_of_lt_succ hi) h''
            subst q
            decide +kernel
  have active : StairPlaceFast.outerPlaceB q ∉ Stair44PointMap.retired := by
    intro h
    simp only [Stair44PointMap.retired, List.mem_cons, List.not_mem_nil, or_false] at h
    have placed : 4835 ≤ StairOuterPlacement.outerPlace q ∧ StairOuterPlacement.outerPlace q ≤ 4839 := by
      rw [StairPlaceFast.outerPlace_eqB]
      dsimp only [Wire] at h ⊢
      omega
    have e := outerPlace_in_4835_4839 q placed
    dsimp only [Wire] at *
    omega
  simp only [Stair44OuterSites.fit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨good, active⟩

private theorem group84Sign_wire_ok (d : Bool) (q : Wire) (hq : q ∈ wires (group84Sign d)) :
    TP q ∈ StairHoleSupport.recordArena ∧ TP q ∉ StairHoleSupport.oldHoles ∧ TP q ∉ reserved := by
  have fit_ok {w : Wire} (h : Stair44OuterSites.fit (StairPlaceFast.outerPlaceB w) = true) :
      TP w ∈ StairHoleSupport.recordArena ∧ TP w ∉ StairHoleSupport.oldHoles ∧ TP w ∉ reserved := by
    rw [← StairPlaceFast.outerPlace_eqB] at h
    exact singleton_ok h
  rcases Finset.mem_insert.mp (group84Sign_sub d hq) with pin | h
  · subst q
    exact fit_ok (by decide +kernel)
  · rcases Finset.mem_union.mp h with h | payload
    · rcases Finset.mem_union.mp h with old | tag
      · have ok := group84_ok d
        exact ⟨(ok.1 q old).1, (ok.1 q old).2, ok.2 q old⟩
      · exact fit_ok (List.all_eq_true.mp tagSites_fit q (List.mem_toFinset.mp tag))
    · exact fit_ok (signPayload_fit q (List.mem_toFinset.mp payload))

theorem group84Sign_ok (d : Bool) : PieceOK reserved TP (group84Sign d) :=
  ⟨fun q hq => ⟨(group84Sign_wire_ok d q hq).1, (group84Sign_wire_ok d q hq).2.1⟩,
    fun q hq => (group84Sign_wire_ok d q hq).2.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowSites


namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open Arithmetic MappedCompressed Baselines StairPhysicalV3 StairRestSupport StairConcreteAssembly
variable {p : StairSchedule.StairPrimitives}
set_option maxRecDepth 14000
set_option maxHeartbeats 1200000
private theorem callerDomain_inDom {q : Wire} (h : q ∈ StairSemanticFinal.callerDomain) : InDom q := by
  rw [StairSemanticFinal.callerDomain, List.mem_toFinset, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only [StairSemanticFinal.callerIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  unfold InDom InDomN MappedCompressed.base
  rcases hi with h1 | h2 | h3 | h4 | h5
  · exact Or.inl ⟨by omega, by omega⟩
  · subst h2; exact Or.inr (by decide)
  · subst h3; exact Or.inr (by decide)
  · subst h4; exact Or.inr (by decide)
  · subst h5; exact Or.inr (by decide)

private theorem oddSound1542 (divide : Bool) (d f c : Nat) (hd : d ≤ 44) (hfc : f + c ≤ 102) :
    Sound (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 divide d f c) :=
  ⟨OddFullPass.P1LifeLoan.hostedGroup_physical OddFullPass.P1LifeLoan.hostPlan1542 divide d f c hfc,
   fun _ hq => callerDomain_inDom (OddFullPass.P1LifeLoan.hostedGroup_wires_sub_1542 divide d f c hd hfc hq)⟩

theorem sound_entryTailPrefix (_H : LoanHyp) (P : PrimitiveSlots p) (_hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryTailPrefix p) := by
  have g0 := group84Sign_ok true
  have g14 := oddSound1542 true 14 85 5 (by decide) (by decide)
  have g23 := oddSound1542 true 23 90 3 (by decide) (by decide)
  have g31 := oddSound1542 true 31 93 3 (by decide) (by decide)
  have g37 := oddSound1542 true 37 96 2 (by decide) (by decide)
  have g42 := oddSound1542 true 42 98 2 (by decide) (by decide)
  have s1 := sound_forwardSegment P 87 62 425 450 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s2 := sound_forwardSegment P 62 47 450 465 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s3 := sound_forwardSegment P 47 32 465 480 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s4 := sound_forwardSegment P 32 22 480 490 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s5 := sound_forwardSegment P 22 12 490 500 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have sl := sound_forwardLast P
  unfold WindowCallerCosts.entryTailPrefix
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append g0 s1) g14) s2) g23) s3) g31) s4) g37) s5) g42) sl

theorem sound_exitHeadSuffix (_H : LoanHyp) (P : PrimitiveSlots p) (_hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitHeadSuffix p) := by
  have g0 := group84Sign_ok false
  let Pc := StairPhysicalV3.primitiveSlots_v3 StairPhysicalV3.primitiveChecks
  have cut0 := PackCutOddExit.cutRow0_sound
    (oddSound1542 false 14 85 5 (by decide) (by decide))
    (sound_reverseSegment Pc 87 62 425 450 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut1 := PackCutOddExit.cutRow1_sound
    (oddSound1542 false 23 90 3 (by decide) (by decide))
    (sound_reverseSegment Pc 62 47 450 465 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut2 := PackCutOddExit.cutRow2_sound
    (oddSound1542 false 31 93 3 (by decide) (by decide))
    (sound_reverseSegment Pc 47 32 465 480 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut3 := PackCutOddExit.cutRow3_sound
    (oddSound1542 false 37 96 2 (by decide) (by decide))
    (sound_reverseSegment Pc 32 22 480 490 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut4 := PackCutOddExit.cutRow4_sound
    (oddSound1542 false 42 98 2 (by decide) (by decide))
    (sound_reverseSegment Pc 22 12 490 500 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have rl := sound_reverseLast P
  unfold WindowCallerCosts.exitHeadSuffix
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append rl cut4) cut3) cut2) cut1) cut0) g0

private theorem sound_firstPacketOdd (divide : Bool) :
    Sound (JointOdd1588.placedFirstPacketOdd WindowCallerCosts.oddFirstHalf divide) := by
  refine ⟨JointOdd1588.placedFirstPacketOdd_physical WindowCallerCosts.oddFirstHalf divide
      (WindowCallerCosts.oddFirstHalf_physical divide), ?_⟩
  intro q hq
  have hsup := StairWireCheck.allSites_sound StairWireCheck.fpSup _
    (JointOdd1588.placedFirstPacketOdd_passSup WindowCallerCosts.oddFirstHalf divide
      (WindowCallerCosts.oddFirstHalf_support divide)) q hq
  rcases WindowCallerCosts.fpSup_bounds q hsup with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by rw [h2]; decide)

attribute [local irreducible] ECDSAAdd.wires OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan
  OddFullPass.InverseTailCOdd.endPacket760OddLoan44 CompareDecoder.BoundaryLoan.endPacket760DivLoan
  StairEndpointLoan44.endPacket760Loan44 in
theorem sound_entryFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryFieldHosted p) := by
  have first := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket true)
    (sound_firstPacketOdd true)
  have pre : Sound (WindowCallerCosts.entryLowPrefix p) := by
    unfold WindowCallerCosts.entryLowPrefix
    exact sound_append (sound_append (sound_append first sound_clearProgram)
      (sound_borrow (sound_entryTailPrefix H P hs))) sound_unprefix
  have tail : Sound (OddFullPass.P1LifeLoan.entryTailSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    unfold OddFullPass.P1LifeLoan.entryTailSuffixOdd
    have hdiv : Sound (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan) := by
      refine ⟨gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
        OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_physical, ?_⟩
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      have hmem : OB5.sig 511 y ∈ wires (renameProgram (OB5.sig 511) CompareDecoder.BoundaryLoan.endPacket760DivLoan) := by
        rw [renameProgram_support]
        exact Finset.mem_image.mpr ⟨y, OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_wires_sub hy, rfl⟩
      exact (sound_sig 511 (by omega) B.divEndpoint).good _ hmem
    have hcan : Sound OddFullPass.HalfConvertOdd.canon760OddLoan :=
      ⟨OddFullPass.HalfConvertOdd.canon760OddLoan_physical,
       fun q hq => (Finset.mem_union.mp (OddFullPass.HalfConvertOdd.canon760OddLoan_wires_sub hq)).elim
         (B.canon.good q) (sound_copyN.good q)⟩
    exact sound_append (sound_append (sound_append
      (oddSound1542 true 44 100 2 (by decide) (by decide)) hdiv) sound_copyN) hcan
  have suf : Sound (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    unfold OddFullPass.P1LifeLoan.entryLowSuffixOdd
    exact sound_append (sound_append sound_clearProgram (sound_borrow tail)) sound_unprefix
  unfold WindowCallerCosts.entryFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_fieldRename pre) sound_paritySetup) sound_hostedX)
    (sound_fieldRename suf)) sound_hostedX) sound_paritySetup

attribute [local irreducible] ECDSAAdd.wires OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan
  OddFullPass.InverseTailCOdd.endPacket760OddLoan44 CompareDecoder.BoundaryLoan.endPacket760DivLoan
  StairEndpointLoan44.endPacket760Loan44 in
theorem sound_exitFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitFieldHosted p) := by
  have head : Sound (OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    unfold OddFullPass.P1LifeLoan.exitHeadPrefixOdd
    have hcen : Sound OddFullPass.HalfConvertOdd.center760OddLoan :=
      ⟨OddFullPass.HalfConvertOdd.center760OddLoan_physical,
       fun q hq => (Finset.mem_union.mp (OddFullPass.HalfConvertOdd.center760OddLoan_wires_sub hq)).elim
         (B.center.good q) (sound_copyN.good q)⟩
    have hmul : Sound (renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44) := by
      refine ⟨gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
        OddFullPass.InverseTailCOdd.endPacket760OddLoan44_physical, ?_⟩
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      have hmem : OB5.sig 511 y ∈ wires (renameProgram (OB5.sig 511) (StairEndpointLoan44.endPacket760Loan44 false)) := by
        rw [renameProgram_support]
        exact Finset.mem_image.mpr ⟨y, OddFullPass.InverseTailCOdd.endPacket760OddLoan44_wires_sub hy, rfl⟩
      exact (sound_sig 511 (by omega) B.multEndpoint).good _ hmem
    exact sound_append (sound_append (sound_append hcen sound_copyN) hmul)
      (oddSound1542 false 44 100 2 (by decide) (by decide))
  have pre : Sound (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    unfold OddFullPass.P1LifeLoan.exitLowPrefixOdd
    exact sound_append (sound_append sound_clearProgram (sound_borrow head)) sound_unprefix
  have last := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket false)
    (sound_firstPacketOdd false)
  have suf : Sound (WindowCallerCosts.exitLowSuffix p) := by
    unfold WindowCallerCosts.exitLowSuffix
    exact sound_append (sound_append (sound_append sound_clearProgram
      (sound_borrow (sound_exitHeadSuffix H P hs))) sound_unprefix) last
  unfold WindowCallerCosts.exitFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    sound_paritySetup sound_hostedX) (sound_fieldRename pre)) sound_paritySetup)
    sound_hostedX) (sound_fieldRename suf)

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairRestSupport
set_option maxRecDepth 14000
set_option maxHeartbeats 1000000
attribute [local irreducible] wires renameProgram Shadow20.MergeCut.forward Shadow20.MergeCut.reverse
  Rolling1588TickGap.forward Rolling1588.reverse Stair44WalkMap.rest Stair44WalkMap.first

abbrev GoodWindow (p : Program) :=
  ∀ q∈wires p, Stair44PhaseSites.valid (Stair44WalkMap.rest q)=true

theorem native {p : Program} (h : GoodWindow p) :
    PieceOK reserved (fun x => PP (Stair44WalkMap.rest x)) p := by
  apply weaken
  apply Stair44OuterSites.fits
  intro x hx
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace (Stair44WalkMap.rest x))=true
  rw [StairPlaceFast.phasePlace_eqB]
  exact h x hx

theorem walkF (d : Bool) (tail : Nat) (bound : 16+(405+tail)≤506)
    (new : GoodWindow (Shadow20.MergeCut.forward d)) :
    PieceOK reserved PP (WindowWalkCosts.forward d tail) := by
  have old := weaken (Stair44PhaseSites.forward d (405+tail) bound)
  have a := StairRestSupport.forward_append d 29 16 (376+tail)
  have b := StairRestSupport.forward_append d 376 45 tail
  change Rolling1588TickGap.forward d 16 (29+(376+tail)) =
    Rolling1588TickGap.forward d 16 29 ++ Rolling1588TickGap.forward d 45 (376+tail) at a
  rw [b] at a
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.forward,num,a,app,ren] at old
  simp only [WindowWalkCosts.forward,app,ren]
  exact ⟨old.1,⟨old.2.1,native new⟩,old.2.2.2⟩

theorem walkR (d : Bool) (tail : Nat) (bound : 16+(405+tail)≤506)
    (new : GoodWindow (Shadow20.MergeCut.reverse d)) :
    PieceOK reserved PP (WindowWalkCosts.backward d tail) := by
  have old := weaken (Stair44PhaseSites.backward d (405+tail) bound)
  have a := StairRestSupport.reverse_append d 29 16 (376+tail)
  have b := StairRestSupport.reverse_append d 376 45 tail
  change Rolling1588.reverse d 16 (29+(376+tail)) =
    Rolling1588.reverse d 45 (376+tail) ++ Rolling1588.reverse d 16 29 at a
  rw [b] at a
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.backward,num,a,app,ren] at old
  simp only [WindowWalkCosts.backward,app,ren]
  exact ⟨⟨⟨old.1.1.1,native new⟩,old.1.2⟩,old.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open Arithmetic MappedCompressed Secp256k1 Baselines StairPhysicalV3 StairRestSupport
open Stair44Outer StairConcreteAssembly Stair44WalkMap
set_option maxHeartbeats 1400000
set_option maxRecDepth 20000
attribute [local irreducible] wires GatePhysical
theorem parts {P Q : Program} (h : Sound (P ++ Q)) : Sound P ∧ Sound Q :=
  ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩

private theorem firstDom (q : Wire) (h : InDom q) : InDom (first q) := by
  unfold first shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))

private theorem restDom (q : Wire) (h : InDom q) : InDom (rest q) := by
  unfold rest shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))


theorem dom {p : Program} (cover : PartialSites.Covered p) : Good p := by
  intro q hq
  have h := cover q hq
  simp only [PartialSites.domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  unfold InDom InDomN
  left
  constructor
  all_goals omega

private theorem fw (d : Bool) (tail n : Nat) (hn : 15+(405+tail)=n)
    (ref_ : Sound (Rolling1588TickGap.forward d 1 n))
    (p : GatePhysical (Shadow20.MergeCut.forward d)) : Sound (WindowWalkCosts.forward d tail) := by
  subst n
  rw [forward_append d 15 1 (405+tail)] at ref_
  obtain ⟨early,late⟩ := parts ref_
  change Sound (Rolling1588TickGap.forward d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,forward_append d 29 16 (376+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 45 (376+tail)) at ms
  rw [forward_append d 376 45 tail] at ms
  have patch : Sound (Shadow20.MergeCut.forward d) := ⟨p,dom (PartialSites.forwardMixed_domain d)⟩
  have last : Sound (Rolling1588TickGap.forward d 421 tail) := (parts ms).2
  exact sound_append (sound_rename _ first.injective firstDom early)
    (sound_rename _ rest.injective restDom (sound_append (sound_append pre patch) last))

private theorem bw (d : Bool) (tail n : Nat) (hn : 15+(405+tail)=n)
    (ref_ : Sound (Rolling1588.reverse d 1 n))
    (p : GatePhysical (Shadow20.MergeCut.reverse d)) : Sound (WindowWalkCosts.backward d tail) := by
  subst n
  rw [reverse_append d 15 1 (405+tail)] at ref_
  obtain ⟨late,early⟩ := parts ref_
  change Sound (Rolling1588.reverse d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,reverse_append d 29 16 (376+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 45 (376+tail)) at ms
  rw [reverse_append d 376 45 tail] at ms
  have patch : Sound (Shadow20.MergeCut.reverse d) := ⟨p,dom (PartialSites.reverseMixed_domain d)⟩
  have last : Sound (Rolling1588.reverse d 421 tail) := (parts ms).1
  exact sound_append (sound_rename _ rest.injective restDom (sound_append (sound_append last patch) pre))
    (sound_rename _ first.injective firstDom early)
theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

variable (ff : ∀d,GatePhysical (Shadow20.MergeCut.forward d)) (rr : ∀d,GatePhysical (Shadow20.MergeCut.reverse d))

include ff rr in
theorem dividePhysical : GatePhysical WindowCallerCosts.divide := by
  have eq : InverseFive23.lastPhase15 false = reverseEnd ++
      Rolling1588.reverse false 1 505 ++ FrontierEntry1591NativeH.inverse base := by
    simp only [InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
      reverseEnd,List.append_assoc]
  have h := sound_lastPhase15
  rw [eq] at h
  have ⟨a,native⟩ := parts h
  have ⟨tail,walk⟩ := parts a
  let P := primitiveSlots_v3 primitiveChecks
  have field := PackCutSub.sound_sub WindowCallerCosts.field_sublist
    (sound_entryFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3)
  simp only [WindowCallerCosts.divide,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw true 4 424 rfl sound_forward424 (ff _)),phase P.firstPack⟩,rest_physical _ field⟩,
    phase tail⟩,phase (bw false 85 505 rfl walk (rr _))⟩,phase (sound_rename _ first.injective firstDom native)⟩

include ff rr in
theorem multiplyPhysical (k : Nat) : GatePhysical (WindowCallerCosts.multiply k) := by
  have eq : Rolling1588TickGap.tailPhase false = Rolling1588TickGap.forward false 1 504 ++ forwardEnd := by
    simp only [Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,
      forwardEnd,List.append_assoc]
  have h := sound_tailPhase
  rw [eq] at h
  have ⟨walk,tail⟩ := parts h
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_exitFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [WindowCallerCosts.multiply,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw false 84 504 rfl walk (ff _)),phase tail⟩,rest_physical _ field⟩,phase P.firstUnpack⟩,
    phase (bw true 4 424 rfl sound_reverse424 (rr _))⟩,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ (phase (sound_x1N k))⟩

include ff rr in
theorem genericPhysical (cx cy : Fp) : GatePhysical (WindowCallerCosts.generic cx cy) := by
  have g := FlagTop2.genericN_physical cx cy
  simp only [FlagExit.genericN,FlagExit.secondStageN,gatePhysical_append] at g
  simp only [WindowCallerCosts.generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨gatePhysical_rename _ Stair44PointMap.duringY.injective _
      (EntryFuseOdd.entryYAllOdd_physical layout layout_widths layout_nodup (-cy)),
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ g.1.1.2⟩,dividePhysical ff rr⟩,
    Stair44Square.physical _⟩,multiplyPhysical ff rr _⟩,
    gatePhysical_rename _ Stair44PointMap.duringY.injective _
      (EntryFuseOdd.exitYAllOdd_physical layout layout_widths layout_nodup cy)⟩

include ff rr in
theorem physical (C : Point) : GatePhysical (WindowCallerCosts.program C) := by
  cases C with
  | zero => simp [WindowCallerCosts.program,GatePhysical]
  | @some cx cy hc =>
    let C : Point := .some hc
    have m := AboveFieldPointDevelop.middle_physical C cx cy
    simp only [AboveFieldPointDevelop.middle,gatePhysical_append] at m
    apply gatePhysical_rename _ (Wrapper5.U layout).injective
    simp only [WindowCallerCosts.finite,gatePhysical_append]
    refine ⟨⟨gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_,?_⟩,
      gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_⟩
    · simp only [gatePhysical_append]
      exact ⟨⟨FlagTop.stageNew_physical hc,m.1.1.1.1⟩,m.1.1.1.2⟩
    · exact gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ FlagTop.rho_injective _ (genericPhysical ff rr cx cy))
    · simp only [gatePhysical_append]
      exact ⟨⟨m.1.2,m.2⟩,ControlPointEncodingDevelop.borrowOut_physical hc⟩
end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
open StairConcreteAssembly Stair44Outer
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires renameProgram

/-- Replacing a child leaves the safety contract on the other children intact. -/
private def SafeChange (f : Wire → Wire) (old new : Program) :=
  PieceOK reserved f old → PieceOK reserved f new
theorem same (f : Wire → Wire) (p : Program) : SafeChange f p p := id
theorem fresh {f : Wire → Wire} {p q : Program} (h : PieceOK reserved f q) :
    SafeChange f p q := fun _ => h
private theorem appendChange {f : Wire → Wire} {a b x y : Program}
    (l : SafeChange f a x) (r : SafeChange f b y) : SafeChange f (a++b) (x++y) :=
  fun old => (l (app.mp old).1).append (r (app.mp old).2)
private theorem renameChange {f g : Wire → Wire} {a b : Program}
    (h : SafeChange (fun x => f (g x)) a b) : SafeChange f (renameProgram g a) (renameProgram g b) :=
  fun old => ren.mpr (h (ren.mp old))

private theorem callerIndices_lt_2428_chk :
    StairSemanticFinal.callerIndices.all (fun i => decide (base i < 2428)) = true := by
  decide +kernel

private theorem roles_736_740_chk :
    ([736, 737, 738, 739, 740] : List Wire).all (fun w => decide (w ∈ StairSchedule.exclusiveRoles)) = true := by
  decide

private theorem tpi_mem_tpList {x : Wire} (h : StairSiteEasy.TPI x) : x ∈ StairSiteEasy.tpList := by
  unfold StairSiteEasy.TPI at h
  simp only [StairSiteEasy.tpList, List.mem_append, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false]
  dsimp only [Wire] at *
  omega

private theorem pieceOK_of_tpi_avoids_roles {P : Program}
    (htpi : ∀ x ∈ wires P, StairSiteEasy.TPI x)
    (hav : ∀ r ∈ StairSchedule.exclusiveRoles, r ∉ wires P) :
    PieceOK reserved TP P := by
  have h39 := StairSiteEasy.ok39_of_tpi htpi
  refine ⟨h39.1, fun x hx bad => ?_⟩
  have hgood := StairSiteEasy.tpList_good x (tpi_mem_tpList (htpi x hx))
  have hnot39 := hgood.2.2
  unfold StairSiteEasy.Hole39 at hnot39
  rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat] at bad
  simp only [StairPhysicalLayout.newHolesNat, List.mem_append, List.mem_range'_1] at bad
  have hrange : 4835 ≤ StairOuterPlacement.outerPlace x ∧ StairOuterPlacement.outerPlace x ≤ 4839 := by
    change 4835 ≤ TP x ∧ TP x ≤ 4839
    dsimp only [Wire] at *
    omega
  have hxeq := outerPlace_in_4835_4839 x hrange
  have hxm : x ∈ ([736, 737, 738, 739, 740] : List Wire) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    dsimp only [Wire] at *
    omega
  have hrole : x ∈ StairSchedule.exclusiveRoles :=
    decide_eq_true_eq.mp (List.all_eq_true.mp roles_736_740_chk x hxm)
  exact hav x hrole hx

private theorem hostPlan1542_nonrole :
    ([14, 23, 31, 37, 42, 44] : List Nat).all (fun d =>
      let hs := OddFullPass.P1LifeLoan.hostPlan1542.group true d 0 0
      let rs := StairSchedule.exclusiveRoles.drop d
      hs.all (fun h => decide (h ∉ StairSchedule.exclusiveRoles) && StairSiteEasy.k5tpiB h) &&
      decide (rs.length = hs.length) &&
      decide rs.Nodup && decide hs.Nodup &&
      rs.all (fun r => decide (r ∉ hs))) = true := by
  decide +kernel

private theorem tpList_mem_tpi {x : Wire} (h : x ∈ StairSiteEasy.tpList) : StairSiteEasy.TPI x := by
  simp only [StairSiteEasy.tpList, List.mem_append, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false] at h
  unfold StairSiteEasy.TPI
  dsimp only [Wire] at *
  omega

private theorem hostedGroup1542_ok (divide : Bool) (d f c : Nat)
    (hsched : (d, f, c) ∈ ([(14, 85, 5), (23, 90, 3), (31, 93, 3), (37, 96, 2), (42, 98, 2), (44, 100, 2)] : List (Nat × Nat × Nat))) :
    PieceOK reserved TP (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 divide d f c) := by
  have hdm : d ∈ ([14, 23, 31, 37, 42, 44] : List Nat) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched ⊢
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
  have hd : d ≤ 44 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hdm; omega
  have hf1 : 1 ≤ f := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
  have hfc : f + c ≤ 102 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
  have hchk := List.all_eq_true.mp hostPlan1542_nonrole d hdm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at hchk
  obtain ⟨⟨⟨⟨hnr_h, hlen⟩, hnd_r⟩, hnd_h⟩, hdisj⟩ := hchk
  have hgrp : OddFullPass.P1LifeLoan.hostPlan1542.group divide d f c =
      OddFullPass.P1LifeLoan.hostPlan1542.group true d 0 0 := rfl
  have hfresh : ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group divide d f c,
      q ∉ wires (StairSchedule.placedGroups StairConcrete.bestLoans divide d f c) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact StairField13V3Fresh.hosts_fresh_group 62 (by decide) divide 14 85 5 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 47 (by decide) divide 23 90 3 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 32 (by decide) divide 31 93 3 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 22 (by decide) divide 37 96 2 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 12 (by decide) divide 42 98 2 (by decide) (by decide) (by decide)
    · intro q hq; simp [OddFullPass.P1LifeLoan.hostPlan1542] at hq
  have hmem_props : ∀ x ∈ wires (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 divide d f c),
      StairSiteEasy.TPI x ∧ x ∉ StairSchedule.exclusiveRoles := by
    intro x hx
    have hstd := OddFullPass.P1LifeLoan.hostedGroup_wires_sub OddFullPass.P1LifeLoan.hostPlan1542 divide d f c hd hx
    unfold StairHostsSchedule.hostedGroup at hstd
    rw [hgrp] at hstd hfresh
    rcases StairSiteEasy.rebind_mem _ _ _ hfresh (fun y hy => hdisj y hy) hnd_r hnd_h hlen.le x hstd with hh | ⟨hP, hnr⟩
    · exact ⟨StairSiteEasy.k5_tpiB _ (hnr_h x hh).2, (hnr_h x hh).1⟩
    · change x ∈ wires (renameProgram (OB5.sig 511) (StairGroups.groups divide d f c)) at hP
      rw [renameProgram_support] at hP
      obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp hP
      obtain ⟨j, hj1, hj2, hjw⟩ := StairSiteEasy.seq_mem divide (StairGroups.packet divide d) c f w hw
      unfold StairGroups.packet at hjw
      rw [renameProgram_support] at hjw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hjw
      have hjr : j ∈ List.range' 1 101 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
      obtain ⟨nt, hr⟩ := StairSiteEasy.basePacket_tgt divide d j hjr hd z hz
      have hnr_all : x ∉ StairSchedule.exclusiveRoles := by
        intro hrole
        rw [← List.take_append_drop d StairSchedule.exclusiveRoles, List.mem_append] at hrole
        exact hrole.elim (fun ht => nt (by change OB5.sig 511 (shifted (Placement5.pi j) z) ∈ _; rw [hwq]; exact ht)) hnr
      rcases hr with hr_role | hr_tpi
      · exact absurd (by rw [← hwq]; exact hr_role) hnr_all
      · exact ⟨by rw [← hwq]; exact hr_tpi, hnr_all⟩
  exact pieceOK_of_tpi_avoids_roles (fun x hx => (hmem_props x hx).1) (fun r hr hmem => (hmem_props r hmem).2 hr)

private theorem callerDomain_lt_2428 {q : Wire} (h : q ∈ StairSemanticFinal.callerDomain) : q < 2428 := by
  rw [StairSemanticFinal.callerDomain, List.mem_toFinset, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact decide_eq_true_eq.mp (List.all_eq_true.mp callerIndices_lt_2428_chk i hi)

private theorem pieceOK_sub {holes : List Wire} {f : Wire → Wire} {P Q : Program}
    (h : ∀ q ∈ wires P, q ∈ wires Q) (hq : PieceOK holes f Q) : PieceOK holes f P :=
  ⟨fun x hx => hq.1 x (h x hx), fun x hx => hq.2 x (h x hx)⟩

private theorem entryTailSuffixOdd_ok :
    PieceOK reserved TP (OddFullPass.P1LifeLoan.entryTailSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have hcopy_ok : PieceOK reserved TP HalfFieldOB5.copyN :=
    StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.copyN_all
  have hcopy_43 : PieceOK Stair44FieldSites.holes TP HalfFieldOB5.copyN :=
    ⟨hcopy_ok.1, fun x hx bad => hcopy_ok.2 x hx (Stair44FieldSites.hsub _ bad)⟩
  have hdom_all := OddFullPass.P1LifeLoan.entryTailSuffixOdd_caller
  unfold OddFullPass.P1LifeLoan.entryTailSuffixOdd at hdom_all ⊢
  refine (((hostedGroup1542_ok true 44 100 2 (by decide)).append ?_).append hcopy_ok).append ?_
  · apply upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [StairConcrete.bestLoans_divEndpoint, renameProgram_support]
        rw [renameProgram_support] at hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨y, OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_wires_sub hy, rfl⟩)
        Stair44FieldSites.endpointD)
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
    intro hmem
    rw [renameProgram_support] at hmem
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hmem
    have h720 : base 720 ∈ StairSchedule.exclusiveRoles := by decide +kernel
    have hyEq : y = base 720 := (StairField13V3Clean.sig_pre h720 y).mp hyeq
    subst hyEq
    have hsub_div := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_wires_sub hy
    unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hsub_div
    rw [renameProgram_support] at hsub_div
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp hsub_div
    have ha720 : a = base 720 := by
      have hfix : Equiv.swap (base 760) (base 717) (base 720) = base 720 := by decide
      exact (Equiv.swap (base 760) (base 717)).injective (haeq.trans hfix.symm)
    subst ha720
    rw [renameProgram_support] at ha
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp ha
    have hb720 : b = base 720 := by
      have hfix : shifted Placement5.pi0 (base 720) = base 720 := by decide +kernel
      exact (shifted Placement5.pi0).injective (hbeq.trans hfix.symm)
    subst hb720
    rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hb) with h | h
    · rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact absurd h (by decide)
    · obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp h
      have hz720 : z = base 720 := by
        have hfix : Equiv.swap (base 719) (base 510) (base 720) = base 720 := by decide
        exact (Equiv.swap (base 719) (base 510)).injective (hzeq.trans hfix.symm)
      subst hz720
      rw [wires_append, Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact StairSiteEasy.k5_loan_avoids (base 720) (by decide +kernel) hz
      · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
        rw [Finset.mem_singleton] at hc
        exact absurd hc (by decide)
  · exact upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [wires_append]
        exact OddFullPass.HalfConvertOdd.canon760OddLoan_wires_sub hq)
        (Stair44FieldSites.canon.append hcopy_43))
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
      OddFullPass.HalfConvertOdd.canon760OddLoan_avoids_720

private theorem exitHeadPrefixOdd_ok :
    PieceOK reserved TP (OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have hcopy_ok : PieceOK reserved TP HalfFieldOB5.copyN :=
    StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.copyN_all
  have hcopy_43 : PieceOK Stair44FieldSites.holes TP HalfFieldOB5.copyN :=
    ⟨hcopy_ok.1, fun x hx bad => hcopy_ok.2 x hx (Stair44FieldSites.hsub _ bad)⟩
  have hdom_all := OddFullPass.P1LifeLoan.exitHeadPrefixOdd_caller
  unfold OddFullPass.P1LifeLoan.exitHeadPrefixOdd at hdom_all ⊢
  refine ((PieceOK.append ?_ hcopy_ok).append ?_).append
      (hostedGroup1542_ok false 44 100 2 (by decide))
  · exact upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [wires_append]
        exact OddFullPass.HalfConvertOdd.center760OddLoan_wires_sub hq)
        (Stair44FieldSites.center.append hcopy_43))
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
      OddFullPass.HalfConvertOdd.center760OddLoan_avoids_720
  · apply upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [StairHostsSchedule.hostedEndpoint, StairSchedule.placedEndPacket,
          show StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false from by
            simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true, if_false, if_true],
          renameProgram_support]
        rw [renameProgram_support] at hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨y, OddFullPass.InverseTailCOdd.endPacket760OddLoan44_wires_sub hy, rfl⟩)
        Stair44FieldSites.endpointM)
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
    intro hmem
    rw [renameProgram_support] at hmem
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hmem
    have h720 : base 720 ∈ StairSchedule.exclusiveRoles := by decide +kernel
    have hyEq : y = base 720 := (StairField13V3Clean.sig_pre h720 y).mp hyeq
    subst hyEq
    exact StairEndpointLoan44.endPacket760Loan44_avoids (base 720) (by decide +kernel)
      (OddFullPass.InverseTailCOdd.endPacket760OddLoan44_wires_sub hy)

private theorem entryField : PieceOK reserved KP
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have ps := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.paritySetup_all
  have hx := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.hostedX_all
  have pk := StairSiteAvoidance.packEnd_rows
  have fpOk : PieceOK reserved lowPlace (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true) :=
    weaken (JointOdd1588.hostedFirstPacketOdd_pieceOK WindowCallerCosts.oddFirstHalf
      StairPhysicalInventory.physicalHoles (fun _ h => h) true
      (WindowCallerCosts.oddFirstHalf_support true))
  have htail : PieceOK reserved TP (WindowCallerCosts.entryTailPrefix checkpointPrimitives) := by
    unfold WindowCallerCosts.entryTailPrefix
    refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
      ?_).append ?_).append ?_).append ?_).append ?_)
    · exact group84Sign_ok true
    · exact StairSiteAvoidance.forwardSegment_ok hsub 87 62 (by decide) (by decide) (by decide) pk.1
    · exact hostedGroup1542_ok true 14 85 5 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 62 47 (by decide) (by decide) (by decide) pk.2.1
    · exact hostedGroup1542_ok true 23 90 3 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 47 32 (by decide) (by decide) (by decide) pk.2.2.1
    · exact hostedGroup1542_ok true 31 93 3 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 32 22 (by decide) (by decide) (by decide) pk.2.2.2.1
    · exact hostedGroup1542_ok true 37 96 2 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 22 12 (by decide) (by decide) (by decide) pk.2.2.2.2
    · exact hostedGroup1542_ok true 42 98 2 (by decide)
    · exact StairSiteAvoidance.forwardLast_ok hsub
  unfold WindowCallerCosts.entryFieldHosted
  refine ((((PieceOK.append ?_ ps).append hx).append ?_).append hx).append ps
  · apply StairSiteAvoidance.ok_field
    unfold WindowCallerCosts.entryLowPrefix
    exact ((fpOk.append (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all)).append
      (StairSiteAvoidance.ok_borrow htail)).append (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)
  · apply StairSiteAvoidance.ok_field
    unfold OddFullPass.P1LifeLoan.entryLowSuffixOdd
    exact ((StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all).append
      (StairSiteAvoidance.ok_borrow entryTailSuffixOdd_ok)).append
      (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)

private theorem exitField : PieceOK reserved KP
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have ps := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.paritySetup_all
  have hx := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.hostedX_all
  have up := StairSiteAvoidance.unpackEnd_rows
  have fpOk : PieceOK reserved lowPlace (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false) :=
    weaken (JointOdd1588.hostedFirstPacketOdd_pieceOK WindowCallerCosts.oddFirstHalf
      StairPhysicalInventory.physicalHoles (fun _ h => h) false
      (WindowCallerCosts.oddFirstHalf_support false))
  have hrows : PieceOK reserved TP
      (StairSchedule.reverseLast checkpointPrimitives ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 42 98 2 ++ StairSchedule.reverseSegment checkpointPrimitives 22 12 490 500 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 37 96 2 ++ StairSchedule.reverseSegment checkpointPrimitives 32 22 480 490 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 31 93 3 ++ StairSchedule.reverseSegment checkpointPrimitives 47 32 465 480 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 23 90 3 ++ StairSchedule.reverseSegment checkpointPrimitives 62 47 450 465 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 14 85 5 ++ StairSchedule.reverseSegment checkpointPrimitives 87 62 425 450) := by
    refine ((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
      ?_).append ?_).append ?_).append ?_)
    · exact StairSiteAvoidance.reverseLast_ok hsub
    · exact hostedGroup1542_ok false 42 98 2 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 22 12 (by decide) (by decide) (by decide) (by decide) up.2.2.2.2
    · exact hostedGroup1542_ok false 37 96 2 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 32 22 (by decide) (by decide) (by decide) (by decide) up.2.2.2.1
    · exact hostedGroup1542_ok false 31 93 3 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 47 32 (by decide) (by decide) (by decide) (by decide) up.2.2.1
    · exact hostedGroup1542_ok false 23 90 3 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 62 47 (by decide) (by decide) (by decide) (by decide) up.2.1
    · exact hostedGroup1542_ok false 14 85 5 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 87 62 (by decide) (by decide) (by decide) (by decide) up.1
  have hhead : PieceOK reserved TP (WindowCallerCosts.exitHeadSuffix checkpointPrimitives) := by
    unfold WindowCallerCosts.exitHeadSuffix
    exact (pieceOK_sub (fun q hq => PackCutOddExit.cutRows_sub hq) hrows).append (group84Sign_ok false)
  unfold WindowCallerCosts.exitFieldHosted
  refine ((((ps.append hx).append ?_).append ps).append hx).append ?_
  · apply StairSiteAvoidance.ok_field
    unfold OddFullPass.P1LifeLoan.exitLowPrefixOdd
    exact ((StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all).append
      (StairSiteAvoidance.ok_borrow exitHeadPrefixOdd_ok)).append
      (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)
  · apply StairSiteAvoidance.ok_field
    unfold WindowCallerCosts.exitLowSuffix
    exact (((StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all).append
      (StairSiteAvoidance.ok_borrow hhead)).append
      (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)).append fpOk

private theorem entryFieldCut : PieceOK reserved KP WindowCallerCosts.entryFieldHostedCut :=
  pieceOK_sub (PackCutSub.wires_sub WindowCallerCosts.field_sublist) entryField

theorem phase {P : Program} (v : PieceOK reserved PP P) :
    PieceOK reserved UG (Stair44Outer.phasePlace P) := ok_kernel (ok_phase v)

theorem division (f : GoodWindow (Shadow20.MergeCut.forward true))
    (r : GoodWindow (Shadow20.MergeCut.reverse false)) :
    PieceOK reserved UG WindowCallerCosts.divide :=
  (((((phase (walkF true 4 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.pack)))).append
    (ok_kernel entryFieldCut)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.reverseTail)))).append
    (phase (walkR false 85 (by decide) r))).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.native)))

theorem multiplication (k : Nat) (f : GoodWindow (Shadow20.MergeCut.forward false))
    (r : GoodWindow (Shadow20.MergeCut.reverse true)) :
    PieceOK reserved UG (WindowCallerCosts.multiply k) :=
  (((((phase (walkF false 84 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.forwardTail)))).append
    (ok_kernel exitField)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.unpack)))).append
    (phase (walkR true 4 (by decide) r))).append (weaken (Stair44PhaseSites.exitX k))

theorem program_width (C : Point) (f : ∀d, GoodWindow (Shadow20.MergeCut.forward d))
    (r : ∀d,GoodWindow (Shadow20.MergeCut.reverse d)) :
    Challenge.qubits (WindowCallerCosts.program C) ≤ 1542 := by
  apply width
  cases C with
  | zero => exact pieceOK_nil _ _
  | @some cx cy hc =>
    apply ok_wrapper
    exact ((weaken (Stair44OuterSites.initial hc)).append (ok_generic
      ((((((weaken (Stair44OuterSites.entryY (-cy))).append (weaken (Stair44OuterSites.entryX (-cx)))).append
        (division (f _) (r _))).append (weaken (Stair44Release.squareSites (ReflectionE1.correction cx)))).append
          (multiplication cx.val (f _) (r _))).append (weaken (Stair44OuterSites.exitY cy))))).append
      (weaken (Stair44OuterSites.finalPart hc))
end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic Secp256k1

theorem physical (C : Point) : GatePhysical (program C) :=
  WindowPhysical.physical (fun d => (Shadow20.MergeCut.physical d).1) (fun d => Shadow20.MergeCut.rphysical d) C

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Secp256k1

theorem qubitBound (C : Point) : Challenge.qubits (program C) ≤ 1542 :=
  WindowSites.program_width C PartialSites.forwardMixed_fits PartialSites.reverseMixed_fits

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end




section


section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify

attribute [local irreducible] run StairArchiveInactive.packet StairArchiveRelease.fieldHook
  StairArchiveTen.first StairArchiveTen.second StairArchiveTen.ten
  StairArchiveRelease.fieldPort StairArchiveRelease.outputCols StairArchiveRelease.inputCols
  StairArchiveNativeCut.canonical CodecBitSliceVerify.get
set_option maxRecDepth 1200
set_option maxHeartbeats 360000
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
open Arithmetic MappedCompressed ArchiveFieldScratch StairArchiveInactive StairArchiveNativeCut StairArchiveRelease WindowFieldMask
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 100000
private theorem splitRange : List.range' 1 84 = List.range' 1 7 ++ List.range' 8 7 ++ List.range' 15 7 ++ List.range' 22 7 ++ List.range' 29 7 ++ List.range' 36 7 ++ List.range' 43 7 ++ List.range' 50 7 ++ List.range' 57 7 ++ List.range' 64 7 ++ List.range' 71 7 ++ List.range' 78 7 := by decide +kernel
attribute [local irreducible] allowed fieldPort packet cover preimage
private theorem pass55 : (List.range' 1 84).all (allowed 55)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h55_1,h55_8⟩,h55_15⟩,h55_22⟩,h55_29⟩,h55_36⟩,h55_43⟩,h55_50⟩,h55_57⟩,h55_64⟩,h55_71⟩,h55_78⟩
private theorem pass67 : (List.range' 1 84).all (allowed 67)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h67_1,h67_8⟩,h67_15⟩,h67_22⟩,h67_29⟩,h67_36⟩,h67_43⟩,h67_50⟩,h67_57⟩,h67_64⟩,h67_71⟩,h67_78⟩
private theorem pass70 : (List.range' 1 84).all (allowed 70)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h70_1,h70_8⟩,h70_15⟩,h70_22⟩,h70_29⟩,h70_36⟩,h70_43⟩,h70_50⟩,h70_57⟩,h70_64⟩,h70_71⟩,h70_78⟩
private theorem pass73 : (List.range' 1 84).all (allowed 73)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h73_1,h73_8⟩,h73_15⟩,h73_22⟩,h73_29⟩,h73_36⟩,h73_43⟩,h73_50⟩,h73_57⟩,h73_64⟩,h73_71⟩,h73_78⟩
private theorem pass76 : (List.range' 1 84).all (allowed 76)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h76_1,h76_8⟩,h76_15⟩,h76_22⟩,h76_29⟩,h76_36⟩,h76_43⟩,h76_50⟩,h76_57⟩,h76_64⟩,h76_71⟩,h76_78⟩
private theorem pass79 : (List.range' 1 84).all (allowed 79)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h79_1,h79_8⟩,h79_15⟩,h79_22⟩,h79_29⟩,h79_36⟩,h79_43⟩,h79_50⟩,h79_57⟩,h79_64⟩,h79_71⟩,h79_78⟩
private theorem pass82 : (List.range' 1 84).all (allowed 82)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h82_1,h82_8⟩,h82_15⟩,h82_22⟩,h82_29⟩,h82_36⟩,h82_43⟩,h82_50⟩,h82_57⟩,h82_64⟩,h82_71⟩,h82_78⟩
private theorem pass10 : (List.range' 1 84).all (allowed 10)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h10_1,h10_8⟩,h10_15⟩,h10_22⟩,h10_29⟩,h10_36⟩,h10_43⟩,h10_50⟩,h10_57⟩,h10_64⟩,h10_71⟩,h10_78⟩
private theorem pass13 : (List.range' 1 84).all (allowed 13)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h13_1,h13_8⟩,h13_15⟩,h13_22⟩,h13_29⟩,h13_36⟩,h13_43⟩,h13_50⟩,h13_57⟩,h13_64⟩,h13_71⟩,h13_78⟩
private theorem pass16 : (List.range' 1 84).all (allowed 16)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h16_1,h16_8⟩,h16_15⟩,h16_22⟩,h16_29⟩,h16_36⟩,h16_43⟩,h16_50⟩,h16_57⟩,h16_64⟩,h16_71⟩,h16_78⟩
private theorem pass19 : (List.range' 1 84).all (allowed 19)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h19_1,h19_8⟩,h19_15⟩,h19_22⟩,h19_29⟩,h19_36⟩,h19_43⟩,h19_50⟩,h19_57⟩,h19_64⟩,h19_71⟩,h19_78⟩
private theorem pass22 : (List.range' 1 84).all (allowed 22)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h22_1,h22_8⟩,h22_15⟩,h22_22⟩,h22_29⟩,h22_36⟩,h22_43⟩,h22_50⟩,h22_57⟩,h22_64⟩,h22_71⟩,h22_78⟩
private theorem pass25 : (List.range' 1 84).all (allowed 25)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h25_1,h25_8⟩,h25_15⟩,h25_22⟩,h25_29⟩,h25_36⟩,h25_43⟩,h25_50⟩,h25_57⟩,h25_64⟩,h25_71⟩,h25_78⟩
private theorem pass28 : (List.range' 1 84).all (allowed 28)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h28_1,h28_8⟩,h28_15⟩,h28_22⟩,h28_29⟩,h28_36⟩,h28_43⟩,h28_50⟩,h28_57⟩,h28_64⟩,h28_71⟩,h28_78⟩
private theorem pass31 : (List.range' 1 84).all (allowed 31)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h31_1,h31_8⟩,h31_15⟩,h31_22⟩,h31_29⟩,h31_36⟩,h31_43⟩,h31_50⟩,h31_57⟩,h31_64⟩,h31_71⟩,h31_78⟩
private theorem pass43 : (List.range' 1 84).all (allowed 43)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h43_1,h43_8⟩,h43_15⟩,h43_22⟩,h43_29⟩,h43_36⟩,h43_43⟩,h43_50⟩,h43_57⟩,h43_64⟩,h43_71⟩,h43_78⟩
private theorem pass35 : (List.range' 1 84).all (allowed 35)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h35_1,h35_8⟩,h35_15⟩,h35_22⟩,h35_29⟩,h35_36⟩,h35_43⟩,h35_50⟩,h35_57⟩,h35_64⟩,h35_71⟩,h35_78⟩
private theorem pass39 : (List.range' 1 84).all (allowed 39)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h39_1,h39_8⟩,h39_15⟩,h39_22⟩,h39_29⟩,h39_36⟩,h39_43⟩,h39_50⟩,h39_57⟩,h39_64⟩,h39_71⟩,h39_78⟩
private theorem pass47 : (List.range' 1 84).all (allowed 47)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h47_1,h47_8⟩,h47_15⟩,h47_22⟩,h47_29⟩,h47_36⟩,h47_43⟩,h47_50⟩,h47_57⟩,h47_64⟩,h47_71⟩,h47_78⟩
private theorem pass51 : (List.range' 1 84).all (allowed 51)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h51_1,h51_8⟩,h51_15⟩,h51_22⟩,h51_29⟩,h51_36⟩,h51_43⟩,h51_50⟩,h51_57⟩,h51_64⟩,h51_71⟩,h51_78⟩
private theorem pass59 : (List.range' 1 84).all (allowed 59)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h59_1,h59_8⟩,h59_15⟩,h59_22⟩,h59_29⟩,h59_36⟩,h59_43⟩,h59_50⟩,h59_57⟩,h59_64⟩,h59_71⟩,h59_78⟩
private theorem pass63 : (List.range' 1 84).all (allowed 63)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h63_1,h63_8⟩,h63_15⟩,h63_22⟩,h63_29⟩,h63_36⟩,h63_43⟩,h63_50⟩,h63_57⟩,h63_64⟩,h63_71⟩,h63_78⟩
theorem pass (h : Nat) (hm : h ∈ banks) : (List.range' 1 84).all (allowed h) = true := by
  simp only [banks,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact pass10
  · exact pass13
  · exact pass16
  · exact pass19
  · exact pass22
  · exact pass25
  · exact pass28
  · exact pass31
  · exact pass35
  · exact pass39
  · exact pass43
  · exact pass47
  · exact pass51
  · exact pass55
  · exact pass59
  · exact pass63
  · exact pass67
  · exact pass70
  · exact pass73
  · exact pass76
  · exact pass79
  · exact pass82

theorem packet_free (h k : Nat) (hm : h∈banks) (km : k∈List.range' 1 84)
    (not0 : k≠h) (not1 : k≠h+1) (d : Bool) : avoids (packet d k) (bank h) := by
  have once := List.all_eq_true.mp (pass h hm) k km
  simp only [allowed, decide_eq_false not0, decide_eq_false not1, Bool.false_or] at once
  intro q member used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp member
  have qmem : fieldPort h i ∈ slots h := List.mem_map.mpr ⟨i,List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩
  have outside := List.all_eq_true.mp once _ qmem
  have limit := (List.mem_range'_1.mp km).2
  have inside := original d k (by omega) used
  simp [compactCover_present inside] at outside

/-- Bit mask of a wire list (kernel-cheap: `Nat.lor`/`Nat.shiftLeft` are GMP-accelerated). -/
def maskOf (l : List Wire) : Nat := l.foldl (fun acc q => acc ||| (1 <<< (q:Nat))) 0

theorem testBit_maskFold (l : List Wire) (acc q : Nat) :
    (l.foldl (fun acc q => acc ||| (1 <<< (q:Nat))) acc).testBit q = (acc.testBit q || l.contains q) := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.contains_cons]
    by_cases h : (a:Nat) = q
    · subst h; simp
    · have h' : (q == a) = false := by simp only [beq_eq_false_iff_ne]; exact fun e => h e.symm
      simp [h, h']

theorem testBit_maskOf {l : List Wire} {q : Wire} (h : q ∈ l) : (maskOf l).testBit q = true := by
  rw [maskOf, testBit_maskFold]
  simp [h]

theorem maskOf_testBit (l : List Wire) (q : Wire) : (maskOf l).testBit q = l.contains q := by
  rw [maskOf, testBit_maskFold, Nat.zero_testBit, Bool.false_or]

theorem not_mem_of_maskOf {l : List Wire} {q : Wire} (h : (maskOf l).testBit q = false) : q ∉ l :=
  fun m => by rw [testBit_maskOf m] at h; exact Bool.noConfusion h

/-- Banks `j ≠ h`: no slot of `h` is a field port of `j` (one `&&&` of two masks per pair). -/
private def distinct (j h : Nat) := j=h ||
  ((maskOf (slots h)) &&& (maskOf ((List.range 121).map (fieldPort j))) == 0)
private def commonFieldTail : Nat := maskOf ((List.range' 16 105).map (fieldPort 0))

private theorem maskOf_append (a b : List Wire) : maskOf (a ++ b) = maskOf a ||| maskOf b := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [maskOf, testBit_maskFold, Nat.zero_testBit, Bool.false_or,
    Nat.testBit_or, List.contains_append]

private theorem field_mask_split (j : Nat) :
    maskOf ((List.range 121).map (fieldPort j)) = maskOf (slots j) ||| commonFieldTail := by
  have ranges : List.range 121 = List.range 16 ++ List.range' 16 105 := by decide +kernel
  have tail : (List.range' 16 105).map (fieldPort j) = (List.range' 16 105).map (fieldPort 0) := by
    apply List.map_congr_left
    intro q hq
    exact fieldPort_tail j q (List.mem_range'_1.mp hq).1
  unfold slots commonFieldTail
  rw [ranges, List.map_append, maskOf_append, tail]

private theorem prefix_masks_separate : banks.all (fun j => banks.all (fun h =>
    j = h || ((maskOf (slots h)) &&& (maskOf (slots j)) == 0))) = true := by
  decide +kernel

private theorem tail_mask_separate : banks.all (fun h =>
    (maskOf (slots h) &&& commonFieldTail) == 0) = true := by
  decide +kernel

private theorem distinct_ok : banks.all (fun j=>banks.all (distinct j))=true := by
  apply List.all_eq_true.mpr
  intro j hj
  apply List.all_eq_true.mpr
  intro h hh
  by_cases same : j = h
  · simp only [distinct, decide_eq_true same, Bool.true_or]
  · have headClear := List.all_eq_true.mp (List.all_eq_true.mp prefix_masks_separate j hj) h hh
    simp only [decide_eq_false same, Bool.false_or, beq_iff_eq] at headClear
    have tail := beq_iff_eq.mp (List.all_eq_true.mp tail_mask_separate h hh)
    simp only [distinct, decide_eq_false same, Bool.false_or, beq_iff_eq, field_mask_split,
      Nat.and_or_distrib_left, headClear, tail, Nat.or_zero]

theorem separate (j h : Nat) (jm : j∈banks) (hm : h∈banks) (ne : j≠h) :
    ∀ q∈inside j, q∉bank h := by
  have ok := List.all_eq_true.mp (List.all_eq_true.mp distinct_ok j jm) h hm
  simp only [distinct, decide_eq_false ne, Bool.false_or, beq_iff_eq] at ok
  intro q own other
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp other
  have qmem : fieldPort h i ∈ slots h := List.mem_map.mpr ⟨i,List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩
  have inside' : fieldPort h i ∈ (List.range 121).map (fieldPort j) := by
    obtain ⟨t,ht,eq⟩ := Finset.mem_image.mp own
    exact List.mem_map.mpr ⟨t,List.mem_range.mpr (Finset.mem_range.mp ht),eq⟩
  have b := congrArg (fun n : Nat => n.testBit (fieldPort h i)) ok
  simp only [Nat.testBit_and, testBit_maskOf qmem, testBit_maskOf inside', Bool.and_self, Nat.zero_testBit] at b
  exact Bool.noConfusion b
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify
def bankIds : Finset Nat := {10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82}
def allBanks : Finset Wire := bankIds.biUnion bank
def others (j : Nat) : Finset Wire := (bankIds.erase j).biUnion bank
def byteFrame (j row : Nat) (cs : Cols) (a : State) := ∀ q∈Finset.range 16,
  a.basis (fieldPort j q) = (get cs q).testBit row
structure Fits (rows : Nat → Nat) (code : Nat → Cols) (a r : State) : Prop where
  phase : a.phase = r.phase
  outside : ∀ q∉allBanks, a.basis q=r.basis q
  bytes : ∀ j∈bankIds, byteFrame j (rows j) (code j) a

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 100000

theorem decompose (j : Nat) (hj : j∈bankIds) : allBanks=bank j ∪ others j := by
  ext q
  simp only [allBanks,others,Finset.mem_union,Finset.mem_biUnion,Finset.mem_erase]
  constructor
  · rintro ⟨k,hk,hq⟩
    by_cases same : k=j
    · subst k; exact Or.inl hq
    · exact Or.inr ⟨k,⟨same,hk⟩,hq⟩
  · rintro (own|⟨k,⟨_,hk⟩,hq⟩)
    · exact ⟨j,hj,own⟩
    · exact ⟨k,hk,hq⟩

private theorem run_on_bank_complement (P : Program) (B : Finset Wire) (m : List Bool) (a r : State)
    (phase : a.phase = r.phase) (rest : ∀ q ∉ B, a.basis q = r.basis q) (safe : avoids P B) :
    (run P m a).phase = (run P m r).phase ∧ ∀ q ∉ B, (run P m a).basis q = (run P m r).basis q := by
  have same : mask B a r = a := by
    apply congrArg₂ State.mk phase.symm
    funext q
    by_cases member : q ∈ B
    · exact if_pos member
    · exact (if_neg member).trans (rest q member).symm
  have outcome := mask_run P B m a r safe
  rw [same] at outcome
  have matched := congrArg State.phase outcome
  refine ⟨matched, ?_⟩
  intro q outside
  exact (congrArg (fun s : State => s.basis q) outcome).trans (if_neg outside)

theorem plain (P : Program) (rows : Nat→Nat) (code : Nat→Cols) (m : List Bool) (a r : State)
    (h : Fits rows code a r) (safe : avoids P allBanks) : Fits rows code (run P m a) (run P m r) := by
  obtain ⟨phase, outside⟩ := run_on_bank_complement P allBanks m a r h.phase h.outside safe
  refine ⟨phase, outside, ?_⟩
  intro j hj q hq
  have member : fieldPort j q ∈ allBanks := Finset.mem_biUnion.mpr
    ⟨j, hj, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  exact (run_preserves_outside P m a _ (safe _ member)).trans (h.bytes j hj q hq)

private theorem initRest (rev : Bool) :
    (List.range' 16 105).all (fun q => get (inputCols (enter rev)) q == get (StairArchiveNativeCut.canonical (!rev) (!rev)) q) = true := by
  cases rev <;> decide +kernel

attribute [local irreducible] run fieldPort StairArchiveNativeCut.canonical inputCols enter CodecBitSliceVerify.get

theorem beforeFrame (j : Nat) (hj : j∈bankIds) (rows : Nat→Nat) (code : Nat→Cols) (rev : Bool) (a r : State)
    (h : Fits rows code a r) (active : code j=inputCols (enter rev))
    (apart : ∀ q∈inside j, q∉others j) (before_ : frame j (rows j) (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (nd : ∀ i∈Finset.range 121,∀ k∈Finset.range 121, fieldPort j i=fieldPort j k→i=k) :
    frame j (rows j) (inputCols (enter rev)) a := by
  intro q hq
  by_cases lo : q<16
  · rw [←active]
    exact h.bytes j hj q (Finset.mem_range.mpr lo)
  · have lq := Finset.mem_range.mp hq
    have own : fieldPort j q ∉ bank j := by
      intro mem
      obtain ⟨k,hk,heq⟩ := Finset.mem_image.mp mem
      have lk := Finset.mem_range.mp hk
      have eq := nd k (Finset.mem_range.mpr (by omega)) q hq heq
      omega
    have outsider : fieldPort j q ∉ allBanks := by
      rw [decompose j hj,Finset.mem_union]
      exact fun hit => hit.elim own (apart _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
    have range : q∈List.range' 16 105 := List.mem_range'_1.mpr ⟨by omega,by omega⟩
    have c := beq_iff_eq.mp (List.all_eq_true.mp (initRest rev) q range)
    rw [h.outside _ outsider, before_ q hq, c]
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveInactive WindowFieldCosts
attribute [local irreducible] packet run allBanks
def nativeRanges (j n : Nat) := (j=1 ∧ n=9) ∨ (j=12 ∧ n=1) ∨ (j=15 ∧ n=1) ∨ (j=18 ∧ n=1) ∨ (j=21 ∧ n=1) ∨ (j=24 ∧ n=1) ∨ (j=27 ∧ n=1) ∨ (j=30 ∧ n=1) ∨ (j=33 ∧ n=2) ∨ (j=37 ∧ n=2) ∨ (j=41 ∧ n=2) ∨ (j=45 ∧ n=2) ∨ (j=49 ∧ n=2) ∨ (j=53 ∧ n=2) ∨ (j=57 ∧ n=2) ∨ (j=61 ∧ n=2) ∨ (j=65 ∧ n=2) ∨ (j=69 ∧ n=1) ∨ (j=72 ∧ n=1) ∨ (j=75 ∧ n=1) ∨ (j=78 ∧ n=1) ∨ (j=81 ∧ n=1) ∨ (j=84 ∧ n=1)
private theorem disjointRange {j n k h : Nat} (valid : nativeRanges j n) (hk : j≤k ∧ k<j+n)
    (isBank : h∈bankIds) : k∈List.range' 1 84 ∧ k≠h ∧ k≠h+1 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at isBank
  unfold nativeRanges at valid
  rw [List.mem_range'_1]; omega
private theorem seqSafe (d : Bool) (j n : Nat)
    (h : ∀ k, j≤k → k<j+n → avoids (packet d k) allBanks) :
    avoids (PacketSequence.program d (packet d) j n) allBanks := by
  induction n generalizing j with
  | zero =>
    intro q _ used; simp [PacketSequence.program,wires] at used
  | succ n ih =>
    have head := h j (by omega) (by omega)
    have tail := ih (j+1) (fun k l u=>h k (by omega) (by omega))
    intro q inbank used
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at used
    · exact used.elim (tail q inbank) (head q inbank)
    · exact used.elim (head q inbank) (tail q inbank)
theorem groupSafe (d : Bool) (j n : Nat) (valid : nativeRanges j n) : avoids (group d j n) allBanks := by
  rw [group,distribute]
  apply seqSafe
  intro k lower upper q mem used
  rw [allBanks] at mem
  obtain ⟨h,hm,hq⟩ := Finset.mem_biUnion.mp mem
  have triple := disjointRange valid ⟨lower,upper⟩ hm
  have hlist : h∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using hm
  exact WindowBankCheck.packet_free h k hlist triple.1 triple.2.1 triple.2.2 d q hq used
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify
set_option maxRecDepth 1600
set_option maxHeartbeats 400000
attribute [local irreducible] run packet fieldPort StairArchiveNativeCut.canonical inputCols outputCols CodecBitSliceVerify.get

private theorem memberList {j : Nat} (h : j∈bankIds) : j∈WindowBankCheck.banks := by
  simpa [bankIds,WindowBankCheck.banks] using h
theorem geometry {j : Nat} (h : j∈bankIds) : j∈ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.mixedBankList ∧ j∈List.range' 1 83 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem apart {j : Nat} (hj : j∈bankIds) : ∀ q∈inside j, q∉others j := by
  intro q hi ho
  obtain ⟨k,hk,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,kid⟩ := Finset.mem_erase.mp hk
  exact WindowBankCheck.separate j k (memberList hj) (memberList kid) ne.symm q hi mem
private theorem native_safe (j k : Nat) (hj : j∈bankIds) (which : k=j ∨ k=j+1) (d : Bool) :
    avoids (packet d k) (others j) := by
  intro q ho used
  obtain ⟨h,hm,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,hid⟩ := Finset.mem_erase.mp hm
  apply WindowBankCheck.packet_free h k (memberList hid) _ _ _ d q mem used
  all_goals simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at hj hid
  · apply List.mem_range'_1.mpr; omega
  all_goals omega
private theorem hook_safe (j : Nat) (hj : j∈bankIds) (s : Stage) :
    avoids (fieldHook j s) (others j) := by
  intro q ho used
  rw [fieldHook,renameProgram_support] at used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  exact apart hj _ (Finset.mem_image.mpr ⟨i,sub s hi,rfl⟩) ho
private theorem append_safe {P Q : Program} {W : Finset Wire} (p : avoids P W) (q : avoids Q W) :
    avoids (P++Q) W := by
  intro i hi used
  rw [wires_append, Finset.mem_union] at used
  exact used.elim (p i hi) (q i hi)

def update (code : Nat→Cols) (j : Nat) (out : Cols) := fun k => if k=j then out else code k
attribute [local irreducible] inside StairArchiveRelease.fieldHook
  StairArchiveTen.first StairArchiveTen.second StairArchiveTen.ten

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open CodecBitSliceVerify WindowFieldMask WindowFieldCosts ArchiveFieldScratch
attribute [local irreducible] run measurementCount WindowFieldCosts.group StairArchiveTen.ten refExit
  inputCols outputCols StairArchiveNativeCut.canonical enter leave
inductive Leg where
  | native (j n : Nat)
  | paired (j : Nat)
def emitted (d : Bool) : Leg → Program
  | .native j n => group d j n
  | .paired j => ten j (!d)
def stock (d : Bool) (m : List Bool) (r : State) : Leg → State
  | .native j n => run (group d j n) m r
  | .paired j => refExit j (!d) m r
def codes (d : Bool) (c : Nat→Cols) : Leg → Nat→Cols
  | .native _ _ => c
  | .paired j => update c j (outputCols (leave (!d)))
def nextTape (d : Bool) (l : Leg) (m : List Bool) := m.drop (measurementCount (emitted d l))
def concatenate (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => emitted d l ++ concatenate d ls
def destination (d : Bool) : List Leg → List Bool → State → State
  | [],_,r => r
  | l::ls,m,r => destination d ls (nextTape d l m) (stock d m r l)
def finalCode (d : Bool) : List Leg → (Nat→Cols) → Nat→Cols
  | [],c => c
  | l::ls,c => finalCode d ls (codes d c l)
def validLeg (d : Bool) (c : Nat→Cols) : Leg → Prop
  | .native j n => nativeRanges j n
  | .paired j => j∈bankIds ∧ c j=inputCols (enter (!d))
def valid (d : Bool) : List Leg → (Nat→Cols) → Prop
  | [],_ => True
  | l::ls,c => validLeg d c l ∧ valid d ls (codes d c l)
def plan : Bool→List Leg
  | true => [.native 1 9,.paired 10,.native 12 1,.paired 13,.native 15 1,.paired 16,.native 18 1,.paired 19,.native 21 1,.paired 22,.native 24 1,.paired 25,.native 27 1,.paired 28,.native 30 1,.paired 31,.native 33 2,.paired 35,.native 37 2,.paired 39,.native 41 2,.paired 43,.native 45 2,.paired 47,.native 49 2,.paired 51,.native 53 2,.paired 55,.native 57 2,.paired 59,.native 61 2,.paired 63,.native 65 2,.paired 67,.native 69 1,.paired 70,.native 72 1,.paired 73,.native 75 1,.paired 76,.native 78 1,.paired 79,.native 81 1,.paired 82,.native 84 1]
  | false => [.native 84 1,.paired 82,.native 81 1,.paired 79,.native 78 1,.paired 76,.native 75 1,.paired 73,.native 72 1,.paired 70,.native 69 1,.paired 67,.native 65 2,.paired 63,.native 61 2,.paired 59,.native 57 2,.paired 55,.native 53 2,.paired 51,.native 49 2,.paired 47,.native 45 2,.paired 43,.native 41 2,.paired 39,.native 37 2,.paired 35,.native 33 2,.paired 31,.native 30 1,.paired 28,.native 27 1,.paired 25,.native 24 1,.paired 22,.native 21 1,.paired 19,.native 18 1,.paired 16,.native 15 1,.paired 13,.native 12 1,.paired 10,.native 1 9]
def initialCode (d : Bool) : Nat→Cols := fun _=>inputCols (enter (!d))
private theorem valid_plan (d : Bool) : valid d (plan d) (initialCode d) := by
  cases d <;> simp [valid,plan,validLeg,nativeRanges,bankIds,codes,update,initialCode]
end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires measurementCount Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

abbrev Z1 : Program :=
  renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8)

abbrev Z2 : Program := renameProgram (sig 507) (W.ReverseCarry.compactReceiverTick base 507)

abbrev Y : Program :=
  (renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++
      W.ReverseCarry.compactReceiverTick base 510) ++
    renameProgram (sig 509) (W.ReverseCarry.compactReceiverTick base 509)) ++
    renameProgram (sig 508) (W.ReverseCarry.compactReceiverTick base 508)

theorem stage_after (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (k : Nat) (hk : 1 + k ≤ 512) (m : List Bool) :
    Rolling1588.Integer.Stage base false x p (1 + k)
      (run (Rolling1588.Integer.regularForward base false 1 k) m s1).basis := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  exact ((Rolling1588.Integer.regularForward_spec base false base_pool_nodup StackOB5.historyAbove
    x p 1 k hp0 hx0 hpo hp gap hx cop hk) s1 m (Rolling1588.Integer.stage_one base false x p s1 first)).2

abbrev Q2 : Program := renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)

theorem run_congr_append (A A' B : Program) (s : State)
    (h : ∀ r, run A r s = run A' r s) (hc : measurementCount A = measurementCount A')
    (r : List Bool) : run (A ++ B) r s = run (A' ++ B) r s := by
  rw [run_append, run_append, hc, h]

theorem cZ : measurementCount Z1 = measurementCount Y := by
  decide +kernel

theorem agree_split (u s1 : State) (M : List Bool) (A B : Program)
    (h : Rolling1588.Integer.regularForward base false 1 510 = A ++ B)
    (hu : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run (Rolling1588.Integer.regularForward base false 1 510) M s1).basis q) :
    ∀ q ∈ skywalkPoolWires base, u.basis q =
      (run B (M.drop (measurementCount A)) (run A (M.take (measurementCount A)) s1)).basis q := by
  intro q hq
  rw [hu q hq, h, run_append]

abbrev Q1 : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFour15.candidate15)

theorem PE2 :
    renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFour15.old15) =
      Z1 ++ Z2 := by
  rw [InverseFour15.unpack51015]
  simp only [Z1, Z2, InverseFour15.same50715, InverseFour15.old15, Six505.rename_append,
    List.append_assoc]

theorem cQ : measurementCount Q1 = measurementCount (Y ++ Z2) := by
  decide +kernel

theorem split507 : Rolling1588.Integer.regularForward base false 1 510 =
    Rolling1588.Integer.regularForward base false 1 506 ++
      ((MorningFour.tick507 ++ tripF) ++ Rolling1588.Integer.packAfter base false 510) := by
  rw [Rolling1588.Integer.regularForward_snoc base false 1 509,show (1:Nat)+509=510 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 508,show (1:Nat)+508=509 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 507,show (1:Nat)+507=508 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 506,show (1:Nat)+506=507 by rfl,
    MorningPlacement.pack507,Rolling1588.Integer.pack508,Rolling1588.Integer.pack509,
    MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
  simp only [tripF,List.append_assoc,List.append_nil]

abbrev P1 : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)

theorem PE1 :
    renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ TerminalFivePlacement.old) =
      Q1 ++ Q2 := by
  rw [Six505.rename_append, TerminalFivePlacement.old_placed]
  simp only [Q1, Q2, Six505.rename_append, List.append_assoc]
  rfl

theorem split506 : Rolling1588.Integer.regularForward base false 1 510 =
    Rolling1588.Integer.regularForward base false 1 505 ++
      (TerminalFiveBridge.forward ++ Rolling1588.Integer.packAfter base false 510) := by
  rw [Rolling1588.Integer.regularForward_snoc base false 1 509,show (1:Nat)+509=510 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 508,show (1:Nat)+508=509 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 507,show (1:Nat)+507=508 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 506,show (1:Nat)+506=507 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 505,show (1:Nat)+505=506 by rfl,
    InverseFive23.pack506,MorningPlacement.pack507,Rolling1588.Integer.pack508,
    Rolling1588.Integer.pack509,
    MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
  simp only [TerminalFiveBridge.forward,tripF,List.append_assoc,List.append_nil]

theorem split508 : Rolling1588.Integer.regularForward base false 1 510 =
    Rolling1588.Integer.regularForward base false 1 507 ++
      (((W.repairedTick base 508 ++ W.repairedTick base 509) ++ W.repairedTick base 510) ++
        Rolling1588.Integer.packAfter base false 510) := by
  rw [Rolling1588.Integer.regularForward_snoc base false 1 509,show (1:Nat)+509=510 from rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 508,show (1:Nat)+508=509 from rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 507,show (1:Nat)+507=508 from rfl,
    Rolling1588.Integer.pack508 false,Rolling1588.Integer.pack509 false]
  simp only [List.append_assoc,List.append_nil]

theorem PE4 : (Y ++ Z2) ++ Q2 = Rolling1588.Integer.reverse false 506 5 := by
  decide +kernel

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.Stair44HostedCut
open ECDSAAdd Arithmetic StairField13V3 StairConcreteAssembly
set_option maxRecDepth 30000
attribute [local irreducible] run wires

private theorem takeCuts (pre : State → Prop) (j : Nat) :
    ∀ ps : List Piece, ∀ X : Program, Cuts pre X ps → Cuts pre X (ps.take j) := by
  induction j with
  | zero => intro ps X _; trivial
  | succ j ih =>
    intro ps X hc
    cases ps with
    | nil => trivial
    | cons p ps => exact ⟨hc.1,hc.2.1,ih ps (X ++ p.L) hc.2.2⟩

theorem runPrefix (pre : State → Prop) (ps : List Piece) (j : Nat)
    (loc : ∀ p∈ps,p.Local)
    (cuts : ∀ i (hi : i<ps.length),
      CutClean pre (((ps.take i).map Piece.L).flatten) (ps[i]).moved ∧
      CutClean pre (((ps.take (i+1)).map Piece.L).flatten) (ps[i]).moved)
    (s : State) (hs : pre s) (m : List Bool) :
    run (((ps.take j).map Piece.H).flatten) m s=run (((ps.take j).map Piece.L).flatten) m s := by
  have all := cuts_of_index pre ps [] (fun i hi => by simpa only [List.nil_append] using cuts i hi)
  exact run_eq_of_cuts pre (ps.take j) [] (fun pc h => loc pc (List.mem_of_mem_take h))
    (takeCuts pre j ps [] all) s hs m

theorem entry (j : Nat) (s : State) (hs : EntryPre s) (m : List Bool) :
    let ps := entryPieces checkpointPrimitives hostPlan
    run (((ps.take j).map Piece.H).flatten) m s=run (((ps.take j).map Piece.L).flatten) m s := by
  have c := StairField13V3Clean.entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760
  have cuts := entrySlotsClean_of _ _ _ (entrySlots_of_v3 (entrySlotsV3_of_parts
    (StairField13V3Fresh.entryParts_of_clean c)))
  exact runPrefix _ _ _ (entryPieces_local _ _) cuts s hs m

theorem exit (k j : Nat) (s : State) (hs : ExitPre k s) (m : List Bool) :
    let ps := exitPieces checkpointPrimitives hostPlan k
    run (((ps.take j).map Piece.H).flatten) m s=run (((ps.take j).map Piece.L).flatten) m s := by
  have c := StairField13V3Clean.exitClean_of_planR StairOpenWiring.exitPlans StairOpenWiring.half760 k
  have cuts := exitSlotsClean_of _ _ _ _ (exitSlots_of_v3 k (exitSlotsV3_of_parts k
    (StairField13V3Fresh.exitParts_of_clean k c)))
  exact runPrefix _ _ _ (exitPieces_local _ _ k) cuts s hs m

end ECDSAAdd.Entrant.Stair44HostedCut

end

section

namespace ECDSAAdd.Entrant.Stair44OuterX
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement Baselines
  ParityXEntry FlagEntry ParityEven Stair44PointMap
set_option maxRecDepth 30000
set_option maxHeartbeats 1800000
attribute [local irreducible] run wires layout pmapR
def cleanIndex (i : Nat) : Prop := i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722

theorem pool (i : Nat) (hi : cleanIndex i) : pmapR layout (base i) ∈ layout.dialogPool := by
  apply pmap_pool _ layout_widths layout_nodup
  · exact List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by unfold cleanIndex at hi; omega))
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold cleanIndex at hi
    omega
  · intro e; have := base_injective e; unfold cleanIndex at hi; omega

private def exitIndices : List Nat := [1542,1541,721,722,500,501,502,503,504,514]

theorem direct (s : State) (m : List Bool) (X : Nat) (hx : regValue layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue layout.dialogPool s.basis=0) (i : Nat) (hi : i∈exitIndices) :
    (run (E1QubitPlacement.tickF layout) m s).basis (pmapR layout (base i)) = false := by
  let f := pmapR layout
  let t := pullState f s
  have cl (j : Nat) (hj : cleanIndex j) : t.basis (base j) = false :=
    (regValue_zero _ _).mp hc _ (pool j hj)
  have blk (a n : Nat) (h : a+n ≤ 515 ∨ (1026 ≤ a ∧ a+n ≤ 1285) ∨ (1540≤a ∧ a+n≤1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact cl j (by unfold cleanIndex; omega)
  have Hx : regValue (wireBlock base 770 256) t.basis = X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (f q)) = X
    rw [regValue_pull,pmap_x layout layout_widths layout_nodup,hx]
  have kv : regValue (E1Merge.kR base) t.basis = X := by
    rw [E1Merge.kR_x base base_pool_nodup, show E1Merge.xR base=wireBlock base 770 256 from rfl,
      Hx,blk 1026 2 (by decide)]
    simp
  have seed : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 X t.basis :=
    ⟨blk 0 258 (by decide), kv, blk 1540 257 (by decide), cl 1797 (by unfold cleanIndex; decide),
      cl 1028 (by unfold cleanIndex; decide),cl 1797 (by unfold cleanIndex; decide)⟩
  have range : cleanIndex i := by simp [exitIndices] at hi; unfold cleanIndex; omega
  have isS : base i∈S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i
    (by unfold cleanIndex at range; omega))
  have phys := run_rename_pool f S (pmap_inj _ layout_widths layout_nodup) _
    forward_S m t s rfl (fun _ _ => rfl)
  rw [E1QubitPlacement.tickF,phys.2 _ isS]
  have out := NativeFirstDirect.forward_spec base base_pool_nodup X hX t m seed
  have cold : base i∉NativeFirstDirect.mutable base :=
    (by decide +kernel : ∀ i ∈ exitIndices,base i∉NativeFirstDirect.mutable base) i hi
  exact (out.2.2.2.2.2 _ cold).trans (cl i range)

theorem tickZero (s : State) (m : List Bool) (X : Nat) (hx : regValue layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue layout.dialogPool s.basis=0) :
    ∀q∈firstClean,(run (E1QubitPlacement.tickF layout) m s).basis q=false := by
  have tab : ∀ q∈firstClean, ∃i∈exitIndices, pmapR layout (base i)=q := by decide +kernel
  intro q hq
  obtain ⟨i,hi,rfl⟩ := tab q hq
  exact direct s m X hx hX hc i hi

private theorem afterAdd (k : Fp) (s : State) (m : List Bool) (X : Fp)
    (hx : regValue layout.point.x s.basis=X.val) (hc : regValue layout.dialogPool s.basis=0)
    (i : Nat) (hi : i∈exitIndices) :
    (run (entryM layout k) m s).basis (pmapR layout (base i)) = false := by
  rw [entry_eq layout layout_widths layout_nodup k s X.val X.isLt _ hx rfl hc m m,run_append]
  let cmd := fastConstAdd layout layout.point.x k
  let s1 := run cmd (m.take (measurementCount cmd)) s
  have facts := fastConstAdd_correct layout layout_widths layout_nodup layout.point.x (Or.inl rfl)
    k X.val _ X.isLt s (m.take (measurementCount cmd)) rfl hx hc
  have fresh : regValue layout.dialogPool s1.basis=0 := by
    exact (regValue_congr _ _ _ (fun q hq => facts.2.2 q
      ((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).1)).trans hc
  apply direct s1 _ _ facts.2.1 _ fresh i hi
  exact Nat.mod_lt _ (by decide)

theorem stockExit (X k : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hc : regValue layout.dialogPool s.basis=0) :
    ∀ q∈firstClean, (run (entryXNew layout (pkW layout) k) m
      (put s (pkW layout) (if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+k.val) else false))).basis q=false := by
  rw [entryXNew_run layout layout_widths layout_nodup _ X k s hx hc (pk_pool layout layout_widths)
    (pk_ne_flag layout layout_widths layout_nodup) (pk_ne_high layout layout_widths layout_nodup)
    (pk_ne_x layout layout_widths layout_nodup) (by rw [pmap_g layout layout_widths layout_nodup]; decide +kernel),
    entryXAll_eq layout layout_widths layout_nodup X k s _ hx hc]
  have mapTable : ∀ q∈firstClean, ∃i∈exitIndices, pmapR layout (base i)=q := by decide +kernel
  intro q hq
  obtain ⟨i,hi,rfl⟩ := mapTable q hq
  exact afterAdd k s _ X hx hc i hi

theorem execute (X k : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hc : regValue layout.dialogPool s.basis=0) :
    let P := entryXNew layout (pkW layout) k
    let logical := put s (pkW layout)
      (if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+k.val) else false)
    run (switchX P) m (pullState outer.symm logical) = pullState integerFirst.symm (run P m logical) := by
  intro P logical
  have prep : ∀q∈([4836,4629]:List Wire), logical.basis q=false := by
    have table : ∀q∈([4836,4629]:List Wire),q∈layout.dialogPool ∧ q≠pkW layout := by decide +kernel
    intro q hq
    have ⟨member,notFlag⟩ := table q hq
    change (put s (pkW layout) _).basis q = false
    simpa [put,writeBit,Function.update_apply,notFlag] using (regValue_zero _ _).mp hc q member
  have full (e : Equiv.Perm Wire) (a : State) : pullState e (pullState e.symm a) = a := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg a.basis (e.symm_apply_apply q)
  rw [at_x_input logical prep, ← at_x_output _ (stockExit X k s m hx hc)]
  have r := run_rename duringX duringX.injective P m (pullState duringX.symm logical)
  rw [full] at r
  have e := congrArg (pullState duringX.symm) r
  have back (a : State) : pullState duringX.symm (pullState duringX a)=a := by
    simpa only [Equiv.symm_symm] using full duringX.symm a
  rw [back] at e
  exact e

end ECDSAAdd.Entrant.Stair44OuterX

end

section

namespace ECDSAAdd.Entrant.Stair44WalkCuts
open Arithmetic MappedCompressed Stair44WalkMap
set_option maxRecDepth 8000
attribute [local irreducible] run wires Rolling1588TickGap.forward Rolling1588.Integer.regularForward

theorem release (s : State) (hp : ∀q∈Stair44WalkExit.atExit,s.basis q=false)
    (h : s.basis (base 514)=false) : pullState rest s=s := by
  have a := cleanWireRebind id s s _ _ rfl (hp _ (by decide : base 1026∈Stair44WalkExit.atExit)) h
  have b := cleanWireRebind _ s s _ _ a (hp _ (by decide : base 1541∈Stair44WalkExit.atExit))
    (hp _ (by decide : base (Placement5.H 1)∈Stair44WalkExit.atExit))
  exact cleanWireRebind _ s s _ _ b (hp _ (by decide : base 1542∈Stair44WalkExit.atExit))
    (hp _ (by decide : base (Placement5.H 0)∈Stair44WalkExit.atExit))

theorem cancel (e : Equiv.Perm Wire) {s t : State}
    (h : pullState e s = pullState e t) : s=t := by
  apply State.extensionality
  · have r := congrArg State.phase h
    exact r
  · funext q; simpa only [pullState, Equiv.apply_symm_apply] using congrFun (congrArg State.basis h) (e.symm q)

theorem forward_done (d : Bool) (a x : Nat) (atCut : 1+(15+a) ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s actual : State) (m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 1 s.basis) (input : pullState first actual=s) :
    run (Stair44WalkRun.forward d a) m actual = run (Rolling1588TickGap.forward d 1 (15+a)) m s := by
  let n := 15+a
  have bounds : 1+n ≤ 506 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut; dsimp [n]; omega
  let stock := run (Rolling1588TickGap.forward d 1 n) m s
  let raw := run (Rolling1588.Integer.regularForward base d 1 n) m s
  have zero : pullState (OB5.sig 0) s=s := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg s.basis (OB5.sig_zero q)
  have eqn := Rolling1588TickGap.forward_gen d x hx0 hx n 1 (by decide) (by omega) s m hs
  rw [show 1-1=0 by decide,zero] at eqn
  have eq' : stock = pullState (OB5.sig (1+n-1)) raw := eqn
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have stage := (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p
    1 n hp0 hx0 hpo hp (by norm_num [p]) hx cop (by omega) s m hs).2
  have flags : ∀q∈Stair44WalkExit.atExit,stock.basis q=false := by
    rw [eq']
    exact Stair44WalkExit.ready d _ x p atCut hp0 hpo raw stage
  have bit := run_preserves_outside _ m s _ (Stair44WalkSites.idle514 d 1 n (by decide) bounds).1
  have fixed := release stock flags (bit.trans (Stair44WalkExit.first_ready d x p s hs 514 (by decide)))
  have out := Stair44WalkRun.forward_run d a x hx0 hx s actual m hs input
  change pullState rest _ = stock at out
  rw [←fixed] at out
  exact cancel rest out

end ECDSAAdd.Entrant.Stair44WalkCuts

end

section

namespace ECDSAAdd.Entrant.StairArchiveNativeRows
open CodecBitSliceVerify StairArchiveGates
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 100000

def chronological (high : Bool) := (List.range 10).map
  (fun q => get integer_load0Trace0In ((if high then 10 else 0)+q))

/-- The literal incumbent's complete encoding program acts on the unmodified chronological
G/S pairs. The byte uses the same eight physical slots for both A and B. -/
theorem stock_code (isA high : Bool) :
    eval ones (Rolling1588.codeEncode isA) (chronological high) = (true, storage (native isA high)) := by
  cases isA <;> cases high <;> decide +kernel

end ECDSAAdd.Entrant.StairArchiveNativeRows

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
attribute [local irreducible] run routed measurementCount body
namespace NativePack270
open ArchiveBoundary270
end NativePack270
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
attribute [local irreducible] run W.compactSkywalkTick

theorem pastOffSpan (i n q:Nat) (bound:i+n≤512) (early:Earlier i q) : q∉wires (span i n) := by
  induction n generalizing i with
  | zero => simp [span,wires]
  | succ n ih =>
    rw [span,wires_append,Finset.mem_union]
    rintro (head|tail)
    · have sub:=W.compactSkywalkTick_support base i (by omega) base_pool_nodup
      exact away (by omega) early (List.mem_toFinset.mp (sub head))
    · exact ih (i+1) (by omega) (earlier_mono (by omega) early) tail

theorem preservePast (i n x p r:Nat) (bound:i+n≤512) (good:Bounds x p) (raw:State)
    (dom:Domain i x p raw) (rOld:r < i) (m:List Bool) :
    let out:=run (span i n) m raw
    out.basis (base r)=raw.basis (base r) ∧ out.basis (base (1028+r))=raw.basis (base (1028+r)) := by
  by_cases old:r+2 ≤ i
  · exact ⟨run_preserves_outside _ _ _ _ (pastOffSpan _ _ _ bound ⟨r,old,Or.inl rfl⟩),
      run_preserves_outside _ _ _ _ (pastOffSpan _ _ _ bound ⟨r,old,Or.inr rfl⟩)⟩
  obtain ⟨ref,same,stage⟩:=dom
  have h1:¬Earlier i (base r) := by
    rintro ⟨k,prev,h|h⟩ <;> simp only [base,Wire] at * <;> omega
  have h2:¬Earlier i (base (1028+r)) := by
    rintro ⟨k,prev,h|h⟩ <;> simp only [base,Wire] at * <;> omega
  have link:=fixed_span i i n (Nat.le_refl _) bound raw ref m same
  have endStage:=full_span i n x p bound good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime ref m stage
  have before:=(W.compactSkywalkStage_fields_iff base _ i (by omega) base_pool_nodup _).mp stage
  have after:=(W.compactSkywalkStage_fields_iff base _ (i+n) bound base_pool_nodup _).mp endStage
  have a:=before.2.2.2.1 r rOld
  have b:=after.2.2.2.1 r (by omega)
  exact ⟨(link.2 _ h1).trans (b.1.trans (a.1.symm.trans (same.2 _ h1).symm)),
    (link.2 _ h2).trans (b.2.trans (a.2.symm.trans (same.2 _ h2).symm))⟩

end ECDSAAdd.Entrant.StairPacket.WideReference

end




section

namespace ECDSAAdd.Entrant.StairPacket.StockCanonicalRow
open Arithmetic ArchivePortAction SkywalkRails IntegerPacket StairArchiveRaw CodecBitSliceVerify StairArchiveTrace
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

def key (b:Nat) (z:SkywalkNat.State) (cross:Bool) (trace:List (Bool×Bool)) (q:Nat):Bool:=
  let f:=decide (Shadow.far b 15 z)
  rawBit (read (trace.drop 5)) f (f && afterFlags (decide (z.v<z.u)) (trace.take 5)) (f && cross) q

def Encodes (v:Nat→Bool) (r:Nat):Prop:=∀q:Fin 23,(rawCol q).testBit r=v q
noncomputable def select (v:Nat→Bool):Nat:=by
  classical
  exact if h:∃r<63145,Encodes v r then h.choose else 0
theorem select_spec {v} (h:∃r<63145,Encodes v r):select v<63145 ∧ Encodes v (select v):=by
  classical
  simpa only [select,dif_pos h] using h.choose_spec

theorem frame_key (j:Fin 26) (ps:Ports) (chron:∀i:Fin 20,ps ⟨i,by omega⟩=nativeRawPort j i)
    (r:Nat) (b:Nat) (z:SkywalkNat.State) (g sg cross:Bool) (before out:State)
    (prior:PastFacts j ps b z g sg cross before)
    (kept:∀i:Fin 23,out.basis (ps ⟨i,by omega⟩)=before.basis (ps ⟨i,by omega⟩))
    (frame:Frame ps raw r out):
    Encodes (key b z cross (SkywalkTrace.trace 15 (encode g sg z.u z.v))) r:=by
  intro q
  have same:(rawCol q).testBit r=before.basis (ps ⟨q,by omega⟩):=
    ((congrArg (fun n:Nat=>n.testBit r) (io true true ⟨q,by omega⟩).1).trans (frame ⟨q,by omega⟩).symm).trans (kept q)
  by_cases h:q.val<20
  · have eq:=row_truth j ps chron r z g sg before out prior.records kept frame ⟨q,h⟩
    simpa only [key,rawBit,if_pos h] using eq
  · rcases q with ⟨q,bound⟩
    change ¬q<20 at h
    have cases:q=20 ∨ q=21 ∨ q=22:=by omega
    rcases cases with rfl|rfl|rfl
    · exact same.trans prior.far
    · simpa only [←prior.records] using same.trans prior.suffix
    · exact same.trans prior.crossed

theorem reframe {v r} (limit:r<63145) (eq:Encodes v r) (ps:Ports) (out:State)
    (frame:Frame ps raw r out):Frame ps raw (select v) out:=by
  have ⟨_,selected⟩:=select_spec ⟨r,limit,eq⟩
  intro i
  rw [frame i]
  by_cases old:i.val<23
  · have read:get raw i=rawCol i:=(io true true i).1.symm
    rw [read,eq ⟨i,old⟩,selected ⟨i,old⟩]
  · have empty:get raw i=0:=(blank true true i (by omega)).1
    rw [empty,Nat.zero_testBit,Nat.zero_testBit]
end ECDSAAdd.Entrant.StairPacket.StockCanonicalRow

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockDelayed
open Arithmetic MappedCompressed WideReference Rolling1588.Integer Secp256k1
attribute [local irreducible] run W.compactSkywalkTick
def packs (d:Bool) (i:Nat):Nat→Program
  | 0=>[]
  | n+1=>packAfter base d i ++ packs d (i+1) n

theorem off (d:Bool) (k i n:Nat) (lo:k < i) (hi:i+n≤512):
    Disjoint (wires (packAfter base d k)) (wires (span i n)):=by
  induction n generalizing i with
  | zero=>simp [span,wires]
  | succ n ih=>
    have offPre:=prefix_disjoint_tick base d base_pool_nodup (k+1) i lo (by omega)
    rw [encodePrefix,wires_append] at offPre
    have step:=Disjoint.mono_left (Finset.subset_union_right (s₁:=wires (encodePrefix base d k))) offPre
    have tail:=ih (i+1) (by omega) (by omega)
    rw [span,wires_append,Finset.disjoint_union_right];exact ⟨step,tail⟩

theorem deferred (d:Bool) (i n:Nat) (hi:i+n≤512) (s:State):
    run (compactForward base d i n) [] s=run (packs d i n) [] (run (span i n) [] s):=by
  induction n generalizing i s with
  | zero=>simp only [compactForward,packs,span,run]
  | succ n ih=>
    simp only [compactForward,packs,span,run_append,run_take,List.drop_nil]
    rw [ih (i+1) (by omega),run_disjoint_commute _ _ (off d i (i+1) n (by omega) (by omega))]

theorem window (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (i n:Nat) (lo:0 < i) (hi:i+n≤512)
    (s:State) (m:List Bool) (stage:Stage base d x p i s.basis):
    run (Rolling1588TickGap.forward d i n) m (pullState (OB5.sig (i-1)) s)=
      pullState (OB5.sig (i+n-1)) (run (packs d i n) [] (run (span i n) [] s)):=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x hx0 hx
  rw [Rolling1588TickGap.forward_gen d x hx0 hx n i lo hi s m stage,
    regularForward_eq base d base_pool_nodup StackOB5.historyAbove x p hp0 hx0 odd cap
      (by norm_num [p]) hx cop n i hi s m [] stage,deferred d i n hi]
end ECDSAAdd.Entrant.StairPacket.StockDelayed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open WindowFieldMask WindowFieldCosts ArchiveFieldScratch StairArchiveInactive
attribute [local irreducible] run measurementCount StairArchiveInactive.packet fieldHook
def joinTapes (P : Program) (m n : List Bool) : List Bool :=
  (m++List.replicate (measurementCount P) false).take (measurementCount P) ++ n
theorem joined (P Q : Program) (m n : List Bool) (s : State) :
    run (P++Q) (joinTapes P m n) s=run Q n (run P m s) := by
  let padded := (m++List.replicate (measurementCount P) false).take (measurementCount P)
  have len : padded.length = measurementCount P := by simp [padded]
  rw [run_append]
  change run Q ((padded++n).drop _) (run P ((padded++n).take _) s)=_
  rw [←len,List.take_left,List.drop_left]
  exact congrArg (run Q n) (TrimSquare.run_padTake P m _ s rfl)
def referenceLeg (d : Bool) : Leg→ Program
  | .native j n => group d j n
  | .paired j => first j (!d) ++ second j (!d)
def legTape (d : Bool) (m : List Bool) : Leg → List Bool
  | .native _ _ => m
  | .paired j => joinTapes (first j (!d)) (tapeA j (!d) m) (tapeB j (!d) m)
def referenceTape0 (d : Bool) : List Leg → List Bool → List Bool
  | [],_ => []
  | l::ls,m => joinTapes (referenceLeg d l) (legTape d m l) (referenceTape0 d ls (nextTape d l m))
/-- the reference tape of the record run, seen from the actual tape `m` of the field group. -/
def referenceTape (d : Bool) (ls : List Leg) (m : List Bool) : List Bool :=
  referenceTape0 d ls (WindowFieldCosts.cellTape d m)

set_option maxRecDepth 8000
set_option maxHeartbeats 900000
private theorem shape' (d : Bool) (p : Nat→Program) : PacketSequence.program d p 1 84 =
  let seq := PacketSequence.program d p
  if d then seq 1 9 ++ ((p 10 ++ p 11) ++ (seq 12 1 ++ ((p 13 ++ p 14) ++ (seq 15 1 ++ ((p 16 ++ p 17) ++ (seq 18 1 ++ ((p 19 ++ p 20) ++ (seq 21 1 ++ ((p 22 ++ p 23) ++ (seq 24 1 ++ ((p 25 ++ p 26) ++ (seq 27 1 ++ ((p 28 ++ p 29) ++ (seq 30 1 ++ ((p 31 ++ p 32) ++ (seq 33 2 ++ ((p 35 ++ p 36) ++ (seq 37 2 ++ ((p 39 ++ p 40) ++ (seq 41 2 ++ ((p 43 ++ p 44) ++ (seq 45 2 ++ ((p 47 ++ p 48) ++ (seq 49 2 ++ ((p 51 ++ p 52) ++ (seq 53 2 ++ ((p 55 ++ p 56) ++ (seq 57 2 ++ ((p 59 ++ p 60) ++ (seq 61 2 ++ ((p 63 ++ p 64) ++ (seq 65 2 ++ ((p 67 ++ p 68) ++ (seq 69 1 ++ ((p 70 ++ p 71) ++ (seq 72 1 ++ ((p 73 ++ p 74) ++ (seq 75 1 ++ ((p 76 ++ p 77) ++ (seq 78 1 ++ ((p 79 ++ p 80) ++ (seq 81 1 ++ ((p 82 ++ p 83) ++ (seq 84 1 ++ []))))))))))))))))))))))))))))))))))))))))))))
  else seq 84 1 ++ ((p 83 ++ p 82) ++ (seq 81 1 ++ ((p 80 ++ p 79) ++ (seq 78 1 ++ ((p 77 ++ p 76) ++ (seq 75 1 ++ ((p 74 ++ p 73) ++ (seq 72 1 ++ ((p 71 ++ p 70) ++ (seq 69 1 ++ ((p 68 ++ p 67) ++ (seq 65 2 ++ ((p 64 ++ p 63) ++ (seq 61 2 ++ ((p 60 ++ p 59) ++ (seq 57 2 ++ ((p 56 ++ p 55) ++ (seq 53 2 ++ ((p 52 ++ p 51) ++ (seq 49 2 ++ ((p 48 ++ p 47) ++ (seq 45 2 ++ ((p 44 ++ p 43) ++ (seq 41 2 ++ ((p 40 ++ p 39) ++ (seq 37 2 ++ ((p 36 ++ p 35) ++ (seq 33 2 ++ ((p 32 ++ p 31) ++ (seq 30 1 ++ ((p 29 ++ p 28) ++ (seq 27 1 ++ ((p 26 ++ p 25) ++ (seq 24 1 ++ ((p 23 ++ p 22) ++ (seq 21 1 ++ ((p 20 ++ p 19) ++ (seq 18 1 ++ ((p 17 ++ p 16) ++ (seq 15 1 ++ ((p 14 ++ p 13) ++ (seq 12 1 ++ ((p 11 ++ p 10) ++ (seq 1 9 ++ [])))))))))))))))))))))))))))))))))))))))))))) := by
  cases d <;> simp [PacketSequence.program,List.append_assoc]
end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
abbrev Hops := List (Wire×Wire)
/-- Each step adds previous carry times a control into a borrowed bit.
The identical gate on exit restores its original value. -/
def chain (src last target : Wire) : Hops→Program
  | [] => [.CCX src last target]
  | (c,b)::xs => [.CCX src c b] ++ chain b last target xs ++ [.CCX src c b]
def mcx (a b src last t : Wire) (xs : Hops) :=
  chain src last t xs ++ ([Instr.CCX a b src] ++ (chain src last t xs ++ [Instr.CCX a b src]))
inductive Aff where
  | x (dst : Wire)
  | cx (src dst : Wire)
  deriving DecidableEq
def gate : Aff→Instr
  | .x w => .X w
  | .cx c w => .CX c w
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed WindowParityDirty
def region : Program := []
def site (j i : Nat) := OB5.sig 511 (NewHistory5.payloadWire base (8*j+i))
def other (j : Nat) := if j=43 then 47 else 43
def port (j q : Nat) : Wire :=
  if q<16 then site j q else if q=16 then FrontierEntry1591Field.host else site (other j) (q-17)
def bankCorrection (j : Nat) := renameProgram (port j) region
def correction := bankCorrection 10 ++ (bankCorrection 13 ++ (bankCorrection 16 ++ (bankCorrection 19 ++ (bankCorrection 22 ++ (bankCorrection 25 ++ (bankCorrection 28 ++ (bankCorrection 31 ++ (bankCorrection 35 ++ (bankCorrection 39 ++ (bankCorrection 43 ++ (bankCorrection 47 ++ (bankCorrection 51 ++ (bankCorrection 55 ++ (bankCorrection 59 ++ (bankCorrection 63 ++ (bankCorrection 67 ++ (bankCorrection 70 ++ (bankCorrection 73 ++ (bankCorrection 76 ++ (bankCorrection 79 ++ (bankCorrection 82)))))))))))))))))))))
def setup := StairSchedule.paritySetup ++ correction
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires measurementCount Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

theorem key510 (x : Nat) (hx0 : 0 < x) (hx : x < p) (a u : State)
    (stage : Rolling1588.Integer.Stage base false x p 508 a.basis) (r2 : List Bool)
    (hu : ∀ q ∈ skywalkPoolWires base, u.basis q =
      (run (((W.repairedTick base 508 ++ W.repairedTick base 509) ++ W.repairedTick base 510) ++
        Rolling1588.Integer.packAfter base false 510) r2 a).basis q)
    (r : List Bool) :
    run Z1 r (pullState (sig 510) u) = run Y r (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32 ≤ 2^256 := by norm_num [p]
  have pool : ∀ q∈sitesT8,q∈(skywalkPoolWires base).toFinset :=
    fun q hq => List.mem_toFinset.mpr (sitesT8_pool q hq)
  have dec : wires (Rolling1588.Integer.decodeBefore base false 510)⊆(skywalkPoolWires base).toFinset := by
    have d := (History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←Rolling1588.Integer.decodeBefore_support_eq base false 510] at d
    exact d
  have hB : wires (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8)⊆(skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,fun q hq => pool q (List.mem_toFinset.mp (tickMR8_wires hq))⟩
  have u10 := Rolling1588.Integer.untick_pool base false base_pool_nodup 510 (by omega)
  have u9 := Rolling1588.Integer.untick_pool base false base_pool_nodup 509 (by omega)
  rw [Rolling1588.Integer.decode509 false,List.nil_append] at u9
  have u8 := Rolling1588.Integer.untick_pool base false base_pool_nodup 508 (by omega)
  rw [Rolling1588.Integer.decode508 false,List.nil_append] at u8
  have hO : wires (Rolling1588.Integer.decodeBefore base false 510 ++ ((W.ReverseCarry.compactReceiverTick base 510 ++
      W.ReverseCarry.compactReceiverTick base 509) ++
      W.ReverseCarry.compactReceiverTick base 508))⊆(skywalkPoolWires base).toFinset := by
    rw [←List.append_assoc,←List.append_assoc,wires_append,wires_append,Finset.union_subset_iff,
      Finset.union_subset_iff]
    exact ⟨⟨u10,u9⟩,u8⟩
  have inner (r : List Bool) :
      run (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8) r u=
        run (Rolling1588.Integer.decodeBefore base false 510 ++ ((W.ReverseCarry.compactReceiverTick base 510 ++
          W.ReverseCarry.compactReceiverTick base 509) ++
          W.ReverseCarry.compactReceiverTick base 508)) r u :=
    Stack5.local_replace _ _ _ hB hO u _ r r
      (fun q hq => hu q (List.mem_toFinset.mp hq))
      (Rolling1588.Integer.blockN_eq_new false x hx0 hx a stage r2 r)
  have s9 := (Rolling1588.Integer.step_spec base false base_pool_nodup StackOB5.historyAbove x p 508 hp0 hx0 hpo hp hgap hx
    cop (by omega) a [] stage).2
  simp only [Rolling1588.Integer.pack508 false,List.append_nil] at s9
  obtain ⟨b8,hb8⟩ : ∃ b8 : State,run (W.repairedTick base 508) [] a=b8 := ⟨_,rfl⟩
  rw [hb8] at s9
  have s10 := (Rolling1588.Integer.step_spec base false base_pool_nodup StackOB5.historyAbove x p 509 hp0 hx0 hpo hp hgap hx
    cop (by omega) b8 [] s9).2
  simp only [Rolling1588.Integer.pack509 false,List.append_nil] at s10
  obtain ⟨b9,hb9⟩ : ∃ b9 : State,run (W.repairedTick base 509) [] b8=b9 := ⟨_,rfl⟩
  rw [hb9] at s10
  have rawE : run (((W.repairedTick base 508 ++ W.repairedTick base 509) ++ W.repairedTick base 510) ++
      Rolling1588.Integer.packAfter base false 510) [] a=
        run (W.repairedTick base 510 ++ Rolling1588.Integer.packAfter base false 510) [] b9 := by
    rw [←hb9,←hb8]
    simp only [List.append_assoc,run_append,List.take_nil,List.drop_nil]
  have hu' : ∀ q∈skywalkPoolWires base,
      u.basis q=(run (W.repairedTick base 510 ++ Rolling1588.Integer.packAfter base false 510) [] b9).basis q := by
    intro q hq
    rw [hu q hq,←rawE]
    exact congrFun (run_basis_records _ a a r2 [] rfl) q
  have z10 := Rolling1588.Integer.stage_zero false x 510 (by omega) b9.basis s10
  have z9 := Rolling1588.Integer.stage_zero false x 509 (by omega) b8.basis s9
  have c9 := Rolling1588.Integer.stage_zero_gen false x 508 509 (by omega) (by omega) a.basis stage
  have c10 := Rolling1588.Integer.stage_zero_gen false x 508 510 (by omega) (by omega) a.basis stage
  have rt10 (r1 : List Bool) := Rolling1588.Integer.oneStep_roundtrip base false base_pool_nodup x p 510 hp0 hx0 hpo hp hgap hx
    cop (by omega) b9 s10 [] r1
  have rt9 (r1 : List Bool) := Rolling1588.Integer.oneStep_roundtrip base false base_pool_nodup x p 509 hp0 hx0 hpo hp hgap hx
    cop (by omega) b8 s9 [] r1
  simp only [Rolling1588.Integer.decode509 false,Rolling1588.Integer.pack509 false,List.nil_append,List.append_nil,hb9] at rt9
  have rt8 (r1 : List Bool) := Rolling1588.Integer.oneStep_roundtrip base false base_pool_nodup x p 508 hp0 hx0 hpo hp hgap hx
    cop (by omega) a stage [] r1
  simp only [Rolling1588.Integer.decode508 false,Rolling1588.Integer.pack508 false,List.nil_append,List.append_nil,hb8] at rt8
  have rn10 := (renameProgram_counts (sig 510)
    (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510)).2
  have rn9 := (renameProgram_counts (sig 509) (W.ReverseCarry.compactReceiverTick base 509)).2
  show run (renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8)) r (pullState (sig 510) u)=
        run ((renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++
            W.ReverseCarry.compactReceiverTick base 510) ++
          renameProgram (sig 509) (W.ReverseCarry.compactReceiverTick base 509)) ++
          renameProgram (sig 508) (W.ReverseCarry.compactReceiverTick base 508)) r
          (pullState (sig 510) u)
  rw [OB5.run_rename 510 (by omega),inner r]
  have e : Rolling1588.Integer.decodeBefore base false 510 ++ ((W.ReverseCarry.compactReceiverTick base 510 ++
      W.ReverseCarry.compactReceiverTick base 509) ++ W.ReverseCarry.compactReceiverTick base 508)=
      ((Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) ++
        W.ReverseCarry.compactReceiverTick base 509) ++ W.ReverseCarry.compactReceiverTick base 508 := by
    simp only [List.append_assoc]
  rw [e,Rolling1588.Integer.run_append3,Rolling1588.Integer.run_append3,rn10,rn9]
  obtain ⟨r1,hr1⟩ : ∃ r1 : List Bool,r.take (measurementCount (Rolling1588.Integer.decodeBefore base false 510 ++
    W.ReverseCarry.compactReceiverTick base 510))=r1 := ⟨_,rfl⟩
  obtain ⟨r3,hr3⟩ : ∃ r3 : List Bool,(r.drop (measurementCount (Rolling1588.Integer.decodeBefore base false 510 ++
    W.ReverseCarry.compactReceiverTick base 510))).take
      (measurementCount (W.ReverseCarry.compactReceiverTick base 509))=r3 := ⟨_,rfl⟩
  obtain ⟨r5,hr5⟩ : ∃ r5 : List Bool,r.drop (measurementCount (Rolling1588.Integer.decodeBefore base false 510 ++
    W.ReverseCarry.compactReceiverTick base 510)+
      measurementCount (W.ReverseCarry.compactReceiverTick base 509))=r5 := ⟨_,rfl⟩
  rw [hr1,hr3,hr5,OB5.run_rename 510 (by omega)]
  have a1 := OB5.pool_agree _ u10 r1 u _ hu'
  rw [rt10 r1] at a1
  have a2 := OB5.pool_agree _ u9 r3 _ _ a1
  rw [rt9 r3] at a2
  have a3 := OB5.pool_agree _ u8 r5 _ _ a2
  rw [rt8 r5] at a3
  have v1c : (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u).basis
      (base (1028+510))=false :=
    (a1 _ (OB5.base_pool _ (by omega))).trans z10.1
  have v1d : 257 ≤ 510 → (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u).basis
      (base (2053-510))=false :=
    fun big => (a1 _ (OB5.base_pool _ (by omega))).trans (z10.2 big)
  rw [←OB5.pull_step 510 (by omega) _ v1c v1d,OB5.run_rename 509 (by omega)]
  have v2c : (run (W.ReverseCarry.compactReceiverTick base 509) r3
      (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u)).basis
      (base (1028+509))=false :=
    (a2 _ (OB5.base_pool _ (by omega))).trans z9.1
  have v2d : 257 ≤ 509 → (run (W.ReverseCarry.compactReceiverTick base 509) r3
      (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u)).basis
      (base (2053-509))=false :=
    fun big => (a2 _ (OB5.base_pool _ (by omega))).trans (z9.2 big)
  rw [←OB5.pull_step 509 (by omega) _ v2c v2d,OB5.run_rename 508 (by omega)]
  have p9 := OB5.pull_step 509 (by omega) _
    ((a3 _ (OB5.base_pool _ (by omega))).trans c9.1)
    (fun big => (a3 _ (OB5.base_pool _ (by omega))).trans (c9.2 big))
  have p10 := OB5.pull_step 510 (by omega) _
    ((a3 _ (OB5.base_pool _ (by omega))).trans c10.1)
    (fun big => (a3 _ (OB5.base_pool _ (by omega))).trans (c10.2 big))
  exact (p9.trans p10).symm

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.Stair44DivisionCut
open ECDSAAdd Arithmetic MappedCompressed Secp256k1
open StairField13V3 StairConcreteAssembly
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires renameProgram

def beforeClose (pr : StairSchedule.StairPrimitives) (h : StairHostsSchedule.HostPlan) :=
  renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase pr) ++
    StairHostsSchedule.entryFieldHosted pr h

theorem selected (pr : StairSchedule.StairPrimitives) (h : StairHostsSchedule.HostPlan) :
    (((entryPieces pr h).take 24).map Piece.H).flatten = beforeClose pr h := by
  simp only [entryPieces,List.take_succ_cons,List.take_zero,groupSlot,firstSlot,lowCommon,common,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,beforeClose,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.entryLowPrefix,StairHostsSchedule.entryTailPrefix,
    StairHostsSchedule.entryLowSuffix,StairHostsSchedule.entryTailSuffix,fieldRename_append,rename_append,List.append_assoc]

theorem logical (h : StairHostsSchedule.HostPlan) :
    (((entryPieces checkpointPrimitives h).take 24).map Piece.L).flatten =
      StairLoanField7Cores.entrySelectedArithmeticFor StairConcrete.bestLoans := by
  simp only [entryPieces,List.take_succ_cons,List.take_zero,groupSlot,firstSlot,lowCommon,common,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    StairLoanField7Cores.entrySelectedArithmeticFor,StairSchedule.entryFieldHosted,
    StairSchedule.entryLowPrefix,StairSchedule.entryTailPrefix,StairSchedule.entryLowSuffix,
    StairSchedule.entryTailSuffix,fieldRename_append,rename_append,List.append_assoc]

theorem reference {t : State} (F : EntryFrame t) (m : List Bool) :
    run (beforeClose checkpointPrimitives hostPlan) m t =
      run (StairLoanRecordSupport.entryFieldHostedShape StairConcrete.bestLoans) []
        (run (Rolling1588.firstPhase true) [] t) := by
  have bridge := Stair44HostedCut.entry 24 t ⟨F⟩ m
  change run (((entryPieces checkpointPrimitives hostPlan).take 24).map Piece.H).flatten m t =
    run (((entryPieces checkpointPrimitives hostPlan).take 24).map Piece.L).flatten m t at bridge
  rw [selected,logical] at bridge
  have core := StairLoanField7RR.entryCoreR_best StairOpenWiring.half760 StairOpenWiring.entryPlans t ⟨F⟩ m []
  rw [bridge,core,StairLoanField7Cores.entryReferenceArithmeticFor,run_append]
  simp only [List.take_nil,List.drop_nil]
  rw [StairLoanField7Values.first_phase_hosted true F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt
    t [] (StairField13V3Clean.entryInput F)]

theorem pool {t : State} (F : EntryFrame t) (m : List Bool) :
    let z := run (beforeClose checkpointPrimitives hostPlan) m t
    let y := run (Rolling1588.firstPhase false) [] t
    z.phase=y.phase ∧ ∀q∈skywalkPoolWires base,z.basis q=y.basis q := by
  rw [reference F]
  have r := StairLoanRecordKernel.shape_entry_boundary StairOpenWiring.half760 F.sharedNodup F.historyAbove
    F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt F.source t [] [] F.input F.selectorG_zero
    F.selectorS_zero F.phase F.outsideNumerator F.numerator
  refine ⟨r.1,fun q hq => r.2.2 q (FrontierEntry1591Kernel.pool_away_numerator q hq)⟩

end ECDSAAdd.Entrant.Stair44DivisionCut

end

section

namespace ECDSAAdd.Entrant.Stair44MultiplyCut
open Arithmetic MappedCompressed Secp256k1
open StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairField2V3Delta StairField2V3Couple StairField2V3Entry
open StairField2V3ExitPlan StairField2V3ExitPlanR StairField2V3Final
open StairLoanField7Transport StairLoanField7R StairLoanExitReachX
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires renameProgram

def lastRows := (XS21 ++ grpFL StairConcrete.bestLoans 0 1 84) ++ lowTail

private theorem reached (k x : Nat) :
    ∃ Q, CRel (XPreX k x) (RowRelL k x 87 (YFL StairConcrete.bestLoans)) lastRows Q := by
  obtain ⟨Q,h⟩ := rch21 k x (StairOpenWiring.exitPlans k x) StairOpenWiring.half760
  have next := sharedL k x 87 (grpFL StairConcrete.bestLoans 0 1 84) ZE
    (away_of_sub _ _ _ exitGroupSub_best.2.2.2.2.2 (grpF_away 87 (by decide) 1 84 (by decide)))
  exact ⟨_,crel_append (crel_append h next)
    (sharedL k x 87 lowTail (ZE ++ grpFL StairConcrete.bestLoans 0 1 84) low_away)⟩

theorem recover (k x : Nat) (u : State) (hp : ExitMiddleX k x u) (rows unpack : List Bool) :
    let a := run (closeSel cp) unpack (run lastRows rows u)
    ∃ (s1 : State) (enc : List Bool),
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis ∧
      pullState Rolling1588Lifetime.phaseHost a = run (Rolling1588TickGap.forward true 1 424) enc s1 := by
  obtain ⟨Q,h⟩ := reached k x
  obtain ⟨old,rel,ref⟩ := h u u ⟨hp,rfl⟩ rows
  have ordinary := (exitReachTransportR_best StairOpenWiring.half760 k x).f _ ref
  obtain ⟨t0,c,adm,eq⟩ := StairField2V3ExitRecClose.closeRec_of
    StairField2V3JuncSel2.ExtraSel StairField2V3JuncSel2.extraSel_genuine k x _ ordinary
  rw [eq] at rel
  have before := relX_unique x 87 _ _ _ rel (StairField2V3JuncSel2.junc x t0 adm [] c)
  have back := StairField2V3JuncSel2.firstTrip_sel x t0 adm [] unpack
  dsimp only
  rw [before,back]
  exact adm.2.2.2

def beforeClose (h : StairHostsSchedule.HostPlan) :=
  exitReferenceOpening ++ StairHostsSchedule.exitFieldHosted cp h

theorem selected (k : Nat) (h : StairHostsSchedule.HostPlan) :
    (((exitPieces cp h k).take 24).map Piece.H).flatten = beforeClose h := by
  simp only [exitPieces,List.take_succ_cons,List.take_zero,groupSlot,firstSlot,lowCommon,common,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,beforeClose,
    exitReferenceOpening,StairHostsSchedule.exitFieldHosted,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.exitHeadPrefix,StairHostsSchedule.exitLowSuffix,StairHostsSchedule.exitHeadSuffix,
    StairHostsSchedule.hostedEndpoint,fieldRename_append,rename_append,List.append_assoc]

theorem logical (k : Nat) :
    (((exitPieces cp hostPlan k).take 24).map Piece.L).flatten = exitReferenceOpening ++ lastRows := by
  change cut (xps k) 24=_
  rw [cut_succ (xps k) 23 (xL k 23 (by decide)),xcut23]
  change (exitReferenceOpening ++ XS23) ++ StairSchedule.fieldRename (Rolling1588.placedFirstPacket false)=_
  simp only [XS23,lastRows,lowTail,fieldRename_append,List.append_assoc]

theorem pool (k : Nat) {t : State} (F : ExitFrame k t) (m tail : List Bool) :
    let a := run (closeSel cp) tail (run (beforeClose hostPlan) m t)
    ∃ (s1 : State) (enc : List Bool),
      W.CompactSkywalkStage base (SkywalkRails.encode false false (F.x:Int) (p:Int)) 1 s1.basis ∧
      pullState Rolling1588Lifetime.phaseHost a = run (Rolling1588TickGap.forward true 1 424) enc s1 := by
  have bridge := Stair44HostedCut.exit k 24 t ⟨F⟩ m
  change run (((exitPieces cp hostPlan k).take 24).map Piece.H).flatten m t =
    run (((exitPieces cp hostPlan k).take 24).map Piece.L).flatten m t at bridge
  rw [selected,logical,run_append exitReferenceOpening lastRows] at bridge
  dsimp only
  rw [bridge]
  exact recover k F.x _ ⟨t,F,rfl,_,rfl⟩ _ tail
end ECDSAAdd.Entrant.Stair44MultiplyCut

end

section

namespace ECDSAAdd.Entrant.Stair44PlacedHead
open Arithmetic MappedCompressed Secp256k1 Baselines ControlledPointLayout CompressedPointDialog
  CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry ParityUniform ParityEven Stair44PointMap
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
attribute [local irreducible] run measurementCount

def plain (kx ky : Fp) := OddOuterBridge.plainOdd kx ky
def routed (kx ky : Fp) := OddOuterBridge.routedOdd kx ky

theorem unpull (f : Equiv.Perm Wire) (s : State) : pullState f.symm (pullState f s)=s := by
  apply State.extensionality
  · rfl
  · funext q; exact congrArg s.basis (f.apply_symm_apply q)

theorem encoded_head (X Y kx ky : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hy : regValue layout.point.y s.basis=Y.val)
    (clean : regValue layout.dialogPool s.basis=0) :
    let flag := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+kx.val) else false
    let initial := put s (pkW layout) flag
    run (routed kx ky) m (pullState outer.symm initial)=pullState integerFirst.symm (run (plain kx ky) m initial) :=
  OddOuterBridge.encoded_head_odd X Y kx ky s m hx hy clean
    (fun sY mX xc pc => Stair44OuterX.execute X kx sY mX xc pc)

theorem cleanInteger (s : State) (hc : regValue layout.dialogPool s.basis=0) : pullState integerFirst s=s := by
  let pairs : List (Wire × Wire) := [(4835,4615),(4837,4616),(4836,4629)]
  have members : ∀ab∈pairs,ab.1∈layout.dialogPool ∧ ab.2∈layout.dialogPool := by decide +kernel
  apply (clean_chain pairs id s s (fun ab hab => ⟨(regValue_zero _ _).mp hc _ (members ab hab).1,
    (regValue_zero _ _).mp hc _ (members ab hab).2⟩)).mpr
  rfl

theorem encodedTick (s : State) (m : List Bool) (hc : regValue layout.dialogPool s.basis=0) :
    run (renameProgram integerFirst (E1QubitPlacement.tickF layout)) m s=
    pullState integerFirst.symm (run (E1QubitPlacement.tickF layout) m s) := by
  have e := congrArg (pullState integerFirst.symm)
    (run_rename integerFirst integerFirst.injective (E1QubitPlacement.tickF layout) m s)
  rw [unpull,cleanInteger s hc] at e
  exact e

end ECDSAAdd.Entrant.Stair44PlacedHead

end

section

namespace ECDSAAdd.Entrant.Stair44WalkCuts
open Arithmetic MappedCompressed Stair44WalkMap
set_option maxRecDepth 8000
attribute [local irreducible] run wires Rolling1588.reverse Rolling1588TickGap.forward
  Rolling1588.Integer.regularForward Rolling1588.Integer.regularReverse measurementCount
  Rolling1588.Integer.reverse Stair44WalkRun.backward

theorem early514 (d : Bool) (x p : Nat) (s : State)
    (hs : Rolling1588.Integer.Stage base d x p 16 s.basis) : s.basis (base 514)=false := by
  obtain ⟨raw,hraw,bits⟩ := hs
  rw [congrFun bits _, Rolling1588.Integer.encodePrefix_index base d 3]
  have far : base 514 ∉ wires (Rolling1588.allEncode base d 3) := by
    intro used
    have h := List.mem_toFinset.mp (Rolling1588.allEncode_history_support base d 3 (by decide) used)
    rcases List.mem_append.mp h with a|a
    all_goals obtain ⟨t,ht,et⟩ := List.mem_map.mp a
    all_goals have r := List.mem_range'_1.mp ht
    all_goals have e := Nat.add_right_cancel et
    all_goals omega
  rw [run_preserves_outside _ [] raw _ far]
  have exp := (W.compactSkywalkStage_fields_iff base _ 16 (by decide) base_pool_nodup raw.basis).mp hraw
  exact (exp.2.2.2.2.1 256 (by decide) (by decide)).1

theorem backward_start (d : Bool) (a x : Nat) (atCut : 16+a ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s v : State) (enc m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 16 s.basis)
    (agree : ∀q ∈ skywalkPoolWires base,v.basis q=(run (Rolling1588.Integer.regularForward base d 16 a) enc s).basis q) :
    let t := pullState (OB5.sig (16+a-1)) v
    pullState first (run (Stair44WalkRun.backward d a) m t) = run (Rolling1588.reverse d 1 (15+a)) m t := by
  let i := 16+a
  have bound : 16+a ≤ 506 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut; omega
  let raw := run (Rolling1588.Integer.regularForward base d 16 a) enc s
  let t := pullState (OB5.sig (i-1)) v
  let ref := pullState (OB5.sig (i-1)) raw
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have stage := (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p
    16 a hp0 hx0 hpo hp (by norm_num [p]) hx cop (by omega) s enc hs).2
  have flags := Stair44WalkExit.ready d i x p atCut hp0 hpo raw stage
  have inpool : ∀ j∈[425,505,506], ∀ q∈base 514 :: Stair44WalkExit.atExit,
      OB5.sig (j-1) q ∈ skywalkPoolWires base := by decide +kernel
  have same (q : Wire) (hq : q∈base 514 :: Stair44WalkExit.atExit) : t.basis q=ref.basis q :=
    agree _ (inpool _ atCut _ hq)
  have stock := Rolling1588TickGap.forward_gen d x hx0 hx a 16 (by decide) (by omega) s enc hs
  have eqn : run (Rolling1588TickGap.forward d 16 a) enc (pullState (OB5.sig 15) s) = ref := stock
  have bit := run_preserves_outside _ enc (pullState (OB5.sig 15) s) _ (Stair44WalkSites.idle514 d 16 a (by decide) bound).1
  rw [eqn] at bit
  have sig : OB5.sig 15 (base 514)=base 514 := by decide
  have t514 : t.basis (base 514)=false := (same _ (List.mem_cons_self)).trans (bit.trans (by simpa only [pullState,sig] using early514 d x p s hs))
  have fix := release t (fun q hq => (same q (List.mem_cons_of_mem _ hq)).trans (flags q hq)) t514
  exact Stair44WalkRun.backward_run d a x (by omega) hx0 hx s v t enc m hs agree fix

private theorem fsplit (d : Bool) (i n m : Nat) :
    Rolling1588.Integer.regularForward base d i (n+m) =
    Rolling1588.Integer.regularForward base d i n ++ Rolling1588.Integer.regularForward base d (i+n) m := by
  induction n generalizing i with
  | zero => simp [Rolling1588.Integer.regularForward]
  | succ n ih =>
    simp only [Nat.succ_add,Rolling1588.Integer.regularForward,List.append_assoc]
    rw [ih]
    rw [show i+(n+1)=i+1+n by omega]

theorem start16 (d : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (enc : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 1 s.basis) :
    Rolling1588.Integer.Stage base d x p 16 (run (Rolling1588.Integer.regularForward base d 1 15) enc s).basis := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  exact (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p
    1 15 hp0 hx0 hpo hp (by norm_num [p]) hx cop (by decide) s enc hs).2

theorem decompose (d : Bool) (i n a : Nat) (s : State) (enc : List Bool) :
    let pr := Rolling1588.Integer.regularForward base d i n
    let late := Rolling1588.Integer.regularForward base d (i+n) a
    run (Rolling1588.Integer.regularForward base d i (n+a)) enc s =
      run late (enc.drop (measurementCount pr)) (run pr (enc.take (measurementCount pr)) s) := by
  rw [fsplit d i n a]
  exact run_append _ _ _ _

theorem restore_raw (d : Bool) (a x : Nat) (atCut : 16+a ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s v : State) (enc m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 1 s.basis)
    (agree : ∀q ∈ skywalkPoolWires base,v.basis q=(run (Rolling1588.Integer.regularForward base d 1 (15+a)) enc s).basis q) :
    let t := pullState (OB5.sig (16+a-1)) v
    ∀q∈skywalkPoolWires base,(run (Rolling1588.reverse d 1 (15+a)) m t).basis q=s.basis q := by
  have bound : 1+(15+a)≤512 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut; omega
  have r := Rolling1588.Integer.reverse_gen d x hx0 hx (15+a) 1 (by decide) bound s enc v m hs agree
  rw [Rolling1588.Integer.reverse_eq_packets] at r
  change ∀q∈skywalkPoolWires base,(run (Rolling1588.reverse d 1 (15+a)) m (pullState (OB5.sig (16+a-1)) v)).basis q=s.basis q
  rw [show 16+a-1=1+(15+a)-1 by omega,r.1]
  intro q hq
  change (run _ _ _).basis (OB5.sig 0 q)=_
  rw [OB5.sig_zero]
  exact r.2 q hq

end ECDSAAdd.Entrant.Stair44WalkCuts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveByte
open Arithmetic Rolling1588 StairArchiveRows StairArchiveHandoff StairArchiveNativeRows StairArchiveRaw CodecBitSliceVerify ArchiveFieldScratch
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 100000
theorem geom (d:Bool):wires (codeEncode d)=Finset.range 10:=by cases d <;> decide +kernel
private theorem cols (hi:Bool):∀q:Fin 10,get (chronological hi) q=rawCol ((if hi then 10 else 0)+q.val):=by
  cases hi <;> decide +kernel
theorem run_byte (d hi:Bool) (row:Nat) (hr:row<63145) (f:Fin 10→Wire) (inj:Function.Injective f)
    (s:State) (m:List Bool)
    (data:∀q:Fin 10,s.basis (f q)=(rawCol ((if hi then 10 else 0)+q.val)).testBit row):
    (run (codeEncodeAt d f) m s).phase=s.phase ∧ ∀q:Fin 10,
      (run (codeEncodeAt d f) m s).basis (f q)=(get (storage (native d hi)) q).testBit row:=by
  let map:=MeasuredCodec5.label f
  let t:=pullState map s
  let x:=value (chronological hi) row
  have rel:Rel (chronological hi) x row:=value_rel _ _
  have checked:=stock_code d hi
  have active:ones.testBit row=true:=by
    rw [ones,Nat.testBit_two_pow_sub_one];exact decide_eq_true hr
  have bounds:∀a∈codeEncode d,target a<(chronological hi).length:=by cases d <;> cases hi <;> decide +kernel
  have eqs(q:Nat)(hq:q∈wires (codeEncode d)):t.basis q=x.testBit q:=by
    have lt:q<10:=Finset.mem_range.mp ((geom d) ▸ hq)
    let i:Fin 10:=⟨q,lt⟩
    have h:map q=f i:=by simp [map,MeasuredCodec5.label,lt,i]
    exact (congrArg s.basis h).trans ((data i).trans ((congrArg (fun n:Nat=>n.testBit row) (cols hi i)).symm.trans (rel q).symm))
  have result:=run_row (codeEncode d) ones row x m t _ _ active bounds rel checked eqs
  have placed:=run_rename_pool map (Finset.range 10) (FirstNonzeroCodec.label_inj' f inj) (codeEncode d)
    (by rw [geom]) m t s rfl (fun _ _=>rfl)
  refine ⟨placed.1.trans result.1,?_⟩
  intro j
  have ge:j.val∈wires (codeEncode d):=(geom d).symm ▸ Finset.mem_range.mpr j.isLt
  have lay:map j.val=f j:=by simp [map,MeasuredCodec5.label,j.isLt]
  exact (congrArg (run (codeEncodeAt d f) m s).basis lay).symm.trans ((placed.2 j.val (Finset.mem_range.mpr j.isLt)).trans (result.2.1 j.val ge))
end ECDSAAdd.Entrant.StairPacket.StockArchiveByte

end



-- ==== w4: build-w4b B2-b selected_receipt (b2b/Main_SelectedReceipt.lean) ====
-- BEGIN build-w4b NativeJ.selected_receipt (B2-b part 4)
-- Main (w4r): next to dadon's `NativePack{240,255}.selected_receipt` (after `StockCanonicalRow`, Main ~5436).
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction StairArchiveTrace StockCanonicalRow Partial
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run Shadow7.onRails Shadow7.routed measurementCount Shadow7.body

/-- dadon's `NativePack{s}.selected_receipt`, generic: block `j` keeps the previous block's archive at the row
`select` picks from the recorded key. -/
theorem selected_receipt (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    let v:=key (Shadow7.sbP (start (prev j))) past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    select v<63145 ∧ Encodes v (select v) ∧ Kept (ArchiveJ7.codePorts (prev j)) d (select v) out:=by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch past pg ps cross po pm prior
  have held:=bank_kept j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1
  have all:=frame_key (prev j) (ArchiveJ7.rawPorts (prev j))
    (ArchiveJ7.chronological_all (prev j) (by simp only [prev]; omega)) row (Shadow7.sbP (start (prev j))) past pg ps cross s _
    prior held frame
  have spec:=select_spec ⟨row,limit,all⟩
  have final:=receipt j (by omega) (by omega) d pre tape _ spec.1 (reframe limit all (ArchiveJ7.rawPorts (prev j)) _ frame)
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨spec.1,spec.2,final.1⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end
-- END build-w4b NativeJ.selected_receipt
-- ==== w4: end selected_receipt ====

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open StockCanonicalRow ArchiveBoundary270 ParkEndpoint Portal270Flag Secp256k1 SkywalkRails StairArchiveTrace
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
def entryFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.fieldRename (WindowCallerCosts.entryLowPrefix p) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (WindowCallerCosts.exitLowSuffix p)

/-- `exitHeadPrefixOdd` without `center760OddLoan`: the register already holds `oddWord (Y / 2)`. -/
def exitHeadPrefixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  HalfFieldOB5.copyN ++ renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44 ++
    OddFullPass.P1LifeLoan.hostedGroup h false 44 100 2

def exitLowPrefixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  FourScratchWindow.clearProgram ++ renameProgram Prefix1590.borrow (exitHeadPrefixOddNC h) ++
    FourScratchWindow.unprefix

def exitFieldHostedNC (p : StairSchedule.StairPrimitives) : Program :=
  WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (WindowCallerCosts.exitLowSuffix p)

def entryFieldHostedCut : Program :=
  StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

/-- `OddFullPass.P1LifeLoan.entryTailSuffixOdd` without the trailing `canon760OddLoan`: the
    division leaves `λ` as `oddWord (λ / 2)` on its numerator register. -/
def entryTailSuffixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  OddFullPass.P1LifeLoan.hostedGroup h true 44 100 2 ++
    renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
    HalfFieldOB5.copyN

def entryLowSuffixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (entryTailSuffixOddNC h) ++
    FourScratchWindow.unprefix

def entryFieldHostedCutNC : Program :=
  StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (entryLowSuffixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

theorem entryTailSuffixOdd_eqNC (h : StairHostsSchedule.HostPlan) :
    OddFullPass.P1LifeLoan.entryTailSuffixOdd h =
      entryTailSuffixOddNC h ++ OddFullPass.HalfConvertOdd.canon760OddLoan := rfl

theorem field_sublist : entryFieldHostedCut.Sublist (entryFieldHosted checkpointPrimitives) := by
  have f : (StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut).Sublist
      (StairSchedule.fieldRename (WindowCallerCosts.entryLowPrefix checkpointPrimitives)) :=
    PackCutSub.rename_sub _ (PackCutSub.rename_sub _ WindowCallerCosts.low_sublist)
  unfold entryFieldHostedCut entryFieldHosted
  exact ((((f.append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append
    (List.Sublist.refl _)).append (List.Sublist.refl _)

open Stair44Outer

def divide : Program :=
  phasePlace (WindowWalkCosts.forward true 4) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace entryFieldHostedCut ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 85) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def divideNC : Program :=
  phasePlace (WindowWalkCosts.forward true 4) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace entryFieldHostedCutNC ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 85) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 84) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 4) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

/-- `multiply` with the multiplication kernel that reads its input in odd-word form. -/
def multiplyNC (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 84) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHostedNC checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 4) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

/-- The square reading `λ` in odd-word form (`SquareOdd.program`). -/
def squareNC (k : Fp) : Program := SquareOdd.program k

/-- `generic` with both field converters deleted: `divideNC`, `squareNC`, `multiplyNC`. -/
def genericNC (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (EntryFuseOdd.entryYAllOdd layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divideNC ++ squareNC (ReflectionE1.correction cx) ++ multiplyNC cx.val ++
    Stair44PointMap.encodeY (EntryFuseOdd.exitYAllOdd layout cy)

/-- The circuit: both field converters deleted (`divideNC`, `multiplyNC`) and the square reading
    the slope in odd-word form (`squareNC`). -/
def generic (cx cy : Fp) : Program := genericNC cx cy

def borrowGenericNC (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (genericNC cx cy))

def finiteNC (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGenericNC cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def programNC (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finiteNC (.some hc) cx cy)

/-- The circuit before the switch (with the two field converters), kept for the cost comparison. -/
def genericOld (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (EntryFuseOdd.entryYAllOdd layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (EntryFuseOdd.exitYAllOdd layout cy)

def borrowGenericOld (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (genericOld cx cy))

def finiteOld (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGenericOld cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def programOld (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finiteOld (.some hc) cx cy)

def borrowGeneric (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (generic cx cy))

def finite (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGeneric cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def program (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finite (.some hc) cx cy)

end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
def flip (q : Wire) (v : Bool) (s : State) : State :=
  ⟨s.phase, writeBit s.basis q (s.basis q ^^ v)⟩
@[simp] theorem at_flip (s : State) (q : Wire) (v : Bool) : (flip q v s).basis q = (s.basis q ^^ v) := by simp [flip,writeBit]
theorem at_other (s : State) (q t : Wire) (v : Bool) (ne : q≠t) : (flip t v s).basis q=s.basis q := by simp [flip,writeBit,ne]
theorem flip_twice (s : State) (t : Wire) (a b : Bool) : flip t b (flip t a s) = flip t (a^^b) s := by
  apply congrArg₂ State.mk rfl; funext q
  by_cases e : q=t
  · subst q; simp [flip,writeBit,Bool.xor_assoc]
  · simp [flip,writeBit,e]
@[simp] theorem flip_zero (s : State) (t : Wire) : flip t false s=s := by
  apply congrArg₂ State.mk rfl; funext q
  by_cases e : q=t <;> simp [flip,writeBit,e]
def outside (q last : Wire) (xs : Hops) := q≠last ∧ ∀ e∈xs,q≠e.1 ∧ q≠e.2
def safe (last target : Wire) : Wire→Hops→Prop
  | src,[] => src≠target ∧ last≠target
  | src,(c,b)::xs => src≠target ∧ c≠target ∧ b≠target ∧ src≠b ∧ c≠b ∧ outside b last xs ∧ safe last target b xs

end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires measurementCount Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

theorem head_chain (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (M : List Bool) (u : State)
    (hu : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run (Rolling1588.Integer.regularForward base false 1 510) M s1).basis q)
    (mD : List Bool) :
    run P1 mD (pullState (sig 510) u) =
      run (Rolling1588.Integer.reverse false 506 5) mD (pullState (sig 510) u) := by
  have st6 := stage_after x hx0 hx s1 first 505 (by omega)
    (M.take (measurementCount (Rolling1588.Integer.regularForward base false 1 505)))
  have ag6 := agree_split u s1 M _ _ split506 hu
  have st7 := stage_after x hx0 hx s1 first 506 (by omega)
    (M.take (measurementCount (Rolling1588.Integer.regularForward base false 1 506)))
  have ag7 := agree_split u s1 M _ _ split507 hu
  have st8 := stage_after x hx0 hx s1 first 507 (by omega)
    (M.take (measurementCount (Rolling1588.Integer.regularForward base false 1 507)))
  have ag8 := agree_split u s1 M _ _ split508 hu
  have hb : ∀ r, run P1 r (pullState (sig 510) u) = run (Q1 ++ Q2) r (pullState (sig 510) u) := by
    intro r
    rw [← PE1]
    show run (renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)) r
      (pullState (sig 510) u) = _
    rw [InverseFour15.unpack51015, OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
      InverseFive23.decoded_replace_pool15 false x hx0 hx _ u st6 _ r ag6]
  have hc : ∀ r, run Q1 r (pullState (sig 510) u) = run (Z1 ++ Z2) r (pullState (sig 510) u) := by
    intro r
    rw [← PE2]
    exact InverseFour15.placed_block15 false x hx0 hx _ u st7 _ r ag7
  have hd : ∀ r, run Z1 r (pullState (sig 510) u) = run Y r (pullState (sig 510) u) :=
    key510 x hx0 hx _ u st8 _ ag8
  have hQ : ∀ r, run Q1 r (pullState (sig 510) u) = run (Y ++ Z2) r (pullState (sig 510) u) :=
    fun r => (hc r).trans (run_congr_append Z1 Y Z2 _ hd cZ r)
  have hP : ∀ r, run P1 r (pullState (sig 510) u) =
      run ((Y ++ Z2) ++ Q2) r (pullState (sig 510) u) :=
    fun r => (hb r).trans (run_congr_append Q1 (Y ++ Z2) Q2 _ hQ cQ r)
  rw [hP mD, PE4]

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.Stair44WalkCuts
open Arithmetic MappedCompressed Stair44WalkMap Rolling1588.Integer
set_option maxRecDepth 12000
attribute [local irreducible] run wires measurementCount Rolling1588.reverse
  Rolling1588TickGap.forward regularForward Stair44WalkRun.backward

theorem backward_record (d : Bool) (a x : Nat) (atCut : 16+a ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s v : State) (enc m : List Bool)
    (hs : Stage base d x p 1 s.basis)
    (agree : ∀q ∈ skywalkPoolWires base,v.basis q=(run (regularForward base d 1 (15+a)) enc s).basis q) :
    let t := pullState (OB5.sig (16+a-1)) v
    pullState first (run (Stair44WalkRun.backward d a) m t) = run (Rolling1588.reverse d 1 (15+a)) m t := by
  obtain ⟨mid,hm⟩ : ∃ u : State,run (regularForward base d 1 15)
    (enc.take (measurementCount (regularForward base d 1 15))) s=u := ⟨_,rfl⟩
  have st := start16 d x hx0 hx s (enc.take (measurementCount (regularForward base d 1 15))) hs
  rw [hm] at st
  have cut := decompose d 1 15 a s enc
  dsimp only at cut
  rw [hm,show (1:Nat)+15=16 by decide] at cut
  obtain ⟨post,he⟩ : ∃ z : List Bool,enc.drop (measurementCount (regularForward base d 1 15))=z := ⟨_,rfl⟩
  rw [he] at cut
  have pool (q : Wire) (hq : q∈skywalkPoolWires base) : v.basis q=(run (regularForward base d 16 a) post mid).basis q :=
    (agree q hq).trans (congrArg (fun w : State => w.basis q) cut)
  exact backward_start d a x atCut hx0 hx mid v post m st pool
end ECDSAAdd.Entrant.Stair44WalkCuts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveHistoryCompare
open Arithmetic MappedCompressed WideReference
attribute [local irreducible] run W.compactSkywalkTick

def Except (qs:List Wire) (s t:State) := ∀q∉qs,s.basis q=t.basis q

theorem runEq {qs:List Wire} (P:Program) (s t:State) (m n:List Bool) (initial:Except qs s t)
    (off:∀q∈qs,q∉wires P) : Except qs (run P m s) (run P n t) := by
  let aligned:State:=⟨s.phase,t.basis⟩
  have localEq:=run_measured_locality P (wires P) (Finset.Subset.refl _) s aligned m rfl
    (fun q used=>initial q (fun mem=>off q mem used))
  have records:=StairDivLoanTop.run_basis_records P m n aligned t rfl
  intro q hq
  by_cases used:q∈wires P
  · exact (localEq.2 q used).trans (congrFun records q)
  · rw [run_preserves_outside _ _ _ _ used,run_preserves_outside _ _ _ _ used]
    exact initial q hq

theorem spanAppend (i n k:Nat) : span i (n+k)=span i n++span (i+n) k := by
  induction n generalizing i with
  | zero=>simp [span]
  | succ n ih=>rw [Nat.succ_add,span,span,ih (i+1),List.append_assoc];simp [Nat.succ_add,Nat.add_assoc]

theorem moveEarlier (i n:Nat) (lim:i+n≤512) (P:Program) (old:∀q∈wires P,Earlier i q) (s:State) :
    run (span i n) [] (run P [] s)=run P [] (run (span i n) [] s) := by
  have disjoint:Disjoint (wires P) (wires (span i n)) :=
    Finset.disjoint_left.mpr (fun _ h=>pastOffSpan _ _ _ lim (old _ h))
  exact (run_disjoint_commute _ _ disjoint [] [] s).symm

theorem join {old added:List Wire} {s a b:State} (h:Except added s a) (k:Except old a b):
    Except (old++added) s b := by
  intro q off
  exact (h q (fun hit=>off (List.mem_append.mpr (Or.inr hit)))).trans (k q (fun hit=>off (List.mem_append.mpr (Or.inl hit))))

/-- Move earlier encoders past the untouched tick span and then add this window's encoder. -/
theorem extend (i n:Nat) (lim:i+n≤512) (old added:List Wire) (prefixProgram nextProgram:Program)
    (raw reference out:State) (pre:Except old raw (run prefixProgram [] reference))
    (window:Except added out (run nextProgram [] (run (span i n) [] raw)))
    (priorOld:∀q∈old,Earlier i q) (opsOld:∀q∈wires prefixProgram,Earlier i q)
    (avoid:∀q∈old,q∉wires nextProgram) :
    Except (old++added) out (run (prefixProgram++nextProgram) [] (run (span i n) [] reference)) := by
  have stable:=runEq (span i n) raw (run prefixProgram [] reference) [] [] pre
    (fun q mem=>pastOffSpan _ _ _ lim (priorOld q mem))
  rw [moveEarlier _ _ lim _ opsOld reference] at stable
  have next:=runEq nextProgram _ _ [] [] stable avoid
  rw [run_append,run_take,List.drop_nil]
  exact join window next

end ECDSAAdd.Entrant.StairPacket.ArchiveHistoryCompare

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveOrdinaryFive
open Arithmetic MappedCompressed Rolling1588
set_option maxRecDepth 25000
set_option maxHeartbeats 2400000
attribute [local irreducible] run

theorem stock_relocated (d:Bool) (f g:Fin 10→Wire) (inj:Function.Injective f) (inj':Function.Injective g)
    (s t:State) (m n:List Bool) (initial:∀i,s.basis (f i)=t.basis (g i)) (i:Fin 10) :
    (run (codeEncodeAt d f) m s).basis (f i)=(run (codeEncodeAt d g) n t).basis (g i) := by
  let a:=MeasuredCodec5.label f
  let b:=MeasuredCodec5.label g
  let src:=pullState a s
  let dst:State:=⟨t.phase,src.basis⟩
  have footprint:wires (codeEncode d)⊆Finset.range 10:=by cases d <;> decide +kernel
  have input (q:Nat) (hq:q∈Finset.range 10) : dst.basis q=t.basis (b q) := by
    have lt:=Finset.mem_range.mp hq
    simpa [dst,src,pullState,a,b,MeasuredCodec5.label,lt] using initial ⟨q,lt⟩
  have srcStep:=run_rename_pool a _ (FirstNonzeroCodec.label_inj' _ inj) _ footprint m src s rfl (fun _ _=>rfl)
  have dstStep:=run_rename_pool b _ (FirstNonzeroCodec.label_inj' _ inj') _ footprint n dst t rfl input
  have basis:=StairDivLoanTop.run_basis_records (codeEncode d) m n src dst rfl
  have h: i.val∈Finset.range 10:=Finset.mem_range.mpr i.isLt
  have srcBit:=srcStep.2 _ h
  have dstBit:=dstStep.2 _ h
  change (run (codeEncodeAt d f) m s).basis (a i.val)=_ at srcBit
  change (run (codeEncodeAt d g) n t).basis (b i.val)=_ at dstBit
  simpa only [a,b,MeasuredCodec5.label,dif_pos i.isLt] using
    srcBit.trans ((congrFun basis i.val).trans dstBit.symm)
end ECDSAAdd.Entrant.StairPacket.ArchiveOrdinaryFive

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveTruth
open Arithmetic MappedCompressed WideReference SkywalkRails StairArchiveTrace StairArchiveRaw StairArchiveNativeRows CodecBitSliceVerify
attribute [local irreducible] run SkywalkNat.step span WideReference.canonical StairArchiveRaw.rawCol SkywalkTrace.trace
private theorem nextCanon (k j x p:Nat):SkywalkTrace.next^[j] (WideReference.canonical k x p)=WideReference.canonical (k+j) x p:=by
  unfold WideReference.canonical
  rw [Nat.add_comm k j]
  exact (Function.iterate_add_apply _ j k _).symm

theorem observedLabel (k x p row:Nat) (truth:ArchiveStockRows.Chronology k x p row) (e:Fin 20):
    (rawCol e).testBit row=letterBit (SkywalkTrace.code (WideReference.canonical (k+(5+e.val/2)) x p)) e:=by
  have h:=truth e
  have drop (cs:List (Bool×Bool)):read (cs.drop 5) (e.val/2)=read cs (5+e.val/2):=by simp only [StairArchiveRaw.read,List.getElem?_drop]
  rw [drop,read_trace _ _ (by omega),nextCanon] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.StockArchiveTruth

end

end
section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryJ
open Arithmetic MappedCompressed IntegerPacket Partial WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2800000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.body Shadow7.routed measurementCount

/-! Generic history hand-off of an interior window block `j` (par-c2; dadon's `Ordinary{s}Exit`, `Ordinary{s}Native`,
`Logical{s}Exit`). The block's pack re-encodes the cells of ticks `s-15..s-11` exactly as the stock encoder of
group `s-15` does, and the logical end state differs from the stock run only on the archived cells of ticks
`s-10..s-1` (`newBank`). Interior: `oldStart s = s-15` (par-a's `oldStart_interior`). Blocks `1 ≤ j ≤ 21`. -/

def plain (j : Fin 26) : Fin 10 → Wire := History5.historyMap base (start j-15)
def newBank (j : Fin 26) : List Wire := (List.range' (start j-10) 10).flatMap (fun r=>[base r,base (1028+r)])

theorem plain_cell (j : Fin 26) (i : Fin 10) :
    (i.val%2=0 ∧ (plain j i:Nat)=start j-15+i.val/2+16) ∨ (i.val%2≠0 ∧ (plain j i:Nat)=start j-15+i.val/2+1044) := by
  simp only [plain,History5.historyMap,History5.historyId,base,Wire]
  split
  · left; constructor; assumption; omega
  · right; constructor; assumption; omega
theorem plain_inj (j : Fin 26) : Function.Injective (plain j) := by
  intro a b e
  have ha:=a.isLt; have hb:=b.isLt
  have ca:=plain_cell j a; have cb:=plain_cell j b
  have e':(plain j a:Nat)=plain j b:=e
  apply Fin.ext
  simp only [Wire] at ca cb e'
  omega
/-- `OB5.sig s` and `OB5.sig (s+14)` agree on these cells (both swap the moved history cells). -/
theorem sig_same (j : Fin 26) (i : Fin 10) :
    (OB5.sig (start j) (plain j i):Nat)=OB5.sig (start j+14) (plain j i) := by
  have c:=plain_cell j i
  have hj:=j.isLt; have hi:=i.isLt
  simp only [OB5.sig,Wire]
  simp only [start,Wire] at *
  split <;> split <;> omega

/-- Cells of the stock encoder of group `t`: ticks `t..t+4`. -/
theorem encode_cells (d:Bool) (t:Nat) : ∀q∈wires (Rolling1588.encodeAt base d t),
    ∃r,t≤r ∧ r≤t+4 ∧ (q=r+16 ∨ q=r+1044) := by
  intro q h
  change q∈wires (renameProgram (MeasuredCodec5.label (History5.historyMap base t)) (Rolling1588.codeEncode d)) at h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
  rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
  refine ⟨t+a/2,by omega,by omega,?_⟩
  simp only [MeasuredCodec5.label,ha,dif_pos,History5.historyMap,History5.historyId,base,Wire]
  split <;> omega

theorem heads_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀i:Fin 10,
    oldRange (start j+1) (windowNet j (NativeJ7.history j i)) ∧
    NativeJ7.history j i∉ArchiveJ7.rawHead (NativeJ7.prev j) ∧ ArchiveJ7.Band (start (NativeJ7.prev j)+15) (NativeJ7.history j i) ∧
    NativeJ7.history j i∉EnterJ7.pending j ∧ NativeJ7.history j i≠EnterJ7.flagN j ∧ NativeJ7.history j i≠EnterJ7.flagF j ∧
    NativeJ7.history j i≠EnterJ7.flagU j ∧ NativeJ7.history j i∉RailPair.sites (EnterJ7.upperPairs j) ∧
    EnterJ7.pull j (NativeJ7.history j i)=plain j i := by
  have hc : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀i:Fin 10,
      oldRange (start j+1) (windowNet j (NativeJ7.history j i)) ∧
      (WindowBankCheck.maskOf (ArchiveJ7.rawHead (NativeJ7.prev j))).testBit (NativeJ7.history j i) = false ∧
      ArchiveJ7.Band (start (NativeJ7.prev j)+15) (NativeJ7.history j i) ∧
      (WindowBankCheck.maskOf (EnterJ7.pending j)).testBit (NativeJ7.history j i) = false ∧
      NativeJ7.history j i≠EnterJ7.flagN j ∧ NativeJ7.history j i≠EnterJ7.flagF j ∧
      NativeJ7.history j i≠EnterJ7.flagU j ∧
      (WindowBankCheck.maskOf (RailPair.sites (EnterJ7.upperPairs j))).testBit (NativeJ7.history j i) = false ∧
      EnterJ7.pull j (NativeJ7.history j i)=plain j i := by
    decide +kernel
  intro j h1 h2 i
  obtain ⟨a, b, c, d, e, f, g, h, k⟩ := hc j h1 h2 i
  exact ⟨a, WindowBankCheck.not_mem_of_maskOf b, c, WindowBankCheck.not_mem_of_maskOf d, e, f, g,
    WindowBankCheck.not_mem_of_maskOf h, k⟩

theorem kept (j:Fin 26) (admin:Program) (m:List Bool) (s:State) (q:Wire) (early:oldRange (start j+1) (windowNet j q)) :
    (run (Shadow7.body j admin) m s).basis q=
      (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)).basis q := by
  simp only [Shadow7.body,run_append,run_take]
  exact Shadow7.route_outside j 1 14 (by decide) q (Shadow7.old_clear (by decide) early) _ _

theorem pastInput (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (x p:Nat) (good:Bounds x p) (raw:State)
    (dom:Domain (start j) x p raw) (i:Fin 10) :
    raw.basis (plain j i)=(run (span (start j) 15) [] raw).basis (plain j i) := by
  have pp:=preservePast (start j) 15 x p (start j-15+i.val/2) (by simp only [start]; omega) good raw dom
    (by simp only [start]; omega) []
  rcases plain_cell j i with ⟨-,e⟩|⟨-,e⟩
  · rw [e]; exact pp.1.symm
  · rw [e,show start j-15+i.val/2+1044=base (1028+(start j-15+i.val/2)) by simp only [base]; omega]; exact pp.2.symm

theorem encode (j : Fin 26) (h1 : 1≤j.val) (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (NativeJ7.history j i)=b.basis (plain j i)) (i:Fin 10) :
    (run (NativeJ7.program j d) tape a).basis (NativeJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] b).basis (plain j i) := by
  rw [(NativeJ7.equals j (by omega) d).1]
  exact ArchiveOrdinaryFive.stock_relocated d (NativeJ7.history j) (plain j) (NativeJ7.histInj j) (plain_inj j) a b tape [] agree i

theorem readback (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw pre wide out:State) (tape:List Bool)
    (input:∀i,pre.basis (NativeJ7.history j i)=raw.basis (plain j i))
    (stable:∀i,raw.basis (plain j i)=wide.basis (plain j i))
    (last:∀i,out.basis (NativeJ7.history j i)=(run (NativeJ7.withArchive j d) tape pre).basis (NativeJ7.history j i)) (i:Fin 10) :
    out.basis (NativeJ7.history j i)=(run (Rolling1588.encodeAt base d (start j-15)) [] wide).basis (plain j i) := by
  apply (last i).trans
  rw [NativeJ7.withArchive,run_append,run_take]
  have hp:(NativeJ7.prev j).val≤23:=by simp only [NativeJ7.prev]; omega
  obtain ⟨-,offHead,band,-⟩:=heads_all j (by omega) h21 i
  have off:NativeJ7.history j i∉ArchiveJ7.rawPortsList (NativeJ7.prev j):=by
    rw [ArchiveJ7.raw_split,List.mem_append]
    rintro (h|h)
    · exact offHead h
    · obtain ⟨k,hk,eq⟩:=List.mem_map.mp h
      exact ArchiveJ7.band_off _ (ArchiveJ.tick_lt _) (List.mem_range.mp hk) band eq
  rw [run_preserves_outside (Shadow7.archiveLoadP (NativeJ7.prev j) d) _ _ _
    (fun h=>off (List.mem_toFinset.mp (ArchiveJ7.load_cover (NativeJ7.prev j) (by omega) d h)))]
  exact encode j (by omega) d pre wide tape (fun k=>(input k).trans (stable k)) i

/-- `Ordinary{s}Exit.result` for every interior block. -/
theorem result (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool) (x p:Nat)
    (good:Bounds x p) (dom:Domain (start j) x p raw)
    (input:∀i,(run (Shadow7.routed j 0 1) m s).basis (NativeJ7.history j i)=raw.basis (plain j i)) :
    ∀i,(run (Shadow7.body j (NativeJ7.withArchive j d)) m s).basis (NativeJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)).basis (plain j i) :=
  readback j (by omega) h21 d raw (run (Shadow7.routed j 0 1) m s) (run (span (start j) 15) [] raw) _ _ input
    (pastInput j (by omega) h21 x p good raw dom) (fun i=>kept j _ m s _ (heads_all j (by omega) h21 i).1)

/-- `Logical{s}Exit.window` for every interior block (par-a's `Fixed`-free `endRaw_*_gen`). -/
theorem window (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24)
    (interior:oldStart (start j)=start j-15 ∧ oldCount (start j)=15) (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,historyState.basis (NativeJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)).basis (plain j i))
    (q:Wire) (ordinarySite:q∉newBank j) :
    (endRaw (start j) raw historyState).basis q=
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)).basis q := by
  have bound:start j+14≤511:=by simp only [start]; omega
  have s15:15≤start j:=by simp only [start]; omega
  by_cases inside:q∈oldSites (start j)
  · obtain ⟨r,r1,r2,hq⟩:=old_cell inside
    rw [interior.1] at r1 r2
    rw [interior.2] at r2
    have young:r<start j-10:=by
      by_contra hr
      apply ordinarySite
      simp only [newBank,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false,base]
      simp only [Wire] at *
      exact ⟨r,⟨by omega,by omega⟩,by omega⟩
    have ex:∃i:Fin 10,q=plain j i:=by
      simp only [Wire] at *
      rcases hq with hq|hq
      · refine ⟨⟨2*(r-(start j-15)),by omega⟩,?_⟩
        rcases plain_cell j ⟨2*(r-(start j-15)),by omega⟩ with ⟨-,e⟩|⟨od,-⟩
        · rw [e]; dsimp only; omega
        · exfalso; simp only at od; omega
      · refine ⟨⟨2*(r-(start j-15))+1,by omega⟩,?_⟩
        rcases plain_cell j ⟨2*(r-(start j-15))+1,by omega⟩ with ⟨ev,-⟩|⟨-,e⟩
        · exfalso; simp only at ev; omega
        · rw [e]; dsimp only; omega
    obtain ⟨i,rfl⟩:=ex
    rw [endRaw_inside_gen _ bound _ _ _ inside,← sig_same j i]
    exact ordinaryBits i
  · rw [endRaw_outside_gen _ bound _ _ _ inside]
    apply (run_preserves_outside _ _ _ q _).symm
    intro used
    obtain ⟨r,r1,r2,hq⟩:=encode_cells d _ q used
    apply inside
    simp only [oldSites,interior.1,interior.2,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
      or_false,base]
    simp only [Wire] at *
    exact ⟨r,⟨by omega,by omega⟩,by omega⟩

/-- `Ordinary{s}Native.result`: block `j`'s window agrees with the stock run except on `newBank j`
(par-d2's `OrdinaryChainW` step for an interior block). -/
theorem native (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24)
    (interior:oldStart (start j)=start j-15 ∧ oldCount (start j)=15) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (domain:Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z (run (Shadow7.enterP j) a s).basis) :
    let historyState:=run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)
    ArchiveHistoryCompare.Except (newBank j) (endRaw (start j) raw historyState)
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)) := by
  let e:=run (Shadow7.enterP j) a s
  have input:∀i,(run (Shadow7.routed j 0 1) b e).basis (NativeJ7.history j i)=raw.basis (plain j i) := by
    intro i
    have kept0:=NativeJ7.prefix_kept j (by omega) h21 s a b z odd active i
    obtain ⟨-,-,-,notTag,hn,hf,hu,hi,same⟩:=heads_all j (by omega) h21 i
    exact kept0.trans (by simpa only [eraseSites,if_neg notTag,pullState,same] using cut.unchanged _ hn hf hu hi)
  exact fun q hq=>window j (by omega) h21 interior d raw _ (result j (by omega) h21 d raw e b x p good domain input) q hq

end ECDSAAdd.Entrant.StairPacket.OrdinaryJ

end

-- ==== end PrizeTail8dd9f9e60 ====

-- ==== begin PrizeTail05e06b1e9 ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.StockStrongChain
open Arithmetic MappedCompressed Secp256k1 IntegerPacket WideReference StockWindowTicket StockCanonicalRow Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 16000
set_option maxHeartbeats 4500000
attribute [local irreducible] run measurementCount Partial.leave225 Partial.leave240 Partial.leave255
  NativePack270.lastWindow
noncomputable def value (x p i b:Nat) (c:SkywalkNat.State→Bool):Nat→Bool:=
  key b (unsigned i x p) (c (unsigned i x p)) (SkywalkTrace.trace 15 (WideReference.canonical i x p))
def SavedKey (v:Nat→Bool) (ps:Ports) (d:Bool) (s:State):Prop:= select v<63145 ∧ Encodes v (select v) ∧ Kept ps d (select v) s

attribute [local irreducible] key select WideReference.canonical
theorem kept_frame (ps:Ports) (d:Bool) (r:Nat) (s:State) (h:Frame ps (code d) r s):
    Kept ps d r s:=fun j=>h ⟨j,by omega⟩
end ECDSAAdd.Entrant.StairPacket.StockStrongChain

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44Resources Stair44Outer
open StairConcreteAssembly WindowFieldParity
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
private theorem setup_eq : setup = StairSchedule.paritySetup := by
  have empty : correction = [] := rfl
  rw [setup, empty, List.append_nil]

theorem programOld_eq (C : Point) : programOld C = WindowCallerCosts.program C := by
  cases C with
  | zero => rfl
  | @some cx cy hc =>
    simp only [programOld, WindowCallerCosts.program, finiteOld, WindowCallerCosts.finite,
      borrowGenericOld, WindowCallerCosts.borrowGeneric, genericOld, WindowCallerCosts.generic,
      divide, WindowCallerCosts.divide, multiply, WindowCallerCosts.multiply,
      entryFieldHosted, WindowCallerCosts.entryFieldHosted, entryFieldHostedCut,
      WindowCallerCosts.entryFieldHostedCut, exitFieldHosted,
      WindowCallerCosts.exitFieldHosted, setup_eq]

theorem metricsOld (C : Point) : toffoliCount (programOld C) ≤ 2008161 ∧
    measurementCount (programOld C) ≤ 1446339 ∧ gateSlots (programOld C) ≤ 67191214 := by
  rw [programOld_eq]
  exact ⟨(WindowCallerCosts.totals C).1, (WindowCallerCosts.totals C).2, WindowSlots.slotBound C⟩

end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
attribute [local irreducible] run chain

end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Baselines Stair44Outer StairConcreteAssembly WindowFieldParity
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Challenge Baselines Stair44Outer WindowFieldParity
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open Arithmetic MappedCompressed Secp256k1 OB5 Rolling1588.Integer
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588.reverse
def head := renameProgram (sig 511) tickR ++ P1

theorem after_head (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (M : List Bool) (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base false 1 511) M s1).basis q) (mD : List Bool) :
    ∃ raw : State, run head mD (pullState (sig 511) t5)=pullState (sig 505) raw ∧
      ∀q∈skywalkPoolWires base,raw.basis q=(run (regularForward base false 1 505) M s1).basis q := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base false x p 511
      (run (regularForward base false 1 510)
        (M.take (measurementCount (regularForward base false 1 510))) s1).basis :=
    ((regularForward_spec base false base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base false x p s1 first)).2
  have whole : run (regularForward base false 1 510)
      (M.take (measurementCount (regularForward base false 1 510))) s1=
        run (regularForward base false 1 510) M s1 := run_take _ M s1
  have last : run (regularForward base false 1 511) M s1=
      run (W.repairedTick base 511) (M.drop (measurementCount (regularForward base false 1 510)))
        (run (regularForward base false 1 510)
          (M.take (measurementCount (regularForward base false 1 510))) s1) := by
    rw [regularForward_snoc base false 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base false 1 510)
    (M.take (measurementCount (regularForward base false 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits false x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero false x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have hu (q : Wire) (hq : q∈skywalkPoolWires base) : (run tickR [] t5).basis q =
      (run (regularForward base false 1 510) M s1).basis q :=
    (uAgree q hq).trans (congrArg (fun w : State => w.basis q) whole)
  let pr := regularForward base false 1 505
  obtain ⟨s6,e6⟩ : ∃ u : State,run pr (M.take (measurementCount pr)) s1=u := ⟨_,rfl⟩
  have stage6 := stage_after x hx0 hx s1 first 505 (by decide) (M.take (measurementCount pr))
  change Stage base false x p 506 (run pr (M.take (measurementCount pr)) s1).basis at stage6
  rw [e6] at stage6
  have split := Stair44WalkCuts.decompose false 1 505 5 s1 M
  change run (regularForward base false 1 510) M s1 =
    run (regularForward base false 506 5) (M.drop (measurementCount pr)) (run pr (M.take (measurementCount pr)) s1) at split
  rw [e6] at split
  have hb (q : Wire) (hq : q∈skywalkPoolWires base) :=
    (hu q hq).trans (congrArg (fun w : State => w.basis q) split)
  have rg := reverse_gen false x hx0 hx 5 506 (by decide) (by decide) s6 (M.drop (measurementCount pr))
    (run tickR [] t5) mD stage6 hb
  refine ⟨run (regularReverse base false 506 5) mD (run tickR [] t5),?_,?_⟩
  · have cn := (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
    rw [head,run_append,cn]
    simp only [List.take_zero,List.drop_zero]
    rw [OB5.run_rename 511 (by decide),tickR_run,move,head_chain x hx0 hx s1 first M _ hu mD]
    simpa only [Rolling1588.Integer.reverse_eq_packets] using rg.1
  · intro q hq
    exact (rg.2 q hq).trans (congrArg (fun w : State => w.basis q) (e6.symm.trans (run_take pr M s1)))

end ECDSAAdd.Entrant.Stair44DivTerm

end




section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary270Terminal
open Arithmetic MappedCompressed NativePack270 ArchivePortAction ArchiveBoundary270 ParkEndpoint CodecBitSliceVerify
set_option maxRecDepth 40000
set_option maxHeartbeats 3800000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Ordinary270Terminal

end


section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldHistory
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairField2V3Seg
attribute [local irreducible] run wires rawCol CodecBitSliceVerify.get SkywalkTrace.next
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1400
set_option maxHeartbeats 400000

/-- Identify the 20 row columns with real raw field history at a ten-cell suffix. -/
theorem originBits (j x row : Nat) (jb : 5*j+10≤512) (lb : 5≤5*j) (origin : BasisState)
    (tr : TraceOK x origin) (record : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (hi : Bool) (q : Fin 10) :
    origin (History5.historyMap base (5*(j+(if hi then 1 else 0))) q) =
      (rawCol ((if hi then 10 else 0)+q.val)).testBit row := by
  let u : Nat := (if hi then 10 else 0)+q.val
  have ql := q.isLt
  have u20 : u<20 := by cases hi <;> simp [u] <;> omega
  let start := 5*(j+(if hi then 1 else 0))
  let tick := start+q.val/2
  have plus : tick=5*j+u/2 := by cases hi <;> simp [tick,start,u] <;> omega
  have full : (5*j-5)+(5+u/2)=tick := by omega
  have small : tick<512 := by omega
  have bits := StairField2V3Trace.origin_letters x origin tr tick small
  have col := StockArchiveTruth.observedLabel (5*j-5) x ECDSAAdd.p row record ⟨u,u20⟩
  change (rawCol u).testBit row=letterBit (SkywalkTrace.code (WideReference.canonical ((5*j-5)+(5+u/2)) x ECDSAAdd.p)) u at col
  rw [full] at col
  unfold WideReference.canonical at col
  change origin (base (if q.val%2=0 then start+q.val/2 else 1028+start+q.val/2))=(rawCol u).testBit row
  rw [col]; unfold letterBit
  have parity : u%2=q.val%2 := by cases hi <;> simp [u] <;> omega
  rw [parity]
  split
  · exact bits.1
  · simpa only [tick,Nat.add_assoc] using bits.2

end ECDSAAdd.Entrant.StairPacket.WindowFieldHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
def lawful (t : Wire) : Aff→Prop
  | .x w => w≠t
  | .cx c w => c≠w ∧ c≠t ∧ w≠t
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityRelease
open Arithmetic Secp256k1 Challenge Baselines

end ECDSAAdd.Entrant.StairPacket.WindowParityRelease

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open Arithmetic MappedCompressed Secp256k1 OB5 DirectSkywalk Rolling1588.Integer
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588.reverse

theorem sig_pool (i : Nat) (hi : i≤511) (q : Wire) (hq : q∈skywalkPoolWires base) :
    sig i q∈skywalkPoolWires base := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  have b := List.mem_range'_1.mp hj
  rw [sig_base i j hi]
  apply OB5.base_pool
  split <;> omega

theorem host_pool (q : Wire) (hq : q∈skywalkPoolWires base) :
    Rolling1588Lifetime.phaseHost q∈skywalkPoolWires base := by
  simp only [Rolling1588Lifetime.phaseHost,Equiv.trans_apply,Equiv.swap_apply_def]
  split_ifs <;> first | assumption | exact OB5.base_pool _ (by decide)

theorem raw511 (hn : (skywalkSharedWires base).Nodup) (d : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (Rolling1588TickGap.stackForward d) m s = pullState (sig 511) (run (regularForward base d 1 511) m s) := by
  rw [Rolling1588TickGap.stackForward_run_eq d x hx0 hx s m first,
    ←Rolling1588.Integer.stackForward_eq_packets,
    Rolling1588.Integer.stackForwardT_run d hn StackOB5.historyAbove x hx0 hx s m first,
    Rolling1588.Integer.forward_run d x hx0 hx s m first]

theorem reverse_input (x y : Nat) (hx0 : 0<x) (hx : x<p) (hn : (skywalkSharedWires base).Nodup)
    (s v : State) (input : SkywalkArithmeticInput base x y s.basis)
    (matchP : v.phase=(run (Rolling1588TickGap.firstPhase false) [] s).phase)
    (matchB : ∀q∈skywalkPoolWires base,v.basis q=(run (Rolling1588TickGap.firstPhase false) [] s).basis q)
    (m : List Bool) :
    let one := run (FrontierEntry1591Native.forward base) [] s
    ∃ raw : State, run (skywalkArithmeticClear base ++ head) m v = pullState (sig 505) raw ∧
      ∀q∈skywalkPoolWires base,raw.basis q=(run (regularForward base false 1 505) [] one).basis q := by
  dsimp only
  obtain ⟨one,eo⟩ : ∃ u : State,run (FrontierEntry1591Native.forward base) [] s=u := ⟨_,rfl⟩
  rw [eo]
  have st := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s [] input
  rw [eo] at st
  obtain ⟨ref,er⟩ : ∃ z : State,run (regularForward base false 1 511) [] one=z := ⟨_,rfl⟩
  let C := skywalkArithmeticClear base
  let w := run C [] v
  have orig : run (Rolling1588TickGap.firstPhase false) [] s = run C [] (pullState (sig 511) ref) := by
    simp only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,run_append,List.take_nil,List.drop_nil]
    rw [eo,raw511 hn false x hx0 hx _ [] st,er]
  rw [orig] at matchP matchB
  have same := pool_run_agrees C (skywalkPoolWires base).toFinset EntryFuse.clear_pool5 [] v _ matchP
    (fun q hq => matchB q (List.mem_toFinset.mp hq))
  have twice : run C [] (run C [] (pullState (sig 511) ref))=pullState (sig 511) ref := by
    exact skywalkTerminalClear_twice (base 511) (base 512) (base 770) (arith_clear_gates base hn) _ [] []
  rw [twice] at same
  let v5 := pullState (sig 511) w
  have eq5 : w=pullState (sig 511) v5 := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg w.basis (sig_invol 511 (by decide) q).symm
  have eqb (q : Wire) (hq : q∈skywalkPoolWires base) : v5.basis q=ref.basis q := by
    have r := same.2 _ (List.mem_toFinset.mpr (sig_pool 511 (by decide) q hq))
    simpa only [pullState,sig_invol 511 (by decide)] using r
  have noM : measurementCount (skywalkArithmeticClear base)=0 := by simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  rw [run_append,noM,List.take_zero,List.drop_zero]
  change ∃ raw,run head m w=pullState (sig 505) raw ∧ _
  rw [eq5]
  rw [←er] at eqb
  exact after_head x hx0 hx one st [] v5 eqb m

end ECDSAAdd.Entrant.Stair44DivTerm

end






section

namespace ECDSAAdd.Entrant.StairPacket.StockBaseline
open Arithmetic MappedCompressed WideReference Secp256k1
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward
theorem forward_phase (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:1 ≤ i) (hi:i+n≤512) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis):
    (run (Rolling1588TickGap.forward d i n) m (pullState (OB5.sig (i-1)) s)).phase=s.phase:=by
  have spec:=Rolling1588TickGap.forward_gen d x good.nonzero good.small n i lo hi s m stage
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have ph:=(Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p i n hp0 good.nonzero odd cap (by norm_num [p]) good.small cop hi s m stage).1
  exact (congrArg State.phase spec).trans ph
end ECDSAAdd.Entrant.StairPacket.StockBaseline

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairArchiveNativeCut StairArchiveRelease
open WindowFieldMask ArchiveFieldScratch StairField2V3Seg
def wire (q : Wire) := StairArchiveInactive.host (OB5.sig 511 q)
theorem injective : Function.Injective wire :=
  StairArchiveInactive.host.injective.comp (OB5.sig_injective 511 (by decide))
def high (q : Nat) := decide (8≤q)
def lane (q : Nat) : Fin 10 := ⟨if q%8<5 then q%8 else q%8+1,by split <;> omega⟩
def histPort (j q : Nat) := History5.historyMap base (5*(j+(if high q then 1 else 0))) (lane q)
def physical (j : Nat) := ((List.range 16).all (fun q=>fieldPort j q == wire (histPort j q))) &&
  (fieldPort j 16 == base 720) &&
  (List.range' 17 104).all (fun q=>fieldPort j q == wire (base (Placement5.H (8+(q-17)))))
/-- A product of swaps fixes every wire outside both of its lists. -/
theorem rebinder_fix : ∀ (rs hs : List Wire) (x : Wire), x ∉ rs → x ∉ hs →
    StairArchiveInactive.rebinder rs hs x = x
  | r :: rs, h :: hs, x, hr, hh => by
    simp only [List.mem_cons, not_or] at hr hh
    simp only [StairArchiveInactive.rebinder, Equiv.trans_apply]
    rw [rebinder_fix rs hs x hr.2 hh.2]
    exact Equiv.swap_apply_of_ne_of_ne hr.1 hh.1
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl

/-- The 352 history images avoid the rebinder's lists, so `wire` needs no swap chain here. -/
private theorem physicalHead :
    WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q=>fieldPort j q == wire (histPort j q)))=true := by
  have hc : WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q =>
      fieldPort j q == OB5.sig 511 (histPort j q) &&
      !(StairLoan.maskOf StairSchedule.exclusiveRoles).testBit (OB5.sig 511 (histPort j q)) &&
      !(StairLoan.maskOf (StairPhysicalLayout.hosts 87)).testBit (OB5.sig 511 (histPort j q)))) = true := by
    decide +kernel
  rw [List.all_eq_true] at hc ⊢
  intro j hj
  rw [List.all_eq_true]
  intro q hq
  have h := List.all_eq_true.mp (hc j hj) q hq
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨e, hr⟩, hh⟩ := h
  rw [beq_iff_eq, e, wire, StairArchiveInactive.host,
    rebinder_fix _ _ _ (StairLoan.not_mem_of_maskOf hr) (StairLoan.not_mem_of_maskOf hh)]
private theorem physicalTail : ((fieldPort 0 16 == base 720) &&
    (List.range' 17 104).all (fun q=>fieldPort 0 q == wire (base (Placement5.H (8+(q-17))))))=true := by
  have hc : ((fieldPort 0 16 == base 720) && (List.range' 17 104).all (fun q =>
      fieldPort 0 q == OB5.sig 511 (base (Placement5.H (8+(q-17)))) &&
      !(StairLoan.maskOf StairSchedule.exclusiveRoles).testBit (OB5.sig 511 (base (Placement5.H (8+(q-17))))) &&
      !(StairLoan.maskOf (StairPhysicalLayout.hosts 87)).testBit
        (OB5.sig 511 (base (Placement5.H (8+(q-17))))))) = true := by
    decide +kernel
  rw [Bool.and_eq_true] at hc ⊢
  refine ⟨hc.1, ?_⟩
  rw [List.all_eq_true] at hc ⊢
  intro q hq
  have h := hc.2 q hq
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨e, hr⟩, hh⟩ := h
  rw [beq_iff_eq, e, wire, StairArchiveInactive.host,
    rebinder_fix _ _ _ (StairLoan.not_mem_of_maskOf hr) (StairLoan.not_mem_of_maskOf hh)]
private theorem physical_ok : WindowBankCheck.banks.all physical=true := by
  rw [List.all_eq_true]
  intro j hj
  have hh := List.all_eq_true.mp physicalHead j hj
  have tl := physicalTail
  simp only [physical, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hh tl ⊢
  refine ⟨⟨hh, by rw [fieldPort_tail j 16 (le_refl _)]; exact tl.1⟩, fun q hq => ?_⟩
  rw [fieldPort_tail j q (by have := List.mem_range'_1.mp hq; omega)]
  exact tl.2 q hq
def lookup (l h : Bool) := (List.range 16).all (fun q=>
  CodecBitSliceVerify.get (StairArchiveNativeCut.canonical l h) q == CodecBitSliceVerify.get (storage (native (if high q then h else l) (high q))) (lane q))
private theorem lookup_ok (l h : Bool) : lookup l h=true := by cases l <;> cases h <;> decide +kernel
private theorem upper_zero (l h : Bool) : (List.range' 16 105).all (fun q=>CodecBitSliceVerify.get (StairArchiveNativeCut.canonical l h) q == 0)=true := by
  cases l <;> cases h <;> decide +kernel
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
attribute [local irreducible] run wire StairArchiveNativeCut.canonical StairArchiveRelease.fieldPort CodecBitSliceVerify.get
def boundaryCols (j c : Nat) := StairArchiveNativeCut.canonical (decide (c≤j)) (decide (c≤j+1))

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run mcx chain

instance (t : Wire) (g : Aff) : Decidable (lawful t g) := by cases g <;> unfold lawful <;> infer_instance
instance (q j : Wire) (xs : Hops) : Decidable (outside q j xs) := by unfold outside; infer_instance
instance dsafe (last target src : Wire) (xs : Hops) : Decidable (safe last target src xs) := by
  cases xs with
  | nil => unfold safe; infer_instance
  | cons pair tail =>
    obtain ⟨c,b⟩ := pair
    letI := dsafe last target b tail
    unfold safe; infer_instance

end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open Arithmetic MappedCompressed Secp256k1 OB5 DirectSkywalk Rolling1588.Integer Stair44WalkMap
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588.reverse
  Stair44WalkRun.backward FrontierEntry1591NativeH.inverse FrontierEntry1591Native.forward

private def firstSites := [1026,514,1541,501,1542,500]
theorem fixed (s : State) (z : ∀j∈firstSites,s.basis (base j)=false) : pullState first s=s := by
  have a := cleanWireRebind id s s _ _ rfl (z 1026 (by decide)) (z 514 (by decide))
  have b := cleanWireRebind _ s s _ _ a (z 1541 (by decide)) (z 501 (by decide))
  exact cleanWireRebind _ s s _ _ b (z 1542 (by decide)) (z 500 (by decide))

private theorem input_zero (x y : Nat) (s : State) (input : SkywalkArithmeticInput base x y s.basis) :
    ∀j∈firstSites,s.basis (base j)=false := by
  have chk : ∀j∈firstSites,base j∈skywalkSharedWires base ∧ base j∉skywalkArithmeticDivisor base ∧
      base j∉skywalkArithmeticNumerator base := by decide +kernel
  intro j hj
  obtain ⟨a,b,c⟩ := chk j hj
  exact input.2.2 _ a b c

private theorem byPool {P : Program} (bound : wires P ⊆ (skywalkPoolWires base).toFinset)
    (t u : State) (bits : ∀q∈skywalkPoolWires base,t.basis q=u.basis q)
    (m : List Bool) : ∀q∈skywalkPoolWires base,(run P m t).basis q=(run P m u).basis q := by
  let v : State := ⟨t.phase,u.basis⟩
  have h := pool_run_agrees P _ bound m t v rfl (fun q hq => bits q (List.mem_toFinset.mp hq))
  intro q hq
  exact (h.2 q (List.mem_toFinset.mpr hq)).trans (congrFun (run_basis_records P v u m m rfl) q)

theorem inverse_end (x y : Nat) (hx : x<p) (hn : (skywalkSharedWires base).Nodup)
    (s logical actual : State) (input : SkywalkArithmeticInput base x y s.basis)
    (eq : pullState first actual=logical)
    (hb : ∀q∈skywalkPoolWires base,logical.basis q=(run (FrontierEntry1591Native.forward base) [] s).basis q)
    (m : List Bool) :
    run (renameProgram first (FrontierEntry1591NativeH.inverse base)) m actual =
      run (FrontierEntry1591NativeH.inverse base) m logical := by
  have bd := (FrontierEntry1591NativeH.wires_sub base base_pool_nodup).trans
    (FrontierEntry1591Native.native_pool base base_pool_nodup).2
  have keep := byPool bd logical _ hb m
  have orig := FrontierEntry1591NativeH.inverse_roundtrip base hn x y hx s [] m input
  rw [orig] at keep
  have z (j : Nat) (hj : j∈firstSites) : (run (FrontierEntry1591NativeH.inverse base) m logical).basis (base j)=false :=
    (keep _ (OB5.base_pool _ (by simp [firstSites] at hj; omega))).trans (input_zero x y s input _ hj)
  apply MappedCompressed.pullState_perm_injective first
  rw [run_rename _ first.injective,eq]
  exact (fixed _ z).symm

def routedClose := (skywalkArithmeticClear base ++ head) ++
  (Stair44WalkRun.backward false 490 ++ renameProgram first (FrontierEntry1591NativeH.inverse base))

theorem close (x y : Nat) (hx0 : 0<x) (hx : x<p) (hn : (skywalkSharedWires base).Nodup)
    (s v : State) (input : SkywalkArithmeticInput base x y s.basis)
    (phase : v.phase=(run (Rolling1588TickGap.firstPhase false) [] s).phase)
    (pool : ∀q∈skywalkPoolWires base,v.basis q=(run (Rolling1588TickGap.firstPhase false) [] s).basis q)
    (m : List Bool) :
    run routedClose m v=run (InverseFive23.lastPhase15 false) m v := by
  let C := skywalkArithmeticClear base ++ head
  let tape := m.drop (measurementCount C)
  let B := Stair44WalkRun.backward false 490
  let R := Rolling1588.reverse false 1 505
  let I := FrontierEntry1591NativeH.inverse base
  have sh : InverseFive23.lastPhase15 false=C ++ (R ++ I) := by
    simp only [C,head,R,I,InverseFive23.lastPhase15,InverseFive23.stackReverse15,
      InverseFive23.reverseTail15,P1,List.append_assoc]
  rw [sh,routedClose,run_append,run_append C]
  change run (B ++ renameProgram first I) tape (run C (m.take (measurementCount C)) v) =
    run (R ++ I) tape (run C (m.take (measurementCount C)) v)
  obtain ⟨a,ha,hb⟩ := reverse_input x y hx0 hx hn s v input phase pool (m.take (measurementCount C))
  change run C _ v=pullState (sig 505) a at ha
  rw [ha,run_append,run_append]
  have bm : measurementCount B=measurementCount R := (Stair44WalkRun.metrics false 490).2.2.1
  rw [bm]
  obtain ⟨one,eo⟩ : ∃ st : State,run (FrontierEntry1591Native.forward base) [] s=st := ⟨_,rfl⟩
  rw [eo] at hb
  have st := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s [] input
  rw [eo] at st
  have h1 := stage_one base false x p one st
  let ws := tape.take (measurementCount R)
  have rr := Stair44WalkCuts.backward_record false 490 x (by decide) hx0 hx one a [] ws h1 hb
  have rp := Stair44WalkCuts.restore_raw false 490 x (by decide) hx0 hx one a [] ws h1 hb
  apply inverse_end x y hx hn s _ _ input rr
  simpa only [eo] using rp

end ECDSAAdd.Entrant.Stair44DivTerm

end





section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 20000
attribute [local irreducible] wires domain
theorem reverse_domain (d : Bool) : ∀ q ∈ wires (Shadow20.MergeCut.reverse d), domain q = true := by
  intro q h
  rw [domain_eq]
  exact Shadow20.MergeCut.rcovered d q h

theorem inside (n:Nat) (use:domain n=true):(16:Nat)≤n ∧ n≤1812:=by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at use
  rcases use with ⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩
  all_goals exact ⟨Nat.le_trans (by decide) lo,Nat.le_trans hi (by decide)⟩
theorem range_pool (n:Nat) (lo:16 ≤ n) (hi:n≤1812):n∈skywalkPoolWires base:=by
  have hit:=StackOB5Base.base_pool (n-16) (by omega)
  simpa only [base,Nat.sub_add_cancel lo] using hit
theorem pool_partial (d:Bool):wires (Shadow20.MergeCut.reverse d)⊆(skywalkPoolWires base).toFinset:=by
  intro q h
  have b:=inside q (reverse_domain d q h)
  exact List.mem_toFinset.mpr (range_pool q b.1 b.2)
theorem pool_old (d:Bool) (i n:Nat) (lo:1 ≤ i) (hi:i+n≤512):wires (Rolling1588.reverse d i n)⊆(skywalkPoolWires base).toFinset:=by
  intro q h
  rw [Rolling1588.reverse_support_eq,NewStackOB5.reverse_support_eq] at h
  obtain ⟨k,rfl,range⟩:=StackOB5Base.integerSites_mem q |>.mp ((StackOB5.support_gen i n lo hi).2 q h)
  exact List.mem_toFinset.mpr (StackOB5Base.base_pool k (by omega))
end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockRowVector
open Arithmetic MappedCompressed Secp256k1 StockCanonicalRow StockStrongChain
open StairArchiveRaw WideReference ArchiveStockSuffix ArchivePortAction
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

theorem historical (b i x p:Nat) (c:SkywalkNat.State→Bool) (r:Nat)
    (labels:Encodes (value x p i b c) r):ArchiveStockRows.Chronology i x p r:=by
  intro j
  have bit:=labels ⟨j,by omega⟩
  simpa only [value,key,rawBit,j.isLt,if_true] using bit

end ECDSAAdd.Entrant.StairPacket.StockRowVector

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkPrefix
open Arithmetic MappedCompressed Secp256k1 WideReference
set_option maxRecDepth 8500
set_option maxHeartbeats 2000000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount renameProgram
def first (d:Bool):Program:=Stair44WalkRun.forward d 29
def regular (d:Bool) (s:State) (m:List Bool):State:=run (Rolling1588.Integer.regularForward base d 1 44) m s
theorem cut120 (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Rolling1588.Integer.Stage base d x p 45 (regular d s m).basis ∧
    pullState Stair44WalkMap.rest (run (first d) m a)=pullState (OB5.sig 44) (regular d s m):=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have spec:=Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p 1 44 hp0 good.nonzero odd cap (by norm_num [p]) good.small cop (by decide) s m stage
  refine ⟨spec.2,?_⟩
  have entry:=Stair44WalkRun.forward_run d 29 x good.nonzero good.small s a m stage input
  have logical:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 44 1 (by decide) (by decide) s m stage
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  rw [show 1-1=0 from rfl,init] at logical
  exact entry.trans logical

def forwardEnd (d:Bool) (n:Nat):Program:=Shadow20.MergeCut.forward d++Rolling1588TickGap.forward d 421 n
theorem split (d:Bool) (n:Nat):WindowWalkCosts.forward d n=first d++renameProgram Stair44WalkMap.rest (forwardEnd d n):=by
  simp only [WindowWalkCosts.forward,first,Stair44WalkRun.forward,forwardEnd,renameProgram,List.map_append,List.append_assoc]
theorem placed (d:Bool) (n x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    pullState Stair44WalkMap.rest (run (WindowWalkCosts.forward d n) m a)=
      run (forwardEnd d n) (m.drop (measurementCount (first d))) (pullState (OB5.sig 44) (regular d s m)):=by
  rw [split,run_append,run_take,run_rename _ Stair44WalkMap.rest.injective,(cut120 d x good s a m stage input).2]
end ECDSAAdd.Entrant.StairPacket.StockWalkPrefix

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg
attribute [local irreducible] run wires measurementCount wire group StairArchiveInactive.packet
set_option maxRecDepth 2600
set_option maxHeartbeats 500000

def surface : Finset Wire := ((Finset.Icc 1 84).biUnion (fun j=>wires (packet false j) ∪ wires (packet true j))) ∪ bankIds.biUnion inside
def tracks (actual ideal : State) := ∀q∈surface,q≠base 720→actual.basis q=ideal.basis q
def StockCut (c : Nat) (origin : BasisState) (r : State) : Prop :=
  r.basis (base 720)=false ∧ ∃ (X Y : Fp) (ideal : State),
    Rolling1588.CutFrame c origin X Y (pullState wire ideal) ∧ tracks r ideal

private def allowedTag (k : Nat) := !(cover k).contains (preimage k (base 720))
theorem tagged : (List.range' 1 84).all allowedTag=true :=
  List.all_eq_true.mpr fun k hk =>
    ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp WindowSites.opk_both_chk k hk)).1
private theorem packetUses (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) {q : Wire} (h : q∈wires (packet d k)) :
    q∈surface ∧ q≠base 720 := by
  constructor
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨k,Finset.mem_Icc.mpr ⟨lo,hi⟩,?_⟩
    cases d
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  · rintro rfl
    have yes := original d k (by omega) h
    have no := List.all_eq_true.mp tagged k (List.mem_range'_1.mpr ⟨lo,by omega⟩)
    simp [allowedTag,yes] at no

private theorem follow (P : Program) (m : List Bool) (a b : State) (h : tracks a b) (tag : a.basis (base 720)=false)
    (incl : ∀q∈wires P,q∈surface ∧ q≠base 720) :
    tracks (run P m a) (run P m b) ∧ (run P m a).basis (base 720)=false := by
  have bound := Arithmetic.run_local_increment P a b m (fun q hq=>h q (incl q hq).1 (incl q hq).2)
  constructor
  · intro q use off
    by_cases gate : q∈wires P
    · exact bound.2 q gate
    · rw [run_preserves_outside _ _ _ _ gate,run_preserves_outside _ _ _ _ gate,h q use off]
  · rw [run_preserves_outside _ _ _ _ (fun use=>(incl _ use).2 rfl),tag]

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify StairArchiveNativeRows WindowParityDirty
set_option maxRecDepth 8000
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 100000
set_option linter.unusedSimpArgs false
def parity (cs : Cols) := ((List.range 16).map (get cs)).foldr (· ^^^ ·) 0
theorem matchedParity (d : Bool) :
    parity (ArchivePortAction.code d) = parity (StairArchiveNativeCut.canonical d d) := by
  cases d <;> decide +kernel
theorem region_run (d : Bool) (row : Nat) (_rb : row<63145) (m : List Bool) (s : State)
    (_data : ∀i<16,s.basis i=(get (ArchivePortAction.code d) i).testBit row) :
    run region m s = flip 16 (((parity (ArchivePortAction.code d)).testBit row) ^^
      ((parity (StairArchiveNativeCut.canonical d d)).testBit row)) s := by
  simp [region, run, matchedParity]
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.Stair44Kernel
open Arithmetic MappedCompressed Secp256k1 OB5 DirectSkywalk Rolling1588.Integer Stair44WalkMap
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588TickGap.forward
  Stair44WalkRun.forward FrontierEntry1591Native.forward

def firstR := renameProgram first (FrontierEntry1591Native.forward base)
def openR (d : Bool) (a : Nat) := firstR ++ Stair44WalkRun.forward d a
def openS (d : Bool) (a : Nat) := FrontierEntry1591Native.forward base ++ Rolling1588TickGap.forward d 1 (15+a)

private theorem inFix (x y : Nat) (s : State) (h : SkywalkArithmeticInput base x y s.basis) : pullState first s=s := by
  let l := [1026,514,1541,501,1542,500]
  have tab : ∀j∈l,base j∈skywalkSharedWires base ∧ base j∉skywalkArithmeticDivisor base ∧
      base j∉skywalkArithmeticNumerator base := by decide +kernel
  have z (j : Nat) (hj : j∈l) := h.2.2 _ (tab j hj).1 (tab j hj).2.1 (tab j hj).2.2
  have a := cleanWireRebind id s s _ _ rfl (z 1026 (by decide)) (z 514 (by decide))
  have b := cleanWireRebind _ s s _ _ a (z 1541 (by decide)) (z 501 (by decide))
  exact cleanWireRebind _ s s _ _ b (z 1542 (by decide)) (z 500 (by decide))

theorem open_count (d : Bool) (a : Nat) : measurementCount (openR d a)=measurementCount (openS d a) := by
  rw [openR,openS,measurementCount_append,measurementCount_append,firstR,(renameProgram_counts _ _).2,
    (Stair44WalkRun.metrics d a).1.2.1]

theorem open_run (d : Bool) (a x y : Nat) (atCut : 1+(15+a)∈[425,505,506]) (hx0 : 0<x) (hx : x<p)
    (hn : (skywalkSharedWires base).Nodup) (s : State) (input : SkywalkArithmeticInput base x y s.basis)
    (m : List Bool) : run (openR d a) m s=run (openS d a) m s := by
  rw [openR,openS,run_append,run_append,firstR,(renameProgram_counts _ _).2]
  let N := FrontierEntry1591Native.forward base
  let mn := m.take (measurementCount N)
  have r := run_rename first first.injective N mn s
  rw [inFix x y s input] at r
  have st := stage_one base d x p _ (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  exact Stair44WalkCuts.forward_done d a x atCut hx0 hx _ _ _ st r

theorem with_tail (d : Bool) (a x y : Nat) (atCut : 1+(15+a)∈[425,505,506]) (hx0 : 0<x) (hx : x<p)
    (hn : (skywalkSharedWires base).Nodup) (s : State) (input : SkywalkArithmeticInput base x y s.basis)
    (T : Program) (m : List Bool) :
    run (openR d a ++ T) m s=run (openS d a ++ T) m s := by
  rw [run_append,run_append,open_count,open_run d a x y atCut hx0 hx hn s input]

end ECDSAAdd.Entrant.Stair44Kernel

end




section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic MappedCompressed BalancedField Secp256k1 StairArchiveRelease StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask StairField2V3RecScratch StairPhysicalLayout
set_option maxRecDepth 2200
set_option maxHeartbeats 500000

def regular (z : Wire) := !(EP.contains z) && !((futurePayload 87).contains z)
private def archiveGood (j : Nat) := (List.range 121).all (fun q => q==16 || regular (host.symm (fieldPort j q)))
/-- `physicalHead` already pins `fieldPort j q = wire (histPort j q)`, so `host.symm` cancels and only
`regular` is evaluated. -/
private theorem portsHead :
    WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q => regular (host.symm (fieldPort j q))))=true := by
  have hr : WindowBankCheck.banks.all (fun j =>
      (List.range 16).all (fun q => regular (OB5.sig 511 (histPort j q)))) = true := by
    have hm : WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q =>
        !(WindowBankCheck.maskOf EP).testBit (OB5.sig 511 (histPort j q)) &&
        !(WindowBankCheck.maskOf (futurePayload 87)).testBit (OB5.sig 511 (histPort j q)))) = true := by
      decide +kernel
    simpa only [regular, WindowBankCheck.maskOf_testBit] using hm
  rw [List.all_eq_true] at hr ⊢
  intro j hj
  rw [List.all_eq_true]
  intro q hq
  have e := List.all_eq_true.mp (List.all_eq_true.mp physicalHead j hj) q hq
  rw [beq_iff_eq] at e
  rw [e, wire, Equiv.symm_apply_apply]
  exact List.all_eq_true.mp (hr j hj) q hq
private theorem portsTail :
    (List.range' 16 105).all (fun q => q==16 || regular (host.symm (fieldPort 0 q)))=true := by
  have hr : (List.range' 17 104).all (fun q => regular (OB5.sig 511 (base (Placement5.H (8+(q-17)))))) = true := by
    have hm : (List.range' 17 104).all (fun q =>
        !(WindowBankCheck.maskOf EP).testBit (OB5.sig 511 (base (Placement5.H (8+(q-17))))) &&
        !(WindowBankCheck.maskOf (futurePayload 87)).testBit
          (OB5.sig 511 (base (Placement5.H (8+(q-17)))))) = true := by
      decide +kernel
    simpa only [regular, WindowBankCheck.maskOf_testBit] using hm
  have tl := physicalTail
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at tl
  rw [List.all_eq_true]
  intro q hq
  by_cases h16 : q = 16
  · subst h16; rfl
  · have hq' : q ∈ List.range' 17 104 := by
      have := List.mem_range'_1.mp hq; exact List.mem_range'_1.mpr ⟨by omega, by omega⟩
    rw [tl.2 q hq', wire, Equiv.symm_apply_apply, List.all_eq_true.mp hr q hq', Bool.or_true]
private theorem portsCheck : WindowBankCheck.banks.all archiveGood=true := by
  rw [List.all_eq_true]
  intro j hj
  have hh := List.all_eq_true.mp portsHead j hj
  rw [archiveGood, List.all_eq_true]
  intro q hq
  have hq' := List.mem_range.mp hq
  by_cases lo : q < 16
  · have e := List.all_eq_true.mp hh q (List.mem_range.mpr lo)
    simp only [e, Bool.or_true]
  · have e := List.all_eq_true.mp portsTail q (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rw [fieldPort_tail j q (by omega)]
    exact e
private theorem cleanPort (j q : Nat) (jb : j∈bankIds) (qb : q<121) (ne : fieldPort j q≠base 720) :
    Off (host.symm (fieldPort j q)) ∧ host.symm (fieldPort j q)∉futurePayload 87 := by
  have jm : j∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using jb
  have ok := List.all_eq_true.mp (List.all_eq_true.mp portsCheck _ jm) q (List.mem_range.mpr qb)
  have eq16 : fieldPort j 16=base 720 := by
    simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at jb
    rcases jb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have qne : q≠16 := fun h=>ne (h ▸ eq16)
  simp only [beq_iff_eq,Bool.or_eq_true,regular,Bool.and_eq_true,Bool.not_eq_true'] at ok
  rcases ok with h|⟨f,g⟩
  · contradiction
  · refine ⟨off_of_not_EP _ ?_,?_⟩
    · intro h; simp [h] at f
    · intro h; simp [h] at g

private theorem packet_original (d : Bool) (k : Nat) :
    packet d k=renameProgram host (renameProgram (OB5.sig 511) (Rolling1588.packet d k)) := by
  rw [packet,hosts_eq,StairGroups.packet_zero]; rfl

private theorem groupOne (d : Bool) (k : Nat) : Rolling1588.groups d k 1=Rolling1588.packet d k := by
  cases d <;> simp only [Rolling1588.groups,PacketSequence.program,Bool.false_eq_true,if_true,if_false,
    List.nil_append,List.append_nil]
attribute [local irreducible] surface StairArchiveInactive.host OB5.sig wires Rolling1588.packet Rolling1588.groups StairArchiveInactive.packet futurePayload Off
theorem reliable {q : Wire} (use : q∈surface) (ntag : q≠base 720) :
    Off (host.symm q) ∧ host.symm q∉futurePayload 87 := by
  rw [surface,Finset.mem_union] at use
  rcases use with packet_|archive_
  · obtain ⟨k,hk,dirs⟩ := Finset.mem_biUnion.mp packet_
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hk
    have both (d : Bool) (used : q∈wires (packet d k)) : Off (host.symm q) ∧ host.symm q∉futurePayload 87 := by
      rw [packet_original,renameProgram_support] at used
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp used
      rw [Equiv.symm_apply_apply]
      rw [←groupOne d k] at hv
      constructor
      · cases d
        · exact StairField2V3ExitRec.groupsF_off k 1 lo (by omega) v hv
        · exact groups_off k 1 lo (by omega) v hv
      · intro bad
        exact StairField2V3Groups.groups_avoid_payload d 87 (by decide) 1 k
          (by change k+1≤85; omega) v bad hv
    exact (Finset.mem_union.mp dirs).elim (both false) (both true)
  · obtain ⟨j,hj,hq⟩ := Finset.mem_biUnion.mp archive_
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact cleanPort j i hj (Finset.mem_range.mp hi) ntag

theorem from_record (c : Nat) (origin : BasisState) (X Y : Fp) (r s : State)
    (cut : Rolling1588.CutFrame c origin X Y (pullState (OB5.sig 511) s))
    (tag : r.basis (base 720)=false)
    (hosted : ∀q, r.basis (host q)=r.basis q)
    (agrees : ∀ q, Off q → q∉futurePayload 87 → r.basis q=s.basis q) :
    StockCut c origin r := by
  let b := pullState host.symm s
  have back : pullState wire b=pullState (OB5.sig 511) s := by
    apply State.extensionality; · rfl
    funext q; change s.basis (host.symm (host (OB5.sig 511 q)))=_
    rw [Equiv.symm_apply_apply]; rfl
  refine ⟨tag,X,Y,b,back.symm ▸ cut,?_⟩
  intro q hq ntag
  have ready := reliable hq ntag
  have fixed := hosted (host.symm q)
  rw [Equiv.apply_symm_apply] at fixed
  exact fixed.trans (agrees _ ready.1 ready.2)

theorem host_fixed (r : State) (zero : ∀q∈StairSchedule.exclusiveRoles++hosts 87,r.basis q=false) :
    ∀q,r.basis (host q)=r.basis q := by
  have general (rs hs : List Wire) (clean : ∀q∈rs++hs,r.basis q=false) :
      ∀q,r.basis (rebinder rs hs q)=r.basis q := by
    induction rs generalizing hs with
    | nil => cases hs <;> intro q <;> rfl
    | cons a rest ih =>
      cases hs with
      | nil => intro q; rfl
      | cons b tail =>
        intro q
        have a0 := clean a (by simp)
        have b0 := clean b (by simp)
        have tails := ih tail (fun q h => clean q (by simpa only [List.mem_append,List.mem_cons] using (show (q=a ∨ q∈rest) ∨ q=b ∨ q∈tail from by rcases List.mem_append.mp h with left|right; exact Or.inl (Or.inr left); exact Or.inr (Or.inr right))))
        change r.basis ((Equiv.swap a b) (rebinder rest tail q)) = _
        rw [←tails q]; generalize rebinder rest tail q=v
        by_cases av : v=a
        · subst v; simp [a0,b0]
        by_cases bv : v=b
        · subst v; simp [a0,b0]
        rw [Equiv.swap_apply_of_ne_of_ne av bv]
  rw [host]; exact general _ _ zero
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
attribute [local irreducible] run group ten measurementCount packet surface
  ArchiveStockRows.Chronology Rolling1588.CutFrame StairArchiveNativeCut.canonical
set_option maxRecDepth 1600
set_option maxHeartbeats 400000

def span : Leg → Nat×Nat
  | .native j n => (j,n)
  | .paired j => (j,2)
def next (d : Bool) (l : Leg) := if d then (span l).1+(span l).2 else (span l).1
def prev (d : Bool) (l : Leg) := if d then (span l).1 else (span l).1+(span l).2
def feasible : Leg→Prop
  | .native j n => 1≤j ∧ j+n≤85
  | .paired j => j∈bankIds
def path (d : Bool) : Nat→List Leg→Prop
  | _,[] => True
  | c,l::ls => c=prev d l ∧ feasible l ∧ path d (next d l) ls
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

-- oddten:begin SEM
section

namespace ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks
open ECDSAAdd.Entrant.StairArchiveInactive

theorem packet_avoids_mixed (j : Nat) (hj : j ∈ mixedBankList) (d second : Bool)
    (q : Wire) (save : q ∈ savedSites j second) :
    q ∉ wires (packet d (if second then j + 1 else j)) :=
  packet_avoids_mixed_from_safe ECDSAAdd.Entrant.StairArchiveInactive.bank10 ECDSAAdd.Entrant.StairArchiveInactive.b60bank j hj d second q save

end ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxHeartbeats 900000
set_option maxRecDepth 22000
attribute [local irreducible] StairPacket.WindowFieldCosts.opk wires preimage cover savedSites

/-- oddten: dadon's `packet_avoids` for the field group's own packets (through the record footprint). -/
theorem ot_packet_avoids (j : Nat) (hj : j∈ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.mixedBankList) (d second : Bool)
    (q : Wire) (save : q∈savedSites j second) :
    q∉wires (StairPacket.WindowFieldCosts.opk d (if second then j+1 else j)) :=
  fun used => ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.packet_avoids_mixed j hj d second q save (StairPacket.WindowFieldCosts.ot_opk_sub d _ used)

/-- oddten: dadon's `advance`, packet := the field group's own packet. -/
theorem ot_advance (start : Nat) (hs : start∈ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.mixedBankList) (d second : Bool) (m : List Bool)
    (reference actual : State)
    (same : ∀ q ∉ savedSites start second, actual.basis q = reference.basis q) :
    let p := StairPacket.WindowFieldCosts.opk d (if second then start+1 else start)
    ((run p m actual).phase ^^ actual.phase) = ((run p m reference).phase ^^ reference.phase) ∧
    (∀ q ∉ savedSites start second, (run p m actual).basis q = (run p m reference).basis q) ∧
    (∀ q ∈ savedSites start second, (run p m actual).basis q = actual.basis q) := by
  let p := StairPacket.WindowFieldCosts.opk d (if second then start+1 else start)
  have unchanged := ot_packet_avoids start hs d second
  have act := Arithmetic.run_local_increment p actual reference m
    (fun q hq => same q (fun h => unchanged q h hq))
  refine ⟨act.1, ?_, fun q hq => run_preserves_outside p m actual q (unchanged q hq)⟩
  intro q keep
  by_cases used : q∈wires p
  · exact act.2 q used
  · exact (run_preserves_outside p m actual q used).trans ((same q keep).trans
      (run_preserves_outside p m reference q used).symm)

end ECDSAAdd.Entrant.StairArchiveInactive
end

section
namespace ECDSAAdd.Entrant.StairArchiveNativeCut
open Arithmetic CodecBitSliceVerify StairArchiveRelease StairArchiveSlots StairArchiveNativeRows
open StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
attribute [local irreducible] run StairPacket.WindowFieldCosts.opk fieldHook fieldPort inputCols outputCols CodecBitSliceVerify.get savedSites

theorem ot_xor_cancel (a b c : Bool) (h : (a ^^ c)=(b ^^ c)) : a=b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- oddten: dadon's `stage_packet` (one hook, then the field group's own packet). -/
theorem ot_stage_packet (j : Nat) (hstart : j∈ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.mixedBankList) (hj : j∈List.range' 1 83)
    (rev last : Bool) (row : Nat) (hr : row<63145) (m n : List Bool) (a ref : State)
    (change : frame j row (inputCols (fromStage rev last)) a)
    (out : exterior j a ref) (phase : a.phase=ref.phase)
    (entryFrame : frame j row (before rev last) ref)
    (endFrame : frame j row (after rev last)
      (run (StairPacket.WindowFieldCosts.opk (!rev) (if rev ^^ last then j+1 else j)) n ref)) :
    let c := run (fieldHook j (fromStage rev last)) m a
    let p := StairPacket.WindowFieldCosts.opk (!rev) (if rev ^^ last then j+1 else j)
    let s := run p n c
    let t := run p n ref
    s.phase=t.phase ∧ exterior j s t ∧ frame j row (inputCols (toStage rev last)) s := by
  let active := rev ^^ last
  let fromC := outputCols (fromStage rev last)
  let toC := inputCols (toStage rev last)
  let c := run (fieldHook j (fromStage rev last)) m a
  let p := StairPacket.WindowFieldCosts.opk (!rev) (if active then j+1 else j)
  have admin := StairArchiveAllPorts.field_run j hj _ row hr m a change
  have hchecks := all_checks rev last
  change (agrees active false fromC (before rev last) &&
    agrees active false toC (after rev last) && agrees active true fromC toC)=true at hchecks
  simp only [Bool.and_eq_true] at hchecks
  have same : ∀ z∉savedSites j active, c.basis z=ref.basis z := by
    intro z hz
    by_cases hz' : z∈inside j
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz'
      have hh : q∉held active := fun h => hz ((held_at j hj active q hq).mpr h)
      exact (admin.2.1 q hq).trans ((congrArg (fun v : Nat => v.testBit row)
        (column _ _ _ _ hchecks.1.1 q hq (decide_eq_false hh))).trans (entryFrame q hq).symm)
    · exact (admin.2.2 z hz').trans (out z hz')
  have body :
      ((run p n c).phase ^^ c.phase) = ((run p n ref).phase ^^ ref.phase) ∧
      (∀ z ∉ savedSites j active, (run p n c).basis z = (run p n ref).basis z) ∧
      (∀ z ∈ savedSites j active, (run p n c).basis z = c.basis z) :=
    ot_advance j hstart (!rev) active n ref c same
  have cphase : c.phase=ref.phase := admin.1.trans phase
  change (run p n c).phase = (run p n ref).phase ∧ exterior j (run p n c) (run p n ref) ∧ frame j row toC (run p n c)
  refine ⟨?_, ?_, ?_⟩
  · have v := body.1
    change ((run p n c).phase ^^ c.phase) = ((run p n ref).phase ^^ ref.phase) at v
    rw [cphase] at v
    exact ot_xor_cancel _ _ _ v
  · intro z hz
    apply body.2.1 z
    intro h
    rw [held_eq j hj active] at h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact hz (Finset.mem_image.mpr ⟨q,held_bounded _ hq,rfl⟩)
  · intro q hq
    by_cases hold : q∈held active
    · exact (body.2.2 _ ((held_at j hj active q hq).mpr hold)).trans
        ((admin.2.1 q hq).trans (congrArg (fun v : Nat => v.testBit row)
          (column _ _ _ _ hchecks.2 q hq (decide_eq_true hold))))
    · exact (body.2.1 _ (fun z => hold ((held_at j hj active q hq).mp z))).trans
        ((endFrame q hq).trans (congrArg (fun v : Nat => v.testBit row)
          (column _ _ _ _ hchecks.1.2 q hq (decide_eq_false hold))).symm)

end ECDSAAdd.Entrant.StairArchiveNativeCut
end

section
namespace ECDSAAdd.Entrant.StairArchiveTen
open CodecBitSliceVerify StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairPacket.WindowFieldCosts

def otapeS (j : Nat) (rev : Bool) (m : List Bool) := (tapeA j rev m).drop (measurementCount (ofirst j rev))
def otapeB (j : Nat) (rev : Bool) (m : List Bool) := (otapeS j rev m).drop (measurementCount (fieldHook j (shift rev)))
def otapeL (j : Nat) (rev : Bool) (m : List Bool) := (otapeB j rev m).drop (measurementCount (osecond j rev))
def orefMiddle (j : Nat) (rev : Bool) (m : List Bool) (s : State) :=
  run (ofirst j rev) (tapeA j rev m) s
def orefExit (j : Nat) (rev : Bool) (m : List Bool) (s : State) :=
  run (osecond j rev) (otapeB j rev m) (orefMiddle j rev m s)

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

/-- oddten: dadon's `ten_run` around the field group's own packets. -/
theorem ot_ten_run (j : Nat) (hs : j∈ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.mixedBankList) (hj : j∈List.range' 1 83)
    (rev : Bool) (row : Nat) (hr : row<63145) (m : List Bool) (a r : State)
    (arch : frame j row (inputCols (enter rev)) a)
    (same : exterior j a r) (ph : a.phase = r.phase)
    (before_ : frame j row (canonical (!rev) (!rev)) r)
    (middle_ : frame j row middle (orefMiddle j rev m r))
    (after_ : frame j row (canonical rev rev) (orefExit j rev m r)) :
    let actual := run (oten j rev) m a
    let final := orefExit j rev m r
    actual.phase=final.phase ∧ exterior j actual final ∧ frame j row (outputCols (leave rev)) actual := by
  let a0 := run (fieldHook j (enter rev)) m a
  let a1 := run (ofirst j rev) (tapeA j rev m) a0
  let a2 := run (fieldHook j (shift rev)) (otapeS j rev m) a1
  let a3 := run (osecond j rev) (otapeB j rev m) a2
  let a4 := run (fieldHook j (leave rev)) (otapeL j rev m) a3
  have f : a1.phase=(orefMiddle j rev m r).phase ∧ exterior j a1 (orefMiddle j rev m r) ∧
      frame j row (inputCols (shift rev)) a1 := by
    simpa only [fromStage, toStage, before, after, Bool.false_eq_true, if_false, Bool.xor_false,
      ofirst, orefMiddle] using ot_stage_packet j hs hj rev false row hr m (tapeA j rev m) a r
        arch same ph before_ (by simpa only [after, Bool.false_eq_true, if_false, Bool.xor_false, ofirst, orefMiddle] using middle_)
  have z : a3.phase=(orefExit j rev m r).phase ∧ exterior j a3 (orefExit j rev m r) ∧
      frame j row (inputCols (leave rev)) a3 := by
    have eq : (if rev ^^ true then j+1 else j) = (if rev then j else j+1) := by cases rev <;> rfl
    simpa only [fromStage, toStage, before, after, if_true, eq, osecond, orefExit] using
      ot_stage_packet j hs hj rev true row hr (otapeS j rev m) (otapeB j rev m) a1 (orefMiddle j rev m r)
        f.2.2 f.2.1 f.1 middle_ (by simpa only [after, if_true, eq, osecond, orefExit] using after_)
  have last := StairArchiveAllPorts.field_run j hj (leave rev) row hr (otapeL j rev m) a3 z.2.2
  have shape : run (oten j rev) m a = a4 := by
    simp only [oten, run_append, run_take]
    rfl
  rw [shape]
  exact ⟨last.1.trans z.1, fun q hq => (last.2.2 q hq).trans (z.2.1 q hq), last.2.1⟩

end ECDSAAdd.Entrant.StairArchiveTen
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify WindowFieldCosts

attribute [local irreducible] run StairArchiveInactive.packet StairArchiveRelease.fieldHook
  WindowFieldCosts.ofirst WindowFieldCosts.osecond WindowFieldCosts.oten
  StairArchiveRelease.fieldPort StairArchiveRelease.outputCols StairArchiveRelease.inputCols
  StairArchiveNativeCut.canonical CodecBitSliceVerify.get
set_option maxRecDepth 1200
set_option maxHeartbeats 360000
set_option linter.constructorNameAsVariable false
/-- oddten: dadon's `ten_masked` around the field group's own packets. -/
theorem ot_ten_masked (j : Nat) (hs : j ∈ ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.mixedBankList) (hj : j ∈ List.range' 1 83)
    (rev : Bool) (row : Nat) (hr : row < 63145) (m : List Bool) (a r : State)
    (other : Finset Wire) (apart : ∀ q ∈ inside j, q ∉ other)
    (ha : avoids (ofirst j rev) other) (hb : avoids (osecond j rev) other)
    (arch : frame j row (inputCols (enter rev)) a) (same : offBanks (bank j) other a r)
    (ph : a.phase = r.phase)
    (before_ : frame j row (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j row middle (orefMiddle j rev m r))
    (after_ : frame j row (StairArchiveNativeCut.canonical rev rev) (orefExit j rev m r)) :
    let next := run (oten j rev) m a
    let final := orefExit j rev m r
    next.phase = final.phase ∧ offBanks (bank j) other next final ∧
      frame j row (outputCols (leave rev)) next := by
  let shadow := mask other a r
  have mid : orefMiddle j rev m shadow = mask other a (orefMiddle j rev m r) := by
    exact mask_run (ofirst j rev) other _ a r ha
  have fin : orefExit j rev m shadow = mask other a (orefExit j rev m r) := by
    unfold orefExit
    rw [mid, mask_run]
    exact hb
  have outer : exterior j a shadow := by
    intro q hq
    by_cases qmem : q ∈ other
    · simp [shadow, mask, qmem]
    · have qbank : q ∉ bank j := by
        intro bad
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp bad
        exact hq (Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega),rfl⟩)
      simpa [shadow,mask,qmem] using same q qbank qmem
  have mm : frame j row middle (orefMiddle j rev m shadow) := mid ▸ mask_frame _ _ _ _ _ _ apart middle_
  have ff : frame j row (StairArchiveNativeCut.canonical rev rev) (orefExit j rev m shadow) := fin ▸ mask_frame _ _ _ _ _ _ apart after_
  have result := ot_ten_run j hs hj rev row hr m a shadow arch outer ph
    (mask_frame _ _ _ _ _ _ apart before_) mm ff
  obtain ⟨phase,ext,stored⟩ := result
  refine ⟨?_,?_,stored⟩
  · rw [fin] at phase
    exact phase
  · intro q notbank notother
    by_cases qin : q ∈ inside j
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp qin
      have lower : 16 ≤ k := by
        by_contra! h
        exact notbank (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr h, rfl⟩)
      have upper := Finset.mem_range.mp hk
      have kn : k ∈ List.range' 16 105 := List.mem_range'_1.mpr ⟨lower,by omega⟩
      have col := beq_iff_eq.mp (List.all_eq_true.mp (restored rev) k kn)
      rw [stored k hk,after_ k hk,col]
    · have x := ext q qin
      rw [fin] at x
      simpa [mask, notother] using x

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify WindowFieldCosts
set_option maxRecDepth 1600
set_option maxHeartbeats 400000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run packet fieldPort StairArchiveNativeCut.canonical inputCols outputCols CodecBitSliceVerify.get
attribute [local irreducible] inside StairArchiveRelease.fieldHook WindowFieldCosts.ofirst WindowFieldCosts.osecond
  WindowFieldCosts.oten WindowFieldCosts.opk WindowFieldCosts.ogroup WindowFieldCosts.group allBanks wires

private theorem ot_native_safe (j k : Nat) (hj : j∈bankIds) (which : k=j ∨ k=j+1) (d : Bool) :
    avoids (opk d k) (others j) :=
  fun q ho used => native_safe j k hj which d q ho (WindowFieldCosts.ot_opk_sub d k used)

/-- oddten: dadon's `stepTen` around the field group's own packets. -/
theorem ot_stepTen (j : Nat) (hj : j∈bankIds) (rows : Nat→Nat) (code : Nat→Cols) (rev : Bool)
    (bound : rows j < 63145) (m : List Bool) (a r : State) (h : Fits rows code a r)
    (active : code j=inputCols (enter rev))
    (before_ : frame j (rows j) (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j (rows j) middle (orefMiddle j rev m r))
    (after_ : frame j (rows j) (StairArchiveNativeCut.canonical rev rev) (orefExit j rev m r)) :
    Fits rows (update code j (outputCols (leave rev))) (run (oten j rev) m a) (orefExit j rev m r) := by
  have ⟨hs,hr⟩ := geometry hj
  have fa : avoids (ofirst j rev) (others j) := by
    rw [ofirst]; apply ot_native_safe _ _ hj; cases rev <;> simp
  have sa : avoids (osecond j rev) (others j) := by
    rw [osecond]; apply ot_native_safe _ _ hj; cases rev <;> simp
  have ea : avoids (oten j rev) (others j) := by
    rw [oten]; exact append_safe (hook_safe j hj _)
      (append_safe fa (append_safe (hook_safe j hj _) (append_safe sa (hook_safe j hj _))))
  have same : offBanks (bank j) (others j) a r := by
    intro q a0 a1; apply h.outside; rw [decompose j hj,Finset.mem_union]; exact fun hit => hit.elim a0 a1
  have result := ot_ten_masked j hs hr rev (rows j) bound m a r (others j) (apart hj) fa sa
    (beforeFrame j hj rows code rev a r h active (apart hj) before_ (field_inj j hr)) same h.phase before_ middle_ after_
  refine ⟨result.1,?_,?_⟩
  · intro q off
    rw [decompose j hj,Finset.mem_union] at off
    exact result.2.1 q (fun a=>off (Or.inl a)) (fun b=>off (Or.inr b))
  · intro k hk i hi
    by_cases eq : k=j
    · subst k
      simpa only [update,if_pos rfl] using result.2.2 i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
    · have ho : fieldPort k i∈others j := Finset.mem_biUnion.mpr
        ⟨k,Finset.mem_erase.mpr ⟨eq,hk⟩,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
      rw [run_preserves_outside _ m a _ (ea _ ho)]
      simpa only [update,if_neg eq] using h.bytes k hk i hi

theorem ot_groupSafe (d : Bool) (j n : Nat) (valid : nativeRanges j n) : avoids (ogroup d j n) allBanks :=
  fun q hq used => groupSafe d j n valid q hq (WindowFieldCosts.ot_ogroup_sub d j n used)

theorem tag_not_bank : base 720∉allBanks := by
  have chk : WindowBankCheck.banks.all (fun b =>
      (List.range 16).all (fun k => StairArchiveRelease.fieldPort b k != base 720))=true := by decide +kernel
  intro hb
  rw [allBanks,Finset.mem_biUnion] at hb
  obtain ⟨j,hj,hjb⟩ := hb
  rw [bank,Finset.mem_image] at hjb
  obtain ⟨k,hk,heq⟩ := hjb
  have jm : j∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using hj
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp chk j jm) k (List.mem_range.mpr (Finset.mem_range.mp hk))
  rw [heq] at h1
  simp at h1

theorem ot_rgroupSafe (d : Bool) (j n : Nat) (valid : nativeRanges j n) :
    avoids (WindowFieldCosts.rgroup d j n) allBanks :=
  fun q hq => WindowFieldCosts.rgroup_avoids d q j n (fun e => tag_not_bank (e ▸ hq)) (ot_groupSafe d j n valid q hq)

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldHistory
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairField2V3Seg
attribute [local irreducible] run wires rawCol CodecBitSliceVerify.get SkywalkTrace.next
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1400
set_option maxHeartbeats 400000

/-- oddten: `cut_byte` for any word code of the field registers (the bytes are history letters). -/
theorem ot_cut_byte (w : Fp → Nat) (cut j x row : Nat) (positive : 1≤j) (bound : j+2≤102)
    (rowBound : row<63145) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (tr : TraceOK x origin) (record : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (X Y : Fp) (s : State) (fr : RouteA.Rolling1588.CutFrame w w cut origin X Y s) (hi : Bool) (q : Fin 10) :
    let k := j+(if hi then 1 else 0)
    s.basis (History5.historyMap base (5*k) q) =
      (CodecBitSliceVerify.get (storage (native (decide (cut≤k)) hi)) q).testBit row := by
  let k := j+(if hi then 1 else 0)
  have boundK : k<102 := by cases hi <;> simp [k] <;> omega
  have posK : k≠0 := by cases hi <;> simp [k] <;> omega
  change s.basis (History5.historyMap base (5*k) q) = (CodecBitSliceVerify.get (storage (native (decide (cut≤k)) hi)) q).testBit row
  obtain ⟨raw,_,pair,eq⟩ := fr
  rw [eq,allEncodeCut_factor base cut base_pool_nodup 102 k (by decide) boundK raw]
  rw [run_preserves_outside _ _ _ _ (StairField2V3LastRecXPar.other_away base cut k
    base_pool_nodup 102 (by decide) boundK q),encodeGroup,if_neg posK,encodeAt]
  apply (StockArchiveByte.run_byte (decide (cut≤k)) hi row rowBound (History5.historyMap base (5*k))
    (History5.historyMap_injective base base_pool_nodup _ (by omega)) raw [] ?_).2 q
  intro i
  have away := History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
    (5*k) (by omega) i
  rw [pair.2.2 _ away.1 away.2]
  exact originBits j x row (by omega) (by omega) origin tr record hi i
end ECDSAAdd.Entrant.StairPacket.WindowFieldHistory
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairArchiveNativeCut StairArchiveRelease
open WindowFieldMask ArchiveFieldScratch StairField2V3Seg
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
attribute [local irreducible] run wire StairArchiveNativeCut.canonical StairArchiveRelease.fieldPort CodecBitSliceVerify.get

/-- oddten: `observed` for any word code of the field registers. -/
theorem oobserved (w : Fp → Nat) (j c x row : Nat) (hj : j∈WindowBankCheck.banks) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (X Y : Fp) (ideal actual : State) (cf : RouteA.Rolling1588.CutFrame w w c origin X Y (pullState wire ideal))
    (tag : actual.basis (base 720)=false)
    (view : ∀q∈inside j,q≠base 720→actual.basis q=ideal.basis q) :
    frame j row (boundaryCols j c) actual := by
  have geometry := List.all_eq_true.mp physical_ok j hj
  simp only [physical,Bool.and_eq_true,beq_iff_eq] at geometry
  have jBounds : 1≤j ∧ j+2≤102 := by
    simp only [WindowBankCheck.banks,List.mem_cons,List.mem_nil_iff,or_false] at hj; omega
  intro q hq
  have upper := Finset.mem_range.mp hq
  have eq16 := geometry.1.2
  have nd := field_inj j (List.mem_range'_1.mpr (by
      simp only [WindowBankCheck.banks,List.mem_cons,List.mem_nil_iff,or_false] at hj; omega))
  by_cases isTag : q=16
  · subst q
    rw [eq16,tag]
    have zero := beq_iff_eq.mp (List.all_eq_true.mp (upper_zero (decide (c≤j)) (decide (c≤j+1))) 16 (by decide))
    simp [boundaryCols,zero]
  · have off : fieldPort j q ≠ base 720 := fun he=>isTag (nd _ hq 16 (by decide) (he.trans eq16.symm))
    rw [view _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩) off]
    by_cases low : q<16
    · have loc := beq_iff_eq.mp (List.all_eq_true.mp geometry.1.1 q (List.mem_range.mpr low))
      rw [loc]
      have byte := WindowFieldHistory.ot_cut_byte w c j x row jBounds.1 jBounds.2 rb origin ctx tr history X Y
        (pullState wire ideal) cf (high q) (lane q)
      change ideal.basis (wire (histPort j q))=_ at byte
      rw [byte]
      have col := beq_iff_eq.mp (List.all_eq_true.mp (lookup_ok (decide (c≤j)) (decide (c≤j+1))) q (List.mem_range.mpr low))
      unfold boundaryCols; rw [col]
      cases high q <;> simp
    · have member : q∈List.range' 17 104 := List.mem_range'_1.mpr ⟨by omega,by omega⟩
      have loc := beq_iff_eq.mp (List.all_eq_true.mp geometry.2 q member)
      rw [loc]
      have clean := RouteA.Rolling1588.cutFrame_zero_region w w c origin ctx X Y _ cf (Placement5.H (8+(q-17)))
        (Or.inr (Placement5.H_region (8+(q-17)) (by omega)))
      change ideal.basis (wire (base (Placement5.H (8+(q-17)))))=false at clean
      have zero := beq_iff_eq.mp (List.all_eq_true.mp (upper_zero (decide (c≤j)) (decide (c≤j+1))) q
        (List.mem_range'_1.mpr ⟨by omega,by omega⟩))
      simp only [boundaryCols,zero,clean,Nat.zero_testBit]
end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run wires measurementCount StairArchiveInactive.packet WindowFieldCosts.opk
  WindowFieldCosts.ogroup

/-- the word code of the field registers at cut `c` (odd words on cuts 1..85). -/
def oddCutWord (c : Nat) : Fp → Nat := if 1≤c ∧ c≤85 then P1Life.oddWord else centerWord
theorem oddCutWord_odd {c : Nat} (h1 : 1≤c) (h2 : c≤85) : oddCutWord c=P1Life.oddWord := if_pos ⟨h1,h2⟩
theorem oddCutWord_center {c : Nat} (h : c<1 ∨ 85<c) : oddCutWord c=centerWord := if_neg (by omega)

/-- `StockCut` with the cut's word code. -/
def OCut (c : Nat) (origin : BasisState) (r : State) : Prop :=
  r.basis (base 720)=false ∧ ∃ (X Y : Fp) (ideal : State),
    RouteA.Rolling1588.CutFrame (oddCutWord c) (oddCutWord c) c origin X Y (pullState wire ideal) ∧ tracks r ideal

theorem ocut_of_stock (c : Nat) (hc : c<1 ∨ 85<c) (origin : BasisState) (r : State)
    (h : StockCut c origin r) : OCut c origin r := by
  obtain ⟨zero,X,Y,ideal,cf,view⟩ := h
  refine ⟨zero,X,Y,ideal,?_,view⟩
  rw [oddCutWord_center hc]
  exact cf

/-- division-kernel packet `k` of the family between its cut frames. -/
theorem pk_frame_div (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple (RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin X Y)
      (oddPk true k)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord (k+1)) (oddCutWord (k+1)) (k+1) origin V.1 V.2 state) := by
  rcases (show (1≤k ∧ k<84) ∨ k=84 ∨ 84<k by omega) with ⟨h1,h2⟩|h|h
  · rw [oddPk_mid true k h1 h2,oddCutWord_odd h1 (by omega),oddCutWord_odd (c := k+1) (by omega) (by omega)]
    exact RouteA.Rolling1588.packet_cut_frame true k lo (by omega) (fun _ => by omega) origin ctx enabled X Y
  · subst h
    rw [oddPk_end,oddCutWord_odd (c := 84) (by omega) (by omega),oddCutWord_odd (c := 84+1) (by omega) (by omega)]
    have h0eq := WindowFieldCosts.half760OddLoan_zero_eq true
    intro state records input
    have raw := RouteA.Rolling1588.cut_window_frame P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord 84 85 84 (by decide) origin X Y _ _
      (OddFullPass.P1LifeLoan.basePacket true 0 84) (ECDSAAdd.Entrant.Rolling1588.otherEncodeCut_step base 84 102)
      (ECDSAAdd.Entrant.Rolling1588.otherEncodeCut_body_disjoint 84 84 (by decide) origin ctx _
        (by
          have hsub : wires (OddFullPass.P1LifeLoan.basePacket true 0 84) ⊆ wires (ECDSAAdd.Entrant.Rolling1588.basePacket true 84) := by
            have hp := OddFullPass.P1LifeLoan.packet_wires_sub true 0 84 (by decide)
            rw [OddFullPass.P1LifeLoan.packet,StairGroups.packet_zero,ECDSAAdd.Entrant.Rolling1588.packet,
              renameProgram_support,renameProgram_support] at hp
            intro q hq
            have hi := Finset.mem_image.mp (hp (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
            obtain ⟨v,hv,eq⟩ := hi; exact (Equiv.injective _ eq) ▸ hv
          exact hsub.trans (ECDSAAdd.Entrant.Rolling1588.basePacket_read_support true 84 (by decide))))
      (fun current tape frame => by
        have hcEq : ∀ a b, OddFullPass.P1LifeLoan.cell true 0 84 a b = RouteA.Rolling1588.cell true 84 a b := by
          intro a b; simp only [OddFullPass.P1LifeLoan.cell,RouteA.Rolling1588.cell,
            OddFullPass.P1LifeLoan.halfWindow,RouteA.Rolling1588.halfWindow,RouteA.Rolling1588.halfWindowWith,if_true,h0eq]
        have normalized : RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
            (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt true (History5.historyMap base (5*84))) origin X Y current := by
          simpa [ECDSAAdd.Entrant.Rolling1588.encodeGroup] using frame
        let Frame (k : Nat) (V : Fp×Fp) :=
          RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
            (ECDSAAdd.Entrant.Rolling1588.stageCodeAt true k (History5.historyMap base (5*84))) origin V.1 V.2
        have opening (V : Fp×Fp) : ECDSAAdd.Entrant.Rolling1588.StateTriple
            (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
              (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt true (History5.historyMap base (5*84))) origin V.1 V.2)
            (ECDSAAdd.Entrant.Rolling1588.onPacket 84 ECDSAAdd.Entrant.Rolling1588.stageOpen) (Frame 0 V) :=
          fun s r h => RouteA.Rolling1588.regular_open_frame P1Life.oddWord P1Life.oddWord true 84 (by decide) origin ctx V.1 V.2 s r h
        have step (k logical physical : Nat) (hk : k<3) (used : (logical,physical)∈ECDSAAdd.Entrant.Rolling1588.activeSlots true k) (V : Fp×Fp) :
            ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame k V) (RouteA.Rolling1588.cell true 84 physical 2)
              (Frame k (ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin logical V)) :=
          fun s r h => RouteA.Rolling1588.regular_cell_frame true 84 k logical physical (by decide) hk used origin ctx enabled V.1 V.2 s r h
        have transfer (k : Nat) (hk : k<2) (V : Fp×Fp) :
            ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame k V)
              (ECDSAAdd.Entrant.Rolling1588.onPacket 84 (ECDSAAdd.Entrant.Rolling1588.stageTransition true k)) (Frame (k+1) V) :=
          fun s r h => RouteA.Rolling1588.regular_transition_frame P1Life.oddWord P1Life.oddWord true 84 k (by decide) hk origin ctx V.1 V.2 s r h
        have closing (V : Fp×Fp) : ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame 2 V)
            (ECDSAAdd.Entrant.Rolling1588.onPacket 84 ECDSAAdd.Entrant.Rolling1588.stageClose)
            (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
              (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt false (History5.historyMap base (5*84))) origin V.1 V.2) :=
          fun s r h => RouteA.Rolling1588.regular_close_frame P1Life.oddWord P1Life.oddWord true 84 (by decide) origin ctx V.1 V.2 s r h
        let V1 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 0 (X,Y)
        let V2 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 1 V1
        let V3 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 2 V2
        let V4 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 3 V3
        let V5 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 4 V4
        have hres := (opening (X,Y)).seq
          ((step 0 0 3 (by decide) (by decide) (X,Y)).seq
          ((step 0 1 4 (by decide) (by decide) V1).seq
          ((transfer 0 (by decide) V2).seq
          ((step 1 2 4 (by decide) (by decide) V2).seq
          ((step 1 3 3 (by decide) (by decide) V3).seq
          ((transfer 1 (by decide) V4).seq
          ((step 2 4 4 (by decide) (by decide) V4).seq (closing V5))))))))
        have hstep := hres current tape normalized
        rw [show V5 = ECDSAAdd.Entrant.Rolling1588.regularPayload true 84 origin (X,Y) from by
              simp only [V5,V4,V3,V2,V1,ECDSAAdd.Entrant.Rolling1588.regularPayload,if_true],
            ECDSAAdd.Entrant.Rolling1588.regularPayload_eq true 84 (by decide) origin enabled] at hstep
        simpa only [OddFullPass.P1LifeLoan.basePacket,hcEq,ECDSAAdd.Entrant.Rolling1588.stageOpen,
          ECDSAAdd.Entrant.Rolling1588.stageClose,ECDSAAdd.Entrant.Rolling1588.stageTransition,
          if_true,if_false,List.append_assoc,ECDSAAdd.Entrant.Rolling1588.encodeGroup] using hstep)
      state records input
    have same := Replay5.placed_eq (Placement5.pi 84) (OddFullPass.P1LifeLoan.basePacket true 0 84)
      (fun q hq => Placement5.pi_outside 84 q (by decide) hq) state records
      (RouteA.Rolling1588.cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
      (RouteA.Rolling1588.cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
    change run (OddFullPass.P1LifeLoan.packet true 0 84) records state = run (OddFullPass.P1LifeLoan.basePacket true 0 84) records state at same
    rw [same]; exact raw
  · rw [oddPk_std true k h,oddCutWord_center (c := k) (by omega),oddCutWord_center (c := k+1) (by omega)]
    exact ECDSAAdd.Entrant.Rolling1588.packet_cut_frame true k lo (by omega) origin ctx enabled X Y

/-- multiplication-kernel packet `k` of the family between its cut frames. -/
theorem pk_frame_mul (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple (RouteA.Rolling1588.CutFrame (oddCutWord (k+1)) (oddCutWord (k+1)) (k+1) origin X Y)
      (oddPk false k)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2 state) := by
  rcases (show (1≤k ∧ k<84) ∨ k=84 ∨ 84<k by omega) with ⟨h1,h2⟩|h|h
  · rw [oddPk_mid false k h1 h2,oddCutWord_odd (c := k+1) (by omega) (by omega),oddCutWord_odd h1 (by omega)]
    exact RouteA.Rolling1588.packet_cut_frame false k lo (by omega) (fun e => absurd e Bool.false_ne_true) origin ctx enabled X Y
  · subst h
    rw [oddPk_end,oddCutWord_odd (c := 84+1) (by omega) (by omega),oddCutWord_odd (c := 84) (by omega) (by omega)]
    have h0eq : OddFullPass.P1LifeLoan.packet false 0 84 = RouteA.Rolling1588.packet false 84 := by
      have hh := WindowFieldCosts.half760OddLoan_zero_eq false
      simp only [OddFullPass.P1LifeLoan.packet,RouteA.Rolling1588.packet,
        OddFullPass.P1LifeLoan.basePacket,RouteA.Rolling1588.basePacket,
        OddFullPass.P1LifeLoan.cell,RouteA.Rolling1588.cell,
        OddFullPass.P1LifeLoan.halfWindow,RouteA.Rolling1588.halfWindow,RouteA.Rolling1588.halfWindowWith,
        hh,Bool.false_eq_true,if_false,if_true]
    rw [h0eq]
    exact RouteA.Rolling1588.packet_cut_frame false 84 (by decide) (by decide) (fun e => absurd e Bool.false_ne_true) origin ctx enabled X Y
  · rw [oddPk_std false k h,oddCutWord_center (c := k+1) (by omega),oddCutWord_center (c := k) (by omega)]
    exact ECDSAAdd.Entrant.Rolling1588.packet_cut_frame false k lo (by omega) origin ctx enabled X Y

private theorem ofield_cut_frame_mul' (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin X Y)
      (PacketSequence.program false (oddPk false) j n)
      (fun state => let V := PacketSequence.payload false (fun k V => directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin V.1 V.2 state) :=
  RouteA.Rolling1588.route_cut_sequence_frame false (oddPk false)
    (fun k V => directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) 85
    (fun k hk kb V => pk_frame_mul k hk (by omega) origin ctx enabled V.1 V.2) j n first bound (X,Y)

/-- the multiplication field packets `j+n-1..j` between cut frames. -/
theorem ofield_cut_frame_mul (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin X Y)
      (PacketSequence.program false (oddPk false) j n)
      (fun state => let V := Replay5.groupsPayload false origin j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin V.1 V.2 state) :=
  ofield_cut_frame_mul' j n first bound origin ctx enabled X Y

/-- the division packet law in the exact shape `route_cut_sequence_frame` instantiates (payload as a redex). -/
private theorem lawDiv (k : Nat) (hk : 1≤k) (kb : k<85) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (V : Fp×Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      ((fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) (if true then k else k+1) V)
      (oddPk true k)
      ((fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) (if true then k+1 else k)
        ((fun k (V : Fp×Fp) => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) k V)) := by
  have h : (fun k (V : Fp×Fp) => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) k V =
      directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (V.1,V.2) := rfl
  rw [h]
  exact pk_frame_div k hk (by omega) origin ctx enabled V.1 V.2

private theorem ofield_cut_frame_div' (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin X Y)
      (PacketSequence.program true (oddPk true) j n)
      (fun state => let V := PacketSequence.payload true (fun k V => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin V.1 V.2 state) :=
  RouteA.Rolling1588.route_cut_sequence_frame true (oddPk true)
    (fun k (V : Fp×Fp) => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) 85
    (fun k hk kb V => lawDiv k hk kb origin ctx enabled V) j n first bound (X,Y)

/-- the division field packets `j..j+n-1` between cut frames. -/
theorem ofield_cut_frame_div (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin X Y)
      (PacketSequence.program true (oddPk true) j n)
      (fun state => let V := Replay5.groupsPayload true origin j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin V.1 V.2 state) :=
  ofield_cut_frame_div' j n first bound origin ctx enabled X Y

/-- the odd field packets 1..84 run directly between odd-word cut frames at cuts 1 and 85. -/
theorem ofield_cut_frame_odd (d : Bool) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if d then 1 else 85) origin X Y)
      (PacketSequence.program d (oddPk d) 1 84)
      (fun state => let V := Replay5.groupsPayload d origin 1 84 (X,Y)
        RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if d then 85 else 1) origin V.1 V.2 state) := by
  have c1 : oddCutWord 1=P1Life.oddWord := oddCutWord_odd (by decide) (by decide)
  have c85 : oddCutWord (1+84)=P1Life.oddWord := oddCutWord_odd (by decide) (by decide)
  cases d
  · simpa only [Bool.false_eq_true,if_false,c1,c85] using
      ofield_cut_frame_mul 1 84 (by decide) (by decide) origin ctx enabled X Y
  · simpa only [if_true,c1,c85] using
      ofield_cut_frame_div 1 84 (by decide) (by decide) origin ctx enabled X Y

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 2600
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run wires measurementCount wire group StairArchiveInactive.packet WindowFieldCosts.opk
  WindowFieldCosts.ogroup

theorem ot_opk_map (d : Bool) (k : Nat) : opk d k=renameProgram wire (oddPk d k) := by
  unfold opk
  calc
    _ = renameProgram StairArchiveInactive.host (renameProgram (OB5.sig 511) (oddPk d k)) :=
      StairArchiveInactive.hosts_eq _ _ _
    _ = _ := by rw [renameProgram_comp]; unfold wire; rfl

/-- oddten: dadon's `step` for the field group's own packet, multiplication kernel (packet `k`: cut `k+1` to cut `k`). -/
theorem ostep_mul (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut (k+1) origin r) :
    OCut k origin (run (opk false k) m r) := by
  have uses : ∀ q∈wires (opk false k), q∈surface ∧ q≠base 720 :=
    fun q h => packetUses false k lo hi (WindowFieldCosts.ot_opk_sub false k h)
  obtain ⟨zero,X,Y,b,fr,match_⟩ := initial
  obtain ⟨same,afterZero⟩ := follow _ m r b match_ zero uses
  have actual := pk_frame_mul k lo hi origin ctx enabled X Y _ m fr
  refine ⟨afterZero,(directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).1,
    (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).2,
    run (opk false k) m b,?_,same⟩
  rw [ot_opk_map,run_rename wire injective]; exact actual.2

/-- oddten: dadon's `step` for the field group's own packet, division kernel (packet `k`: cut `k` to cut `k+1`). -/
theorem ostep_div (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut k origin r) :
    OCut (k+1) origin (run (opk true k) m r) := by
  have uses : ∀ q∈wires (opk true k), q∈surface ∧ q≠base 720 :=
    fun q h => packetUses true k lo hi (WindowFieldCosts.ot_opk_sub true k h)
  obtain ⟨zero,X,Y,b,fr,match_⟩ := initial
  obtain ⟨same,afterZero⟩ := follow _ m r b match_ zero uses
  have actual := pk_frame_div k lo hi origin ctx enabled X Y _ m fr
  refine ⟨afterZero,(directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).1,
    (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).2,
    run (opk true k) m b,?_,same⟩
  rw [ot_opk_map,run_rename wire injective]; exact actual.2

/-- oddten: dadon's `step` for the field group's own packet. -/
theorem ostep (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut (if d then k else k+1) origin r) :
    OCut (if d then k+1 else k) origin (run (opk d k) m r) := by
  cases d
  · exact ostep_mul k lo hi origin ctx enabled r m initial
  · exact ostep_div k lo hi origin ctx enabled r m initial

/-- oddten: dadon's `selected` for the field group's own packets. -/
theorem oselected (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut (if d then j else j+n) origin r) :
    OCut (if d then j+n else j) origin (run (ogroup d j n) m r) := by
  rw [ogroup]
  induction n generalizing j r m with
  | zero =>
    simpa only [PacketSequence.program,run,Nat.add_zero] using initial
  | succ n ih =>
    cases d with
    | false =>
      simp only [Bool.false_eq_true,if_false] at initial ⊢
      simp only [PacketSequence.program,Bool.false_eq_true,if_false,run_append,run_take]
      apply ostep false j lo (by omega) origin ctx enabled
      apply ih (j+1) (by omega) (by omega) r m
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using initial
    | true =>
      simp only [if_true] at initial ⊢
      simp only [PacketSequence.program,if_true,run_append,run_take]
      have first := ostep true j lo (by omega) origin ctx enabled r m initial
      have last := ih (j+1) (by omega) (by omega) _ (m.drop (measurementCount (opk true j))) first
      simpa only [if_true,Nat.add_assoc,Nat.add_comm 1 n] using last

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run wires measurementCount StairArchiveInactive.packet WindowFieldCosts.opk
  WindowFieldCosts.ogroup

/-- `CutFrame` determines the complete basis state. -/
theorem cutFrame_basis_unique (w : Fp → Nat) (c : Nat) (origin : BasisState) (X Y : Fp) (s1 s2 : State)
    (h1 : RouteA.Rolling1588.CutFrame w w c origin X Y s1)
    (h2 : RouteA.Rolling1588.CutFrame w w c origin X Y s2) : s1.basis=s2.basis := by
  obtain ⟨raw1,_,f1,e1⟩ := h1
  obtain ⟨raw2,_,f2,e2⟩ := h2
  have same := PairFrame.unique _ _ origin _ _ raw1.basis raw2.basis f1 f2
  rw [e1,e2]
  exact Arithmetic.run_basis_records _ raw1 raw2 [] [] same

/-- The retired carry `base 760` is clean in every cut frame. -/
theorem cutFrame_760 (w : Fp → Nat) (c : Nat) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (X Y : Fp) (s : State) (h : RouteA.Rolling1588.CutFrame w w c origin X Y s) : s.basis (base 760)=false := by
  obtain ⟨raw,_,f,e⟩ := h
  have clean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
  have away := Rolling1588Lifetime.half_work_away (base 760) RouteA.Rolling1588.host760_work
  have support : wires (Rolling1588.allEncodeCut base c 102)⊆
      (wireBlock base 0 512++wireBlock base 1028 512).toFinset := by
    rw [Rolling1588.allEncodeCut_support_eq]
    exact NewHistory5.allEncode_history_support base 102 (by decide)
  have notEnc : base 760∉wires (Rolling1588.allEncodeCut base c 102) := by
    intro used
    have member := support used
    simp only [List.mem_toFinset,List.mem_append] at member
    rcases member with low|high
    · exact OwnPlusHost.not_block 760 0 512 (by omega) low
    · exact OwnPlusHost.not_block 760 1028 512 (by omega) high
  rw [e,run_preserves_outside _ _ _ _ notEnc]
  exact (f.2.2 _ away.1 away.2).trans (clean _ RouteA.Rolling1588.host760_work)

/-- Two runs that agree from `b` agree from any `a` that matches `b` on a common footprint. -/
theorem lift_on (P Q : Program) (F : Finset Wire) (hP : wires P⊆F) (hQ : wires Q⊆F) (m n : List Bool)
    (a b : State) (agree : ∀ q∈F, a.basis q=b.basis q) (same : run P m b=run Q n b) :
    run P m a=run Q n a := by
  have hp := Arithmetic.run_local_increment P a b m (fun q hq => agree q (hP hq))
  have hq := Arithmetic.run_local_increment Q a b n (fun q hq => agree q (hQ hq))
  apply State.extensionality
  · have e1 := hp.1
    rw [same] at e1
    have e := e1.trans hq.1.symm
    revert e
    generalize (run P m a).phase = x
    generalize (run Q n a).phase = y
    generalize a.phase = z
    cases x <;> cases y <;> cases z <;> decide
  · funext q
    by_cases inP : q∈wires P
    · by_cases inQ : q∈wires Q
      · rw [hp.2 q inP,same,← hq.2 q inQ]
      · rw [hp.2 q inP,same,run_preserves_outside Q n b q inQ,run_preserves_outside Q n a q inQ,
          agree q (hP inP)]
    · by_cases inQ : q∈wires Q
      · rw [run_preserves_outside P m a q inP,agree q (hQ inQ),← run_preserves_outside P m b q inP,
          same,← hq.2 q inQ]
      · rw [run_preserves_outside P m a q inP,run_preserves_outside Q n a q inQ]

theorem pull_injective_of_surjective (f : Wire → Wire) (hs : Function.Surjective f) :
    Function.Injective (pullState f) := by
  intro s t h
  apply State.extensionality
  · have e := congrArg State.phase h
    exact e
  · funext p
    obtain ⟨q,rfl⟩ := hs p
    exact congrArg (fun x : State => x.basis q) h

theorem opk_surface (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) {q : Wire} (h : q∈wires (opk d k)) :
    q∈surface := by
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  refine ⟨k,Finset.mem_Icc.mpr ⟨lo,hi⟩,?_⟩
  have h' := WindowFieldCosts.ot_opk_sub d k h
  cases d
  · exact Finset.mem_union_left _ h'
  · exact Finset.mem_union_right _ h'

theorem wire_760 : wire (base 760)=base 760 := by decide +kernel

theorem rpk_map (d : Bool) (k : Nat) (h : 10≤k) (h' : k≤84) :
    rpk d k=renameProgram (fun q => rawSwap (wire q)) (RouteA.Rolling1588.rawPacket d k) := by
  rw [rpk,if_pos ⟨h,h'⟩,StairArchiveInactive.hosts_eq,renameProgram_comp,renameProgram_comp]
  unfold wire
  rfl

/-- On a reference cut state (archive tag clean), the fully decoded packet runs exactly as the
regular packet, for any pair of measurement tapes. -/
theorem rpk_run_eq (d : Bool) (k : Nat) (lo : 10≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m m' : List Bool) (initial : OCut (if d then k else k+1) origin r) :
    run (rpk d k) m r=run (opk d k) m' r := by
  obtain ⟨zero,X,Y,b,fr,match_⟩ := initial
  let φ : Wire → Wire := fun q => rawSwap (wire q)
  have φinj : Function.Injective φ := rawSwap.injective.comp injective
  have φsurj : Function.Surjective φ := by
    intro p
    refine ⟨OB5.sig 511 (StairArchiveInactive.host.symm (rawSwap p)),?_⟩
    simp only [φ,wire,OB5.sig_invol 511 (by decide),Equiv.apply_symm_apply,rawSwap,Equiv.swap_apply_self]
  have no760 := WindowFieldCosts.opk_avoid760 d k (by omega) hi
  have no720 := WindowFieldCosts.opk_avoid720 d k (by omega) hi
  have fixOn : ∀ q∈wires (oddPk d k), φ q=wire q := by
    intro q hq
    have hw : wire q∈wires (opk d k) := by
      rw [ot_opk_map,renameProgram_support]; exact Finset.mem_image_of_mem _ hq
    exact Equiv.swap_apply_of_ne_of_ne (fun e => no760 (e ▸ hw)) (fun e => no720 (e ▸ hw))
  have opkφ : opk d k=renameProgram φ (oddPk d k) :=
    (ot_opk_map d k).trans (RouteA.Rolling1588.renameProgram_congr_on _ _ _ (fun q hq => (fixOn q hq).symm))
  let t := pullState wire b
  let u := pullState φ r
  have wordIn : oddCutWord (if d then k else k+1)=P1Life.oddWord :=
    oddCutWord_odd (by split <;> omega) (by split <;> omega)
  have wordOut : oddCutWord (if d then k+1 else k)=P1Life.oddWord :=
    oddCutWord_odd (by split <;> omega) (by split <;> omega)
  rw [wordIn] at fr
  have idealEq : run (RouteA.Rolling1588.rawPacket d k) m t=run (oddPk d k) m' t := by
    have rawStep := RouteA.Rolling1588.rawPacket_cut_frame d k (by omega) (by omega) origin ctx enabled X Y t m fr
    cases d
    · have oddStep := pk_frame_mul k (by omega) hi origin ctx enabled X Y t m'
        (by simpa only [Bool.false_eq_true,if_false,oddCutWord_odd (c := k+1) (by omega) (by omega)] using fr)
      simp only [Bool.false_eq_true,if_false,Bool.not_false] at rawStep wordOut
      rw [wordOut] at oddStep
      exact State.extensionality _ _ (rawStep.1.trans oddStep.1.symm)
        (cutFrame_basis_unique _ _ _ _ _ _ _ rawStep.2 oddStep.2)
    · have oddStep := pk_frame_div k (by omega) hi origin ctx enabled X Y t m'
        (by simpa only [if_true,oddCutWord_odd (c := k) (by omega) (by omega)] using fr)
      simp only [if_true,Bool.not_true] at rawStep wordOut
      rw [wordOut] at oddStep
      exact State.extensionality _ _ (rawStep.1.trans oddStep.1.symm)
        (cutFrame_basis_unique _ _ _ _ _ _ _ rawStep.2 oddStep.2)
  have rawSub : wires (RouteA.Rolling1588.rawPacket d k)⊆insert (base 760) (wires (oddPk d k)) := by
    rw [WindowFieldCosts.oddPk_regular d k (by omega) hi]
    exact RouteA.Rolling1588.rawPacket_wires d k (by omega)
  have agree : ∀ q∈insert (base 760) (wires (oddPk d k)), u.basis q=t.basis q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with e|member
    · subst e
      have a : u.basis (base 760)=r.basis (base 720) := by
        change r.basis (rawSwap (wire (base 760)))=_
        rw [wire_760,rawSwap,Equiv.swap_apply_left]
      rw [a,zero]
      exact (cutFrame_760 _ _ _ ctx _ _ _ fr).symm
    · have hw : wire q∈wires (opk d k) := by
        rw [ot_opk_map,renameProgram_support]; exact Finset.mem_image_of_mem _ member
      change r.basis (φ q)=b.basis (wire q)
      rw [fixOn q member]
      exact match_ _ (opk_surface d k (by omega) hi hw) (fun e => no720 (e ▸ hw))
  have lifted := lift_on _ _ _ rawSub (Finset.subset_insert _ _) m m' u t agree idealEq
  apply pull_injective_of_surjective φ φsurj
  rw [rpk_map d k lo hi,run_rename φ φinj,opkφ,run_rename φ φinj]
  exact lifted

theorem gpk_map (d : Bool) (k : Nat) :
    gpk d k=renameProgram (fun q => rawSwap (wire q)) (RouteA.Rolling1588.rawPacket d k) := by
  rw [gpk,StairArchiveInactive.hosts_eq,renameProgram_comp,renameProgram_comp]
  unfold wire
  rfl

/-- On a reference cut state (archive tag clean), the fully decoded packet runs exactly as the
regular packet, for any pair of measurement tapes. -/
theorem gpk_run_eq (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m m' : List Bool) (initial : OCut (if d then k else k+1) origin r) :
    run (gpk d k) m r=run (opk d k) m' r := by
  obtain ⟨zero,X,Y,b,fr,match_⟩ := initial
  let φ : Wire → Wire := fun q => rawSwap (wire q)
  have φinj : Function.Injective φ := rawSwap.injective.comp injective
  have φsurj : Function.Surjective φ := by
    intro p
    refine ⟨OB5.sig 511 (StairArchiveInactive.host.symm (rawSwap p)),?_⟩
    simp only [φ,wire,OB5.sig_invol 511 (by decide),Equiv.apply_symm_apply,rawSwap,Equiv.swap_apply_self]
  have no760 := WindowFieldCosts.opk_avoid760 d k (by omega) hi
  have no720 := WindowFieldCosts.opk_avoid720 d k (by omega) hi
  have fixOn : ∀ q∈wires (oddPk d k), φ q=wire q := by
    intro q hq
    have hw : wire q∈wires (opk d k) := by
      rw [ot_opk_map,renameProgram_support]; exact Finset.mem_image_of_mem _ hq
    exact Equiv.swap_apply_of_ne_of_ne (fun e => no760 (e ▸ hw)) (fun e => no720 (e ▸ hw))
  have opkφ : opk d k=renameProgram φ (oddPk d k) :=
    (ot_opk_map d k).trans (RouteA.Rolling1588.renameProgram_congr_on _ _ _ (fun q hq => (fixOn q hq).symm))
  let t := pullState wire b
  let u := pullState φ r
  have wordIn : oddCutWord (if d then k else k+1)=P1Life.oddWord :=
    oddCutWord_odd (by split <;> omega) (by split <;> omega)
  have wordOut : oddCutWord (if d then k+1 else k)=P1Life.oddWord :=
    oddCutWord_odd (by split <;> omega) (by split <;> omega)
  rw [wordIn] at fr
  have idealEq : run (RouteA.Rolling1588.rawPacket d k) m t=run (oddPk d k) m' t := by
    have rawStep := RouteA.Rolling1588.rawPacket_cut_frame d k (by omega) (by omega) origin ctx enabled X Y t m fr
    cases d
    · have oddStep := pk_frame_mul k (by omega) hi origin ctx enabled X Y t m'
        (by simpa only [Bool.false_eq_true,if_false,oddCutWord_odd (c := k+1) (by omega) (by omega)] using fr)
      simp only [Bool.false_eq_true,if_false,Bool.not_false] at rawStep wordOut
      rw [wordOut] at oddStep
      exact State.extensionality _ _ (rawStep.1.trans oddStep.1.symm)
        (cutFrame_basis_unique _ _ _ _ _ _ _ rawStep.2 oddStep.2)
    · have oddStep := pk_frame_div k (by omega) hi origin ctx enabled X Y t m'
        (by simpa only [if_true,oddCutWord_odd (c := k) (by omega) (by omega)] using fr)
      simp only [if_true,Bool.not_true] at rawStep wordOut
      rw [wordOut] at oddStep
      exact State.extensionality _ _ (rawStep.1.trans oddStep.1.symm)
        (cutFrame_basis_unique _ _ _ _ _ _ _ rawStep.2 oddStep.2)
  have rawSub : wires (RouteA.Rolling1588.rawPacket d k)⊆insert (base 760) (wires (oddPk d k)) := by
    rw [WindowFieldCosts.oddPk_regular d k (by omega) hi]
    exact RouteA.Rolling1588.rawPacket_wires d k (by omega)
  have agree : ∀ q∈insert (base 760) (wires (oddPk d k)), u.basis q=t.basis q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with e|member
    · subst e
      have a : u.basis (base 760)=r.basis (base 720) := by
        change r.basis (rawSwap (wire (base 760)))=_
        rw [wire_760,rawSwap,Equiv.swap_apply_left]
      rw [a,zero]
      exact (cutFrame_760 _ _ _ ctx _ _ _ fr).symm
    · have hw : wire q∈wires (opk d k) := by
        rw [ot_opk_map,renameProgram_support]; exact Finset.mem_image_of_mem _ member
      change r.basis (φ q)=b.basis (wire q)
      rw [fixOn q member]
      exact match_ _ (opk_surface d k (by omega) hi hw) (fun e => no720 (e ▸ hw))
  have lifted := lift_on _ _ _ rawSub (Finset.subset_insert _ _) m m' u t agree idealEq
  apply pull_injective_of_surjective φ φsurj
  rw [gpk_map d k,run_rename φ φinj,opkφ,run_rename φ φinj]
  exact lifted


end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run wires measurementCount StairArchiveInactive.packet WindowFieldCosts.opk

/-- A body leg of fully decoded packets runs exactly as the regular leg from a reference cut. -/
theorem rgroup_run_eq (d : Bool) (j n : Nat) (lo : 10≤j) (hi : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m m' : List Bool) (initial : OCut (if d then j else j+n) origin r) :
    run (rgroup d j n) m r=run (ogroup d j n) m' r := by
  unfold rgroup ogroup
  induction n generalizing j r m m' with
  | zero => simp only [PacketSequence.program,run]
  | succ n ih =>
    cases d with
    | true =>
      simp only [if_true] at initial
      simp only [PacketSequence.program,if_true,run_append]
      have first := rpk_run_eq true j lo (by omega) origin ctx enabled r
        (m.take (measurementCount (rpk true j))) (m'.take (measurementCount (opk true j)))
        (by simpa only [if_true] using initial)
      rw [first]
      have next := ostep true j (by omega) (by omega) origin ctx enabled r
        (m'.take (measurementCount (opk true j))) (by simpa only [if_true] using initial)
      exact ih (j+1) (by omega) (by omega) _ _ _
        (by simpa only [if_true] using next)
    | false =>
      simp only [Bool.false_eq_true,if_false] at initial
      simp only [PacketSequence.program,Bool.false_eq_true,if_false,run_append]
      have start : OCut (if false then j+1 else j+1+n) origin r := by
        simpa only [Bool.false_eq_true,if_false,Nat.add_assoc,Nat.add_comm 1 n] using initial
      have rest := ih (j+1) (by omega) (by omega) r
        (m.take (measurementCount (PacketSequence.program false (rpk false) (j+1) n)))
        (m'.take (measurementCount (PacketSequence.program false (opk false) (j+1) n))) start
      rw [rest]
      have mid := oselected false (j+1) n (by omega) (by omega) origin ctx enabled r
        (m'.take (measurementCount (PacketSequence.program false (opk false) (j+1) n))) start
      exact rpk_run_eq false j lo (by omega) origin ctx enabled _ _ _
        (by simpa only [ogroup,Bool.false_eq_true,if_false] using mid)

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 1600
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run group ten measurementCount packet surface ArchiveStockRows.Chronology
  Rolling1588.CutFrame StairArchiveNativeCut.canonical WindowFieldCosts.opk

theorem osee (j c x row : Nat) (hj : j∈bankIds) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (r : State) (state : OCut c origin r) : frame j row (boundaryCols j c) r := by
  obtain ⟨zero,X,Y,model,fr,view⟩ := state
  have list : j∈WindowBankCheck.banks := by simpa [WindowBankCheck.banks,bankIds] using hj
  apply oobserved (oddCutWord c) j c x row list rb origin ctx tr history X Y model r fr zero
  intro q inside_ off
  exact view q (by rw [surface];exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,inside_⟩)) off

/-- oddten: dadon's `pair_cuts` for the field group's own packets. -/
theorem opair_cuts (d : Bool) (j x row : Nat) (hj : j∈bankIds) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (r : State) (m : List Bool) (state : OCut (if d then j else j+2) origin r) :
    (frame j row (StairArchiveNativeCut.canonical d d) r ∧ frame j row middle (orefMiddle j (!d) m r) ∧
      frame j row (StairArchiveNativeCut.canonical (!d) (!d)) (orefExit j (!d) m r)) ∧
    OCut (if d then j+2 else j) origin (orefExit j (!d) m r) := by
  have bounds : 1≤j ∧ j+1≤84 := by simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at hj; omega
  let observe := fun c t (h : OCut c origin t) => osee j c x row hj rb origin ctx tr history t h
  have lo : boundaryCols j j=StairArchiveNativeCut.canonical true true := by simp [boundaryCols]
  have mid : boundaryCols j (j+1)=middle := by simp [boundaryCols,middle]
  have hi : boundaryCols j (j+2)=StairArchiveNativeCut.canonical false false := by simp [boundaryCols]
  cases d
  · have one : OCut (j+1) origin (orefMiddle j true m r) :=
      ostep false (j+1) (by omega) (by omega) origin ctx en r _ state
    have two : OCut j origin (orefExit j true m r) :=
      ostep false j (by omega) (by omega) origin ctx en _ _ one
    exact ⟨⟨hi ▸ observe _ _ state,mid ▸ observe _ _ one,lo ▸ observe _ _ two⟩,two⟩
  · have one : OCut (j+1) origin (orefMiddle j false m r) :=
      ostep true j (by omega) (by omega) origin ctx en r _ state
    have two : OCut (j+2) origin (orefExit j false m r) :=
      ostep true (j+1) (by omega) (by omega) origin ctx en _ _ one
    exact ⟨⟨lo ▸ observe _ _ state,mid ▸ observe _ _ one,hi ▸ observe _ _ two⟩,two⟩

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open CodecBitSliceVerify WindowFieldMask WindowFieldCosts ArchiveFieldScratch
attribute [local irreducible] run measurementCount WindowFieldCosts.ogroup WindowFieldCosts.oten orefExit
  inputCols outputCols StairArchiveNativeCut.canonical enter leave WindowFieldCosts.opk
set_option linter.constructorNameAsVariable false

def oemitted (d : Bool) : Leg → Program
  | .native j n => rgroup d j n
  | .paired j => oten j (!d)
def ostock (d : Bool) (m : List Bool) (r : State) : Leg → State
  | .native j n => run (ogroup d j n) m r
  | .paired j => orefExit j (!d) m r
def onextTape (d : Bool) (l : Leg) (m : List Bool) := m.drop (measurementCount (oemitted d l))
def oconcatenate (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => oemitted d l ++ oconcatenate d ls
def odestination (d : Bool) : List Leg → List Bool → State → State
  | [],_,r => r
  | l::ls,m,r => odestination d ls (onextTape d l m) (ostock d m r l)
def OCuts (d : Bool) (row : Nat→Nat) (m : List Bool) (r : State) : Leg → Prop
  | .native j n => 10≤j → run (rgroup d j n) m r=run (ogroup d j n) m r
  | .paired j => frame j (row j) (StairArchiveNativeCut.canonical d d) r ∧
      frame j (row j) middle (orefMiddle j (!d) m r) ∧ frame j (row j) (StairArchiveNativeCut.canonical (!d) (!d)) (orefExit j (!d) m r)
def ONativeTrail (d : Bool) (row : Nat→Nat) : List Leg → List Bool → State → Prop
  | [],_,_ => True
  | l::ls,m,r => OCuts d row m r l ∧ ONativeTrail d row ls (onextTape d l m) (ostock d m r l)

theorem otravel (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (ls : List Leg) (m : List Bool) (a r : State) (c : Nat→Cols)
    (shape : valid d ls c) (cuts : ONativeTrail d row ls m r) (initial : Fits row c a r) :
    Fits row (finalCode d ls c) (run (oconcatenate d ls) m a) (odestination d ls m r) := by
  induction ls generalizing c m a r with
  | nil =>
    simpa only [oconcatenate,run,finalCode,odestination] using initial
  | cons l ls ih =>
    obtain ⟨loc,tail⟩ := shape
    obtain ⟨here,rest⟩ := cuts
    have one : Fits row (codes d c l) (run (oemitted d l) m a) (ostock d m r l) := by
      cases l with
      | native j n =>
        by_cases big : 10≤j
        · have p := plain (rgroup d j n) row c m a r initial (ot_rgroupSafe d j n loc)
          have same : run (rgroup d j n) m r=run (ogroup d j n) m r := here big
          rw [same] at p
          exact p
        · have low : j=1 ∧ n=9 := by
            have v : nativeRanges j n := loc
            unfold nativeRanges at v
            omega
          obtain ⟨rfl,rfl⟩ := low
          have p := plain (ogroup d 1 9) row c m a r initial (ot_groupSafe d 1 9 (Or.inl ⟨rfl,rfl⟩))
          change Fits row c (run (rgroup d 1 9) m a) (run (ogroup d 1 9) m r)
          rw [rgroup_low]
          exact p
      | paired j =>
        exact ot_stepTen j loc.1 row c (!d) (bounded j loc.1) m a r initial loc.2
          (by simpa only [Bool.not_not] using here.1) here.2.1 here.2.2
    rw [oconcatenate,run_append,run_take]
    exact ih _ _ _ _ tail rest one

theorem oemits_raw (d : Bool) : group84Raw d=oconcatenate d (plan d) := by
  cases d <;> simp only [group84Raw,group84Body,ordered,oconcatenate,oemitted,plan,if_true,if_false,Bool.false_eq_true,
    List.append_assoc,List.append_nil,rgroup_low]

/-- The 44-leg body plan (`plan d` without the `.native 1 9` leg). -/
def planBody (d : Bool) : List Leg :=
  if d then (plan true).tail else (plan false).dropLast

theorem plan_split_true : plan true = Leg.native 1 9 :: planBody true := rfl
theorem plan_split_false : plan false = planBody false ++ [Leg.native 1 9] := rfl

theorem oemits_body (d : Bool) : group84Body d = oconcatenate d (planBody d) := by
  cases d <;> simp only [group84Body,ordered,oconcatenate,oemitted,planBody,plan,if_true,if_false,Bool.false_eq_true,
    List.tail_cons,List.dropLast,List.append_assoc,List.append_nil]

theorem ogroup_run (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (m : List Bool) (a r : State) (initial : Fits row (initialCode d) a r)
    (native : ONativeTrail d row (plan d) m r) :
    Fits row (finalCode d (plan d) (initialCode d)) (run (group84Raw d) m a) (odestination d (plan d) m r) := by
  rw [oemits_raw]
  exact otravel d row bounded _ m a r _ (valid_plan d) native initial

end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open WindowFieldMask WindowFieldCosts ArchiveFieldScratch StairArchiveInactive
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run measurementCount StairArchiveInactive.packet fieldHook WindowFieldCosts.opk
set_option maxRecDepth 8000
set_option maxHeartbeats 900000

def oreferenceLeg (d : Bool) : Leg → Program
  | .native j n => ogroup d j n
  | .paired j => ofirst j (!d) ++ osecond j (!d)
def olegTape (d : Bool) (m : List Bool) : Leg → List Bool
  | .native _ _ => m
  | .paired j => joinTapes (ofirst j (!d)) (tapeA j (!d) m) (otapeB j (!d) m)
theorem olocalTape (d : Bool) (m : List Bool) (s : State) (l : Leg) :
    ostock d m s l = run (oreferenceLeg d l) (olegTape d m l) s := by
  cases l with
  | native j n => rfl
  | paired j => exact (joined _ _ _ _ _).symm
def oreferenceProgram (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => oreferenceLeg d l ++ oreferenceProgram d ls
def oreferenceTape (d : Bool) : List Leg → List Bool → List Bool
  | [],_ => []
  | l::ls,m => joinTapes (oreferenceLeg d l) (olegTape d m l) (oreferenceTape d ls (onextTape d l m))
theorem oref_run (d : Bool) (ls : List Leg) (m : List Bool) (r : State) :
    odestination d ls m r = run (oreferenceProgram d ls) (oreferenceTape d ls m) r := by
  induction ls generalizing m r with
  | nil => simp only [odestination,oreferenceProgram,oreferenceTape,run]
  | cons l ls ih => rw [odestination,oreferenceProgram,oreferenceTape,joined,←olocalTape,←ih]

theorem oreference_eq (d : Bool) : oreferenceProgram d (plan d)=PacketSequence.program d (opk d) 1 84 := by
  rw [shape' d (opk d)]
  cases d <;> simp only [oreferenceProgram,plan,oreferenceLeg,ofirst,osecond,ogroup,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false]

/-- Reference tape for the 1542-qubit `group84 d` (strips the 51+51 measurement bits of `packTag`/`unpackTag`). -/
def oreferenceTape1542 (d : Bool) (m : List Bool) : List Bool :=
  if d then
    let m19 := m.take (measurementCount (ogroup true 1 9))
    let mTail := m.drop (measurementCount (ogroup true 1 9))
    let mBody := (mTail.drop (measurementCount packTag)).take (measurementCount (group84Body true))
    joinTapes (ogroup true 1 9) m19 (oreferenceTape true (planBody true) mBody)
  else
    let mBody := (m.drop (measurementCount packTag)).take (measurementCount (group84Body false))
    let m19 := m.drop (measurementCount (packTag ++ renameProgram tagSwap (group84Body false) ++ unpackTag))
    joinTapes (oreferenceProgram false (planBody false)) (oreferenceTape false (planBody false) mBody) m19

end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 1600
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run group ten measurementCount packet surface ArchiveStockRows.Chronology
  Rolling1588.CutFrame StairArchiveNativeCut.canonical WindowFieldCosts.opk

/-- oddten: dadon's `trail` for the field group's own packets. -/
theorem otrail (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (c : Nat) (ls : List Leg) (m : List Bool) (r : State) (route : path d c ls) (start : OCut c origin r) :
    ONativeTrail d rows ls m r := by
  induction ls generalizing c m r with
  | nil => trivial
  | cons l ls ih =>
    obtain ⟨rfl,good,more⟩ := route
    cases l with
    | native j n =>
      have post := oselected d j n good.1 good.2 origin ctx en r m start
      exact ⟨fun big => rgroup_run_eq d j n big good.2 origin ctx en r m m start,ih _ _ _ more post⟩
    | paired j =>
      have event := opair_cuts d j x (rows j) good (rb _ good) origin ctx en tr (history _ good) r m start
      exact ⟨event.1,ih _ _ _ more event.2⟩

/-- two runs that agree from `b` agree from any `a` that matches `b` on the larger footprint. -/
theorem ot_lift (P Q : Program) (sub : wires P⊆wires Q) (m n : List Bool) (a b : State)
    (agree : ∀ q∈wires Q, a.basis q=b.basis q) (same : run P m b=run Q n b) :
    run P m a=run Q n a := by
  have hp := Arithmetic.run_local_increment P a b m (fun q hq => agree q (sub hq))
  have hq := Arithmetic.run_local_increment Q a b n agree
  apply State.extensionality
  · have e1 := hp.1
    rw [same] at e1
    have e := e1.trans hq.1.symm
    revert e
    generalize (run P m a).phase = x
    generalize (run Q n a).phase = y
    generalize a.phase = z
    cases x <;> cases y <;> cases z <;> decide
  · funext q
    by_cases inQ : q∈wires Q
    · rw [hq.2 q inQ]
      by_cases inP : q∈wires P
      · rw [hp.2 q inP,same]
      · rw [run_preserves_outside P m a q inP,agree q inQ,←run_preserves_outside P m b q inP,same]
    · have inP : q∉wires P := fun h => inQ (sub h)
      rw [run_preserves_outside P m a q inP,run_preserves_outside Q n a q inQ]

set_option linter.unusedSimpArgs false in
theorem ot_seqWires (d : Bool) (p : Nat→Program) (j n : Nat) {q : Wire}
    (h : q∈wires (PacketSequence.program d p j n)) : ∃ k, j≤k ∧ k<j+n ∧ q∈wires (p k) := by
  induction n generalizing j with
  | zero => simp [PacketSequence.program,wires] at h
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at h
    · rcases h with h|h
      · obtain ⟨k,l,u,hk⟩ := ih (j+1) h
        exact ⟨k,by omega,by omega,hk⟩
      · exact ⟨j,Nat.le_refl j,by omega,h⟩
    · rcases h with h|h
      · exact ⟨j,Nat.le_refl j,by omega,h⟩
      · obtain ⟨k,l,u,hk⟩ := ih (j+1) h
        exact ⟨k,by omega,by omega,hk⟩

theorem ot_groupUses (d : Bool) {q : Wire} (h : q∈wires (group d 1 84)) : q∈surface ∧ q≠base 720 := by
  rw [WindowFieldCosts.group,WindowFieldCosts.distribute,WindowFieldCosts.distributed] at h
  obtain ⟨k,l,u,hk⟩ := ot_seqWires d _ 1 84 h
  exact packetUses d k (by omega) (by omega) hk

theorem ot_group_map (d : Bool) (j n : Nat) : group d j n=renameProgram wire (Rolling1588.groups d j n) := by
  rw [WindowFieldCosts.ot_group_eq,StairArchiveInactive.hosts_eq,renameProgram_comp]
  have g := StairGroups.groups_zero d j n
  unfold StairGroups.groups at g
  rw [g]
  unfold wire
  rfl

theorem ot_ogroup_map (d : Bool) (j n : Nat) :
    PacketSequence.program d (opk d) j n=renameProgram wire (PacketSequence.program d (oddPk d) j n) := by
  have ren (f : Wire → Wire) (a b : Program) : renameProgram f (a++b)=renameProgram f a++renameProgram f b :=
    List.map_append
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,ren,ih,ot_opk_map]

theorem ofield_sub (d : Bool) :
    wires (PacketSequence.program d (oddPk d) 1 84) ⊆ wires (Rolling1588.groups d 1 84) :=
  StairLoanGroupSupport.sequence_sub d _ _ (fun k => oddPk_sub d k) 1 84

-- `ofinal` retired: `othree_run` directly relates `group84 d` to `PacketSequence.program d (opk d) 1 84` on `OCut`.

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end
-- oddten:end SEM

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Archive-coupled field-group runner directly between odd-word `OCut` endpoints (cuts 1 and 85). -/
theorem othree_run_raw (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (start : OCut (if d then 1 else 85) origin r) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84Raw d) m a)
      (run (PacketSequence.program d (opk d) 1 84) (oreferenceTape d (plan d) m) r) := by
  have route : path d (if d then 1 else 85) (plan d) := by cases d <;> simp [path,plan,prev,next,span,feasible,bankIds]
  have all := ogroup_run d rows rb m a r initial (otrail d x rows rb origin ctx en tr history _ _ m r route start)
  rwa [oref_run,oreference_eq] at all

/-- TagPack1542 preconditions at the start of `group84`: `rest87A < 87` and `p0Sites ∈ used7`. -/
def TagReady (s : State) : Prop :=
  regValue rest87A s.basis < 87 ∧ regValue p0Sites s.basis ∈ TagPack1542.used7

private theorem tagSites_disjoint_allBanks : ∀ q ∈ tagSites, q ∉ allBanks := by
  intro q hq hb
  rw [allBanks, Finset.mem_biUnion] at hb
  obtain ⟨j, hj, hjb⟩ := hb
  rw [bank, Finset.mem_image] at hjb
  obtain ⟨i, hi, rfl⟩ := hjb
  have hchk : let ts := tagSites
      WindowBankCheck.banks.all (fun b =>
        (List.range 16).all (fun k => !ts.contains (StairArchiveRelease.fieldPort b k))) = true := by
    have hm : WindowBankCheck.banks.all (fun b => (List.range 16).all (fun k =>
        !(WindowBankCheck.maskOf tagSites).testBit (StairArchiveRelease.fieldPort b k))) = true := by
      decide +kernel
    simpa only [WindowBankCheck.maskOf_testBit] using hm
  have jm : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hchk j jm) i (List.mem_range.mpr (Finset.mem_range.mp hi))
  simp [hq] at h1

/-- The 14 field-side tag wires: their preimage is packet-independent, and it avoids every cover. -/
private theorem rest87A_p0_avoids_opk_chk :
    let fc := [base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base
    (rest87A ++ p0Sites).all (fun q =>
      let x := OB5.sig 511 (StairArchiveInactive.host.symm q)
      decide (16 ≤ x) && !decide (Placement5.workRegion (x - 16)) &&
      !decide (Placement5.holeRegion (x - 16)) &&
      (List.range' 10 75).all (fun k =>
        !fc.contains x &&
        (List.finRange 10).all (fun j => History5.historyMap base (5 * k) j != x))) = true := by
  decide +kernel

private theorem pkSites_avoids_fixedCover_chk :
    let fc := [base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base
    (List.range 9).all (fun k1 =>
      (List.finRange 8).all (fun p1 =>
        let x := History5.historyMap base (5 * (k1 + 1)) (NewHistory5.payloadPort p1)
        !fc.contains x)) = true := by
  have hm : (List.range 9).all (fun k1 =>
      (List.finRange 8).all (fun p1 =>
        !(WindowBankCheck.maskOf ([base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base)).testBit
          (History5.historyMap base (5 * (k1 + 1)) (NewHistory5.payloadPort p1)))) = true := by
    decide +kernel
  simpa only [WindowBankCheck.maskOf_testBit] using hm

private theorem pkSites_fixed_by_pi (k1 k : Nat) (hk1_lo : 1 ≤ k1) (hk1_hi : k1 ≤ 9)
    (hk : k < 102) (p1 : Fin 8) :
    (shifted (Placement5.pi k)).symm (History5.historyMap base (5 * k1) (NewHistory5.payloadPort p1)) =
    History5.historyMap base (5 * k1) (NewHistory5.payloadPort p1) := by
  apply (Equiv.symm_apply_eq (shifted (Placement5.pi k))).mpr
  change _ = shifted (Placement5.pi k) (base (History5.historyId (5 * k1) (NewHistory5.payloadPort p1)))
  rw [shifted_base, Placement5.pi_outside k _ hk]
  · rfl
  · unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      History5.historyId NewHistory5.payloadPort
    have hp := p1.isLt
    dsimp only
    by_cases hlt : p1.val < 5
    · rw [if_pos hlt]; split <;> omega
    · rw [if_neg hlt]; split <;> omega

private theorem pkSites_avoids_hist (k1 k : Nat) (hk1_lo : 1 ≤ k1) (hk1_hi : k1 ≤ 9)
    (hk_lo : 10 ≤ k) (hk_hi : k ≤ 84) (p1 : Fin 8) (j : Fin 10) :
    History5.historyMap base (5 * k) j ≠ History5.historyMap base (5 * k1) (NewHistory5.payloadPort p1) := by
  intro heq
  have h1 : History5.historyId (5 * k) j = History5.historyId (5 * k1) (NewHistory5.payloadPort p1) :=
    base_injective heq
  unfold History5.historyId NewHistory5.payloadPort at h1
  have hp := p1.isLt
  have hj := j.isLt
  dsimp only at h1
  by_cases hlt : p1.val < 5
  · rw [if_pos hlt] at h1; split at h1 <;> split at h1 <;> omega
  · rw [if_neg hlt] at h1; split at h1 <;> split at h1 <;> omega

private theorem bridge7_payload_in_wires : ∀ p : Fin 8, (NewHistory5.payloadPort p).val ∈ wires Rolling1588.bridge7 := by
  decide +kernel

private theorem tagPort_anc_wire_chk :
    (List.range' 86 19).all (fun i => tagPort i == wire (base (Placement5.H (8 + (i - 86))))) = true := by
  decide +kernel

private theorem tagPort_anc_port_chk :
    (List.range' 86 19).all (fun i => tagPort i == StairArchiveRelease.fieldPort 10 (17 + (i - 86))) = true := by
  decide +kernel

private theorem tagPort_anc_ne720_chk :
    (List.range' 86 19).all (fun i => tagPort i != base 720) = true := by
  decide +kernel

private theorem fieldPort_ne720_chk :
    WindowBankCheck.banks.all (fun b =>
      (List.range 16).all (fun k => StairArchiveRelease.fieldPort b k != base 720)) = true := by
  decide +kernel

attribute [local irreducible] ECDSAAdd.wires WindowFieldCosts.opk WindowFieldCosts.rpk surface oddCutWord

private theorem tagData_avoids_opk (d : Bool) (i : Nat) (hi : i < 86) (k : Nat) (hk1 : 10 ≤ k) (hk2 : k ≤ 84) :
    tagPort i ∉ wires (opk d k) := by
  intro hw
  have yes := StairArchiveInactive.original d k (by omega) (WindowFieldCosts.ot_opk_sub d k hw)
  have hi' : i < tagSites.length := by rw [tagSites_length]; omega
  have hlen14 : (rest87A ++ p0Sites).length = 14 := by decide
  have hlen72 : pkSites.length = 72 := by decide
  have hlen86 : ((rest87A ++ p0Sites) ++ pkSites).length = 86 := by rw [List.length_append, hlen14, hlen72]
  by_cases h14 : i < 14
  · have hmem : tagPort i ∈ rest87A ++ p0Sites := by
      have heq : tagPort i = (rest87A ++ p0Sites)[i]'(by omega) := by
        rw [tagPort, List.getElem?_eq_getElem hi', Option.getD_some]
        simp only [tagSites,
          List.getElem_append_left (by omega : i < ((rest87A ++ p0Sites) ++ pkSites).length),
          List.getElem_append_left (by omega : i < (rest87A ++ p0Sites).length)]
      rw [heq]; exact List.getElem_mem _
    have h0 := List.all_eq_true.mp rest87A_p0_avoids_opk_chk (tagPort i) hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at h0
    obtain ⟨⟨⟨h16, hw⟩, hh⟩, h1⟩ := h0
    rw [WindowSites.preimage_const k (by omega) _ h16 hw hh] at yes
    have h2 := List.all_eq_true.mp h1 k (List.mem_range'_1.mpr ⟨hk1, by omega⟩)
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, bne_iff_ne] at h2
    rw [StairArchiveInactive.cover, List.mem_append] at yes
    rcases yes with hfc | hhist
    · have hc := List.contains_iff_mem.mpr hfc
      rw [hc] at h2
      exact Bool.noConfusion h2.1
    · obtain ⟨j, hj_mem, hj⟩ := List.mem_map.mp hhist
      exact h2.2 j hj_mem hj
  · have hmem : tagPort i ∈ pkSites := by
      have heq : tagPort i = pkSites[i - 14]'(by omega) := by
        rw [tagPort, List.getElem?_eq_getElem hi', Option.getD_some]
        simp only [tagSites,
          List.getElem_append_left (by omega : i < ((rest87A ++ p0Sites) ++ pkSites).length),
          List.getElem_append_right (by omega : (rest87A ++ p0Sites).length ≤ i), hlen14]
      rw [heq]; exact List.getElem_mem _
    simp only [pkSites, List.mem_flatMap, List.mem_range'_1, pkSitesOf, List.mem_map,
      List.mem_finRange, true_and] at hmem
    obtain ⟨k1', ⟨hk1_lo, hk1_hi⟩, p1, heq⟩ := hmem
    rw [← heq] at yes
    simp only [StairArchiveInactive.preimage, Equiv.symm_apply_apply, OB5.sig_invol 511 (by decide)] at yes
    have hfix := pkSites_fixed_by_pi k1' k hk1_lo (by omega) (by omega) p1
    rw [hfix, StairArchiveInactive.cover, List.mem_append] at yes
    rcases yes with hfc | hhist
    · have h1 := List.all_eq_true.mp (List.all_eq_true.mp pkSites_avoids_fixedCover_chk
        (k1' - 1) (List.mem_range.mpr (by omega))) p1 (List.mem_finRange p1)
      have hk1_eq : k1' - 1 + 1 = k1' := by omega
      rw [hk1_eq] at h1
      dsimp only at h1
      have hmem_c : ([base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base).contains
          (History5.historyMap base (5 * k1') (NewHistory5.payloadPort p1)) = true :=
        List.contains_iff_mem.mpr hfc
      rw [hmem_c] at h1
      exact Bool.noConfusion h1
    · obtain ⟨j, _, hj⟩ := List.mem_map.mp hhist
      exact pkSites_avoids_hist k1' k hk1_lo (by omega) hk1 hk2 p1 j hj

/-- Membership through two bit masks (built once) instead of 2662 list scans. -/
private theorem tagData_avoids_hook_chk :
    WindowBankCheck.banks.all (fun b =>
      (StairArchiveRelease.fieldSites b).all (fun w =>
        !(rest87A ++ p0Sites).contains w && !pkSites.contains w)) = true := by
  have hm : WindowBankCheck.banks.all (fun b =>
      (StairArchiveRelease.fieldSites b).all (fun w =>
        !(WindowBankCheck.maskOf (rest87A ++ p0Sites)).testBit w &&
        !(WindowBankCheck.maskOf pkSites).testBit w)) = true := by
    decide +kernel
  simpa only [WindowBankCheck.maskOf_testBit] using hm

private theorem tagPort_mem_take86 (i : Nat) (hi : i < 86) :
    tagPort i ∈ rest87A ++ p0Sites ∨ tagPort i ∈ pkSites := by
  have hi' : i < tagSites.length := by rw [tagSites_length]; omega
  have hlen14 : (rest87A ++ p0Sites).length = 14 := by decide
  have hlen72 : pkSites.length = 72 := by decide
  have hlen86 : ((rest87A ++ p0Sites) ++ pkSites).length = 86 := by rw [List.length_append, hlen14, hlen72]
  by_cases h14 : i < 14
  · left
    have heq : tagPort i = (rest87A ++ p0Sites)[i]'(by omega) := by
      rw [tagPort, List.getElem?_eq_getElem hi', Option.getD_some]
      simp only [tagSites,
        List.getElem_append_left (by omega : i < ((rest87A ++ p0Sites) ++ pkSites).length),
        List.getElem_append_left (by omega : i < (rest87A ++ p0Sites).length)]
    rw [heq]; exact List.getElem_mem _
  · right
    have heq : tagPort i = pkSites[i - 14]'(by omega) := by
      rw [tagPort, List.getElem?_eq_getElem hi', Option.getD_some]
      simp only [tagSites,
        List.getElem_append_left (by omega : i < ((rest87A ++ p0Sites) ++ pkSites).length),
        List.getElem_append_right (by omega : (rest87A ++ p0Sites).length ≤ i), hlen14]
    rw [heq]; exact List.getElem_mem _

private theorem tagData_avoids_group84Body (d : Bool) (i : Nat) (hi : i < 86) :
    tagPort i ∉ wires (group84Body d) := by
  have hpk : ∀ k, 10 ≤ k → k ≤ 84 → tagPort i ∉ wires (opk d k) :=
    fun k hk1 hk2 => tagData_avoids_opk d i hi k hk1 hk2
  have hhk : ∀ j ∈ WindowBankCheck.banks, ∀ op, tagPort i ∉ wires (StairArchiveRelease.fieldHook j op) := by
    intro j hj op hw
    have hspan : j ∈ List.range' 1 83 := by
      simp only [WindowBankCheck.banks, List.mem_cons, List.not_mem_nil, or_false] at hj
      apply List.mem_range'_1.mpr; omega
    rw [StairArchiveRelease.fieldHook, renameProgram_support] at hw
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hw
    have len : (StairArchiveRelease.fieldSites j).length = 121 := by
      have hh := (ArchiveFieldScratch.layout_frame j hspan).2
      rwa [← StairArchiveRelease.field_layout, List.length_map] at hh
    have lt : x < (StairArchiveRelease.fieldSites j).length :=
      len ▸ (Finset.mem_range.mp (StairArchiveRelease.sub op hx))
    have hmem : StairArchiveRelease.fieldPort j x ∈ StairArchiveRelease.fieldSites j := by
      simp only [StairArchiveRelease.fieldPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
    rw [hxeq] at hmem
    have h1 := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp tagData_avoids_hook_chk j hj) (tagPort i) hmem)
    rcases tagPort_mem_take86 i hi with hm | hm
    · simp [hm] at h1
    · simp [hm] at h1
  have hot : ∀ j ∈ WindowBankCheck.banks, tagPort i ∉ wires (oten j (!d)) := by
    intro j hj hw
    have jb : 10 ≤ j ∧ j ≤ 82 := by
      simp only [WindowBankCheck.banks, List.mem_cons, List.not_mem_nil, or_false] at hj; omega
    simp only [oten, wires_append, Finset.mem_union] at hw
    rcases hw with h | h | h | h | h
    · exact hhk j hj _ h
    · cases d <;> simp only [ofirst, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h
      · exact hpk (j + 1) (by omega) (by omega) h
      · exact hpk j (by omega) (by omega) h
    · exact hhk j hj _ h
    · cases d <;> simp only [osecond, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h
      · exact hpk j (by omega) (by omega) h
      · exact hpk (j + 1) (by omega) (by omega) h
    · exact hhk j hj _ h
  have hog : ∀ j n, 10 ≤ j → j + n ≤ 85 → tagPort i ∉ wires (ogroup d j n) := by
    intro j n hlo hhi
    unfold ogroup
    induction n generalizing j with
    | zero => intro h; simp [PacketSequence.program, wires] at h
    | succ n ih =>
      intro h
      cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
        wires_append, Finset.mem_union] at h
      · rcases h with h1 | h2
        · exact ih (j + 1) (by omega) (by omega) h1
        · exact hpk j hlo (by omega) h2
      · rcases h with h1 | h2
        · exact hpk j hlo (by omega) h1
        · exact ih (j + 1) (by omega) (by omega) h2
  have hord : ∀ {a b : Program}, tagPort i ∉ wires a → tagPort i ∉ wires b → tagPort i ∉ wires (ordered d a b) := by
    intro a b ha hb
    cases d <;> simp only [ordered, if_true, if_false, Bool.false_eq_true, wires_append, Finset.mem_union]
    · exact fun h => h.elim hb ha
    · exact fun h => h.elim ha hb
  have hne : tagPort i ≠ base 720 := by
    have lt : i < tagSites.length := by rw [tagSites_length]; omega
    have hmem : tagPort i ∈ tagSites := by
      simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
    exact fun h => (by decide +kernel : base 720 ∉ tagSites) (h ▸ hmem)
  have hrg : ∀ j n, 10 ≤ j → j + n ≤ 85 → tagPort i ∉ wires (rgroup d j n) :=
    fun j n hlo hhi => rgroup_avoids d (tagPort i) j n hne (hog j n hlo hhi)
  have hrpk : ∀ k, 10 ≤ k → k ≤ 84 → tagPort i ∉ wires (rpk d k) :=
    fun k hk1 hk2 h => (Finset.mem_insert.mp (rpk_sub d k h)).elim hne (hpk k hk1 hk2)
  unfold group84Body
  repeat (first | apply hord | exact hot _ (by decide) | exact hrg _ _ (by decide) (by decide) | exact hrpk _ (by decide) (by decide))

private theorem tagData_avoids_group84Body_ref (d : Bool) (i : Nat) (hi : i < 86) :
    tagPort i ∉ wires (oreferenceProgram d (planBody d)) := by
  have hpk : ∀ k, 10 ≤ k → k ≤ 84 → tagPort i ∉ wires (opk d k) :=
    fun k hk1 hk2 => tagData_avoids_opk d i hi k hk1 hk2
  have hog : ∀ j n, 10 ≤ j → j + n ≤ 85 → tagPort i ∉ wires (ogroup d j n) := by
    intro j n hlo hhi
    unfold ogroup
    induction n generalizing j with
    | zero => intro h; simp [PacketSequence.program, wires] at h
    | succ n ih =>
      intro h
      cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
        wires_append, Finset.mem_union] at h
      · rcases h with h1 | h2
        · exact ih (j + 1) (by omega) (by omega) h1
        · exact hpk j hlo (by omega) h2
      · rcases h with h1 | h2
        · exact hpk j hlo (by omega) h1
        · exact ih (j + 1) (by omega) (by omega) h2
  have hleg : ∀ l ∈ planBody d, tagPort i ∉ wires (oreferenceLeg d l) := by
    intro l hl
    have hchk_b : (planBody d).all (fun leg => match leg with
        | .native j n => decide (10 ≤ j ∧ j + n ≤ 85)
        | .paired j => decide (10 ≤ j ∧ j ≤ 82)) = true := by
      cases d <;> decide +kernel
    have hb := List.all_eq_true.mp hchk_b l hl
    cases l with
    | native j n =>
      simp only [decide_eq_true_eq] at hb
      exact hog j n hb.1 hb.2
    | paired j =>
      simp only [decide_eq_true_eq] at hb
      simp only [oreferenceLeg, wires_append, Finset.mem_union]
      intro hw
      rcases hw with h | h
      · cases d <;> simp only [ofirst, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h
        · exact hpk (j + 1) (by omega) (by omega) h
        · exact hpk j (by omega) (by omega) h
      · cases d <;> simp only [osecond, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h
        · exact hpk j (by omega) (by omega) h
        · exact hpk (j + 1) (by omega) (by omega) h
  have hgo : ∀ ls : List Leg, (∀ l ∈ ls, tagPort i ∉ wires (oreferenceLeg d l)) →
      tagPort i ∉ wires (oreferenceProgram d ls) := by
    intro ls hls
    induction ls with
    | nil => intro h; simp [oreferenceProgram, wires] at h
    | cons l ls ih =>
      intro h
      simp only [oreferenceProgram, wires_append, Finset.mem_union] at h
      exact h.elim (hls l List.mem_cons_self) (ih (fun l' hl' => hls l' (List.mem_cons_of_mem _ hl')))
  exact hgo (planBody d) hleg

private theorem ogroup19_avoids_rest87A_p0 (d : Bool) (q : Wire) (hq : q ∈ rest87A ++ p0Sites) :
    q ∉ wires (ogroup d 1 9) := by
  have hchk : (rest87A ++ p0Sites).all (fun w =>
      (List.range' 1 9).all (fun k => !(StairArchiveInactive.cover k).contains (StairArchiveInactive.preimage k w))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hchk q hq
  have hpk : ∀ k, 1 ≤ k → k ≤ 9 → q ∉ wires (opk d k) := by
    intro k hk1 hk2 hw
    have h2 := List.all_eq_true.mp h1 k (List.mem_range'_1.mpr ⟨hk1, by omega⟩)
    have yes := StairArchiveInactive.original d k (by omega) (WindowFieldCosts.ot_opk_sub d k hw)
    simp [yes] at h2
  unfold ogroup
  have hgo : ∀ j n, 1 ≤ j → j + n ≤ 10 → q ∉ wires (PacketSequence.program d (opk d) j n) := by
    intro j n hlo hhi
    induction n generalizing j with
    | zero => intro h; simp [PacketSequence.program, wires] at h
    | succ n ih =>
      intro h
      cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
        wires_append, Finset.mem_union] at h
      · rcases h with h1 | h2
        · exact ih (j + 1) (by omega) (by omega) h1
        · exact hpk j hlo (by omega) h2
      · rcases h with h1 | h2
        · exact hpk j hlo (by omega) h1
        · exact ih (j + 1) (by omega) (by omega) h2
  exact hgo 1 9 (by decide) (by decide)

private theorem parityEncode_used8_and_safe_chk :
    (List.range 1024).all (fun x =>
      !MeasuredCodec5.legalNat x ||
      (MeasuredCodec5.safe (Rolling1588.codeEncode false) x &&
        let y := MeasuredCodec5.bitRun (Rolling1588.codeEncode false) x
        let v := (([0, 1, 2, 3, 4, 6, 7, 8] : List Nat).zipIdx).foldl
          (fun acc p => if y.testBit p.1 then acc + 2 ^ p.2 else acc) 0
        TagPack1542.used8.contains v)) = true := by
  decide +kernel

private theorem parityEncode_in_used8 :
    ∀ x < 1024, MeasuredCodec5.legalNat x = true →
      let y := MeasuredCodec5.bitRun (Rolling1588.codeEncode false) x
      let v := (([0, 1, 2, 3, 4, 6, 7, 8] : List Nat).zipIdx).foldl
        (fun acc p => if y.testBit p.1 then acc + 2 ^ p.2 else acc) 0
      TagPack1542.used8.contains v = true := by
  intro x hx hleg
  have h := List.all_eq_true.mp parityEncode_used8_and_safe_chk x (List.mem_range.mpr hx)
  simp only [hleg, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.2

private theorem codeEncode_false_safe :
    ∀ x < 1024, MeasuredCodec5.legalNat x = true →
      MeasuredCodec5.safe (Rolling1588.codeEncode false) x = true := by
  intro x hx hleg
  have h := List.all_eq_true.mp parityEncode_used8_and_safe_chk x (List.mem_range.mpr hx)
  simp only [hleg, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.1

private theorem codeEncode_false_wires_lt :
    wires (Rolling1588.codeEncode false) ⊆ Finset.range 10 := by
  decide +kernel

set_option maxRecDepth 8000 in
private theorem ocut_pk_in_used8 (c : Nat) (hc : 10 ≤ c) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (r : State) (hcut : OCut c origin r) (k : Nat) (hk : k < 9) :
    regValue (pkSitesOf (k + 1)) r.basis ∈ TagPack1542.used8 := by
  obtain ⟨_, X, Y, ideal, cf, htr⟩ := hcut
  -- Every wire in `pkSitesOf (k + 1)` is in `surface` and `≠ base 720`, so `r.basis` agrees with `ideal.basis`.
  -- In `CutFrame c origin X Y (pullState wire ideal)` with `k + 1 < c`, packet `k + 1` is encoded by
  -- `ParityCodec5New.encode` on a `RawLegal` 10-bit word (`tr.2.2.2`), whose 8 payload bits lie in `used8`.
  have hmem_surf : ∀ i : Fin 8,
      wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i)) ∈ surface ∧
      wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i)) ≠ base 720 := by
    intro i
    have hchk : (List.range 9).all (fun k' =>
        (List.finRange 8).all (fun i' =>
          wire (History5.historyMap base (5 * (k' + 1)) (NewHistory5.payloadPort i')) != base 720)) = true := by
      decide +kernel
    have hne : wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i)) ≠ base 720 := by
      have h1 := List.all_eq_true.mp (List.all_eq_true.mp hchk k (List.mem_range.mpr hk)) i (List.mem_finRange i)
      simpa using h1
    refine ⟨?_, hne⟩
    -- Packet `k + 1` uses all 8 payload wires of `History5.historyMap base (5 * (k + 1))`
    -- via `Rolling1588.dp` inside `packet true (k + 1)`.
    rw [surface]
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_union_right _ ?_⟩
    rw [packet_original, renameProgram_support]
    refine Finset.mem_image.mpr ⟨OB5.sig 511 (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i)), ?_, rfl⟩
    rw [renameProgram_support]
    refine Finset.mem_image.mpr ⟨History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i), ?_, rfl⟩
    have hbase : History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i) ∈
        wires (Rolling1588.onPacket (k + 1) Rolling1588.bridge7) := by
      rw [Rolling1588.onPacket, renameProgram_support]
      exact Finset.mem_image.mpr ⟨(NewHistory5.payloadPort i).val, bridge7_payload_in_wires i, by simp [MeasuredCodec5.label]⟩
    rw [Rolling1588.packet, renameProgram_support]
    have hfix : shifted (Placement5.pi (k + 1)) (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i)) =
        History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i) := by
      have hchk2 : (List.range 9).all (fun k' =>
          (List.finRange 8).all (fun i' =>
            shifted (Placement5.pi (k' + 1)) (History5.historyMap base (5 * (k' + 1)) (NewHistory5.payloadPort i')) ==
              History5.historyMap base (5 * (k' + 1)) (NewHistory5.payloadPort i'))) = true := by
        decide +kernel
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp hchk2 k (List.mem_range.mpr hk)) i (List.mem_finRange i)
      simpa using h2
    refine Finset.mem_image.mpr ⟨History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i), ?_, hfix⟩
    simp only [Rolling1588.basePacket, if_true, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hbase))))))
  have hagree : ∀ q ∈ pkSitesOf (k + 1), r.basis q = ideal.basis q := by
    intro q hq
    simp only [pkSitesOf, List.mem_map, List.mem_finRange, true_and] at hq
    obtain ⟨i, rfl⟩ := hq
    exact htr _ (hmem_surf i).1 (hmem_surf i).2
  rw [Arithmetic.regValue_congr (pkSitesOf (k + 1)) r.basis ideal.basis hagree]
  -- Now evaluate `pkSitesOf (k + 1)` on `ideal` = `pullState wire ideal` at `History5.historyMap base (5*(k+1))`
  obtain ⟨raw, _, pair, eq⟩ := cf
  have hle : ¬ (c ≤ k + 1) := by omega
  have hbits : ∀ i : Fin 8,
      ideal.basis (wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i))) =
      (run (Rolling1588.codeEncode false) [] ⟨false, fun p =>
        if h : p < 10 then origin (History5.historyMap base (5 * (k + 1)) ⟨p, h⟩) else false⟩).basis
        (NewHistory5.payloadPort i).val := by
    intro i
    change (pullState wire ideal).basis (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i)) = _
    rw [eq, Rolling1588.allEncodeCut_factor base c base_pool_nodup 102 (k + 1) (by decide) (by omega) raw,
        run_preserves_outside _ _ _ _ (StairField2V3LastRecXPar.other_away base c (k + 1)
          base_pool_nodup 102 (by decide) (by omega) (NewHistory5.payloadPort i)),
        Rolling1588.encodeGroup, if_neg (by omega : k + 1 ≠ 0), Rolling1588.encodeAt,
        decide_eq_false hle, Rolling1588.codeEncodeAt]
    have hpool := run_rename_pool (MeasuredCodec5.label (History5.historyMap base (5 * (k + 1))))
      (Finset.range 10)
      (FirstNonzeroCodec.label_inj' _ (History5.historyMap_injective base base_pool_nodup _ (by omega)))
      (Rolling1588.codeEncode false) codeEncode_false_wires_lt []
      ⟨raw.phase, fun p => if h : p < 10 then origin (History5.historyMap base (5 * (k + 1)) ⟨p, h⟩) else false⟩
      raw rfl (fun p hp => by
        have hlt : p < 10 := Finset.mem_range.mp hp
        simp only [hlt, ↓reduceDIte, MeasuredCodec5.label]
        have haway := History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
          (5 * (k + 1)) (by omega) ⟨p, hlt⟩
        exact (pair.2.2 _ haway.1 haway.2).symm)
    have h2 := hpool.2 (NewHistory5.payloadPort i).val (Finset.mem_range.mpr (NewHistory5.payloadPort i).isLt)
    simp only [MeasuredCodec5.label, (NewHistory5.payloadPort i).isLt, ↓reduceDIte] at h2
    have hi_eq : (⟨(NewHistory5.payloadPort i).val, (NewHistory5.payloadPort i).isLt⟩ : Fin 10) = NewHistory5.payloadPort i := Fin.eta _ _
    rw [hi_eq] at h2
    rw [h2]
    exact congrFun (run_basis_records (Rolling1588.codeEncode false) _ _ [] [] rfl) _
  let x10 := regValue ((List.finRange 10).map (History5.historyMap base (5 * (k + 1)))) origin
  have hx10_lt : x10 < 1024 := by
    have hlt := Arithmetic.regValue_lt ((List.finRange 10).map (History5.historyMap base (5 * (k + 1)))) origin
    simpa [x10] using hlt
  have hx10_leg : MeasuredCodec5.legalNat x10 = true := by
    have hraw := tr.2.2.2 (k + 1) (by omega)
    rw [MeasuredCodec5.legalAt_iff] at hraw
    have hbit : ∀ j : Fin 10, x10.testBit j.val = origin (History5.historyMap base (5 * (k + 1)) j) := by
      intro j
      have hb := Arithmetic.regValue_bit ((List.finRange 10).map (History5.historyMap base (5 * (k + 1)))) j.val 0 origin (by simp)
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange] at hb
      change (origin (History5.historyMap base (5 * (k + 1)) j)).toNat = x10 / 2 ^ j.val % 2 at hb
      rw [Nat.testBit_eq_decide_div_mod_eq, ← hb]
      cases origin (History5.historyMap base (5 * (k + 1)) j) <;> simp
    have h0 := hraw ⟨0, by decide⟩; have h1 := hraw ⟨1, by decide⟩
    have h2 := hraw ⟨2, by decide⟩; have h3 := hraw ⟨3, by decide⟩
    have h4 := hraw ⟨4, by decide⟩
    dsimp only at h0 h1 h2 h3 h4
    simp only [MeasuredCodec5.legalNat, hbit ⟨0, by decide⟩, hbit ⟨1, by decide⟩,
      hbit ⟨2, by decide⟩, hbit ⟨3, by decide⟩, hbit ⟨4, by decide⟩, hbit ⟨5, by decide⟩,
      hbit ⟨6, by decide⟩, hbit ⟨7, by decide⟩, hbit ⟨8, by decide⟩, hbit ⟨9, by decide⟩]
    rw [h0, h1, h2, h3, h4]; rfl
  have hfin := parityEncode_in_used8 x10 hx10_lt hx10_leg
  have hsim := MeasuredCodec5.run_sim (Rolling1588.codeEncode false) [] false x10
  have hsafe : MeasuredCodec5.safe (Rolling1588.codeEncode false) x10 = true :=
    codeEncode_false_safe x10 hx10_lt hx10_leg
  rw [MeasuredCodec5.sim_safe _ _ hsafe] at hsim
  have hst_eq : (⟨false, fun p => if h : p < 10 then origin (History5.historyMap base (5 * (k + 1)) ⟨p, h⟩) else false⟩ : State) =
      ⟨false, MeasuredCodec5.bitsOf x10⟩ := by
    congr 1; funext p
    by_cases hp : p < 10
    · simp only [hp, ↓reduceDIte, MeasuredCodec5.bitsOf]
      have hb := Arithmetic.regValue_bit ((List.finRange 10).map (History5.historyMap base (5 * (k + 1)))) p 0 origin (by simp [hp])
      rw [List.getD_eq_getElem _ _ (by simp [hp]), List.getElem_map, List.getElem_finRange] at hb
      simp only [Fin.cast_mk] at hb
      rw [Nat.testBit_eq_decide_div_mod_eq, ← hb]
      cases hb_val : origin (History5.historyMap base (5 * (k + 1)) ⟨p, hp⟩) <;> simp
    · simp only [hp, ↓reduceDIte, MeasuredCodec5.bitsOf]
      have h10p : 10 ≤ p := by dsimp only [Wire] at hp ⊢; omega
      have hpow : 2 ^ 10 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide : 0 < 2) h10p
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx10_lt hpow)).symm
  have hval_eq : regValue (pkSitesOf (k + 1)) ideal.basis =
      (([0, 1, 2, 3, 4, 6, 7, 8] : List Nat).zipIdx).foldl
        (fun acc p => if (MeasuredCodec5.bitRun (Rolling1588.codeEncode false) x10).testBit p.1 then acc + 2 ^ p.2 else acc) 0 := by
    have hbit_i : ∀ i : Fin 8,
        ideal.basis (wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort i))) =
        (MeasuredCodec5.bitRun (Rolling1588.codeEncode false) x10).testBit (NewHistory5.payloadPort i).val := by
      intro i
      rw [hbits i, hst_eq, hsim]
      rfl
    have hlist : pkSitesOf (k + 1) =
        [ wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨0, by decide⟩))
        , wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨1, by decide⟩))
        , wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨2, by decide⟩))
        , wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨3, by decide⟩))
        , wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨4, by decide⟩))
        , wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨5, by decide⟩))
        , wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨6, by decide⟩))
        , wire (History5.historyMap base (5 * (k + 1)) (NewHistory5.payloadPort ⟨7, by decide⟩)) ] := rfl
    rw [hlist]
    simp only [regValue, List.foldr_cons, List.foldr_nil]
    rw [hbit_i ⟨0, by decide⟩, hbit_i ⟨1, by decide⟩, hbit_i ⟨2, by decide⟩, hbit_i ⟨3, by decide⟩,
        hbit_i ⟨4, by decide⟩, hbit_i ⟨5, by decide⟩, hbit_i ⟨6, by decide⟩, hbit_i ⟨7, by decide⟩]
    simp only [NewHistory5.payloadPort]
    have hfold : ∀ (idxs : List Nat) (f : Nat → Bool) (acc k : Nat),
        (idxs.zipIdx k).foldl (fun a p => if f p.1 = true then a + 2 ^ p.2 else a) acc =
        acc + 2 ^ k * List.foldr (fun idx a => (if f idx = true then 1 else 0) + 2 * a) 0 idxs := by
      intro idxs; induction idxs with
      | nil => intro f acc k; simp
      | cons idx idxs ih =>
        intro f acc k
        simp only [List.zipIdx_cons, List.foldl_cons, List.foldr_cons, ih]
        cases f idx <;> simp [Nat.pow_succ] <;> ring
    have h := hfold [0, 1, 2, 3, 4, 6, 7, 8] (MeasuredCodec5.bitRun (Rolling1588.codeEncode false) x10).testBit 0 0
    simpa [List.foldr_cons, List.foldr_nil] using h.symm
  rw [hval_eq]
  exact List.contains_iff_mem.mp hfin

private theorem mask_phase (S : Finset Wire) (r a : State) : (mask S r a).phase = a.phase := rfl
theorem pullState_phase (f : Wire → Wire) (a : State) : (pullState f a).phase = a.phase := rfl

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8000 in
private theorem ocut_anc_zero (c : Nat) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (r : State) (hcut : OCut c origin r) (a : Nat) (ha1 : 86 ≤ a) (ha2 : a < 105) :
    r.basis (tagPort a) = false := by
  obtain ⟨_, X, Y, ideal, cf, htr⟩ := hcut
  have hwire : tagPort a = wire (base (Placement5.H (8 + (a - 86)))) :=
    beq_iff_eq.mp (List.all_eq_true.mp tagPort_anc_wire_chk a (List.mem_range'_1.mpr ⟨ha1, by omega⟩))
  have hsurf : tagPort a ∈ surface ∧ tagPort a ≠ base 720 := by
    have h10 : 10 ∈ bankIds := by decide
    have hport : tagPort a = StairArchiveRelease.fieldPort 10 (17 + (a - 86)) :=
      beq_iff_eq.mp (List.all_eq_true.mp tagPort_anc_port_chk a (List.mem_range'_1.mpr ⟨ha1, by omega⟩))
    have hne : tagPort a ≠ base 720 := by
      simpa using List.all_eq_true.mp tagPort_anc_ne720_chk a (List.mem_range'_1.mpr ⟨ha1, by omega⟩)
    refine ⟨?_, hne⟩
    rw [surface]; apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨10, h10, Finset.mem_image.mpr ⟨17 + (a - 86), Finset.mem_range.mpr (by omega), hport.symm⟩⟩
  have hpull : ∀ (s : State) (q : Wire), s.basis (wire q) = (pullState wire s).basis q := fun _ _ => rfl
  rw [htr _ hsurf.1 hsurf.2, hwire, hpull]
  exact RouteA.Rolling1588.cutFrame_zero_region (oddCutWord c) (oddCutWord c) c origin ctx X Y
    (pullState wire ideal) cf
    (Placement5.H (8 + (a - 86))) (Or.inr (Placement5.H_region (8 + (a - 86)) (by omega)))

private theorem oreferenceProgram_cons (d : Bool) (l : Leg) (ls : List Leg) :
    oreferenceProgram d (l :: ls) = oreferenceLeg d l ++ oreferenceProgram d ls := rfl

private theorem oreferenceProgram_append (d : Bool) (l1 l2 : List Leg) :
    oreferenceProgram d (l1 ++ l2) = oreferenceProgram d l1 ++ oreferenceProgram d l2 := by
  induction l1 with
  | nil => rfl
  | cons x xs ih => rw [List.cons_append, oreferenceProgram_cons, oreferenceProgram_cons, ih, List.append_assoc]

private theorem finalCode_native_cons (d : Bool) (j n : Nat) (ls : List Leg) (c : Nat → CodecBitSliceVerify.Cols) :
    finalCode d (Leg.native j n :: ls) c = finalCode d ls c := rfl

private theorem href_eq_true :
    PacketSequence.program true (opk true) 1 84 =
      ogroup true 1 9 ++ oreferenceProgram true (planBody true) := by
  rw [← oreference_eq true, plan_split_true, oreferenceProgram_cons]
  rfl

private theorem href_eq_false :
    PacketSequence.program false (opk false) 1 84 =
      oreferenceProgram false (planBody false) ++ ogroup false 1 9 := by
  rw [← oreference_eq false, plan_split_false, oreferenceProgram_append, oreferenceProgram_cons]
  change oreferenceProgram false (planBody false) ++ (ogroup false 1 9 ++ []) = _
  rw [List.append_nil]

private theorem orefBody_false_eq :
    oreferenceProgram false (planBody false) = ogroup false 10 75 := by
  have hfull := href_eq_false
  have hsp : PacketSequence.program false (opk false) 1 84 = ogroup false 10 75 ++ ogroup false 1 9 := by
    have hgo : ∀ n j, PacketSequence.program false (opk false) j (n + 75) =
        PacketSequence.program false (opk false) (j + n) 75 ++ PacketSequence.program false (opk false) j n := by
      intro n; induction n with
      | zero => intro j; simp [PacketSequence.program]
      | succ n ih =>
        intro j
        rw [Nat.succ_add, PacketSequence.program, if_neg Bool.false_ne_true, ih (j + 1)]
        simp only [List.append_assoc, show j + 1 + n = j + (n + 1) by omega]
        simp only [PacketSequence.program, Bool.false_eq_true, if_false]
    simpa [ogroup] using hgo 9 1
  rw [hsp] at hfull
  exact (List.append_cancel_right hfull).symm

private theorem orefBody_true_eq :
    oreferenceProgram true (planBody true) = ogroup true 10 75 := by
  have hfull := href_eq_true
  have hsp : PacketSequence.program true (opk true) 1 84 = ogroup true 1 9 ++ ogroup true 10 75 := by
    have hgo : ∀ n j, PacketSequence.program true (opk true) j (n + 75) =
        PacketSequence.program true (opk true) j n ++ PacketSequence.program true (opk true) (j + n) 75 := by
      intro n; induction n with
      | zero => intro j; simp [PacketSequence.program]
      | succ n ih =>
        intro j
        rw [Nat.succ_add, PacketSequence.program, if_pos rfl, ih (j + 1)]
        simp only [show j + 1 + n = j + (n + 1) by omega]
        rw [← List.append_assoc]
        simp only [PacketSequence.program, if_true]
    simpa [ogroup] using hgo 9 1
  rw [hsp] at hfull
  exact (List.append_cancel_left hfull).symm

attribute [local irreducible] group84Body

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8000 in
/-- Core bracket lemma for `packTag ++ renameProgram tagSwap (group84Body d) ++ unpackTag`:
    runs `group84Body d` with `base 720` swapped to `sLetter 435` (`rest87A[6]`),
    preserving `Fits` and restoring all 105 `tagSites` identically! -/
theorem othree_body_bracket (d : Bool) (x : Nat) (rows : Nat → Nat) (rb : ∀ j ∈ bankIds, rows j < 63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a0 r0 : State) (c0 : Nat → CodecBitSliceVerify.Cols)
    (hvalid : valid d (planBody d) c0)
    (hroute : path d (if d then 10 else 85) (planBody d))
    (initial : Fits rows c0 a0 r0)
    (start : OCut (if d then 10 else 85) origin r0)
    (htag : TagReady r0) :
    let mBody := (m.drop (measurementCount packTag)).take (measurementCount (group84Body d))
    let r1 := run (oreferenceProgram d (planBody d)) (oreferenceTape d (planBody d) mBody) r0
    Fits rows (finalCode d (planBody d) c0)
      (run (packTag ++ renameProgram tagSwap (group84Body d) ++ unpackTag) m a0) r1 := by
  intro mBody r1
  let mPack := m.take (measurementCount packTag)
  let mUnpack := (m.drop (measurementCount packTag)).drop (measurementCount (group84Body d))
  have hmc_body : measurementCount (renameProgram tagSwap (group84Body d)) = measurementCount (group84Body d) :=
    (renameProgram_counts _ _).2
  have hrun_split :
      run (packTag ++ renameProgram tagSwap (group84Body d) ++ unpackTag) m a0 =
      run unpackTag mUnpack (run (renameProgram tagSwap (group84Body d)) mBody (run packTag mPack a0)) := by
    rw [run_append, run_append, measurementCount_append, hmc_body]
    simp only [mPack, mBody, mUnpack, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _),
      List.drop_take, List.drop_drop]
    congr 1
    · congr 1
      have hlen_sub : measurementCount packTag + measurementCount (group84Body d) - measurementCount packTag =
          measurementCount (group84Body d) := Nat.add_sub_cancel_left _ _
      rw [hlen_sub]
  -- Lift `packTag_spec` and `unpackTag_packTag_roundtrip` to `a0` via `tagPort`!
  let s0 : State := ⟨a0.phase, fun q => a0.basis (tagPort q)⟩
  have hagree_a0_r0 : ∀ i < 105, a0.basis (tagPort i) = r0.basis (tagPort i) := by
    intro i hi
    have hmem : tagPort i ∈ tagSites := by
      have lt : i < tagSites.length := tagSites_length ▸ hi
      simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
    exact initial.outside _ (tagSites_disjoint_allBanks _ hmem)
  have hreg_map : ∀ (xs : List Nat) (ys : List Wire),
      xs.map tagPort = ys → (∀ i ∈ xs, i < 105) →
      regValue xs s0.basis = regValue ys r0.basis := by
    intro xs ys hmap hlt
    subst hmap
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, regValue, List.foldr_cons, s0]
      rw [hagree_a0_r0 x (hlt x List.mem_cons_self)]
      have htail := ih (fun i hi => hlt i (List.mem_cons_of_mem _ hi))
      simp only [regValue, s0] at htail
      rw [htail]
  have hc0 : TagPack1542.cVal s0 < 87 := by
    have heq : TagPack1542.cVal s0 = regValue rest87A r0.basis :=
      hreg_map TagPack1542.cWires rest87A (by decide +kernel) (by decide)
    rw [heq]; exact htag.1
  have hp0 : TagPack1542.p0Val s0 ∈ TagPack1542.used7 := by
    have heq : TagPack1542.p0Val s0 = regValue p0Sites r0.basis :=
      hreg_map TagPack1542.p0Wires p0Sites (by decide +kernel) (by decide)
    rw [heq]; exact htag.2
  have hpk0 : ∀ k < 9, TagPack1542.pkVal k s0 ∈ TagPack1542.used8 := by
    intro k hk
    have hmap_k : (TagPack1542.pkWires k).map tagPort = pkSitesOf (k + 1) := by
      have hchk : (List.range 9).all (fun k' =>
          (TagPack1542.pkWires k').map tagPort == pkSitesOf (k' + 1)) = true := by
        decide +kernel
      exact beq_iff_eq.mp (List.all_eq_true.mp hchk k (List.mem_range.mpr hk))
    have heq : TagPack1542.pkVal k s0 = regValue (pkSitesOf (k + 1)) r0.basis :=
      hreg_map (TagPack1542.pkWires k) (pkSitesOf (k + 1)) hmap_k (fun i hi => by
        simp only [TagPack1542.pkWires, TagPack1542.pkWire, List.mem_cons, List.not_mem_nil, or_false] at hi
        omega)
    rw [heq]
    exact ocut_pk_in_used8 (if d then 10 else 85) (by cases d <;> decide) origin ctx tr r0 start k hk
  have hanc0 : ∀ a, 86 ≤ a → a < 105 → s0.basis a = false := by
    intro a ha1 ha2
    exact (hagree_a0_r0 a (by omega)).trans (ocut_anc_zero _ origin ctx r0 start a ha1 ha2)
  -- Step 1: `a1 := run packTag mPack a0`
  let a1 := run packTag mPack a0
  have hp_pool := run_rename_pool tagPort (Finset.range 105) tagPort_inj TagPack1542.packTagProg
    (fun q hq => Finset.mem_range.mpr (TagPack1542.packTagProg_wires_lt q hq)) mPack s0 a0 rfl (fun _ _ => rfl)
  have hspec := TagPack1542.packTag_spec s0 mPack hc0 hp0 hpk0 hanc0
  have ha1_ph : a1.phase = a0.phase := hp_pool.1.trans hspec.1
  have ha1_435 : a1.basis (StairPhysicalLayout.sLetter 435) = false := by
    have h6 : tagPort 6 = StairPhysicalLayout.sLetter 435 := by decide +kernel
    rw [← h6]
    change (run (renameProgram tagPort TagPack1542.packTagProg) mPack a0).basis (tagPort 6) = false
    rw [hp_pool.2 6 (by decide)]
    exact hspec.2.1
  have ha1_anc : ∀ i, 86 ≤ i → i < 105 → a1.basis (tagPort i) = false := fun i hi1 hi2 =>
    (hp_pool.2 i (Finset.mem_range.mpr (by omega))).trans (hspec.2.2.1 i hi1 hi2)
  have ha1_out : ∀ w, w ∉ tagSites → a1.basis w = a0.basis w := fun w hw =>
    run_preserves_outside packTag mPack a0 w (fun hm => by
      rw [packTag, renameProgram_support] at hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      have lt : i < tagSites.length := tagSites_length ▸ TagPack1542.packTagProg_wires_lt i hi
      exact hw (by simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]))
  -- Step 2: `a2 := run (renameProgram tagSwap (group84Body d)) mBody a1`
  -- Run `group84Body d` on `a1m := mask tagDataSet r0 (pullState tagSwap a1)` against `r0`!
  let a1' := pullState tagSwap a1
  have h720_not_tag : base 720 ∉ tagSites := by decide +kernel
  let tagDataSet : Finset Wire := (tagSites.take 86).toFinset
  have hbody_avoids_tagData : avoids (group84Body d) tagDataSet := by
    intro q hq
    rw [List.mem_toFinset] at hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have hi86 : i < 86 := by have := List.length_take_le 86 tagSites; omega
    have hget : (tagSites.take 86)[i] = tagPort i := by
      have lt : i < tagSites.length := by rw [tagSites_length]; omega
      simp [tagPort, List.getElem_take, List.getElem?_eq_getElem lt]
    rw [hget]
    exact tagData_avoids_group84Body d i hi86
  let a1m := mask tagDataSet r0 a1'
  have hfits_m : Fits rows c0 a1m r0 := by
    refine ⟨ha1_ph.trans initial.phase, ?_, ?_⟩
    · intro q hq
      by_cases hqm : q ∈ tagDataSet
      · simp [a1m, mask, hqm]
      · simp only [a1m, mask, hqm, ↓reduceIte]
        change a1.basis (tagSwap q) = r0.basis q
        by_cases hq720 : q = base 720
        · subst hq720; simp [tagSwap, ha1_435, start.1]
        · have hq435 : q ≠ StairPhysicalLayout.sLetter 435 := by
            intro h; exact hqm (h ▸ (by decide +kernel : StairPhysicalLayout.sLetter 435 ∈ tagDataSet))
          rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hq720 hq435]
          by_cases hqt : q ∈ tagSites
          · -- `q ∈ tagSites` and `q ∉ tagSites.take 86`, so `q = tagPort i` with `86 ≤ i < 105` (ancilla)!
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hqt
            have hi105 : i < 105 := tagSites_length ▸ hi
            have hi86 : 86 ≤ i := by
              by_contra! hlt
              exact hqm (List.mem_toFinset.mpr (List.mem_iff_getElem.mpr ⟨i, by rw [List.length_take, tagSites_length]; omega, by simp [List.getElem_take]⟩))
            have hget : tagSites[i] = tagPort i := by simp [tagPort, List.getElem?_eq_getElem hi]
            rw [hget, ha1_anc i hi86 hi105, ocut_anc_zero _ origin ctx r0 start i hi86 hi105]
          · exact (ha1_out q hqt).trans (initial.outside q hq)
    · intro j hj i hi
      have hmem_b : StairArchiveRelease.fieldPort j i ∈ allBanks :=
        Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
      have hnt : StairArchiveRelease.fieldPort j i ∉ tagSites :=
        fun ht => tagSites_disjoint_allBanks _ ht hmem_b
      have hnm : StairArchiveRelease.fieldPort j i ∉ tagDataSet := fun hm =>
        hnt (List.take_subset 86 tagSites (List.mem_toFinset.mp hm))
      have hn720 : StairArchiveRelease.fieldPort j i ≠ base 720 := by
        have jm : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
        simpa using List.all_eq_true.mp (List.all_eq_true.mp fieldPort_ne720_chk j jm) i (List.mem_range.mpr (Finset.mem_range.mp hi))
      have hn435 : StairArchiveRelease.fieldPort j i ≠ StairPhysicalLayout.sLetter 435 :=
        fun h => hnt (h ▸ (by decide +kernel : StairPhysicalLayout.sLetter 435 ∈ tagSites))
      simp only [a1m, mask, hnm, ↓reduceIte]
      change a1.basis (tagSwap (StairArchiveRelease.fieldPort j i)) = _
      rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hn720 hn435, ha1_out _ hnt]
      exact initial.bytes j hj i hi
  have htrail := otrail d x rows rb origin ctx en tr history _ (planBody d) mBody r0 hroute start
  have htrav := otravel d rows rb (planBody d) mBody a1m r0 c0 hvalid htrail hfits_m
  rw [← oemits_body, oref_run] at htrav
  have hmask_eq : run (group84Body d) mBody a1m = mask tagDataSet r0 (run (group84Body d) mBody a1') :=
    mask_run (group84Body d) tagDataSet mBody r0 a1' hbody_avoids_tagData
  rw [hmask_eq] at htrav
  -- Now let `a2 := run (renameProgram tagSwap (group84Body d)) mBody a1 = pullState tagSwap (run (group84Body d) mBody a1')`!
  let a2' := run (group84Body d) mBody a1'
  let a2 := run (renameProgram tagSwap (group84Body d)) mBody a1
  have ha2_eq : a2 = pullState tagSwap a2' := by
    have hconj := StairField2V3Seg.rename_conj tagSwap tagSwap.injective (fun q => Equiv.swap_apply_self _ _ q)
      (group84Body d) a1 mBody
    exact hconj
  -- Check that `a2` agrees with `a1` on all 105 `tagSites`!
  have hr1_720 : r1.basis (base 720) = false := by
    have h720_av : base 720 ∉ wires (oreferenceProgram d (planBody d)) := by
      have hsub : wires (oreferenceProgram d (planBody d)) ⊆ wires (group d 1 84) := by
        intro q hq
        have h1 : wires (oreferenceProgram d (planBody d)) ⊆ wires (oreferenceProgram d (plan d)) := by
          cases d
          · rw [plan_split_false]
            have : ∀ l1 l2, wires (oreferenceProgram false (l1 ++ l2)) = wires (oreferenceProgram false l1) ∪ wires (oreferenceProgram false l2) := by
              intro l1 l2; induction l1 with | nil => simp [oreferenceProgram, wires] | cons x xs ih => simp [oreferenceProgram, wires_append, ih, Finset.union_assoc]
            rw [this]; exact Finset.subset_union_left
          · rw [plan_split_true]; simp [oreferenceProgram, wires_append]
        have h2 := h1 hq
        rw [oreference_eq] at h2
        exact ot_ogroup_sub d 1 84 h2
      exact fun hw => (ot_groupUses d (hsub hw)).2 rfl
    rw [run_preserves_outside _ _ _ _ h720_av]
    exact start.1
  have hr1_anc : ∀ i, 86 ≤ i → i < 105 → r1.basis (tagPort i) = false := by
    intro i hi1 hi2
    have hcut_end : OCut (if d then 85 else 10) origin r1 := by
      have hseq : oreferenceProgram d (planBody d) = ogroup d 10 75 := by
        cases d
        · exact orefBody_false_eq
        · exact orefBody_true_eq
      have hsel := oselected d 10 75 (by decide) (by decide) origin ctx en r0 (oreferenceTape d (planBody d) mBody)
        (by cases d <;> simpa using start)
      cases d <;> simpa [r1, hseq] using hsel
    exact ocut_anc_zero _ origin ctx r1 hcut_end i hi1 hi2
  have ha2_agree_a1 : ∀ i < 105, a2.basis (tagPort i) = a1.basis (tagPort i) := by
    intro i hi
    rw [ha2_eq]
    change a2'.basis (tagSwap (tagPort i)) = a1.basis (tagPort i)
    by_cases h6 : i = 6
    · subst h6
      have htp6 : tagPort 6 = StairPhysicalLayout.sLetter 435 := by decide +kernel
      rw [htp6, show tagSwap (StairPhysicalLayout.sLetter 435) = base 720 from Equiv.swap_apply_right _ _, ha1_435]
      have h720_not_b : base 720 ∉ allBanks := by
        intro hb
        rw [allBanks, Finset.mem_biUnion] at hb
        obtain ⟨j, hj, hjb⟩ := hb
        rw [bank, Finset.mem_image] at hjb
        obtain ⟨k, hk, heq⟩ := hjb
        have jm : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
        have h1 := List.all_eq_true.mp (List.all_eq_true.mp fieldPort_ne720_chk j jm) k (List.mem_range.mpr (Finset.mem_range.mp hk))
        rw [heq] at h1; simp at h1
      have h720_not_m : base 720 ∉ tagDataSet := fun hm =>
        h720_not_tag (List.take_subset 86 tagSites (List.mem_toFinset.mp hm))
      have hout := htrav.outside (base 720) h720_not_b
      simp only [mask, h720_not_m, ↓reduceIte] at hout
      exact hout.trans hr1_720
    · have hne435 : tagPort i ≠ StairPhysicalLayout.sLetter 435 := by
        intro h
        have htp6 : tagPort 6 = StairPhysicalLayout.sLetter 435 := by decide +kernel
        exact h6 (tagPort_inj i (Finset.mem_range.mpr hi) 6 (by decide) (h.trans htp6.symm))
      have hne720 : tagPort i ≠ base 720 := fun h => h720_not_tag (h ▸ by
        have lt : i < tagSites.length := tagSites_length ▸ hi
        simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem])
      rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hne720 hne435]
      by_cases hi86 : i < 86
      · rw [run_preserves_outside (group84Body d) mBody a1' (tagPort i) (tagData_avoids_group84Body d i hi86)]
        change a1.basis (tagSwap (tagPort i)) = a1.basis (tagPort i)
        rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hne720 hne435]
      · have hmem_t : tagPort i ∈ tagSites := by
          have lt : i < tagSites.length := tagSites_length ▸ hi
          simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
        have hnot_b : tagPort i ∉ allBanks := tagSites_disjoint_allBanks _ hmem_t
        have hnot_m : tagPort i ∉ tagDataSet := by
          intro hm
          obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hm)
          have hj86 : j < 86 := by have := List.length_take_le 86 tagSites; omega
          have hget : (tagSites.take 86)[j] = tagPort j := by
            have lt : j < tagSites.length := by rw [tagSites_length]; omega
            simp [tagPort, List.getElem_take, List.getElem?_eq_getElem lt]
          rw [hget] at hjeq
          have hij := tagPort_inj j (Finset.mem_range.mpr (by omega)) i (Finset.mem_range.mpr hi) hjeq
          omega
        have hout := htrav.outside (tagPort i) hnot_b
        simp only [mask, hnot_m, ↓reduceIte] at hout
        rw [hout, hr1_anc i (by omega) hi, ha1_anc i (by omega) hi]
  -- Step 3: `a3 := run unpackTag mUnpack a2` via `TagPack1542.unpackTag_packTag_roundtrip`!
  let u0 : State := ⟨a2.phase, fun q => a2.basis (tagPort q)⟩
  have hu_pool := run_rename_pool tagPort (Finset.range 105) tagPort_inj TagPack1542.unpackTagProg
    (fun q hq => Finset.mem_range.mpr (TagPack1542.unpackTagProg_wires_lt q hq)) mUnpack u0 a2 rfl (fun _ _ => rfl)
  have hrt := TagPack1542.unpackTag_packTag_roundtrip s0 u0 mPack mUnpack hc0 hp0 hpk0 hanc0
    (fun w hw => (ha2_agree_a1 w hw).trans (hp_pool.2 w (Finset.mem_range.mpr hw)))
  let a3 := run unpackTag mUnpack a2
  have ha3_out : ∀ w, w ∉ tagSites → a3.basis w = a2.basis w := fun w hw =>
    run_preserves_outside unpackTag mUnpack a2 w (fun hm => by
      rw [unpackTag, renameProgram_support] at hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      have lt : i < tagSites.length := tagSites_length ▸ TagPack1542.unpackTagProg_wires_lt i hi
      exact hw (by simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]))
  rw [hrun_split]
  refine ⟨?_, ?_, ?_⟩
  · -- Phase
    have ha2_ph : a2.phase = r1.phase := by
      have hp1 : a2.phase = a2'.phase := by rw [ha2_eq, pullState_phase]
      exact hp1.trans ((mask_phase tagDataSet r0 a2').symm.trans htrav.phase)
    exact (hu_pool.1.trans hrt.1).trans ha2_ph
  · -- Outside `allBanks`
    intro q hq
    by_cases hqt : q ∈ tagSites
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hqt
      have hi105 : i < 105 := tagSites_length ▸ hi
      have hget : tagSites[i] = tagPort i := by simp [tagPort, List.getElem?_eq_getElem hi]
      rw [hget]
      have hrest : a3.basis (tagPort i) = a0.basis (tagPort i) :=
        (hu_pool.2 i (Finset.mem_range.mpr hi105)).trans (hrt.2.1 i hi105)
      rw [hrest, hagree_a0_r0 i hi105]
      by_cases hi86 : i < 86
      · exact (run_preserves_outside _ _ _ _ (tagData_avoids_group84Body_ref d i hi86)).symm
      · rw [ocut_anc_zero _ origin ctx r0 start i (by omega) hi105, hr1_anc i (by omega) hi105]
    · rw [ha3_out q hqt, ha2_eq]
      change a2'.basis (tagSwap q) = r1.basis q
      by_cases hq720 : q = base 720
      · subst hq720
        rw [show tagSwap (base 720) = StairPhysicalLayout.sLetter 435 from Equiv.swap_apply_left _ _]
        have h435_av : StairPhysicalLayout.sLetter 435 ∉ wires (group84Body d) := by
          have h6 : tagPort 6 = StairPhysicalLayout.sLetter 435 := by decide +kernel
          rw [← h6]
          exact tagData_avoids_group84Body d 6 (by decide)
        rw [run_preserves_outside _ _ _ _ h435_av]
        change a1.basis (tagSwap (StairPhysicalLayout.sLetter 435)) = r1.basis (base 720)
        rw [show tagSwap (StairPhysicalLayout.sLetter 435) = base 720 from Equiv.swap_apply_right _ _,
            ha1_out _ h720_not_tag, initial.outside _ hq, start.1, hr1_720]
      · have hq435 : q ≠ StairPhysicalLayout.sLetter 435 := fun h =>
          hqt (h ▸ (by decide +kernel : StairPhysicalLayout.sLetter 435 ∈ tagSites))
        rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hq720 hq435]
        have hnm : q ∉ tagDataSet := fun hm => hqt (List.take_subset 86 tagSites (List.mem_toFinset.mp hm))
        have hout := htrav.outside q hq
        simpa [mask, hnm] using hout
  · -- Archive bytes on `allBanks`
    intro j hj i hi
    have hmem_b : StairArchiveRelease.fieldPort j i ∈ allBanks :=
      Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    have hnt : StairArchiveRelease.fieldPort j i ∉ tagSites :=
      fun ht => tagSites_disjoint_allBanks _ ht hmem_b
    have hnm : StairArchiveRelease.fieldPort j i ∉ tagDataSet := fun hm =>
      hnt (List.take_subset 86 tagSites (List.mem_toFinset.mp hm))
    have hn720 : StairArchiveRelease.fieldPort j i ≠ base 720 := by
      have hchk : WindowBankCheck.banks.all (fun b =>
          (List.range 16).all (fun k => StairArchiveRelease.fieldPort b k != base 720)) = true := by decide +kernel
      have jm : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
      simpa using List.all_eq_true.mp (List.all_eq_true.mp hchk j jm) i (List.mem_range.mpr (Finset.mem_range.mp hi))
    have hn435 : StairArchiveRelease.fieldPort j i ≠ StairPhysicalLayout.sLetter 435 :=
      fun h => hnt (h ▸ (by decide +kernel : StairPhysicalLayout.sLetter 435 ∈ tagSites))
    rw [ha3_out _ hnt, ha2_eq]
    change a2'.basis (tagSwap (StairArchiveRelease.fieldPort j i)) = _
    rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hn720 hn435]
    have hby := htrav.bytes j hj i hi
    simpa [mask, hnm] using hby

private theorem othree_true_glue (P1 P2 R1 R2 : Program) (c1 c2 : Nat → CodecBitSliceVerify.Cols)
    (rows : Nat → Nat) (m t2 : List Bool) (a r : State)
    (hc : c1 = c2)
    (h : Fits rows c1 (run P2 (m.drop (measurementCount P1)) (run P1 (m.take (measurementCount P1)) a))
           (run R2 t2 (run R1 (m.take (measurementCount P1)) r))) :
    Fits rows c2 (run (P1 ++ P2) m a) (run (R1 ++ R2) (joinTapes R1 (m.take (measurementCount P1)) t2) r) := by
  subst hc; rw [run_append, joined]; exact h

private theorem othree_false_glue (P1 P2 R1 R2 : Program) (c1 c2 : Nat → CodecBitSliceVerify.Cols)
    (rows : Nat → Nat) (m t1 t1' : List Bool) (a r : State)
    (hc : c1 = c2) (ht : t1 = t1')
    (h : Fits rows c1 (run P2 (m.drop (measurementCount P1)) (run P1 (m.take (measurementCount P1)) a))
           (run R2 (m.drop (measurementCount P1)) (run R1 t1 r))) :
    Fits rows c2 (run (P1 ++ P2) m a) (run (R1 ++ R2) (joinTapes R1 t1' (m.drop (measurementCount P1))) r) := by
  subst hc; subst ht; rw [run_append, joined]; exact h

private theorem drop_take_take_eq (a b c : Nat) (m : List Bool) :
    ((m.take (a + b + c)).drop a).take b = (m.drop a).take b := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

private theorem route_plan_true : path true 1 (plan true) := by
  simp [path, plan, prev, next, span, feasible, bankIds]

private theorem route_plan_false : path false 85 (plan false) := by
  simp [path, plan, prev, next, span, feasible, bankIds]

private theorem group84_true_eq :
    group84 true = ogroup true 1 9 ++ (packTag ++ renameProgram tagSwap (group84Body true) ++ unpackTag) := rfl

private theorem group84_false_eq :
    group84 false = (packTag ++ renameProgram tagSwap (group84Body false) ++ unpackTag) ++ ogroup false 1 9 := rfl

private theorem oreferenceTape1542_true_eq (m : List Bool) :
    oreferenceTape1542 true m =
      joinTapes (ogroup true 1 9) (m.take (measurementCount (ogroup true 1 9)))
        (oreferenceTape true (planBody true)
          (((m.drop (measurementCount (ogroup true 1 9))).drop (measurementCount packTag)).take (measurementCount (group84Body true)))) := rfl

private theorem oreferenceTape1542_false_eq (m : List Bool) :
    oreferenceTape1542 false m =
      joinTapes (oreferenceProgram false (planBody false))
        (oreferenceTape false (planBody false) ((m.drop (measurementCount packTag)).take (measurementCount (group84Body false))))
        (m.drop (measurementCount (packTag ++ renameProgram tagSwap (group84Body false) ++ unpackTag))) := rfl

private theorem hfin_eq_false :
    finalCode false (plan false) (initialCode false) =
      finalCode false (planBody false) (initialCode false) := by
  rw [plan_split_false]
  have hfc : ∀ ls c, finalCode false (ls ++ [Leg.native 1 9]) c = finalCode false ls c := by
    intro ls; induction ls with | nil => intro c; rfl | cons l ls ih => intro c; exact ih _
  exact hfc _ _

private theorem valid_plan_false_split :
    valid false (planBody false) (initialCode false) ∧ nativeRanges 1 9 := by
  have hv : ∀ ls c, valid false (ls ++ [Leg.native 1 9]) c → valid false ls c ∧ nativeRanges 1 9 := by
    intro ls
    induction ls with
    | nil => intro c h; exact ⟨trivial, h.1⟩
    | cons l ls ih => intro c h; obtain ⟨h1, h2⟩ := ih _ h.2; exact ⟨⟨h.1, h1⟩, h2⟩
  have h := valid_plan false
  rw [plan_split_false] at h
  exact hv _ _ h

private theorem route_plan_false_body : path false 85 (planBody false) := by
  have hp : ∀ ls c, path false c (ls ++ [Leg.native 1 9]) → path false c ls := by
    intro ls
    induction ls with
    | nil => intros; trivial
    | cons l ls ih => intro c h; exact ⟨h.1, h.2.1, ih _ h.2.2⟩
  have h := route_plan_false
  rw [plan_split_false] at h
  exact hp _ _ h

private theorem tagReady_run_outside (P : Program) (m : List Bool) (s : State)
    (h : ∀ q ∈ rest87A ++ p0Sites, q ∉ wires P) (ht : TagReady s) :
    TagReady (run P m s) := by
  constructor
  · rw [Arithmetic.regValue_congr rest87A _ s.basis (fun q hq =>
      run_preserves_outside P m s q (h q (List.mem_append_left _ hq)))]
    exact ht.1
  · rw [Arithmetic.regValue_congr p0Sites _ s.basis (fun q hq =>
      run_preserves_outside P m s q (h q (List.mem_append_right _ hq)))]
    exact ht.2

attribute [local irreducible] ogroup oreferenceProgram oreferenceTape planBody packTag unpackTag tagSwap

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem othree_run_true (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode true) a r)
    (start : OCut 1 origin r)
    (htag : TagReady r) :
    Fits rows (finalCode true (plan true) (initialCode true)) (run (group84 true) m a)
      (run (PacketSequence.program true (opk true) 1 84) (oreferenceTape1542 true m) r) := by
  have hvalid_all := valid_plan true
  have hroute_all := route_plan_true
  rw [plan_split_true] at hvalid_all hroute_all ⊢
  obtain ⟨hloc19, hval_body⟩ := hvalid_all
  obtain ⟨_, _, hroute_body⟩ := hroute_all
  let m19 := m.take (measurementCount (ogroup true 1 9))
  let mTail := m.drop (measurementCount (ogroup true 1 9))
  have h19_fits : Fits rows (initialCode true) (run (ogroup true 1 9) m19 a) (run (ogroup true 1 9) m19 r) :=
    plain (ogroup true 1 9) rows (initialCode true) m19 a r initial (ot_groupSafe true 1 9 hloc19)
  have h19_cut : OCut 10 origin (run (ogroup true 1 9) m19 r) := by
    have hs := oselected true 1 9 (by decide) (by decide) origin ctx en r m19 start
    simpa only [if_true] using hs
  have h19_tag : TagReady (run (ogroup true 1 9) m19 r) :=
    tagReady_run_outside _ m19 r (ogroup19_avoids_rest87A_p0 true) htag
  have hbody := othree_body_bracket true x rows rb origin ctx en tr history mTail
    (run (ogroup true 1 9) m19 a) (run (ogroup true 1 9) m19 r) (initialCode true)
    hval_body hroute_body h19_fits h19_cut h19_tag
  rw [group84_true_eq, href_eq_true, oreferenceTape1542_true_eq]
  exact othree_true_glue _ _ _ _ _ _ rows m _ a r
    (finalCode_native_cons true 1 9 (planBody true) (initialCode true)).symm hbody

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem othree_run_false (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode false) a r)
    (start : OCut 85 origin r)
    (htag : TagReady r) :
    Fits rows (finalCode false (plan false) (initialCode false)) (run (group84 false) m a)
      (run (PacketSequence.program false (opk false) 1 84) (oreferenceTape1542 false m) r) := by
  let P1 := packTag ++ renameProgram tagSwap (group84Body false) ++ unpackTag
  let mPre := m.take (measurementCount P1)
  let m19 := m.drop (measurementCount P1)
  have hbody := othree_body_bracket false x rows rb origin ctx en tr history mPre a r (initialCode false)
    valid_plan_false_split.1 route_plan_false_body initial start htag
  have h19 := plain (ogroup false 1 9) rows (finalCode false (planBody false) (initialCode false)) m19 _ _ hbody
    (ot_groupSafe false 1 9 valid_plan_false_split.2)
  have hmBody_eq : (mPre.drop (measurementCount packTag)).take (measurementCount (group84Body false)) =
      (m.drop (measurementCount packTag)).take (measurementCount (group84Body false)) := by
    have hmc : measurementCount P1 =
        measurementCount packTag + measurementCount (group84Body false) + measurementCount unpackTag := by
      simp only [P1, measurementCount_append, (renameProgram_counts _ _).2]
    dsimp only [mPre]
    rw [hmc]
    exact drop_take_take_eq _ _ _ m
  rw [group84_false_eq, href_eq_false, oreferenceTape1542_false_eq]
  exact othree_false_glue P1 _ _ _ _ _ rows m _ _ a r hfin_eq_false.symm
    (congrArg (oreferenceTape false (planBody false)) hmBody_eq) h19

/-- Archive-coupled field-group runner directly between odd-word `OCut` endpoints (cuts 1 and 85),
    for the 1542-qubit `group84 d` bracketed by `TagPack1542.{packTag, unpackTag}`. -/
theorem othree_run (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (start : OCut (if d then 1 else 85) origin r)
    (htag : TagReady r) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84 d) m a)
      (run (PacketSequence.program d (opk d) 1 84) (oreferenceTape1542 d m) r) := by
  cases d with
  | true => exact othree_run_true x rows rb origin ctx en tr history m a r initial start htag
  | false => exact othree_run_false x rows rb origin ctx en tr history m a r initial start htag
end ECDSAAdd.Entrant.StairPacket.WindowFieldView


namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView

open Arithmetic Secp256k1 MappedCompressed WindowFieldCosts StairArchiveInactive
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires run opk rpk

def SignReady (s : State) : Prop :=
  s.basis signHost =
    (TraceParity5.parity (signPayload.map s.basis) ^^ prefixParityValue (regValue p0Sites s.basis))

/-- The relocated raw packet has the ordinary packet's full result on an archive
    stage when the relocated sign site is clear and the ordinary support agrees
    with an ordinary cut. The two tapes are independent. -/
theorem spk_run_eq (d : Bool) (k : Nat) (lo : 10 ≤ k) (hi : k ≤ 84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (r a : State) (m n : List Bool)
    (initial : OCut (if d then k else k + 1) origin r)
    (clean : a.basis signHost = false)
    (agree : ∀ q ∈ wires (opk d k), a.basis q = r.basis q) :
    run (spk d k) m a = run (opk d k) n a := by
  let f := Equiv.swap (base 720) signHost
  let b := pullState f r
  have fix : ∀ q ∈ wires (opk d k), f q = q := by
    intro q used
    exact Equiv.swap_apply_of_ne_of_ne
      (fun he => opk_avoid720 d k (by omega) hi (he ▸ used))
      (fun he => opk_avoids_sign d k (by omega) hi (he ▸ used))
  have renameOld : renameProgram f (opk d k) = opk d k := by
    rw [RouteA.Rolling1588.renameProgram_congr_on f id _ (fun q hq => fix q hq)]
    exact StairField2V3Win.renameProgram_id' _
  have symm : pullState f b = r :=
    StairReplay.pullState_involutive f (fun q => Equiv.swap_apply_self _ _ q) r
  have lift (P : Program) (t : List Bool) :
      run (renameProgram f P) t b = pullState f (run P t r) := by
    rw [StairField2V3Seg.rename_conj f f.injective (fun q => Equiv.swap_apply_self _ _ q), symm]
  have eqb : run (spk d k) m b = run (opk d k) n b := by
    change run (renameProgram f (rpk d k)) m b = run (opk d k) n b
    rw [lift, rpk_run_eq d k lo hi origin ctx enabled r m n initial, ← lift, renameOld]
  have agree' : ∀ q ∈ insert signHost (wires (opk d k)), a.basis q = b.basis q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with h | h
    · subst q
      change a.basis signHost = r.basis (f signHost)
      rw [show f signHost = base 720 from Equiv.swap_apply_right _ _, clean, initial.1]
    · change a.basis q = r.basis (f q)
      rw [fix q h]
      exact agree q h
  exact lift_on _ _ _ (spk_sub d k (by omega) hi) (Finset.subset_insert _ _) m n a b agree' eqb

theorem spk_returns_zero (d : Bool) (k : Nat) (lo : 10 ≤ k) (hi : k ≤ 84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (r a : State) (m n : List Bool)
    (initial : OCut (if d then k else k + 1) origin r)
    (clean : a.basis signHost = false)
    (agree : ∀ q ∈ wires (opk d k), a.basis q = r.basis q) :
    (run (spk d k) m a).basis signHost = false := by
  rw [spk_run_eq d k lo hi origin ctx enabled r a m n initial clean agree,
    run_preserves_outside _ _ _ _ (opk_avoids_sign d k (by omega) hi), clean]

section
attribute [local irreducible] gpk

/-- The relocated fully decoded packet has the ordinary packet's result when the sign site is
    clear and the ordinary support agrees with a reference cut. The two tapes are independent. -/
theorem epk_run_eq (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (r a : State) (m n : List Bool)
    (initial : OCut (if d then k else k + 1) origin r)
    (clean : a.basis signHost = false)
    (agree : ∀ q ∈ wires (opk d k), a.basis q = r.basis q) :
    run (epk d k) m a = run (opk d k) n a := by
  let f := Equiv.swap (base 720) signHost
  let b := pullState f r
  have fix : ∀ q ∈ wires (opk d k), f q = q := by
    intro q used
    exact Equiv.swap_apply_of_ne_of_ne
      (fun he => opk_avoid720 d k lo hi (he ▸ used))
      (fun he => opk_avoids_sign d k lo hi (he ▸ used))
  have renameOld : renameProgram f (opk d k) = opk d k := by
    rw [RouteA.Rolling1588.renameProgram_congr_on f id _ (fun q hq => fix q hq)]
    exact StairField2V3Win.renameProgram_id' _
  have symm : pullState f b = r :=
    StairReplay.pullState_involutive f (fun q => Equiv.swap_apply_self _ _ q) r
  have lift (P : Program) (t : List Bool) :
      run (renameProgram f P) t b = pullState f (run P t r) := by
    rw [StairField2V3Seg.rename_conj f f.injective (fun q => Equiv.swap_apply_self _ _ q), symm]
  have eqb : run (epk d k) m b = run (opk d k) n b := by
    change run (renameProgram f (gpk d k)) m b = run (opk d k) n b
    rw [lift, gpk_run_eq d k lo hi origin ctx enabled r m n initial, ← lift, renameOld]
  have agree' : ∀ q ∈ insert signHost (wires (opk d k)), a.basis q = b.basis q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with h | h
    · subst q
      change a.basis signHost = r.basis (f signHost)
      rw [show f signHost = base 720 from Equiv.swap_apply_right _ _, clean, initial.1]
    · change a.basis q = r.basis (f q)
      rw [fix q h]
      exact agree q h
  exact lift_on _ _ _ (epk_sub d k lo hi) (Finset.subset_insert _ _) m n a b agree' eqb

end

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

namespace ECDSAAdd.Entrant.StairArchiveNativeCut

open Arithmetic CodecBitSliceVerify StairArchiveRelease StairArchiveInactive StairArchiveNativeRows StairArchiveSlots
open StairPacket StairPacket.WindowFieldCosts StairPacket.WindowFieldView
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
attribute [local irreducible] wires run opk fieldHook CodecBitSliceVerify.get savedSites

/-- The packet footprint sees the reference history at the output of either
    archive hook. The held byte and tag lie outside that footprint. -/
theorem spk_after_hook (j : Nat) (hs : j ∈ StairPacket.Shadow20.MixedFieldBanks.mixedBankList)
    (hj : j ∈ List.range' 1 83) (hb : j ∈ WindowBankCheck.banks) (lo : 10 ≤ j)
    (rev last : Bool) (row : Nat) (hr : row < 63145) (m n n' : List Bool)
    (a shadow r : State) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true)
    (change : frame j row (inputCols (fromStage rev last)) a)
    (out : exterior j a shadow) (entryFrame : frame j row (before rev last) shadow)
    (refCut : OCut (if !rev then (if rev ^^ last then j + 1 else j)
      else (if rev ^^ last then j + 1 else j) + 1) origin r)
    (match_ : ∀ q ∈ wires (opk (!rev) (if rev ^^ last then j + 1 else j)),
      shadow.basis q = r.basis q)
    (clean : a.basis signHost = false) :
    let c := run (fieldHook j (fromStage rev last)) m a
    let k := if rev ^^ last then j + 1 else j
    run (spk (!rev) k) n c = run (opk (!rev) k) n' c := by
  let active := rev ^^ last
  let k := if active then j + 1 else j
  let c := run (fieldHook j (fromStage rev last)) m a
  have admin := StairArchiveAllPorts.field_run j hj _ row hr m a change
  have checks := all_checks rev last
  change (agrees active false (outputCols (fromStage rev last)) (before rev last) &&
    agrees active false (inputCols (toStage rev last)) (after rev last) &&
    agrees active true (outputCols (fromStage rev last)) (inputCols (toStage rev last))) = true at checks
  simp only [Bool.and_eq_true] at checks
  have same : ∀ z ∈ wires (opk (!rev) k), c.basis z = r.basis z := by
    intro z used
    have off : z ∉ savedSites j active := fun held => ot_packet_avoids j hs (!rev) active z held used
    apply Eq.trans _ (match_ z used)
    by_cases hz : z ∈ inside j
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hh : q ∉ held active := fun h => off ((held_at j hj active q hq).mpr h)
      exact (admin.2.1 q hq).trans ((congrArg (fun v : Nat => v.testBit row)
        (column _ _ _ _ checks.1.1 q hq (decide_eq_false hh))).trans (entryFrame q hq).symm)
    · exact (admin.2.2 z hz).trans (out z hz)
  have z : c.basis signHost = false :=
    (run_preserves_outside _ _ _ _ (hook_avoids_sign j hb (fromStage rev last))).trans clean
  have hi := List.mem_range'_1.mp hj
  exact spk_run_eq _ k (by dsimp [k]; split <;> omega) (by dsimp [k]; split <;> omega)
    origin ctx enabled r c n n' refCut z same

end ECDSAAdd.Entrant.StairArchiveNativeCut


namespace ECDSAAdd.Entrant.CheckpointSignLoan

open ECDSAAdd

def xorBits : List Bool → Bool
  | [] => false
  | b :: bs => b ^^ xorBits bs

def into (target : Wire) (sources : List Wire) : Program :=
  sources.map fun q => .CX q target

def flip (q : Wire) (b : Bool) (s : State) : State :=
  ⟨s.phase, writeBit s.basis q (s.basis q ^^ b)⟩

private theorem flip_at (q : Wire) (b : Bool) (s : State) :
    (flip q b s).basis q = (s.basis q ^^ b) := by
  simp [flip, writeBit]

theorem flip_off (q w : Wire) (h : w ≠ q) (b : Bool) (s : State) :
    (flip q b s).basis w = s.basis w := by
  simp [flip, writeBit, h]

private theorem flip_false (q : Wire) (s : State) : flip q false s = s := by
  cases s
  simp [flip, writeBit]

theorem flip_flip (q : Wire) (a b : Bool) (s : State) :
    flip q b (flip q a s) = flip q (a ^^ b) s := by
  cases a <;> cases b <;> simp [flip, writeBit, Function.update_idem]

theorem into_measurementCount (target : Wire) (sources : List Wire) :
    measurementCount (into target sources) = 0 := by
  induction sources with
  | nil => rfl
  | cons x xs ih => exact ih

theorem run_into (target : Wire) (sources : List Wire) (h : target ∉ sources)
    (m : List Bool) (s : State) :
    run (into target sources) m s = flip target (xorBits (sources.map s.basis)) s := by
  induction sources generalizing s with
  | nil => exact (flip_false target s).symm
  | cons q qs ih =>
    have hn : ∀ r ∈ qs, r ≠ target := by
      intro r hr e
      exact h (List.mem_cons_of_mem _ (e ▸ hr))
    have ht : target ∉ qs := by
      intro hm
      exact hn target hm rfl
    let u := flip target (s.basis q) s
    have same : qs.map u.basis = qs.map s.basis := by
      apply List.map_congr_left
      intro r hr
      exact flip_off target r (hn r hr) _ _
    change run (into target qs) m u = flip target (s.basis q ^^ xorBits (qs.map s.basis)) s
    rw [ih ht, same, flip_flip]

theorem round_trip (target : Wire) (a b : Bool) (s : State) (h : a = b) :
    flip target b (flip target a s) = s := by
  rw [← h, flip_flip, Bool.xor_self, flip_false]

theorem clear_target (target : Wire) (b : Bool) (s : State) (h : s.basis target = b) :
    (flip target b s).basis target = false := by
  rw [flip_at, h, Bool.xor_self]

end ECDSAAdd.Entrant.CheckpointSignLoan


namespace ECDSAAdd.Entrant.CheckpointPrefixFinite

open ECDSAAdd Challenge
open _root_.ECDSAAdd.Entrant.CodecBitSliceVerify (Cols Rel get packBits pack_rows)
open _root_.ECDSAAdd.Entrant.MeasuredCodec5 (bitRun)

set_option maxRecDepth 14000
set_option maxHeartbeats 3000000
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

abbrev bitsOf := MeasuredCodec5.bitsOf
def invV : Program := FourScratchPrefix.invV
def clearV : Program := FourScratchPrefix.clearV
def decoded : List Nat := [0, 1, 2, 3, 4, 6, 7, 8]
def packed : List Nat := decoded.drop 1
def expand (n : Nat) : Nat :=
  packed.zipIdx.foldl (fun acc p => if n.testBit p.2 then acc + 2 ^ p.1 else acc) 0
def parity (n : Nat) : Bool := (decoded.map (bitRun invV (expand n)).testBit).foldr (· ^^ ·) false
def initial (n : Nat) (b : Bool) : Nat := if b then expand n + 4096 else expand n
def final (n : Nat) (b : Bool) : Nat := initial n (b ^^ parity n)
def bracket : Program := invV ++ decoded.map (fun q => .CX q 12) ++ clearV
def used : List Nat := [0, 1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 64, 65, 66, 67, 68, 69, 70, 72, 73, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 120, 121, 122, 123, 124, 125, 126, 127]

private def rows : List (Nat × Bool) := used.flatMap fun n => [(n,false),(n,true)]
private def row (r : Nat) : Nat × Bool := (rows[r]?).getD (0,false)
private def rawColumns : Cols := [0, 345083368128590617579509237112959869905330560315251764034428002880716, 405983917690345643379270502607314466949755229610076382586122302328816, 429680629582079116016823740028901829587320687171071560687523888631552, 431352565057909333347209311432980312283816490763838098950330465120256, 0, 431359146272675726024069090269738145037179870151499058997379196780544, 431359146674410236340527822235602948910347852120108263138641324277760, 431359146674410236714672241392314085585897452225821531167161434767360, 0, 0, 0, 0]
private def inputColumns : Cols := [0, 345083368128590617579509237112959869905330560315251764034428002880716, 405983917690345643379270502607314466949755229610076382586122302328816, 429680629582079116016823740028901829587320687171071560687523888631552, 431352565057909333347209311432980312283816490763838098950330465120256, 0, 431359146272675726024069090269738145037179870151499058997379196780544, 431359146674410236340527822235602948910347852120108263138641324277760, 431359146674410236714672241392314085585897452225821531167161434767360, 0, 0, 0, 287572764449606824476448160928209393852129540507099439798438509324970]
private def invertedColumns : Cols := [81216839089046446303320618930319777084989458408771558609346738797760, 325119182429462738101007938385232482339775104043806324665319543749839, 20323723222685895629530000504468585749592226943051933601983177490428, 429680629582079116016823740028901829587320687171071560687523888631552, 26933701778361197018290294217874584988938741063867830149013930036416, 0, 5061572013606073506372551935893514865499168103810708718083152015372, 26940117076774481745042336754095838560022516616438865324938757356736, 5061571621299474634887510789353068612972694563564325774757486391308, 0, 0, 0, 0]
private def parityColumn := decoded.foldr (fun q v => get invertedColumns q ^^^ v) 0
private def outputColumns : Cols := inputColumns.set 12 (get inputColumns 12 ^^^ parityColumn)
private def mask : Nat := 2^228-1

private theorem row_count : rows.length = 228 := by decide +kernel

private theorem row_exists (n : Nat) (hn : n ∈ used) (b : Bool) :
    ∃ r : Fin 228, row r.val = (n,b) := by
  have hm : (n,b) ∈ rows := by
    unfold rows
    exact List.mem_flatMap.mpr ⟨n,hn,by cases b <;> simp⟩
  refine ⟨⟨rows.idxOf (n,b),row_count ▸ List.idxOf_lt_length_of_mem hm⟩,?_⟩
  simp only [row, List.getElem?_idxOf hm, Option.getD_some]

private theorem row_word (value : Nat × Bool → Nat) (r : Fin 228) :
    ((rows.map value)[r.val]?).getD 0 = value (row r.val) := by
  have hr : r.val < rows.length := by rw [row_count]; exact r.isLt
  simp only [row, List.getElem?_map, List.getElem?_eq_getElem hr, Option.map_some, Option.getD_some]

private theorem expand_bound : ∀ n : Fin 128, expand n.val < 4096 := by decide +kernel
private theorem row_code_bound : ∀ r : Fin 228, (row r.val).1 < 128 := by decide +kernel

private theorem raw_bound (r : Fin 228) : expand (row r.val).1 < 4096 :=
  expand_bound ⟨(row r.val).1,row_code_bound r⟩

private theorem initial_bound (r : Fin 228) : initial (row r.val).1 (row r.val).2 < 2^13 := by
  have h := raw_bound r
  unfold initial
  split <;> omega

private theorem initial_bit (n : Nat) (low : expand n < 4096) (b : Bool) (q : Nat) :
    (initial n b).testBit q = if q = 12 then b else (expand n).testBit q := by
  have h12 : (expand n).testBit 12 = false := Nat.testBit_lt_two_pow low
  cases b with
  | false =>
    by_cases hq : q = 12
    · simpa only [hq, initial, Bool.false_eq_true, if_false, if_true] using h12
    · simp only [initial, Bool.false_eq_true, if_false, if_neg hq]
  | true =>
    have hor : expand n + 4096 = expand n ||| 4096 := by
      have h := Nat.two_pow_add_eq_or_of_lt (i := 12) low 1
      simpa only [Nat.mul_one, Nat.add_comm, Nat.or_comm] using h
    simp only [initial, if_true, hor, Nat.testBit_or]
    by_cases hq : q = 12
    · subst q
      rw [h12, show (4096 : Nat).testBit 12 = true from rfl]
      rfl
    · rw [if_neg hq, show (4096 : Nat).testBit q = false from
          Nat.testBit_two_pow_of_ne (Ne.symm hq)]
      simp only [Bool.or_false]

private theorem packed_rel (value : Nat × Bool → Nat) (cols : Cols)
    (len : cols.length = 13)
    (columns : ∀ q : Fin 13, get cols q.val = packBits ((rows.map value).map (fun x => x.testBit q.val)))
    (bound : ∀ r : Fin 228, value (row r.val) < 2^13) (r : Fin 228) :
    Rel cols (value (row r.val)) r.val := by
  intro q
  by_cases hq : q < 13
  · rw [columns ⟨q,hq⟩,pack_rows,row_word]
  · have colBound : cols.length ≤ q := len ▸ Nat.le_of_not_gt hq
    have hz : get cols q = 0 := by
      simp only [CodecBitSliceVerify.get, List.getElem?_eq_none colBound, Option.getD_none]
    rw [hz, Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow ((bound r).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hq)))

private theorem raw_rel (r : Fin 228) : Rel rawColumns (expand (row r.val).1) r.val := by
  refine packed_rel (fun p => expand p.1) rawColumns (by decide +kernel) (by decide +kernel) ?_ r
  intro r'
  have hb := raw_bound r'
  change expand (row r'.val).1 < 8192
  omega

private theorem input_rel (r : Fin 228) :
    Rel inputColumns (initial (row r.val).1 (row r.val).2) r.val :=
  packed_rel (fun p => initial p.1 p.2) inputColumns
    (by decide +kernel) (by decide +kernel) initial_bound r

private theorem inverse_check : CodecBitSliceVerify.eval mask invV rawColumns = (true,invertedColumns) := by
  decide +kernel

private theorem bracket_check : CodecBitSliceVerify.eval mask bracket inputColumns = (true,outputColumns) := by
  decide +kernel

private theorem mask_row (r : Fin 228) : mask.testBit r.val = true := by
  simp only [mask, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact r.isLt

private theorem inverted_rel (r : Fin 228) :
    Rel invertedColumns (bitRun invV (expand (row r.val).1)) r.val := by
  have a := CodecBitSliceVerify.eval_sound mask r.val (mask_row r) invV rawColumns
    (expand (row r.val).1) (by decide +kernel) (raw_rel r) (congrArg Prod.fst inverse_check)
  simpa only [inverse_check] using a.2

private theorem fold_columns (qs : List Nat) (cols : Cols) (x r : Nat) (h : Rel cols x r) :
    (qs.foldr (fun q v => get cols q ^^^ v) 0).testBit r =
      (qs.map x.testBit).foldr (· ^^ ·) false := by
  induction qs with
  | nil => exact Nat.zero_testBit _
  | cons q qs ih => simp only [List.foldr_cons, Nat.testBit_xor, ← h q, ih, List.map_cons]

private theorem output_rel (r : Fin 228) :
    Rel outputColumns (final (row r.val).1 (row r.val).2) r.val := by
  intro q
  have hin := input_rel r q
  have hb := raw_bound r
  have hp : parityColumn.testBit r.val = parity (row r.val).1 :=
    fold_columns decoded invertedColumns _ _ (inverted_rel r)
  unfold final outputColumns
  rw [initial_bit _ hb, CodecBitSliceVerify.get_set inputColumns 12 _ (by decide +kernel) q]
  rw [initial_bit _ hb] at hin
  split_ifs at hin ⊢ with hq
  · subst q
    rw [Nat.testBit_xor, hp, ← hin]
  · exact hin

theorem checked_phase_and_basis (n : Nat) (hn : n ∈ used) (b ph : Bool) (m : List Bool) :
    run bracket m ⟨ph, bitsOf (initial n b)⟩ = ⟨ph, bitsOf (final n b)⟩ := by
  obtain ⟨r,hr⟩ := row_exists n hn b
  have low : Rel inputColumns (initial n b) r.val := by simpa only [hr] using input_rel r
  have high : Rel outputColumns (final n b) r.val := by simpa only [hr] using output_rel r
  have a := CodecBitSliceVerify.eval_sound mask r.val (mask_row r) bracket inputColumns
    (initial n b) (by decide +kernel) low (congrArg Prod.fst bracket_check)
  have atOut : Rel outputColumns (bitRun bracket (initial n b)) r.val := by
    simpa only [bracket_check] using a.2
  have result : bitRun bracket (initial n b) = final n b :=
    Nat.eq_of_testBit_eq fun q => (atOut q).trans (high q).symm
  rw [MeasuredCodec5.run_sim, MeasuredCodec5.sim_safe _ _ a.1, result]

theorem counts :
    toffoliCount bracket = 13 ∧ measurementCount bracket = 11 ∧ gateSlots bracket = 775 := by
  decide +kernel

end ECDSAAdd.Entrant.CheckpointPrefixFinite

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

open Arithmetic MappedCompressed MeasuredCodec5
set_option maxRecDepth 10000
set_option maxHeartbeats 2200000
attribute [local irreducible] run wires FourScratchPrefix.V FourScratchPrefix.invV FourScratchPrefix.clearV

private def prefixIndex (i : Nat) : Nat :=
  ([7, 0, 1, 2, 3, 7, 4, 5, 6, 7, 7, 7] : List Nat)[i]?.getD 7

private theorem expand_bit : ∀ (w : Fin 128) (i : Fin 12),
    (prefixExpand w).testBit i = w.val.testBit (prefixIndex i) := by decide +kernel

private theorem prefix_index_at (i : Fin 12) (h : prefixIndex i < 7) :
    prefixEncodedPorts.getD (prefixIndex i) 0 = i.val := by
  have a : ∀ x : Fin 12, prefixIndex x < 7 →
      prefixEncodedPorts.getD (prefixIndex x) 0 = x.val := by decide +kernel
  exact a i h

private theorem prefix_index_blank (i : Fin 12) (h : ¬ prefixIndex i < 7) :
    i.val ∈ [0, 5, 9, 10, 11] := by
  have a : ∀ x : Fin 12, ¬ prefixIndex x < 7 → x.val ∈ [0, 5, 9, 10, 11] := by decide +kernel
  exact a i h

private theorem prefix_expand_basis (label : Nat → Wire) (s : State)
    (clear : ∀ i ∈ [0, 5, 9, 10, 11], s.basis (label i) = false)
    (i : Nat) (hi : i < 12) :
    bitsOf (prefixExpand (regValue (prefixEncodedPorts.map label) s.basis)) i = s.basis (label i) := by
  let w := regValue (prefixEncodedPorts.map label) s.basis
  have plen : prefixEncodedPorts.length = 7 := by decide +kernel
  have wlt : w < 128 := by
    have h := Arithmetic.regValue_lt (prefixEncodedPorts.map label) s.basis
    simpa only [List.length_map, plen] using h
  change (prefixExpand w).testBit i = s.basis (label i)
  have e := expand_bit ⟨w, wlt⟩ ⟨i, hi⟩
  change (prefixExpand w).testBit i = w.testBit (prefixIndex i) at e
  rw [e]
  by_cases h : prefixIndex i < 7
  · have atIdx := prefix_index_at ⟨i, hi⟩ h
    have hl : prefixIndex i < (prefixEncodedPorts.map label).length := by simp only [List.length_map, plen]; exact h
    have hl' : prefixIndex i < prefixEncodedPorts.length := by rw [plen]; exact h
    have hget : (prefixEncodedPorts.map label).getD (prefixIndex i) 0 = label i := by
      rw [List.getD_eq_getElem _ _ hl, List.getElem_map, ← List.getD_eq_getElem _ _ hl']
      rw [atIdx]
    have bit := Arithmetic.regValue_bit (prefixEncodedPorts.map label) (prefixIndex i) 0 s.basis hl
    rw [hget] at bit
    change (s.basis (label i)).toNat = w / 2 ^ prefixIndex i % 2 at bit
    rw [Nat.testBit_eq_decide_div_mod_eq, ← bit]
    cases s.basis (label i) <;> decide
  · have h7 := Nat.pow_le_pow_right (by decide : 0 < 2) (show 7 ≤ prefixIndex i by omega)
    rw [Nat.testBit_lt_two_pow (wlt.trans_le h7)]
    exact (clear i (prefix_index_blank ⟨i, hi⟩ h)).symm

private theorem sim_basis_eq_bitRun (P : Program) (m : List Bool) (ph : Bool) (x : Nat) :
    (MeasuredCodec5.sim P m ph x).2 = bitRun P x := by
  induction P generalizing m ph x with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [MeasuredCodec5.sim, bitRun, MeasuredCodec5.bitStep] <;> apply ih

private theorem p0_site_shape : prefixEncodedPorts.map FourScratchWindow.label = p0Sites := by
  decide +kernel

private theorem p0_parity_shape :
    prefixDataPorts.map FourScratchWindow.label = (List.range 8).map StairField2V3Win.pctrl := by
  decide +kernel

/-- Read the original eight-bit packet-zero parity from the seven-bit field code. -/
theorem prefixParityValue_correct (s1 : State) (cl : FourScratchWindow.Clean s1)
    (cn : StairField2V3Win.Canon s1) :
    prefixParityValue (regValue p0Sites (run FourScratchWindow.prefixProgram [] s1).basis) =
      TraceParity5.xorRange 8 (fun i => s1.basis (StairField2V3Win.pctrl i)) := by
  let b := run FourScratchWindow.prefixProgram [] s1
  let z := regValue p0Sites b.basis
  let decodedIn := run FourScratchPrefix.V [] (FourScratchWindow.pull s1)
  have bitMap := (FourScratchWindow.mapped_run FourScratchPrefix.V FourScratchPrefix.support.1 s1 []).2
  have clB := FourScratchWindow.prefix_clean s1 [] cl
  have zeroB := FourScratchWindow.prefix_zero s1 [] cl cn
  have blank (i : Nat) (hi : i ∈ [0, 5, 9, 10, 11]) :
      b.basis (FourScratchWindow.label i) = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact zeroB
    · exact clB.1
    · exact clB.2.1
    · exact clB.2.2.1
    · exact clB.2.2.2
  have matchLocal (q : Wire) (hq : q ∈ wires FourScratchPrefix.invV) :
      bitsOf (prefixExpand z) q = decodedIn.basis q := by
    have hlt := Finset.mem_range.mp (FourScratchPrefix.support.2.2 hq)
    rw [show z = regValue (prefixEncodedPorts.map FourScratchWindow.label) b.basis by rw [p0_site_shape]]
    exact (prefix_expand_basis FourScratchWindow.label b blank q hlt).trans (bitMap q hlt)
  have close : run FourScratchPrefix.invV [] decodedIn = FourScratchWindow.pull s1 :=
    FourScratchPrefix.invV_V _ _ _ cl ((FourScratchWindow.code_compat s1).symm ▸ cn)
  have inc := Arithmetic.run_local_increment FourScratchPrefix.invV
    ⟨false, bitsOf (prefixExpand z)⟩ decodedIn [] matchLocal
  have result (q : Nat) (hq : q ∈ prefixDataPorts) :
      (bitRun FourScratchPrefix.invV (prefixExpand z)).testBit q = s1.basis (FourScratchWindow.label q) := by
    have hlt : ∀ i ∈ prefixDataPorts, i < 12 := by decide +kernel
    have hmem : q ∈ wires FourScratchPrefix.invV := by
      rw [FourScratchPrefix.support_exact.2.2]
      exact Finset.mem_range.mpr (hlt q hq)
    have h := inc.2 q hmem
    rw [close, MeasuredCodec5.run_sim, sim_basis_eq_bitRun] at h
    exact h
  change TraceParity5.parity (prefixDataPorts.map (bitRun FourScratchPrefix.invV (prefixExpand z)).testBit) = _
  have mapEq : prefixDataPorts.map (bitRun FourScratchPrefix.invV (prefixExpand z)).testBit =
      prefixDataPorts.map (fun q => s1.basis (FourScratchWindow.label q)) :=
    List.map_congr_left result
  have controls : prefixDataPorts.map (fun q => s1.basis (FourScratchWindow.label q)) =
      (List.range 8).map (fun i => s1.basis (StairField2V3Win.pctrl i)) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map s1.basis) p0_parity_shape
  rw [mapEq, controls, TraceParity5.parity_range]

end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts


namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

open Arithmetic MappedCompressed
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

private def checkpointPrefixPlace (q : Wire) : Wire :=
  if q = 12 then signHost else prefixLoanPort q

private theorem checkpointPrefixPlace_lo {q : Wire} (hq : q < 12) :
    checkpointPrefixPlace q = prefixLoanPort q :=
  if_neg (Nat.ne_of_lt hq)

private theorem checkpointPrefixPlace_end : checkpointPrefixPlace 12 = signHost := rfl

private theorem checkpointPrefixPlace_inj :
    ∀ i j : Fin 13, checkpointPrefixPlace i = checkpointPrefixPlace j → i = j := by
  decide +kernel

private theorem checkpointPrefix_support :
    wires CheckpointPrefixFinite.bracket ⊆ Finset.range 13 := by
  decide +kernel

theorem prefixLoanEncoded_eq : prefixEncodedPorts.map prefixLoanPort = p0Sites := by
  decide +kernel

theorem checkpointPrefix_used_eq : CheckpointPrefixFinite.used = TagPack1542.used7 := by
  decide +kernel

private theorem checkpointPrefix_inv :
    CheckpointPrefixFinite.invV = FourScratchPrefix.invV := rfl

private theorem checkpointPrefix_clear :
    CheckpointPrefixFinite.clearV = FourScratchPrefix.clearV := rfl

private theorem checkpointPrefix_program :
    renameProgram checkpointPrefixPlace CheckpointPrefixFinite.bracket = prefixParity := by
  have placeSmall (P : Program) (support : wires P ⊆ Finset.range 12) :
      renameProgram checkpointPrefixPlace P = renameProgram prefixLoanPort P :=
    RouteA.Rolling1588.renameProgram_congr_on _ _ _ (fun q hq =>
      checkpointPrefixPlace_lo (Finset.mem_range.mp (support hq)))
  simp only [CheckpointPrefixFinite.bracket, renameProgram, List.map_append]
  change renameProgram checkpointPrefixPlace CheckpointPrefixFinite.invV ++
    renameProgram checkpointPrefixPlace (CheckpointPrefixFinite.decoded.map (fun q => .CX q 12)) ++
    renameProgram checkpointPrefixPlace CheckpointPrefixFinite.clearV = prefixParity
  rw [checkpointPrefix_inv, checkpointPrefix_clear,
    placeSmall _ FourScratchPrefix.support.2.2, placeSmall _ FourScratchPrefix.support.2.1]
  rfl

private theorem parity_fold (xs : List Bool) :
    xs.foldr (· ^^ ·) false = TraceParity5.parity xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, TraceParity5.parity, ih]

private theorem checkpointPrefix_parity (n : Nat) :
    CheckpointPrefixFinite.parity n = prefixParityValue n := by
  change (CheckpointPrefixFinite.decoded.map
    (MeasuredCodec5.bitRun CheckpointPrefixFinite.invV (prefixExpand n)).testBit).foldr
    (· ^^ ·) false = prefixParityValue n
  rewrite [checkpointPrefix_inv, parity_fold]
  rfl

private theorem checkpointPrefix_expand_lt :
    ∀ n : Fin 128, prefixExpand n < 4096 := by
  decide +kernel

private theorem checkpointPrefix_initial_lo {n i : Nat} (hn : n < 128) (hi : i < 12) (b : Bool) :
    CheckpointPrefixFinite.bitsOf (CheckpointPrefixFinite.initial n b) i =
      MeasuredCodec5.bitsOf (prefixExpand n) i := by
  cases b
  · rfl
  · change (prefixExpand n + 4096).testBit i = (prefixExpand n).testBit i
    have he : 2 ^ 12 + prefixExpand n = 2 ^ 12 ||| prefixExpand n := by
      have h := Nat.shiftLeft_add_eq_or_of_lt (i := 12) (b := prefixExpand n)
        (checkpointPrefix_expand_lt ⟨n, hn⟩) 1
      exact h
    rw [Nat.add_comm, show (4096 : Nat) = 2 ^ 12 from rfl, he,
      Nat.testBit_or, Nat.testBit_two_pow_of_ne (by omega : 12 ≠ i), Bool.false_or]

private theorem checkpointPrefix_initial_end {n : Nat} (hn : n < 128) (b : Bool) :
    CheckpointPrefixFinite.bitsOf (CheckpointPrefixFinite.initial n b) 12 = b := by
  have lo : (prefixExpand n).testBit 12 = false :=
    Nat.testBit_lt_two_pow (checkpointPrefix_expand_lt ⟨n, hn⟩)
  cases b
  · exact lo
  · change (prefixExpand n + 4096).testBit 12 = true
    rw [Nat.add_comm, show (4096 : Nat) = 2 ^ 12 from rfl, Nat.testBit_two_pow_add_eq, lo]
    rfl

/-- The placed prefix restores every bit except the sign and preserves the phase. -/
theorem prefixParity_run (s : State) (m : List Bool)
    (clean : ∀ i ∈ [0, 5, 9, 10, 11], s.basis (prefixLoanPort i) = false)
    (used : regValue p0Sites s.basis ∈ TagPack1542.used7) :
    run prefixParity m s =
      CheckpointSignLoan.flip signHost (prefixParityValue (regValue p0Sites s.basis)) s := by
  let n := regValue p0Sites s.basis
  let b := s.basis signHost
  let parity := prefixParityValue n
  have hn : n < 128 := by
    have h := Arithmetic.regValue_lt p0Sites s.basis
    have hlen : p0Sites.length = 7 := by simp [p0Sites]
    simpa only [hlen] using h
  have hUsed : n ∈ CheckpointPrefixFinite.used := checkpointPrefix_used_eq.symm ▸ used
  have bitLo (q : Wire) (hq : q < 12) :
      MeasuredCodec5.bitsOf (prefixExpand n) q = s.basis (prefixLoanPort q) := by
    rw [show n = regValue (prefixEncodedPorts.map prefixLoanPort) s.basis from
      congrArg (fun sites => regValue sites s.basis) prefixLoanEncoded_eq.symm]
    exact prefix_expand_basis prefixLoanPort s clean q hq
  have haveInput (q : Wire) (hq : q ∈ Finset.range 13) :
      CheckpointPrefixFinite.bitsOf (CheckpointPrefixFinite.initial n b) q =
        s.basis (checkpointPrefixPlace q) := by
    have hlt := Finset.mem_range.mp hq
    by_cases atSign : q = 12
    · subst q
      rw [checkpointPrefix_initial_end hn, checkpointPrefixPlace_end]
    · have hq' : q < 12 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) atSign
      rw [checkpointPrefix_initial_lo hn hq', checkpointPrefixPlace_lo hq']
      exact bitLo q hq'
  have h := run_rename_pool checkpointPrefixPlace (Finset.range 13)
    (fun i hi j hj eq => congrArg Fin.val
      (checkpointPrefixPlace_inj ⟨i, Finset.mem_range.mp hi⟩ ⟨j, Finset.mem_range.mp hj⟩ eq))
    CheckpointPrefixFinite.bracket checkpointPrefix_support m
    ⟨s.phase, CheckpointPrefixFinite.bitsOf (CheckpointPrefixFinite.initial n b)⟩ s rfl haveInput
  rw [CheckpointPrefixFinite.checked_phase_and_basis n hUsed b s.phase m,
    checkpointPrefix_program] at h
  refine State.extensionality (run prefixParity m s)
    (CheckpointSignLoan.flip signHost parity s) h.1 ?_
  funext q
  by_cases inside : q ∈ (Finset.range 13).image checkpointPrefixPlace
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp inside
    have hlt := Finset.mem_range.mp hi
    have result := h.2 i hi
    change (run prefixParity m s).basis (checkpointPrefixPlace i) =
      CheckpointPrefixFinite.bitsOf
        (CheckpointPrefixFinite.initial n (b ^^ CheckpointPrefixFinite.parity n)) i at result
    rw [checkpointPrefix_parity] at result
    by_cases atSign : i = 12
    · subst i
      rw [checkpointPrefix_initial_end hn, checkpointPrefixPlace_end] at result
      simpa only [CheckpointSignLoan.flip, writeBit, Function.update_self] using result
    · have hSmall : i < 12 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) atSign
      have hOff : checkpointPrefixPlace i ≠ signHost := by
        intro eq
        exact atSign (congrArg Fin.val (checkpointPrefixPlace_inj ⟨i, hlt⟩
          ⟨12, by decide⟩ (eq.trans checkpointPrefixPlace_end.symm)))
      rw [CheckpointSignLoan.flip_off _ _ hOff]
      rw [checkpointPrefixPlace_lo hSmall]
      rw [checkpointPrefix_initial_lo hn hSmall, checkpointPrefixPlace_lo hSmall] at result
      exact result.trans (bitLo i hSmall)
  · have hOff : q ≠ signHost := by
      intro eq
      apply inside
      exact Finset.mem_image.mpr ⟨12, by decide, checkpointPrefixPlace_end.trans eq.symm⟩
    rw [CheckpointSignLoan.flip_off _ _ hOff, ← checkpointPrefix_program]
    exact run_rename_pool_outside _ _ _ checkpointPrefix_support m s q inside

theorem signPayload_avoids_sign : signHost ∉ signPayload := by
  intro member
  have band := signPayload_band signHost member
  have outside : ¬ signPayloadBand signHost := by
    unfold signPayloadBand
    decide +kernel
  exact outside band

private theorem loan_parity (xs : List Bool) :
    CheckpointSignLoan.xorBits xs = TraceParity5.parity xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [CheckpointSignLoan.xorBits, TraceParity5.parity, ih]

/-- The complete bracket changes only the sign bit. -/
theorem signBracket_run (s : State) (m : List Bool)
    (clean : ∀ i ∈ [0, 5, 9, 10, 11], s.basis (prefixLoanPort i) = false)
    (used : regValue p0Sites s.basis ∈ TagPack1542.used7) :
    run signBracket m s = CheckpointSignLoan.flip signHost
      (TraceParity5.parity (signPayload.map s.basis) ^^
        prefixParityValue (regValue p0Sites s.basis)) s := by
  let parity := prefixParityValue (regValue p0Sites s.basis)
  let t := CheckpointSignLoan.flip signHost parity s
  have payload : signPayload.map t.basis = signPayload.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact CheckpointSignLoan.flip_off signHost q (fun eq => signPayload_avoids_sign (eq ▸ hq)) parity s
  rw [signBracket, run_append, run_take, prefixParity_run s _ clean used]
  change run (CheckpointSignLoan.into signHost signPayload) _ t = _
  rw [CheckpointSignLoan.run_into _ _ signPayload_avoids_sign, payload, loan_parity,
    CheckpointSignLoan.flip_flip, Bool.xor_comm parity]

theorem signBracket_clears (s : State) (m : List Bool)
    (clean : ∀ i ∈ [0, 5, 9, 10, 11], s.basis (prefixLoanPort i) = false)
    (used : regValue p0Sites s.basis ∈ TagPack1542.used7)
    (ready : s.basis signHost = (TraceParity5.parity (signPayload.map s.basis) ^^
      prefixParityValue (regValue p0Sites s.basis))) :
    (run signBracket m s).basis signHost = false := by
  rw [signBracket_run s m clean used]
  exact CheckpointSignLoan.clear_target _ _ _ ready

end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts


namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney

open WindowFieldCosts StairArchiveNativeCut StairArchiveRelease StairArchiveTen
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
attribute [local irreducible] measurementCount run ogroup opk rgroup fieldHook packTag unpackTag

def stenOldTape (j : Nat) (rev : Bool) (m : List Bool) : List Bool :=
  let E := fieldHook j (enter rev)
  let S := fieldHook j (shift rev)
  let L := fieldHook j (leave rev)
  let mA := m.drop (measurementCount E)
  let mS := mA.drop (measurementCount (sfirst j rev))
  let mB := mS.drop (measurementCount S)
  let mL := mB.drop (measurementCount (ssecond j rev))
  joinTapes E m (joinTapes (ofirst j rev) []
    (joinTapes S mS (joinTapes (osecond j rev) [] (mL.take (measurementCount L)))))

def signEmitted (d : Bool) : Leg → Program
  | .native j n => rgroup d j n
  | .paired j => sten j (!d)

def signConcatenate (d : Bool) : List Leg → Program
  | [] => []
  | l :: ls => signEmitted d l ++ signConcatenate d ls

theorem signEmits_body (d : Bool) : group84SignBody d = signConcatenate d (planBody d) := by
  cases d <;> simp only [group84SignBody, ordered, signConcatenate, signEmitted, planBody, plan,
    if_true, if_false, Bool.false_eq_true, List.tail_cons, List.dropLast,
    List.append_assoc, List.append_nil]

def signOldLegTape (d : Bool) (l : Leg) (m : List Bool) : List Bool :=
  match l with
  | .native _ _ => m
  | .paired j => stenOldTape j (!d) m

def signOldBodyTape (d : Bool) : List Leg → List Bool → List Bool
  | [], _ => []
  | l :: ls, m => joinTapes (oemitted d l) (signOldLegTape d l m)
      (signOldBodyTape d ls (m.drop (measurementCount (signEmitted d l))))

def signOldGroupTape (d : Bool) (m : List Bool) : List Bool :=
  let m0 := m.drop (measurementCount signBracket)
  let early := ogroup d 1 9
  let mPack := if d then m0.drop (measurementCount early) else m0
  let mBody := mPack.drop (measurementCount packTag)
  let mUnpack := mBody.drop (measurementCount (group84SignBody d))
  let mLate := mUnpack.drop (measurementCount unpackTag)
  let mOld := joinTapes packTag mPack (joinTapes (group84Body d)
    (signOldBodyTape d (planBody d) mBody) (mUnpack.take (measurementCount unpackTag)))
  if d then joinTapes early m0 mOld
  else joinTapes (packTag ++ renameProgram tagSwap (group84Body d) ++ unpackTag) mOld mLate

/-- The old core tape seen by the early leg: the fully decoded early packets are independent of
    their tape, so the ordinary early leg may use a zero tape. -/
def signEarlyTape (d : Bool) (t : List Bool) : List Bool :=
  if d then joinTapes (ogroup true 1 9) [] (t.drop (measurementCount (egroup true 1 9)))
  else joinTapes (packTag ++ renameProgram tagSwap (group84SignBody false) ++ unpackTag) t []

def signPadTape (d : Bool) (m : List Bool) : List Bool :=
  List.replicate (measurementCount signBracket) false ++
    signEarlyTape d (m.drop (measurementCount signBracket))

/-- The same three hook tapes on each bank. The reference arithmetic on the
    two packets may use a zero tape, because the raw-packet law is independent
    of either packet tape. -/
def oreferenceTapeSign (d : Bool) (m : List Bool) : List Bool :=
  oreferenceTape1542 d (signOldGroupTape d (signPadTape d m))

end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney


namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView

open Arithmetic MappedCompressed CodecBitSliceVerify
open StairArchiveRelease StairArchiveNativeCut StairArchiveInactive StairArchiveTen
open WindowFieldCosts WindowFieldMask WindowFieldJourney StairField2V3Seg
set_option maxRecDepth 12000
set_option maxHeartbeats 2800000
attribute [local irreducible] run wires measurementCount fieldHook opk ofirst osecond sfirst ssecond

/-- Both raw substitutions use the original hook records, including short
    tapes. Each reference packet can consume an independent zero tape. -/
theorem sten_run_eq (j : Nat) (hj : j ∈ bankIds) (lo : 10 ≤ j) (hi : j ≤ 83)
    (rev : Bool) (rows : Nat → Nat) (code : Nat → Cols) (hr : rows j < 63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true)
    (m : List Bool) (a r : State) (h : Fits rows code a r)
    (active : code j = inputCols (enter rev))
    (before_ : frame j (rows j) (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j (rows j) middle (run (ofirst j rev) [] r))
    (refCut : OCut (if rev then j + 2 else j) origin r)
    (otherApart : ∀ q ∈ inside j, q ∉ others j)
    (safeA : avoids (ofirst j rev) (others j))
    (safeB : avoids (osecond j rev) (others j))
    (clear : a.basis signHost = false) :
    run (sten j rev) m a = run (oten j rev) (stenOldTape j rev m) a := by
  let E := fieldHook j (enter rev)
  let S := fieldHook j (shift rev)
  let L := fieldHook j (leave rev)
  let A := ofirst j rev
  let B := osecond j rev
  let AS := sfirst j rev
  let BS := ssecond j rev
  let mA := m.drop (measurementCount E)
  let mS := mA.drop (measurementCount AS)
  let mB := mS.drop (measurementCount S)
  let mL := mB.drop (measurementCount BS)
  let rM := run A [] r
  let shadow := mask (others j) a r
  let shadowM := run A [] shadow
  let aE := run E m a
  let aM := run A [] aE
  let aS := run S mS aM
  have ⟨hBanks, hRange⟩ := geometry hj
  have hList : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
  have arch := beforeFrame j hj rows code rev a r h active otherApart before_
    (StairArchiveRelease.field_inj j hRange)
  have beforeShadow := mask_frame j (rows j) _ (others j) a r otherApart before_
  have outside : exterior j a shadow := by
    intro q hq
    by_cases other : q ∈ others j
    · simp [shadow, mask, other]
    · have notOwn : q ∉ bank j := by
        intro own
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp own
        exact hq (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), rfl⟩)
      have notBank : q ∉ allBanks := by
        rw [decompose j hj, Finset.mem_union]
        exact fun mem => mem.elim notOwn other
      simpa [shadow, mask, other] using h.outside q notBank
  have agreeA (q : Wire) (hq : q ∈ wires A) : shadow.basis q = r.basis q := by
    have hqOff : q ∉ others j := fun other => safeA q other hq
    simp [shadow, mask, hqOff]
  have hFirst : run AS mA aE = aM := by
    have ref : OCut ((if !rev then (if rev ^^ false then j + 1 else j)
      else (if rev ^^ false then j + 1 else j) + 1)) origin r := by
      cases rev <;> simpa using refCut
    simpa only [fromStage, sfirst, ofirst, Bool.xor_false, Bool.false_eq_true, if_false,
      A, AS, E, aM, aE] using
      spk_after_hook j hBanks hRange hList lo rev false (rows j) hr m mA []
        a shadow r origin ctx enabled arch outside beforeShadow ref
        (by simpa only [Bool.xor_false, A, ofirst] using agreeA) clear
  have mFrame : frame j (rows j) middle shadowM := by
    have hmask : shadowM = mask (others j) a rM := mask_run A (others j) [] a r safeA
    rw [hmask]
    exact mask_frame _ _ _ _ _ _ otherApart middle_
  have midFacts : aM.phase = shadowM.phase ∧ exterior j aM shadowM ∧
      frame j (rows j) (inputCols (shift rev)) aM := by
    simpa only [fromStage, toStage, before, after, ofirst, Bool.xor_false,
      Bool.false_eq_true, if_false, aM, A, aE, E, shadowM] using
      ot_stage_packet j hBanks hRange rev false (rows j) hr m [] a shadow
        arch outside h.phase beforeShadow (by simpa only [shadowM,A,ofirst,Bool.xor_false] using mFrame)
  have midCut : OCut (j + 1) origin rM := by
    cases rev
    · simpa [rM, A, ofirst] using
        (ostep true j (by omega) (by omega) origin ctx enabled r [] refCut)
    · simpa [rM, A, ofirst] using
        (ostep false (j + 1) (by omega) (by omega) origin ctx enabled r [] refCut)
  have agreeB (q : Wire) (hq : q ∈ wires B) : shadowM.basis q = rM.basis q := by
    have hmask : shadowM = mask (others j) a rM := mask_run A (others j) [] a r safeA
    rw [hmask]
    have hqOff : q ∉ others j := fun other => safeB q other hq
    simp [mask, hqOff]
  have midClear : aM.basis signHost = false := by
    have hA : signHost ∉ wires A := by
      unfold A ofirst
      exact opk_avoids_sign _ _ (by split <;> omega) (by split <;> omega)
    rw [show aM = run A [] (run E m a) from rfl]
    rw [run_preserves_outside _ _ _ _ hA, run_preserves_outside _ _ _ _ (hook_avoids_sign j hList (enter rev)), clear]
  have hSecond : run BS mB aS = run B [] aS := by
    have key : (if rev ^^ true then j + 1 else j) = (if rev then j else j + 1) := by cases rev <;> rfl
    have ref : OCut ((if !rev then (if rev ^^ true then j + 1 else j)
      else (if rev ^^ true then j + 1 else j) + 1)) origin rM := by
      cases rev <;> simpa using midCut
    simpa only [fromStage, before, ssecond, osecond, if_true, key, aS, S, BS, B] using
      spk_after_hook j hBanks hRange hList lo rev true (rows j) hr mS mB []
        aM shadowM rM origin ctx enabled midFacts.2.2 midFacts.2.1 mFrame ref
        (by simpa only [key, B, osecond] using agreeB) midClear
  have actualShape :
      run (sten j rev) m a =
        run L mL (run BS mB (run S mS (run AS mA (run E m a)))) := by
    simp only [sten, run_append, run_take, E, S, L, AS, BS, mA, mS, mB, mL]
  have oldShape :
      run (oten j rev) (stenOldTape j rev m) a =
        run L mL (run B [] (run S mS (run A [] (run E m a)))) := by
    simp only [oten, stenOldTape, joined, run_take, E, S, L, A, B, AS, BS, mA, mS, mB, mL]
  rw [actualShape, oldShape, hFirst, hSecond]

end ECDSAAdd.Entrant.StairPacket.WindowFieldView


namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView

open Arithmetic MappedCompressed CodecBitSliceVerify
open StairArchiveRelease StairArchiveNativeCut StairArchiveInactive StairArchiveTen
open WindowFieldCosts WindowFieldMask WindowFieldJourney StairField2V3Seg
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000
attribute [local irreducible] run wires measurementCount fieldHook opk ofirst osecond rgroup

theorem ogroup_avoids_sign (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    signHost ∉ wires (ogroup d j n) := by
  unfold ogroup
  induction n generalizing j with
  | zero => simp [PacketSequence.program, wires]
  | succ n ih =>
    have a := opk_avoids_sign d j lo (by omega)
    have b := ih (j + 1) (by omega) (by omega)
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      wires_append, Finset.mem_union, not_or] <;> first | exact ⟨a,b⟩ | exact ⟨b,a⟩

theorem rgroup_avoids_sign (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    signHost ∉ wires (rgroup d j n) := fun h =>
  (Finset.mem_insert.mp (rgroup_sub d j n h)).elim signHost_ne_tag (ogroup_avoids_sign d j n lo hi)

private theorem oten_avoids_sign (j : Nat) (hj : j ∈ bankIds) (rev : Bool) :
    signHost ∉ wires (oten j rev) := by
  have list : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
  have ⟨_, hn⟩ := geometry hj
  have range := List.mem_range'_1.mp hn
  have hA : signHost ∉ wires (ofirst j rev) := by
    rw [ofirst]
    exact opk_avoids_sign _ _ (by split <;> omega) (by split <;> omega)
  have hB : signHost ∉ wires (osecond j rev) := by
    rw [osecond]
    exact opk_avoids_sign _ _ (by split <;> omega) (by split <;> omega)
  simp only [oten, wires_append, Finset.mem_union, not_or]
  exact ⟨hook_avoids_sign j list _, hA, hook_avoids_sign j list _, hB, hook_avoids_sign j list _⟩

private theorem paired_apart (j : Nat) (hj : j ∈ bankIds) : ∀ q ∈ inside j, q ∉ others j := by
  intro q hi ho
  obtain ⟨k, hk, mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne, kid⟩ := Finset.mem_erase.mp hk
  have lists (h : Nat) (hm : h ∈ bankIds) : h ∈ WindowBankCheck.banks := by
    simpa [bankIds, WindowBankCheck.banks] using hm
  exact WindowBankCheck.separate j k (lists j hj) (lists k kid) ne.symm q hi mem

private theorem paired_safe (j k : Nat) (hj : j ∈ bankIds) (which : k = j ∨ k = j + 1)
    (d : Bool) : avoids (opk d k) (others j) := by
  intro q ho used
  obtain ⟨h, hm, mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne, hid⟩ := Finset.mem_erase.mp hm
  have hlist : h ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hid
  apply WindowBankCheck.packet_free h k hlist _ _ _ d q mem (ot_opk_sub d k used)
  all_goals simp only [bankIds, Finset.mem_insert, Finset.mem_singleton] at hj hid
  · apply List.mem_range'_1.mpr; omega
  all_goals omega

theorem signTravel_eq (d : Bool) (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (ls : List Leg) (c : Nat) (route : path d c ls)
    (scope : ∀ l ∈ ls, 10 ≤ (span l).1)
    (code : Nat → Cols) (valid_ : valid d ls code)
    (m : List Bool) (a r : State) (fits : Fits rows code a r)
    (cut : OCut c origin r) (clear : a.basis signHost = false) :
    run (signConcatenate d ls) m a =
      run (oconcatenate d ls) (signOldBodyTape d ls m) a := by
  induction ls generalizing c code m a r with
  | nil => simp only [signConcatenate, oconcatenate, run]
  | cons l ls ih =>
    obtain ⟨one, restRoute⟩ := route.2
    obtain ⟨loc, restValid⟩ := valid_
    have lower := scope l (by simp)
    have nextScope (k : Leg) (hk : k ∈ ls) : 10 ≤ (span k).1 := scope k (List.mem_cons_of_mem _ hk)
    let t := signOldLegTape d l m
    let a' := run (oemitted d l) t a
    let r' := ostock d t r l
    let cs := codes d code l
    have initial : OCut (prev d l) origin r := route.1 ▸ cut
    have hlocal : run (signEmitted d l) m a = a' ∧ Fits rows cs a' r' ∧
        OCut (next d l) origin r' ∧ a'.basis signHost = false := by
      cases l with
      | native j n =>
        have lo : 10 ≤ j := lower
        have hi : j + n ≤ 85 := one.2
        have p := plain (rgroup d j n) rows code t a r fits (ot_rgroupSafe d j n loc)
        rw [rgroup_run_eq d j n lo hi origin ctx en r t t initial] at p
        refine ⟨rfl, p, oselected d j n (by omega) hi origin ctx en r t initial, ?_⟩
        exact (run_preserves_outside _ _ _ _ (rgroup_avoids_sign d j n (by omega) hi)).trans clear
      | paired j =>
        have hj : j ∈ bankIds := loc.1
        have hb := geometry hj
        have range := List.mem_range'_1.mp hb.2
        have lo : 10 ≤ j := lower
        have z := opair_cuts d j x (rows j) hj (rb j hj) origin ctx en tr (history j hj) r [] initial
        have p := opair_cuts d j x (rows j) hj (rb j hj) origin ctx en tr (history j hj) r t initial
        have hrev : OCut (if !d then j + 2 else j) origin r := by cases d <;> exact initial
        have fa : avoids (ofirst j (!d)) (others j) := by
          rw [ofirst]; apply paired_safe _ _ hj; cases d <;> simp
        have fb : avoids (osecond j (!d)) (others j) := by
          rw [osecond]; apply paired_safe _ _ hj; cases d <;> simp
        have eq := sten_run_eq j hj lo (by omega) (!d) rows code (rb j hj)
          origin ctx en m a r fits loc.2 (by simpa only [Bool.not_not] using z.1.1)
          (by simpa only [orefMiddle, tapeA, List.drop_nil] using z.1.2.1)
          hrev (paired_apart j hj) fa fb clear
        refine ⟨eq, ?_, p.2, ?_⟩
        · exact ot_stepTen j hj rows code (!d) (rb j hj) t a r fits loc.2
            (by simpa only [Bool.not_not] using p.1.1) p.1.2.1 p.1.2.2
        · exact (run_preserves_outside _ _ _ _ (oten_avoids_sign j hj (!d))).trans clear
    rw [signConcatenate, oconcatenate, signOldBodyTape, run_append, run_take, joined, hlocal.1]
    exact ih (next d l) restRoute nextScope cs restValid _ a' r' hlocal.2.1 hlocal.2.2.1 hlocal.2.2.2

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView

open Arithmetic MappedCompressed CodecBitSliceVerify
open StairArchiveRelease StairArchiveNativeCut StairArchiveInactive StairArchiveTen
open WindowFieldCosts WindowFieldMask WindowFieldJourney StairField2V3Seg
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000
attribute [local irreducible] run measurementCount fieldHook opk epk

section
attribute [local irreducible] StairArchiveInactive.packet wires

theorem opk_early_safe (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 9) : avoids (opk d k) allBanks := by
  intro q mem used
  rw [allBanks] at mem
  obtain ⟨h, hm, hq⟩ := Finset.mem_biUnion.mp mem
  have hlist : h ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hm
  have hb : 10 ≤ h := by
    simp only [bankIds, Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  exact WindowBankCheck.packet_free h k hlist (List.mem_range'_1.mpr (by omega)) (by omega) (by omega)
    d q hq (ot_opk_sub d k used)

end

theorem early_seq_safe (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 10) :
    avoids (ogroup d j n) allBanks := by
  unfold ogroup
  induction n generalizing j with
  | zero =>
    intro q _ used
    simp [PacketSequence.program, wires] at used
  | succ n ih =>
    have head := opk_early_safe d j lo (by omega)
    have tail := ih (j + 1) (by omega) (by omega)
    intro q inbank used
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      wires_append, Finset.mem_union] at used
    · exact used.elim (tail q inbank) (head q inbank)
    · exact used.elim (head q inbank) (tail q inbank)

attribute [local irreducible] wires

/-- An early leg of relocated fully decoded packets runs exactly as the regular leg, from any state
    that fits a reference cut and has a clear sign site. The two tapes are independent. -/
theorem egroup_run_eq (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 10)
    (rows : Nat → Nat) (code : Nat → Cols)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true)
    (a r : State) (m m' : List Bool) (fits : Fits rows code a r)
    (initial : OCut (if d then j else j + n) origin r) (clear : a.basis signHost = false) :
    run (egroup d j n) m a = run (ogroup d j n) m' a := by
  unfold egroup ogroup
  induction n generalizing j a r m m' with
  | zero => simp only [PacketSequence.program, run]
  | succ n ih =>
    cases d with
    | true =>
      simp only [if_true] at initial
      simp only [PacketSequence.program, if_true, run_append]
      have agree : ∀ q ∈ wires (opk true j), a.basis q = r.basis q :=
        fun q hq => fits.outside q (fun hb => opk_early_safe true j lo (by omega) q hb hq)
      have first := epk_run_eq true j lo (by omega) origin ctx en r a
        (m.take (measurementCount (epk true j))) (m'.take (measurementCount (opk true j)))
        (by simpa only [if_true] using initial) clear agree
      rw [first]
      have next := ostep true j lo (by omega) origin ctx en r
        (m'.take (measurementCount (opk true j))) (by simpa only [if_true] using initial)
      have fits' := plain (opk true j) rows code (m'.take (measurementCount (opk true j))) a r fits
        (opk_early_safe true j lo (by omega))
      have clear' : (run (opk true j) (m'.take (measurementCount (opk true j))) a).basis signHost = false :=
        (run_preserves_outside _ _ _ _ (opk_avoids_sign true j lo (by omega))).trans clear
      exact ih (j + 1) (by omega) (by omega) _ _ _ _ fits'
        (by simpa only [if_true] using next) clear'
    | false =>
      simp only [Bool.false_eq_true, if_false] at initial
      simp only [PacketSequence.program, Bool.false_eq_true, if_false, run_append]
      have start : OCut (if false then j + 1 else j + 1 + n) origin r := by
        simpa only [Bool.false_eq_true, if_false, Nat.add_assoc, Nat.add_comm 1 n] using initial
      have rest := ih (j + 1) (by omega) (by omega) a r
        (m.take (measurementCount (PacketSequence.program false (epk false) (j + 1) n)))
        (m'.take (measurementCount (PacketSequence.program false (opk false) (j + 1) n))) fits start clear
      rw [rest]
      have mid := oselected false (j + 1) n (by omega) (by omega) origin ctx en r
        (m'.take (measurementCount (PacketSequence.program false (opk false) (j + 1) n))) start
      have fits' := plain (ogroup false (j + 1) n) rows code
        (m'.take (measurementCount (PacketSequence.program false (opk false) (j + 1) n))) a r fits
        (early_seq_safe false (j + 1) n (by omega) (by omega))
      have clear' : (run (ogroup false (j + 1) n)
          (m'.take (measurementCount (PacketSequence.program false (opk false) (j + 1) n))) a).basis signHost = false :=
        (run_preserves_outside _ _ _ _ (ogroup_avoids_sign false (j + 1) n (by omega) (by omega))).trans clear
      have agree : ∀ q ∈ wires (opk false j),
          (run (ogroup false (j + 1) n)
            (m'.take (measurementCount (PacketSequence.program false (opk false) (j + 1) n))) a).basis q =
          (run (ogroup false (j + 1) n)
            (m'.take (measurementCount (PacketSequence.program false (opk false) (j + 1) n))) r).basis q :=
        fun q hq => fits'.outside q (fun hb => opk_early_safe false j lo (by omega) q hb hq)
      exact epk_run_eq false j lo (by omega) origin ctx en
        (run (ogroup false (j + 1) n)
          (m'.take (measurementCount (PacketSequence.program false (opk false) (j + 1) n))) r) _ _ _
        (by simpa only [Bool.false_eq_true, if_false] using mid) clear' agree

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end


namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView

open Arithmetic MappedCompressed Secp256k1 CodecBitSliceVerify
open StairField2V3Seg WindowFieldCosts WindowFieldMask WindowFieldJourney
open StairArchiveRelease StairArchiveNativeCut StairArchiveInactive ArchiveFieldScratch
set_option maxRecDepth 12000
set_option maxHeartbeats 2700000
attribute [local irreducible] run wires StairArchiveInactive.packet Rolling1588.packet
  surface Rolling1588.allEncodeCut CodecBitSliceVerify.get

private theorem payload_on_surface (j : Nat) (lo : 1 ≤ j) (hi : j ≤ 84) (i : Fin 8) :
    let p := History5.historyMap base (5*j) (NewHistory5.payloadPort i)
    wire p ∈ surface ∧ wire p ≠ base 720 := by
  let p := History5.historyMap base (5*j) (NewHistory5.payloadPort i)
  have mem : wire p ∈ signPayload :=
    List.mem_flatMap.mpr ⟨j, List.mem_range'_1.mpr ⟨lo, by omega⟩,
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩
  have hne : wire p ≠ base 720 := by
    have band := WindowFieldCosts.signPayload_band (wire p) mem
    unfold WindowFieldCosts.signPayloadBand at band
    intro eq
    rw [eq] at band
    norm_num [MappedCompressed.base] at band
  have hfix : shifted (Placement5.pi j) p = p := by
    change shifted (Placement5.pi j) (base (History5.historyId (5*j) (NewHistory5.payloadPort i))) =
      base (History5.historyId (5*j) (NewHistory5.payloadPort i))
    rw [shifted_base, Placement5.pi_outside j _ (by omega)]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      History5.historyId NewHistory5.payloadPort
    have h := i.isLt
    dsimp only
    by_cases small : i.val < 5
    · rw [if_pos small]; split <;> omega
    · rw [if_neg small]; split <;> omega
  refine ⟨?_,hne⟩
  rw [surface]
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_Icc.mpr ⟨lo,hi⟩,Finset.mem_union_right _ ?_⟩
  have original : packet true j =
      renameProgram host (renameProgram (OB5.sig 511) (Rolling1588.packet true j)) := by
    rw [packet, hosts_eq, StairGroups.packet_zero]; rfl
  rw [original, renameProgram_support]
  refine Finset.mem_image.mpr ⟨OB5.sig 511 p, ?_, rfl⟩
  rw [renameProgram_support]
  refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
  have hbridge : ∀ v : Fin 8, (NewHistory5.payloadPort v).val ∈ wires Rolling1588.bridge7 := by
    decide +kernel
  have hbase : p ∈ wires (Rolling1588.onPacket j Rolling1588.bridge7) := by
    rw [Rolling1588.onPacket, renameProgram_support]
    exact Finset.mem_image.mpr ⟨(NewHistory5.payloadPort i).val, hbridge i,
      by simp [p, MeasuredCodec5.label]⟩
  rw [Rolling1588.packet, renameProgram_support]
  refine Finset.mem_image.mpr ⟨p, ?_, hfix⟩
  simp only [Rolling1588.basePacket, if_true, wires_append, Finset.mem_union]
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hbase))))))

private theorem cut_packet_parity_odd (c x j : Nat) (lo : 1 ≤ j) (hi : j ≤ 84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (tr : TraceOK x origin) (r : State) (hcut : OCut c origin r) :
    TraceParity5.xorRange 8 (fun i => r.basis (wire (NewHistory5.payloadWire base (8*j+i)))) =
      TraceParity5.xorRange 5 (fun i => TraceParity5.rawS x (5*j+i)) := by
  obtain ⟨_, X, Y, ideal, cf, tracked⟩ := hcut
  obtain ⟨raw, _, pair, encoded⟩ := cf
  have rawLegal := NewHistory5.frame_history_legal base (base 2409) ctx.hn
    (ctx.hp _ (by simp)) 102 (by decide) origin raw.basis _ _ tr.2.2.2 pair
  have h := StairField2V3LastRecXPar.cut_packet_parity base c base_pool_nodup 102 j
    (by decide) (by omega) raw rawLegal
  rw [← encoded] at h
  refine Eq.trans ?_ (h.trans ?_)
  · apply TraceParity5.xorRange_congr
    intro i hi'
    rw [NewHistory5.payloadWire_packet base j i hi']
    have z := payload_on_surface j lo hi ⟨i,hi'⟩
    exact tracked _ z.1 z.2
  · apply TraceParity5.xorRange_congr
    intro i hi'
    have away := History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
      (5*j) (by omega) ⟨2*i+1, by omega⟩
    rw [StairField2V3LastRecXPar.history_sign base (5*j) i hi'] at away
    rw [pair.2.2 _ away.1 away.2,
      show 1028+5*j+i = 1028+(5*j+i) by omega,
      StairField2V3LastRecXPar.rawS_origin x origin tr (5*j+i) (by omega)]

private theorem signPayload_wire_shape :
    signPayload = (List.range' 8 672).map (fun i => wire (NewHistory5.payloadWire base i)) :=
  WindowFieldCosts.signPayload_hosted_shape

theorem ocut_signPayload_parity (c x : Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (r : State) (hcut : OCut c origin r) :
    TraceParity5.parity (signPayload.map r.basis) =
      TraceParity5.xorRange 84 (fun j => TraceParity5.xorRange 5
        (fun i => TraceParity5.rawS x (5*(j+1)+i))) := by
  simp only [signPayload_wire_shape, List.range'_eq_map_range, List.map_map, Function.comp_def,
    TraceParity5.parity_range]
  rw [show (672 : Nat) = 84*8 from rfl, TraceParity5.xorRange_group]
  apply TraceParity5.xorRange_congr
  intro j hj
  have h := cut_packet_parity_odd c x (j+1) (by omega) (by omega) origin ctx tr r hcut
  rw [← h]
  apply TraceParity5.xorRange_congr
  intro i hi
  rw [show 8 + (8*j+i) = 8*(j+1)+i by omega]

private def parityBlock : Leg → List Wire
  | .native j n => (List.range' j n).flatMap pkSitesOf
  | .paired j => (List.range 16).map (fieldPort j)

private def parityPacketSites (start : Nat) : List Wire :=
  [StairPhysicalLayout.letterSite start, StairPhysicalLayout.sLetter start,
   StairPhysicalLayout.letterSite (start+1), StairPhysicalLayout.sLetter (start+1),
   StairPhysicalLayout.letterSite (start+2), StairPhysicalLayout.letterSite (start+3),
   StairPhysicalLayout.sLetter (start+3), StairPhysicalLayout.letterSite (start+4)]

private theorem parity_packet_sites (j : Nat) (lo : 1 ≤ j) (hi : j ≤ 84) :
    pkSitesOf j = parityPacketSites (5*j) := by
  have hosted : pkSitesOf j = (List.finRange 8).map (fun i =>
      OB5.sig 511 (History5.historyMap base (5*j) (NewHistory5.payloadPort i))) := by
    unfold pkSitesOf
    exact List.map_congr_left fun i _ =>
      WindowFieldCosts.signPayload_host_fix j (List.mem_range'_1.mpr ⟨lo, by omega⟩) i
  have letter (k : Nat) (hk : k < 5) :
      OB5.sig 511 (base (5*j+k)) = StairPhysicalLayout.letterSite (5*j+k) := by
    have away : ¬ ((1285 ≤ 5*j+k ∧ 5*j+k ≤ 1028+511) ∨
        (2053 ≤ 5*j+k+511 ∧ 5*j+k ≤ 1796)) := by omega
    have endpoint : 5*j+k ≠ 511 := by omega
    rw [OB5.sig_base 511 _ (by decide), if_neg away, StairPhysicalLayout.letterSite, if_neg endpoint]
  have first : OB5.sig 511 (base (5*j)) = StairPhysicalLayout.letterSite (5*j) :=
    letter 0 (by decide)
  rw [hosted]
  change [OB5.sig 511 (base (5*j)), StairPhysicalLayout.sLetter (5*j),
    OB5.sig 511 (base (5*j+1)), StairPhysicalLayout.sLetter (5*j+1),
    OB5.sig 511 (base (5*j+2)), OB5.sig 511 (base (5*j+3)),
    StairPhysicalLayout.sLetter (5*j+3), OB5.sig 511 (base (5*j+4))] = parityPacketSites (5*j)
  rw [first, letter 1 (by decide), letter 2 (by decide), letter 3 (by decide), letter 4 (by decide)]
  rfl

private theorem parity_paired_sites (j : Nat) (lo : 1 ≤ j) (hi : j+1 ≤ 84) :
    parityBlock (.paired j) = (List.range' j 2).flatMap pkSitesOf := by
  have packets : ArchiveFieldScratch.packetSites j =
      parityPacketSites (5*j) ++ parityPacketSites (5*(j+1)) := by
    simpa only [Nat.mul_succ] using (show ArchiveFieldScratch.packetSites j =
      parityPacketSites (5*j) ++ parityPacketSites (5*j+5) from rfl)
  have size : (ArchiveFieldScratch.packetSites j).length = 16 :=
    (congrArg List.length packets).trans rfl
  have fields : (List.range 16).map (fieldPort j) = ArchiveFieldScratch.packetSites j := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, size]
    · intro q hq hs
      rw [List.getElem_map, List.getElem_range]
      change ((ArchiveFieldScratch.packetSites j ++
        (base 720 :: ArchiveFieldScratch.indices.map ArchiveFieldScratch.hole))[q]?).getD q =
        (ArchiveFieldScratch.packetSites j)[q]
      rw [List.getElem?_append_left hs, List.getElem?_eq_getElem hs]
      rfl
  calc
    parityBlock (.paired j) = ArchiveFieldScratch.packetSites j := fields
    _ = parityPacketSites (5*j) ++ parityPacketSites (5*(j+1)) := packets
    _ = pkSitesOf j ++ pkSitesOf (j+1) :=
      congrArg₂ List.append (parity_packet_sites j lo (by omega)).symm
        (parity_packet_sites (j+1) (by omega) hi).symm
    _ = (List.range' j 2).flatMap pkSitesOf := by
      simp only [List.range'_succ, List.range'_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil]

private theorem parity_block_shape : (plan true).flatMap parityBlock = signPayload := by
  have schedule : (plan true).flatMap (fun l => List.range' (span l).1 (span l).2) =
      List.range' 1 84 := by decide +kernel
  have paired : (plan true).all (fun l => match l with
      | .native _ _ => true
      | .paired j => decide (1 ≤ j ∧ j+1 ≤ 84)) = true := by decide +kernel
  calc
    (plan true).flatMap parityBlock =
        ((plan true).flatMap (fun l => List.range' (span l).1 (span l).2)).flatMap pkSitesOf := by
      rw [List.flatMap_assoc]
      apply List.flatMap_congr
      intro l mem
      cases l with
      | native j n => rfl
      | paired j =>
        have b : 1 ≤ j ∧ j+1 ≤ 84 :=
          of_decide_eq_true (List.all_eq_true.mp paired (.paired j) mem)
        exact parity_paired_sites j b.1 b.2
    _ = signPayload := by rw [schedule, signPayload]

private theorem parity_append (xs ys : List Bool) :
    TraceParity5.parity (xs ++ ys) =
      (TraceParity5.parity xs ^^ TraceParity5.parity ys) := by
  induction xs with
  | nil => simp [TraceParity5.parity]
  | cons x xs ih => simp [TraceParity5.parity, ih]

private theorem bank_lookup (q : Wire) (mem : q ∈ allBanks) :
    q ∈ WindowBankCheck.banks.flatMap (fun j => (List.range 16).map (fieldPort j)) := by
  obtain ⟨j, hj, hq⟩ := Finset.mem_biUnion.mp mem
  have list : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  exact List.mem_flatMap.mpr ⟨j,list,List.mem_map.mpr ⟨i,
    List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩⟩

private theorem native_parity_avoids (j n : Nat) (inPlan : Leg.native j n ∈ plan true) :
    ∀ q ∈ parityBlock (.native j n), q ∉ allBanks := by
  let bankSites := WindowBankCheck.banks.flatMap (fun b => (List.range 16).map (fieldPort b))
  have check : (plan true).all (fun l => match l with
    | .native j n => (parityBlock (.native j n)).all
        (fun q => !(WindowBankCheck.maskOf bankSites).testBit q)
    | .paired _ => true) = true := by decide +kernel
  have native := List.all_eq_true.mp check (.native j n) inPlan
  intro q hq hm
  have off := List.all_eq_true.mp native q hq
  rw [WindowBankCheck.maskOf_testBit] at off
  simp [bankSites, bank_lookup q hm] at off

private theorem parity_column (cs : Cols) (row : Nat) :
    TraceParity5.parity ((List.range 16).map (fun i => (get cs i).testBit row)) =
      (WindowFieldParity.parity cs).testBit row := by
  have fold (xs : List Nat) : TraceParity5.parity (xs.map (fun n => n.testBit row)) =
      (xs.foldr (· ^^^ ·) 0).testBit row := by
    induction xs with
    | nil => simp [TraceParity5.parity]
    | cons x xs ih => simp [TraceParity5.parity, ih, Nat.testBit_xor]
  rw [WindowFieldParity.parity]
  simpa only [List.map_map, Function.comp_def] using fold ((List.range 16).map (get cs))

private theorem parity_join (ls : List Leg) (a r : State)
    (same : ∀ l ∈ ls, TraceParity5.parity ((parityBlock l).map a.basis) =
      TraceParity5.parity ((parityBlock l).map r.basis)) :
    TraceParity5.parity ((ls.flatMap parityBlock).map a.basis) =
      TraceParity5.parity ((ls.flatMap parityBlock).map r.basis) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.flatMap_cons, List.map_append, parity_append]
    rw [same l (by simp), ih (fun k hk => same k (List.mem_cons_of_mem _ hk))]

theorem fits_signPayload_parity (d : Bool) (rows : Nat → Nat) (code : Nat → Cols)
    (a r : State) (h : Fits rows code a r)
    (codeShape : ∀ j ∈ bankIds, (code j).take 16 = (ArchivePortAction.code d).take 16)
    (reference : ∀ j ∈ bankIds, frame j (rows j) (StairArchiveNativeCut.canonical d d) r) :
    TraceParity5.parity (signPayload.map a.basis) = TraceParity5.parity (signPayload.map r.basis) := by
  rw [← parity_block_shape]
  apply parity_join
  intro l member
  cases l with
  | native j n =>
    exact congrArg TraceParity5.parity
      (List.map_congr_left (fun q hq => h.outside q (native_parity_avoids j n member q hq)))
  | paired j =>
    have incl : (plan true).all (fun l => match l with
        | .native _ _ => true
        | .paired j => decide (j ∈ bankIds)) = true := by decide +kernel
    have hj : j ∈ bankIds := of_decide_eq_true (List.all_eq_true.mp incl (.paired j) member)
    have ha : ((parityBlock (.paired j)).map a.basis) =
        (List.range 16).map (fun i => (get (ArchivePortAction.code d) i).testBit (rows j)) := by
      simp only [parityBlock, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro i hi
      have i_lt := List.mem_range.mp hi
      exact (h.bytes j hj i (Finset.mem_range.mpr i_lt)).trans
        (StairArchiveHandoff.wires_eq _ _ 16 (codeShape j hj) i _ i_lt)
    have hr : ((parityBlock (.paired j)).map r.basis) =
        (List.range 16).map (fun i => (CodecBitSliceVerify.get (StairArchiveNativeCut.canonical d d) i).testBit (rows j)) := by
      simp only [parityBlock, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro i hi
      exact reference j hj i (Finset.mem_range.mpr (by have := List.mem_range.mp hi; omega))
    rw [ha, hr, parity_column, parity_column, WindowFieldParity.matchedParity d]

theorem initial_signCode (d : Bool) (j : Nat) :
    (initialCode d j).take 16 = (ArchivePortAction.code d).take 16 := by
  symm
  cases d
  · simpa only [ArchivePortAction.code,List.take_take,Nat.min_self] using StairArchiveHandoff.archive_edges.2.1
  · simpa only [ArchivePortAction.code,List.take_take,Nat.min_self] using StairArchiveHandoff.archive_edges.1

theorem final_signCode (d : Bool) (j : Nat) (hj : j ∈ bankIds) :
    (finalCode d (plan d) (initialCode d) j).take 16 = (ArchivePortAction.code (!d)).take 16 := by
  have state : (finalCode d (plan d) (initialCode d) j).take 16 =
      (outputCols (leave (!d))).take 16 := by
    simp only [bankIds, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> cases d <;> rfl
  rw [state]
  cases d
  · exact StairArchiveHandoff.archive_edges.2.2.2.2.2.2.2.trans (initial_signCode true j)
  · exact StairArchiveHandoff.archive_edges.2.2.2.2.2.2.1.trans (initial_signCode false j)

theorem ocut_signFrames (d : Bool) (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (r : State) (hcut : OCut (if d then 1 else 85) origin r) :
    ∀ j ∈ bankIds, frame j (rows j) (StairArchiveNativeCut.canonical d d) r := by
  intro j hj
  have geom := List.mem_range'_1.mp (geometry hj).2
  have shape : boundaryCols j (if d then 1 else 85) = StairArchiveNativeCut.canonical d d := by
    cases d
    · simp [boundaryCols, show ¬85 ≤ j by omega, show ¬85 ≤ j+1 by omega]
    · simp [boundaryCols, show 1 ≤ j by omega, show 1 ≤ j+1 by omega]
  rw [← shape]
  exact osee j _ x (rows j) hj (rb j hj) origin ctx tr (history j hj) r hcut

end ECDSAAdd.Entrant.StairPacket.WindowFieldView


section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView

open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
open StairArchiveRelease CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires measurementCount group84Body group84SignBody
  packTag unpackTag tagSwap ogroup oreferenceProgram oreferenceTape planBody

private def signedTagView (a : State) : State :=
  ⟨a.phase, fun q => a.basis (tagPort q)⟩

private theorem signedTagPool (a : State) (m : List Bool) :
    (run packTag m a).phase = (run TagPack1542.packTagProg m (signedTagView a)).phase ∧
    ∀ i ∈ Finset.range 105, (run packTag m a).basis (tagPort i) =
      (run TagPack1542.packTagProg m (signedTagView a)).basis i := by
  have program_eq : packTag = renameProgram tagPort TagPack1542.packTagProg := by
    simp only [packTag]
  have placed := run_rename_pool tagPort (Finset.range 105) tagPort_inj TagPack1542.packTagProg
    (fun i hi => Finset.mem_range.mpr (TagPack1542.packTagProg_wires_lt i hi))
    m (signedTagView a) a rfl (fun _ _ => rfl)
  have state_eq := congrArg (fun p : Program => run p m a) program_eq
  exact ⟨(congrArg State.phase state_eq).trans placed.1,
    fun i hi => (congrArg (fun s : State => s.basis (tagPort i)) state_eq).trans (placed.2 i hi)⟩

private theorem signedTagReads (a : State) (m : List Bool)
    (hc : TagPack1542.cVal (signedTagView a) < 87)
    (hp0 : TagPack1542.p0Val (signedTagView a) ∈ TagPack1542.used7)
    (hpk : ∀ k < 9, TagPack1542.pkVal k (signedTagView a) ∈ TagPack1542.used8)
    (hanc : ∀ i, 86 ≤ i → i < 105 → (signedTagView a).basis i = false) :
    (run packTag m a).phase = a.phase ∧
    (run packTag m a).basis (StairPhysicalLayout.sLetter 435) = false ∧
    ∀ i, 86 ≤ i → i < 105 → (run packTag m a).basis (tagPort i) = false := by
  have placed := signedTagPool a m
  have spec := TagPack1542.packTag_spec (signedTagView a) m hc hp0 hpk hanc
  have port6 : tagPort 6 = StairPhysicalLayout.sLetter 435 := by decide +kernel
  have cleared := (placed.2 6 (by decide)).trans spec.2.1
  exact ⟨placed.1.trans spec.1,
    (congrArg (fun q => (run packTag m a).basis q) port6.symm).trans cleared,
    fun i lo hi => (placed.2 i (Finset.mem_range.mpr hi)).trans (spec.2.2.1 i lo hi)⟩

private theorem maskedPull_phase (sites : Finset Wire) (r a : State) (f : Wire → Wire) :
    (mask sites r (pullState f a)).phase = a.phase := rfl

private theorem signBody_after_nine (d : Bool) :
    ∀ l ∈ planBody d, 10 ≤ (span l).1 := by
  have checks : (planBody d).all (fun l => decide (10 ≤ (span l).1)) = true := by
    cases d <;> decide +kernel
  exact fun l h => of_decide_eq_true (List.all_eq_true.mp checks l h)

/-- Compare the outputs on the masked state and use unchanged bits on the mask. -/
private theorem signRuns_eq_of_mask (P Q : Program) (sites : Finset Wire)
    (m n : List Bool) (archive start : State) (p : avoids P sites) (q : avoids Q sites)
    (equal : run P m (mask sites archive start) = run Q n (mask sites archive start)) :
    run P m start = run Q n start := by
  have masked : mask sites archive (run P m start) = mask sites archive (run Q n start) :=
    (mask_run P sites m archive start p).symm.trans (equal.trans (mask_run Q sites n archive start q))
  apply State.extensionality
  · have phase : (mask sites archive (run P m start)).phase =
        (mask sites archive (run Q n start)).phase := congrArg State.phase masked
    exact phase
  · funext wire
    by_cases hit : wire ∈ sites
    · rw [run_preserves_outside _ _ _ _ (p wire hit),
        run_preserves_outside _ _ _ _ (q wire hit)]
    · simpa only [mask, hit, ↓reduceIte] using congrArg (fun s : State => s.basis wire) masked

/-- Compare the two bodies after tag packing. The mask represents the restored
    values on ports that both bodies avoid. -/
private theorem signPacked_body_eq (d : Bool) (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (mPack mBody : List Bool) (a0 r0 : State) (c0 : Nat → Cols)
    (hvalid : valid d (planBody d) c0)
    (hroute : path d (if d then 10 else 85) (planBody d))
    (initial : Fits rows c0 a0 r0) (start : OCut (if d then 10 else 85) origin r0)
    (htag : TagReady r0) (hclear : a0.basis signHost = false) :
    run (group84SignBody d) mBody (pullState tagSwap (run packTag mPack a0)) =
      run (group84Body d) (signOldBodyTape d (planBody d) mBody)
        (pullState tagSwap (run packTag mPack a0)) := by
  let s0 : State := ⟨a0.phase, fun q => a0.basis (tagPort q)⟩
  have hagree_a0_r0 : ∀ i < 105, a0.basis (tagPort i) = r0.basis (tagPort i) := by
    intro i hi
    have hmem : tagPort i ∈ tagSites := by
      have lt : i < tagSites.length := tagSites_length ▸ hi
      simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
    exact initial.outside _ (tagSites_disjoint_allBanks _ hmem)
  have hreg_map : ∀ (xs : List Nat) (ys : List Wire),
      xs.map tagPort = ys → (∀ i ∈ xs, i < 105) →
      regValue xs s0.basis = regValue ys r0.basis := by
    intro xs ys hmap hlt
    subst hmap
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, regValue, List.foldr_cons, s0]
      rw [hagree_a0_r0 x (hlt x List.mem_cons_self)]
      have htail := ih (fun i hi => hlt i (List.mem_cons_of_mem _ hi))
      simp only [regValue, s0] at htail
      rw [htail]
  have hc0 : TagPack1542.cVal s0 < 87 := by
    have heq : TagPack1542.cVal s0 = regValue rest87A r0.basis :=
      hreg_map TagPack1542.cWires rest87A (by decide +kernel) (by decide)
    rw [heq]; exact htag.1
  have hp0 : TagPack1542.p0Val s0 ∈ TagPack1542.used7 := by
    have heq : TagPack1542.p0Val s0 = regValue p0Sites r0.basis :=
      hreg_map TagPack1542.p0Wires p0Sites (by decide +kernel) (by decide)
    rw [heq]; exact htag.2
  have hpk0 : ∀ k < 9, TagPack1542.pkVal k s0 ∈ TagPack1542.used8 := by
    intro k hk
    have hmap_k : (TagPack1542.pkWires k).map tagPort = pkSitesOf (k + 1) := by
      have hchk : (List.range 9).all (fun k' =>
          (TagPack1542.pkWires k').map tagPort == pkSitesOf (k' + 1)) = true := by
        decide +kernel
      exact beq_iff_eq.mp (List.all_eq_true.mp hchk k (List.mem_range.mpr hk))
    have heq : TagPack1542.pkVal k s0 = regValue (pkSitesOf (k + 1)) r0.basis :=
      hreg_map (TagPack1542.pkWires k) (pkSitesOf (k + 1)) hmap_k (fun i hi => by
        simp only [TagPack1542.pkWires, TagPack1542.pkWire, List.mem_cons, List.not_mem_nil, or_false] at hi
        omega)
    rw [heq]
    exact ocut_pk_in_used8 (if d then 10 else 85) (by cases d <;> decide) origin ctx tr r0 start k hk
  have hanc0 : ∀ a, 86 ≤ a → a < 105 → s0.basis a = false := by
    intro a ha1 ha2
    exact (hagree_a0_r0 a (by omega)).trans (ocut_anc_zero _ origin ctx r0 start a ha1 ha2)
  obtain ⟨ha1_ph, ha1_435, ha1_anc⟩ :=
    signedTagReads a0 mPack hc0 hp0 hpk0 hanc0
  have ha1_out : ∀ w, w ∉ tagSites → (run packTag mPack a0).basis w = a0.basis w := fun w hw =>
    run_preserves_outside packTag mPack a0 w (fun hm => by
      rw [packTag, renameProgram_support] at hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      have lt : i < tagSites.length := tagSites_length ▸ TagPack1542.packTagProg_wires_lt i hi
      exact hw (by simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]))
  let a1' := pullState tagSwap (run packTag mPack a0)
  let tagDataSet : Finset Wire := (tagSites.take 86).toFinset
  have hbody_avoids_tagData : avoids (group84Body d) tagDataSet := by
    intro q hq
    rw [List.mem_toFinset] at hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have hi86 : i < 86 := by have := List.length_take_le 86 tagSites; omega
    have hget : (tagSites.take 86)[i] = tagPort i := by
      have lt : i < tagSites.length := by rw [tagSites_length]; omega
      simp [tagPort, List.getElem_take, List.getElem?_eq_getElem lt]
    rw [hget]
    exact tagData_avoids_group84Body d i hi86
  let a1m := mask tagDataSet r0 a1'
  have hfits_m : Fits rows c0 a1m r0 := by
    refine ⟨?_, ?_, ?_⟩
    · exact (maskedPull_phase tagDataSet r0 (run packTag mPack a0) tagSwap).trans
        (ha1_ph.trans initial.phase)
    · intro q hq
      by_cases hqm : q ∈ tagDataSet
      · simp [a1m, mask, hqm]
      · simp only [a1m, mask, hqm, ↓reduceIte]
        change (run packTag mPack a0).basis (tagSwap q) = r0.basis q
        by_cases hq720 : q = base 720
        · subst hq720; simp [tagSwap, ha1_435, start.1]
        · have hq435 : q ≠ StairPhysicalLayout.sLetter 435 := by
            intro h; exact hqm (h ▸ (by decide +kernel : StairPhysicalLayout.sLetter 435 ∈ tagDataSet))
          rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hq720 hq435]
          by_cases hqt : q ∈ tagSites
          · -- `q ∈ tagSites` and `q ∉ tagSites.take 86`, so `q = tagPort i` with `86 ≤ i < 105` (ancilla)!
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hqt
            have hi105 : i < 105 := tagSites_length ▸ hi
            have hi86 : 86 ≤ i := by
              by_contra! hlt
              exact hqm (List.mem_toFinset.mpr (List.mem_iff_getElem.mpr ⟨i, by rw [List.length_take, tagSites_length]; omega, by simp [List.getElem_take]⟩))
            have hget : tagSites[i] = tagPort i := by simp [tagPort, List.getElem?_eq_getElem hi]
            rw [hget, ha1_anc i hi86 hi105, ocut_anc_zero _ origin ctx r0 start i hi86 hi105]
          · exact (ha1_out q hqt).trans (initial.outside q hq)
    · intro j hj i hi
      have hmem_b : StairArchiveRelease.fieldPort j i ∈ allBanks :=
        Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
      have hnt : StairArchiveRelease.fieldPort j i ∉ tagSites :=
        fun ht => tagSites_disjoint_allBanks _ ht hmem_b
      have hnm : StairArchiveRelease.fieldPort j i ∉ tagDataSet := fun hm =>
        hnt (List.take_subset 86 tagSites (List.mem_toFinset.mp hm))
      have hn720 : StairArchiveRelease.fieldPort j i ≠ base 720 := by
        have jm : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
        simpa using List.all_eq_true.mp (List.all_eq_true.mp fieldPort_ne720_chk j jm) i (List.mem_range.mpr (Finset.mem_range.mp hi))
      have hn435 : StairArchiveRelease.fieldPort j i ≠ StairPhysicalLayout.sLetter 435 :=
        fun h => hnt (h ▸ (by decide +kernel : StairPhysicalLayout.sLetter 435 ∈ tagSites))
      simp only [a1m, mask, hnm, ↓reduceIte]
      change (run packTag mPack a0).basis (tagSwap (StairArchiveRelease.fieldPort j i)) = _
      rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hn720 hn435, ha1_out _ hnt]
      exact initial.bytes j hj i hi
  have noSign : signHost ∉ tagSites := by decide +kernel
  have noSignMask : signHost ∉ tagDataSet :=
    fun h => noSign (List.take_subset 86 tagSites (List.mem_toFinset.mp h))
  have hclear_masked : a1m.basis signHost = false := by
    simp only [a1m, mask, noSignMask, ↓reduceIte]
    change (run packTag mPack a0).basis (tagSwap signHost) = false
    rw [tagSwap_signHost, ha1_out _ noSign, hclear]
  have ha := signTravel_eq d x rows rb origin ctx en tr history (planBody d) _ hroute
    (signBody_after_nine d) c0 hvalid mBody a1m r0 hfits_m start hclear_masked
  rw [← signEmits_body, ← oemits_body] at ha
  have hbody_sign_avoids : avoids (group84SignBody d) tagDataSet := by
    intro q hq use
    rcases Finset.mem_insert.mp (signBody_sub d use) with rfl | old
    · exact noSignMask hq
    · exact hbody_avoids_tagData q hq old
  exact signRuns_eq_of_mask (group84SignBody d) (group84Body d) tagDataSet
    mBody (signOldBodyTape d (planBody d) mBody) r0 a1' hbody_sign_avoids hbody_avoids_tagData ha

private def signTagCore (body : Program) : Program :=
  packTag ++ renameProgram tagSwap body ++ unpackTag

private def oldTagTape (d : Bool) (m : List Bool) : List Bool :=
  let mb := m.drop (measurementCount packTag)
  let mu := mb.drop (measurementCount (group84SignBody d))
  joinTapes packTag m (joinTapes (group84Body d) (signOldBodyTape d (planBody d) mb)
    (mu.take (measurementCount unpackTag)))

private theorem signTagCore_split (body : Program) (m : List Bool) (a : State) :
    run (signTagCore body) m a =
      run unpackTag ((m.drop (measurementCount packTag)).drop (measurementCount body))
        (run (renameProgram tagSwap body) (m.drop (measurementCount packTag)) (run packTag m a)) := by
  simp only [signTagCore, List.append_assoc, run_append, run_take]
  rw [(renameProgram_counts tagSwap body).2]

private theorem signTagCore_joined (body : Program) (mp mb mu : List Bool) (a : State) :
    run (signTagCore body) (joinTapes packTag mp (joinTapes body mb mu)) a =
      run unpackTag mu (run (renameProgram tagSwap body) mb (run packTag mp a)) := by
  rw [signTagCore, List.append_assoc, joined]
  have count := (renameProgram_counts tagSwap body).2
  rw [show joinTapes body mb mu = joinTapes (renameProgram tagSwap body) mb mu by
    simp only [joinTapes, count], joined]

/-- Keep the true pack, body and unpack tape boundaries. The old body's padded
    tape is used only for the old program. -/
theorem othree_body_sign_bracket (d : Bool) (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a0 r0 : State) (c0 : Nat → Cols)
    (hvalid : valid d (planBody d) c0)
    (hroute : path d (if d then 10 else 85) (planBody d))
    (initial : Fits rows c0 a0 r0) (start : OCut (if d then 10 else 85) origin r0)
    (htag : TagReady r0) (hclear : a0.basis signHost = false) :
    run (signTagCore (group84SignBody d)) m a0 =
      run (signTagCore (group84Body d)) (oldTagTape d m) a0 := by
  let mb := m.drop (measurementCount packTag)
  let mu := mb.drop (measurementCount (group84SignBody d))
  have core := signPacked_body_eq d x rows rb origin ctx en tr history m mb a0 r0 c0
    hvalid hroute initial start htag hclear
  have renamed (P : Program) (t : List Bool) :
      run (renameProgram tagSwap P) t (run packTag m a0) =
        pullState tagSwap (run P t (pullState tagSwap (run packTag m a0))) :=
    StairField2V3Seg.rename_conj tagSwap tagSwap.injective
      (fun q => by unfold tagSwap; exact Equiv.swap_apply_self _ _ q) P _ t
  rw [signTagCore_split, oldTagTape, signTagCore_joined, renamed, renamed]
  change run unpackTag mu (pullState tagSwap
    (run (group84SignBody d) mb (pullState tagSwap (run packTag m a0)))) =
    run unpackTag (mu.take (measurementCount unpackTag)) (pullState tagSwap
      (run (group84Body d) (signOldBodyTape d (planBody d) mb) (pullState tagSwap (run packTag m a0))))
  rw [core, run_take]

private def signCore (d : Bool) : Program :=
  ordered d (ogroup d 1 9) (signTagCore (group84SignBody d))

private theorem signTagCore_drop (body : Program) (t : List Bool) :
    t.drop (measurementCount (signTagCore body)) =
      (((t.drop (measurementCount packTag)).drop (measurementCount body)).drop
        (measurementCount unpackTag)) := by
  simp only [signTagCore, measurementCount_append, (renameProgram_counts _ _).2,
    List.drop_drop, Nat.add_assoc]

private theorem signAppendAfter (P Q R : Program) (t b u : List Bool) (a : State)
    (tail : t.drop (measurementCount P) = u)
    (body : run P t a = run Q b a) :
    run (P ++ R) t a = run (Q ++ R) (joinTapes Q b u) a := by
  rw [run_append, run_take, joined, tail, body]

private theorem signAppendBefore (E P Q : Program) (t u b : List Bool) (a a1 : State)
    (tape : t.drop (measurementCount E) = u) (early : run E t a = a1)
    (body : run P u a1 = run Q b a1) :
    run (E ++ P) t a = run (E ++ Q) (joinTapes E t b) a := by
  rw [run_append, run_take, joined, tape, early, body]

private theorem signTransportRun (P A Q B : Program) (m n k : List Bool) (a : State)
    (left : P = A) (right : Q = B) (tape : n = k)
    (inner : run A m a = run B k a) : run P m a = run Q n a :=
  (congrArg (fun X => run X m a) left).trans
    (inner.trans ((congrArg₂ (fun X t => run X t a) right tape).symm))


private theorem signCore_matches_false (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode false) a r)
    (start : OCut (if false then 1 else 85) origin r) (htag : TagReady r)
    (hclear : a.basis signHost = false) :
    run (signCore false) (m.drop (measurementCount signBracket)) a =
      run (group84 false) (signOldGroupTape false m) a := by
  let t := m.drop (measurementCount signBracket)
  let P := signTagCore (group84SignBody false)
  let P' := signTagCore (group84Body false)
  let R := ogroup false 1 9
  let u := (((t.drop (measurementCount packTag)).drop (measurementCount (group84SignBody false))).drop
    (measurementCount unpackTag))
  have drop_eq : t.drop (measurementCount P) = u := signTagCore_drop (group84SignBody false) t
  have body := othree_body_sign_bracket false x rows rb origin ctx en tr history t a r (initialCode false)
    valid_plan_false_split.1 route_plan_false_body initial start htag hclear
  have lp : signCore false = P ++ R := rfl
  have rp : group84 false = P' ++ R := rfl
  have tp : signOldGroupTape false m = joinTapes P' (oldTagTape false t) u := rfl
  exact signTransportRun _ _ _ _ t _ _ a lp rp tp
    (signAppendAfter P P' R t (oldTagTape false t) u a drop_eq body)


private def forwardBodyEq (m : List Bool) (a : State) : Prop :=
  let t := m.drop (measurementCount signBracket)
  let early := ogroup true 1 9
  let mt := t.drop (measurementCount early)
  let a1 := run early t a
  run (signTagCore (group84SignBody true)) mt a1 =
    run (signTagCore (group84Body true)) (oldTagTape true mt) a1

private def forwardJoinEq (m : List Bool) (a : State) : Prop :=
  let t := m.drop (measurementCount signBracket)
  let early := ogroup true 1 9
  run (early ++ signTagCore (group84SignBody true)) t a =
    run (early ++ signTagCore (group84Body true))
      (joinTapes early t (oldTagTape true (t.drop (measurementCount early)))) a

private def coreRunEq (d : Bool) (m : List Bool) (a : State) : Prop :=
  run (signCore d) (m.drop (measurementCount signBracket)) a =
    run (group84 d) (signOldGroupTape d m) a


set_option linter.unusedVariables false in
private theorem forwardBodyRun
    (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode true) a r)
    (start : OCut (if true then 1 else 85) origin r) (htag : TagReady r)
    (hclear : a.basis signHost = false) : forwardBodyEq m a := by
  let t := m.drop (measurementCount signBracket)
  let early := ogroup true 1 9
  let mt := t.drop (measurementCount early)
  let a1 := run early t a
  let r1 := run early t r
  have valid_all := valid_plan true
  have route_all := route_plan_true
  rw [plan_split_true] at valid_all route_all
  have fits : Fits rows (initialCode true) a1 r1 :=
    plain early rows (initialCode true) t a r initial (ot_groupSafe true 1 9 valid_all.1)
  have cut : OCut 10 origin r1 := by
    simpa only [r1, early, if_true] using oselected true 1 9 (by decide) (by decide) origin ctx en r t start
  have tag : TagReady r1 :=
    tagReady_run_outside early t r (ogroup19_avoids_rest87A_p0 true) htag
  have clear : a1.basis signHost = false :=
    (run_preserves_outside early t a _ (ogroup_avoids_sign true 1 9 (by decide) (by decide))).trans hclear
  have body := othree_body_sign_bracket true x rows rb origin ctx en tr history mt a1 r1
    (initialCode true) valid_all.2 route_all.2.2 fits cut tag clear
  change run (signTagCore (group84SignBody true)) mt a1 =
    run (signTagCore (group84Body true)) (oldTagTape true mt) a1
  exact body


private theorem forwardJoin (m : List Bool) (a : State) (body : forwardBodyEq m a) :
    forwardJoinEq m a := by
  let t := m.drop (measurementCount signBracket)
  let early := ogroup true 1 9
  let mt := t.drop (measurementCount early)
  let a1 := run early t a
  let P := signTagCore (group84SignBody true)
  let P' := signTagCore (group84Body true)
  have bodyRun : run P mt a1 = run P' (oldTagTape true mt) a1 := body
  change run (early ++ P) t a =
    run (early ++ P') (joinTapes early t (oldTagTape true mt)) a
  exact signAppendBefore early P P' t mt (oldTagTape true mt) a a1 rfl rfl bodyRun



private theorem forwardActualProgram :
    signCore true = ogroup true 1 9 ++ signTagCore (group84SignBody true) := by
  simp only [signCore, ordered, if_true]


private theorem forwardReferenceProgram :
    group84 true = ogroup true 1 9 ++ signTagCore (group84Body true) := by
  simp only [group84, signTagCore, ordered, if_true]


private theorem forwardTape (m : List Bool) :
    signOldGroupTape true m = joinTapes (ogroup true 1 9) (m.drop (measurementCount signBracket))
      (oldTagTape true ((m.drop (measurementCount signBracket)).drop
        (measurementCount (ogroup true 1 9)))) := by
  simp only [signOldGroupTape, oldTagTape, if_true]


private theorem runGoalCongr (P A Q B : Program) (m n k : List Bool) (a : State)
    (left : P = A) (right : Q = B) (tape : n = k) :
    (run P m a = run Q n a) = (run A m a = run B k a) := by
  subst A
  subst B
  subst k
  rfl


private theorem forwardGoalEq (m : List Bool) (a : State) :
    coreRunEq true m a = forwardJoinEq m a := by
  unfold coreRunEq forwardJoinEq
  exact runGoalCongr (signCore true) (ogroup true 1 9 ++ signTagCore (group84SignBody true))
    (group84 true) (ogroup true 1 9 ++ signTagCore (group84Body true))
    (m.drop (measurementCount signBracket)) (signOldGroupTape true m)
    (joinTapes (ogroup true 1 9) (m.drop (measurementCount signBracket))
      (oldTagTape true ((m.drop (measurementCount signBracket)).drop
        (measurementCount (ogroup true 1 9)))))
    a forwardActualProgram forwardReferenceProgram (forwardTape m)


private theorem forwardAlign (m : List Bool) (a : State) (joinProof : forwardJoinEq m a) :
    coreRunEq true m a :=
  Eq.mpr (forwardGoalEq m a) joinProof


set_option linter.unusedVariables false in
private theorem forwardCore
    (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (htag : TagReady r) (hclear : a.basis signHost = false) :
    Fits rows (initialCode true) a r → OCut (if true then 1 else 85) origin r → coreRunEq true m a :=
  fun initial start =>
    forwardAlign m a (forwardJoin m a
      (forwardBodyRun x rows rb origin ctx en tr history m a r initial start htag hclear))


private theorem coreCases (d : Bool) (rows : Nat → Nat) (origin : BasisState)
    (m : List Bool) (a r : State)
    (reverse : Fits rows (initialCode false) a r →
      OCut (if false then 1 else 85) origin r → coreRunEq false m a)
    (forward : Fits rows (initialCode true) a r →
      OCut (if true then 1 else 85) origin r → coreRunEq true m a)
    (initial : Fits rows (initialCode d) a r) (start : OCut (if d then 1 else 85) origin r) :
    coreRunEq d m a :=
  (Bool.rec (motive := fun bit =>
    Fits rows (initialCode bit) a r → OCut (if bit then 1 else 85) origin r → coreRunEq bit m a)
    reverse forward d) initial start

private theorem signCore_matches (d : Bool) (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (start : OCut (if d then 1 else 85) origin r) (htag : TagReady r)
    (hclear : a.basis signHost = false) :
    run (signCore d) (m.drop (measurementCount signBracket)) a =
      run (group84 d) (signOldGroupTape d m) a := by
  change coreRunEq d m a
  exact coreCases d rows origin m a r
    (fun startFit startCut =>
      signCore_matches_false x rows rb origin ctx en tr history m a r startFit startCut htag hclear)
    (forwardCore x rows rb origin ctx en tr history m a r htag hclear) initial start

private theorem signHost_outside_surface : signHost ∉ surface := by
  intro h
  have away := (reliable h signHost_ne_tag).2
  have fix : StairArchiveInactive.host.symm signHost = signHost := by decide +kernel
  rw [fix] at away
  exact away (by decide +kernel)

private theorem bank_mem_surface (j : Nat) (hj : j ∈ bankIds) {q : Wire} (hq : q ∈ bank j) :
    q ∈ surface := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨j, hj, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hi
      omega), rfl⟩⟩)

private theorem signHost_outside_banks : signHost ∉ allBanks := by
  intro h
  obtain ⟨j, hj, hq⟩ := Finset.mem_biUnion.mp h
  exact signHost_outside_surface (bank_mem_surface j hj hq)

private theorem bank_bit_not_sign (j i : Nat) (hj : j ∈ bankIds) (hi : i ∈ Finset.range 16) :
    fieldPort j i ≠ signHost :=
  fun eq => signHost_outside_banks (Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨i, hi, eq⟩⟩)

private def signZero (s : State) : State :=
  mask {signHost} ⟨false, fun _ => false⟩ s

private theorem signZero_at (s : State) : (signZero s).basis signHost = false := by
  simp [signZero, mask]

private theorem signZero_off (s : State) (q : Wire) (hq : q ≠ signHost) :
    (signZero s).basis q = s.basis q := by
  simp [signZero, mask, hq]

private theorem signZero_fits {rows : Nat → Nat} {c : Nat → Cols} {a r : State}
    (h : Fits rows c a r) : Fits rows c (signZero a) (signZero r) := by
  refine ⟨h.phase, ?_, ?_⟩
  · intro q hq
    by_cases eq : q = signHost
    · subst q; simp only [signZero_at]
    · simpa only [signZero_off _ _ eq] using h.outside q hq
  · intro j hj i hi
    rw [signZero_off _ _ (bank_bit_not_sign j i hj hi)]
    exact h.bytes j hj i hi

private theorem signZero_cut {c : Nat} {origin : BasisState} {s : State} (h : OCut c origin s) :
    OCut c origin (signZero s) := by
  obtain ⟨zero, X, Y, ideal, frame, view⟩ := h
  refine ⟨?_, X, Y, ideal, frame, ?_⟩
  · exact (signZero_off s _ (Ne.symm signHost_ne_tag)).trans zero
  · intro q hq hne
    rw [signZero_off s q (fun eq => signHost_outside_surface (eq ▸ hq))]
    exact view q hq hne

private theorem sign_not_tag_ready_ports :
    signHost ∉ rest87A ++ p0Sites := by decide +kernel

private theorem signZero_tag (s : State) (h : TagReady s) : TagReady (signZero s) := by
  have eq (q : Wire) (hq : q ∈ rest87A ++ p0Sites) :
      (signZero s).basis q = s.basis q :=
    signZero_off s q (fun e => sign_not_tag_ready_ports (e ▸ hq))
  constructor
  · rw [regValue_congr rest87A _ s.basis (fun q hq => eq q (List.mem_append_left _ hq))]
    exact h.1
  · rw [regValue_congr p0Sites _ s.basis (fun q hq => eq q (List.mem_append_right _ hq))]
    exact h.2

private theorem ref_avoids_tag_ready (d : Bool) (q : Wire) (hq : q ∈ rest87A ++ p0Sites) :
    q ∉ wires (PacketSequence.program d (opk d) 1 84) := by
  have h19 := ogroup19_avoids_rest87A_p0 d q hq
  have hs : tagSites.take 14 = rest87A ++ p0Sites := by decide +kernel
  rw [← hs] at hq
  obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.mp hq
  have hi14 : i < 14 := by have := List.length_take_le 14 tagSites; omega
  have eq : (tagSites.take 14)[i] = tagPort i := by
    have lt : i < tagSites.length := tagSites_length ▸ (by omega : i < 105)
    simp [tagPort, List.getElem_take, List.getElem?_eq_getElem lt]
  rw [eq] at hqi
  have hBody := tagData_avoids_group84Body_ref d i (by omega)
  rw [hqi] at hBody
  cases d
  · rw [href_eq_false, wires_append, Finset.mem_union, not_or]
    exact ⟨hBody, h19⟩
  · rw [href_eq_true, wires_append, Finset.mem_union, not_or]
    exact ⟨h19, hBody⟩

private theorem signedRefProgram (d : Bool) :
    ogroup d 1 84 = PacketSequence.program d (opk d) 1 84 := by
  simp only [ogroup]

private theorem signCutTransport (C : Nat → State → Prop) {i j : Nat} {s t : State}
    (idx : i = j) (view : s = t) (h : C i s) : C j t := by
  subst j
  subst t
  exact h

private theorem signedReferenceEndCut (C : Nat → State → Prop) (d : Bool) (tape : List Bool) (r : State)
    (out : C (if d then 1 + 84 else 1) (run (ogroup d 1 84) tape r)) :
    C (if !d then 1 else 85) (run (PacketSequence.program d (opk d) 1 84) tape r) := by
  have idx : (if d then 1 + 84 else 1) = (if !d then 1 else 85) := by
    cases d <;> decide
  exact signCutTransport C idx (congrArg (fun p : Program => run p tape r) (signedRefProgram d)) out

private theorem ref_avoids_sign (d : Bool) :
    signHost ∉ wires (PacketSequence.program d (opk d) 1 84) := by
  rw [← signedRefProgram d]
  exact ogroup_avoids_sign d 1 84 (by decide) (by decide)

private theorem signZero_run (P : Program) (m : List Bool) (s : State) (avoid : signHost ∉ wires P) :
    run P m (signZero s) = signZero (run P m s) :=
  mask_run P {signHost} m _ s (fun q member => by
    have eq : q = signHost := Finset.mem_singleton.mp member
    exact eq.symm ▸ avoid)

private def signDatum (s : State) : Bool :=
  TraceParity5.parity (signPayload.map s.basis) ^^ prefixParityValue (regValue p0Sites s.basis)

private theorem p0_in_tag (q : Wire) (hq : q ∈ p0Sites) : q ∈ tagSites := by
  have check : p0Sites.all (fun q => tagSites.contains q) = true := by decide +kernel
  exact List.contains_iff_mem.mp (List.all_eq_true.mp check q hq)

private theorem signBracket_admits {rows : Nat → Nat} {c : Nat → Cols} {a r : State}
    {cut : Nat} {origin : BasisState} (ctx : FrontierReplay1591.Context origin)
    (h : Fits rows c a r) (frame : OCut cut origin r) (tag : TagReady r) :
    (∀ i ∈ [0, 5, 9, 10, 11], a.basis (prefixLoanPort i) = false) ∧
      regValue p0Sites a.basis ∈ TagPack1542.used7 := by
  constructor
  · intro i hi
    have index : ∃ k : Fin 19, prefixLoanPort i = tagPort (86 + k.val) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    obtain ⟨k, eq⟩ := index
    have hlt : 86 + k.val < tagSites.length := by rw [tagSites_length]; omega
    have mem : tagPort (86 + k.val) ∈ tagSites := by
      simp only [tagPort, List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_mem]
    rw [eq, h.outside _ (tagSites_disjoint_allBanks _ mem)]
    exact ocut_anc_zero cut origin ctx r frame _ (by omega) (by omega)
  · rw [regValue_congr p0Sites a.basis r.basis
      (fun q hq => h.outside q (tagSites_disjoint_allBanks q (p0_in_tag q hq)))]
    exact tag.2

private theorem signDatum_of_fits {rows : Nat → Nat} {c : Nat → Cols} {a r : State}
    (h : Fits rows c a r)
    (payload : TraceParity5.parity (signPayload.map a.basis) =
      TraceParity5.parity (signPayload.map r.basis)) :
    signDatum a = signDatum r := by
  unfold signDatum
  rw [payload, regValue_congr p0Sites a.basis r.basis
    (fun q hq => h.outside q (tagSites_disjoint_allBanks q (p0_in_tag q hq)))]

private theorem signBracket_zero (s : State) (m : List Bool)
    (clean : ∀ i ∈ [0, 5, 9, 10, 11], s.basis (prefixLoanPort i) = false)
    (used : regValue p0Sites s.basis ∈ TagPack1542.used7)
    (ready : s.basis signHost = signDatum s) :
    run signBracket m s = signZero s := by
  rw [signBracket_run s m clean used]
  change CheckpointSignLoan.flip signHost (signDatum s) s = signZero s
  apply State.extensionality
  · rfl
  · funext q
    by_cases same : q = signHost
    · subst q
      simp [CheckpointSignLoan.flip, writeBit, ← ready, signZero_at]
    · rw [CheckpointSignLoan.flip_off _ _ same, signZero_off _ _ same]

private theorem signZero_datum (s : State) : signDatum (signZero s) = signDatum s := by
  have payload : signPayload.map (signZero s).basis = signPayload.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact signZero_off s q (fun e => signPayload_avoids_sign (e ▸ hq))
  unfold signDatum
  rw [payload, regValue_congr p0Sites (signZero s).basis s.basis
    (fun q hq => signZero_off s q (fun e =>
      sign_not_tag_ready_ports (List.mem_append_right rest87A (e ▸ hq))))]

private theorem restore_fits {rows : Nat → Nat} {c : Nat → Cols} {a r : State}
    (m : List Bool) (h : Fits rows c a (signZero r))
    (clean : ∀ i ∈ [0, 5, 9, 10, 11], a.basis (prefixLoanPort i) = false)
    (used : regValue p0Sites a.basis ∈ TagPack1542.used7)
    (datum : signDatum a = r.basis signHost) :
    Fits rows c (run signBracket m a) r := by
  rw [signBracket_run a m clean used]
  change Fits rows c (CheckpointSignLoan.flip signHost (signDatum a) a) r
  refine ⟨h.phase, ?_, ?_⟩
  · intro q hq
    by_cases same : q = signHost
    · subst q
      have clear := (h.outside signHost signHost_outside_banks).trans (signZero_at r)
      simp [CheckpointSignLoan.flip, writeBit, clear, datum]
    · rw [CheckpointSignLoan.flip_off _ _ same]
      exact (h.outside q hq).trans (signZero_off r q same)
  · intro j hj i hi
    rw [CheckpointSignLoan.flip_off _ _ (bank_bit_not_sign j i hj hi)]
    exact h.bytes j hj i hi

private def signCoreE (d : Bool) : Program :=
  ordered d (egroup d 1 9) (signTagCore (group84SignBody d))

section
attribute [local irreducible] egroup

private theorem signCoreE_true (rows : Nat → Nat) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true)
    (t : List Bool) (a r : State) (initial : Fits rows (initialCode true) a r)
    (start : OCut (if true then 1 else 85) origin r) (hclear : a.basis signHost = false) :
    run (signCoreE true) t a = run (signCore true) (signEarlyTape true t) a := by
  have lp : signCoreE true = egroup true 1 9 ++ signTagCore (group84SignBody true) := by
    simp only [signCoreE, ordered, if_true]
  have tp : signEarlyTape true t =
      joinTapes (ogroup true 1 9) [] (t.drop (measurementCount (egroup true 1 9))) := by
    simp only [signEarlyTape, if_true]
  have early := egroup_run_eq true 1 9 (by decide) (by decide) rows (initialCode true) origin ctx en a r
    t [] initial (by simpa using start) hclear
  have left : run (egroup true 1 9 ++ signTagCore (group84SignBody true)) t a =
      run (signTagCore (group84SignBody true)) (t.drop (measurementCount (egroup true 1 9)))
        (run (egroup true 1 9) t a) := by
    rw [run_append, run_take]
  have right := joined (ogroup true 1 9) (signTagCore (group84SignBody true)) []
    (t.drop (measurementCount (egroup true 1 9))) a
  rw [lp, forwardActualProgram, tp, left, right, early]

private theorem signCoreE_false (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (t : List Bool) (a r : State) (initial : Fits rows (initialCode false) a r)
    (start : OCut (if false then 1 else 85) origin r) (htag : TagReady r)
    (hclear : a.basis signHost = false) :
    run (signCoreE false) t a = run (signCore false) (signEarlyTape false t) a := by
  let P := signTagCore (group84SignBody false)
  let told := oldTagTape false t
  let tref := oreferenceTape false (planBody false)
    ((told.drop (measurementCount packTag)).take (measurementCount (group84Body false)))
  have bodyEq : run P t a = run (signTagCore (group84Body false)) told a :=
    othree_body_sign_bracket false x rows rb origin ctx en tr history t a r (initialCode false)
      valid_plan_false_split.1 route_plan_false_body initial start htag hclear
  have bodyFit : Fits rows (finalCode false (planBody false) (initialCode false)) (run P t a)
      (run (ogroup false 10 75) tref r) := by
    have h : Fits rows (finalCode false (planBody false) (initialCode false))
        (run (packTag ++ renameProgram tagSwap (group84Body false) ++ unpackTag) told a)
        (run (oreferenceProgram false (planBody false)) tref r) :=
      othree_body_bracket false x rows rb origin ctx en tr history told a r (initialCode false)
        valid_plan_false_split.1 route_plan_false_body initial start htag
    rw [orefBody_false_eq] at h
    rw [bodyEq]
    exact h
  have cut : OCut 10 origin (run (ogroup false 10 75) tref r) := by
    simpa using oselected false 10 75 (by decide) (by decide) origin ctx en r tref (by simpa using start)
  have clear2 : (run P t a).basis signHost = false :=
    (bodyFit.outside signHost signHost_outside_banks).trans
      ((run_preserves_outside _ _ _ _ (ogroup_avoids_sign false 10 75 (by decide) (by decide))).trans
        ((initial.outside signHost signHost_outside_banks).symm.trans hclear))
  have early := egroup_run_eq false 1 9 (by decide) (by decide) rows
    (finalCode false (planBody false) (initialCode false)) origin ctx en (run P t a)
    (run (ogroup false 10 75) tref r) (t.drop (measurementCount P)) [] bodyFit (by simpa using cut) clear2
  have lp : signCoreE false = P ++ egroup false 1 9 := rfl
  have rp : signCore false = P ++ ogroup false 1 9 := rfl
  have tp : signEarlyTape false t = joinTapes P t [] := rfl
  have left : run (P ++ egroup false 1 9) t a =
      run (egroup false 1 9) (t.drop (measurementCount P)) (run P t a) := by
    rw [run_append, run_take]
  have right := joined P (ogroup false 1 9) t [] a
  rw [lp, rp, tp, left, right]
  exact early

private theorem signCoreE_matches (d : Bool) (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (t : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (start : OCut (if d then 1 else 85) origin r) (htag : TagReady r)
    (hclear : a.basis signHost = false) :
    run (signCoreE d) t a = run (signCore d) (signEarlyTape d t) a := by
  cases d with
  | false => exact signCoreE_false x rows rb origin ctx en tr history t a r initial start htag hclear
  | true => exact signCoreE_true rows origin ctx en t a r initial start hclear

end

private theorem signGroup_split (d : Bool) (m : List Bool) (a : State) :
    run (group84Sign d) m a =
      let t := m.drop (measurementCount signBracket)
      run signBracket (t.drop (measurementCount (signCoreE d)))
        (run (signCoreE d) t (run signBracket m a)) := by
  change run ((signBracket ++ signCoreE d) ++ signBracket) m a = _
  simp only [List.append_assoc, run_append, run_take]

/-- The signed group has the same endpoint relation as the original runner,
    with the reference tape obtained from the real new measurement boundaries. -/
theorem othree_run_sign (d : Bool) (x : Nat) (rows : Nat → Nat)
    (rb : ∀ j ∈ bankIds, rows j < 63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400) = true) (tr : TraceOK x origin)
    (history : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (start : OCut (if d then 1 else 85) origin r) (htag : TagReady r) (hsign : SignReady r) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84Sign d) m a)
      (run (PacketSequence.program d (opk d) 1 84) (oreferenceTapeSign d m) r) := by
  let ref := PacketSequence.program d (opk d) 1 84
  let tape := oreferenceTapeSign d m
  let a1 := run (signCoreE d) (m.drop (measurementCount signBracket)) (signZero a)
  have startFrames := ocut_signFrames d x rows rb origin ctx tr history r start
  have startDatum := signDatum_of_fits initial
    (fits_signPayload_parity d rows (initialCode d) a r initial (fun j _ => initial_signCode d j) startFrames)
  have aReady : a.basis signHost = signDatum a :=
    (initial.outside signHost signHost_outside_banks).trans ((show r.basis signHost = signDatum r from hsign).trans
      startDatum.symm)
  obtain ⟨aClean, aUsed⟩ := signBracket_admits ctx initial start htag
  have aZero := signBracket_zero a m aClean aUsed aReady
  have zeroFit := signZero_fits initial
  have zeroCut := signZero_cut start
  have zeroTag := signZero_tag r htag
  have hpad : (signPadTape d m).drop (measurementCount signBracket) =
      signEarlyTape d (m.drop (measurementCount signBracket)) :=
    List.drop_left' List.length_replicate
  have core0 := signCore_matches d x rows rb origin ctx en tr history (signPadTape d m) (signZero a) (signZero r)
    zeroFit zeroCut zeroTag (signZero_at a)
  rw [hpad] at core0
  have core : a1 = run (group84 d) (signOldGroupTape d (signPadTape d m)) (signZero a) :=
    (signCoreE_matches d x rows rb origin ctx en tr history (m.drop (measurementCount signBracket))
      (signZero a) (signZero r) zeroFit zeroCut zeroTag (signZero_at a)).trans core0
  have mid := othree_run d x rows rb origin ctx en tr history (signOldGroupTape d (signPadTape d m))
    (signZero a) (signZero r) zeroFit zeroCut zeroTag
  have midFit : Fits rows (finalCode d (plan d) (initialCode d)) a1 (signZero (run ref tape r)) := by
    change Fits rows (finalCode d (plan d) (initialCode d))
      (run (group84 d) (signOldGroupTape d (signPadTape d m)) (signZero a)) (run ref tape (signZero r)) at mid
    rw [← core, signZero_run ref tape r (ref_avoids_sign d)] at mid
    exact mid
  have endCut : OCut (if !d then 1 else 85) origin (run ref tape r) :=
    signedReferenceEndCut (fun c s => OCut c origin s) d tape r
      (oselected d 1 84 (by decide) (by decide) origin ctx en r tape start)
  have endTag := tagReady_run_outside ref tape r (ref_avoids_tag_ready d) htag
  have endZeroCut := signZero_cut endCut
  have endZeroTag := signZero_tag (run ref tape r) endTag
  obtain ⟨endClean, endUsed⟩ := signBracket_admits ctx midFit endZeroCut endZeroTag
  have r1Ready : (run ref tape r).basis signHost = signDatum (run ref tape r) := by
    have sameSign := run_preserves_outside ref tape r signHost (ref_avoids_sign d)
    have sameP0 := regValue_congr p0Sites (run ref tape r).basis r.basis (fun q hq =>
      run_preserves_outside ref tape r q (ref_avoids_tag_ready d q (List.mem_append_right _ hq)))
    have samePayload := (ocut_signPayload_parity _ x origin ctx tr (run ref tape r) endCut).trans
      (ocut_signPayload_parity _ x origin ctx tr r start).symm
    unfold signDatum
    rw [sameSign, sameP0, samePayload]
    exact hsign
  have endFrames := ocut_signFrames (!d) x rows rb origin ctx tr history (signZero (run ref tape r)) endZeroCut
  have endDatum := signDatum_of_fits midFit
    (fits_signPayload_parity (!d) rows (finalCode d (plan d) (initialCode d)) a1 (signZero (run ref tape r))
      midFit (final_signCode d) endFrames)
  have value : signDatum a1 = (run ref tape r).basis signHost :=
    endDatum.trans ((signZero_datum (run ref tape r)).trans r1Ready.symm)
  rw [signGroup_split, aZero]
  exact restore_fits _ midFit endClean endUsed value

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end



end

end
