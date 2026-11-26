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

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts
open Arithmetic MappedCompressed Stair44Resources StairConcreteAssembly StairArchiveInactive
open StairArchiveRelease StairArchiveNativeCut StairArchiveTen StairArchiveGates
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount measurementCount StairGroups.packet
  StairArchiveInactive.packet fieldHook

def distributed (d : Bool) (j n : Nat) :=
  PacketSequence.program d (StairArchiveInactive.packet d) j n
theorem ren (f : Wire → Wire) (a b : Program) : renameProgram f (a++b)=renameProgram f a++renameProgram f b := List.map_append
theorem distribute (d : Bool) (j n : Nat) :
    StairHostsSchedule.hostedGroup hostPlan d 0 j n = distributed d j n := by
  change StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (PacketSequence.program d (StairGroups.packet d 0) j n)) = _
  simp only [hosts_eq,distributed,renameProgram_comp]
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,
      ren,ih,StairArchiveInactive.packet,hosts_eq,renameProgram_comp]

def group (d : Bool) (j n : Nat) := StairHostsSchedule.hostedGroup hostPlan d 0 j n

def ordered (d : Bool) (a b : Program) := if d then a++b else b++a


/-- oddten: packets `1..84` of both kernels run the odd-word cell (`dstart` / `dend` on the division kernel,
`mend` / `mstart` on the multiplication kernel), inside the archive ten-blocks too; packets `85..84` run the
record packets. -/
def oddPk (d : Bool) (k : Nat) : Program :=
  if 1≤k ∧ k<84 then RouteA.Rolling1588.packet d k
  else if k=84 then OddFullPass.P1LifeLoan.packet d 0 84
  else ECDSAAdd.Entrant.Rolling1588.packet d k

/-- packet `k` of the field group, hosted like the record packets. -/
def opk (d : Bool) (k : Nat) : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (oddPk d k))

def ogroup (d : Bool) (j n : Nat) : Program := PacketSequence.program d (opk d) j n
def ofirst (j : Nat) (rev : Bool) := opk (!rev) (if rev then j+1 else j)
def osecond (j : Nat) (rev : Bool) := opk (!rev) (if rev then j else j+1)
/-- dadon's archive ten-block around the field group's own packets `j`, `j+1`. -/
def oten (j : Nat) (rev : Bool) :=
  fieldHook j (enter rev) ++ (ofirst j rev ++ (fieldHook j (shift rev) ++
    (osecond j rev ++ fieldHook j (leave rev))))

/-- Swap replacing `base 720` with `sLetter 435` (`rest87_A[6]`) as the 1-bit archive tag. -/
def tagSwap : Equiv.Perm Wire :=
  Equiv.swap (base 720) (StairPhysicalLayout.sLetter 435)

/-- The 7 wires of `rest87_A` (checkpoint bit-length register at `B = 87`, value `< 87`). -/
def rest87A : List Wire :=
  [ StairPhysicalLayout.sLetter 425, StairPhysicalLayout.sLetter 426
  , StairPhysicalLayout.sLetter 428, StairPhysicalLayout.sLetter 430
  , StairPhysicalLayout.sLetter 431, StairPhysicalLayout.sLetter 433
  , StairPhysicalLayout.sLetter 435 ]

/-- The 7 payload wires `Prefix1590.payload0 1..7` (value in `TagPack1542.used7`). -/
def p0Sites : List Wire :=
  (List.finRange 7).map (fun i => Prefix1590.payload0 ⟨i.val + 1, by omega⟩)

/-- The 8 payload wires of packet `k` (`1 ≤ k ≤ 9`) in field-tail coordinates. -/
def pkSitesOf (k : Nat) : List Wire :=
  (List.finRange 8).map (fun i =>
    StairArchiveInactive.host (OB5.sig 511 (History5.historyMap base (5 * k) (NewHistory5.payloadPort i))))

/-- The 72 payload wires of packets `1..9`. -/
def pkSites : List Wire :=
  (List.range' 1 9).flatMap pkSitesOf

/-- The 19 clean ancillas from `ArchiveFieldScratch.indices.map hole`. -/
def ancSites : List Wire :=
  (ArchiveFieldScratch.indices.map ArchiveFieldScratch.hole).take 19

/-- The 105-wire placement table for `TagPack1542` (`0..6 ↦ rest87A`, `7..13 ↦ p0Sites`,
    `14..85 ↦ pkSites`, `86..104 ↦ ancSites`). -/
def tagSites : List Wire :=
  rest87A ++ p0Sites ++ pkSites ++ ancSites

def tagPort (q : Nat) : Wire :=
  tagSites[q]?.getD q

def packTag : Program :=
  renameProgram tagPort TagPack1542.packTagProg

def unpackTag : Program :=
  renameProgram tagPort TagPack1542.unpackTagProg

theorem tagSites_length : tagSites.length = 105 := by decide +kernel

theorem tagSites_nodup : tagSites.Nodup := by decide +kernel

theorem tagPort_inj : ∀ a ∈ Finset.range 105, ∀ b ∈ Finset.range 105, tagPort a = tagPort b → a = b := by
  intro a ha b hb eq
  have ha' : a < tagSites.length := by rw [tagSites_length]; exact Finset.mem_range.mp ha
  have hb' : b < tagSites.length := by rw [tagSites_length]; exact Finset.mem_range.mp hb
  simp only [tagPort, List.getElem?_eq_getElem ha', List.getElem?_eq_getElem hb', Option.getD_some] at eq
  exact (List.Nodup.getElem_inj_iff tagSites_nodup).mp eq

theorem packTag_counts :
    toffoliCount packTag = 98 ∧ measurementCount packTag = 43 ∧ Challenge.gateSlots packTag = 453 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [packTag, (renameProgram_counts _ _).1, TagPack1542.packTagProg_toffoliCount]
  · rw [packTag, (renameProgram_counts _ _).2, TagPack1542.packTagProg_measurementCount]
  · rw [packTag, Baselines.rename_gateSlots, TagPack1542.packTagProg_gateSlots]

theorem unpackTag_counts :
    toffoliCount unpackTag = 99 ∧ measurementCount unpackTag = 42 ∧ Challenge.gateSlots unpackTag = 452 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [unpackTag, (renameProgram_counts _ _).1, TagPack1542.unpackTagProg_toffoliCount]
  · rw [unpackTag, (renameProgram_counts _ _).2, TagPack1542.unpackTagProg_measurementCount]
  · rw [unpackTag, Baselines.rename_gateSlots, TagPack1542.unpackTagProg_gateSlots]

/-- Inner body of the field group (packets `10..84` + 22 archive ten-blocks). -/
def group84Body (d : Bool) : Program :=
  ordered d (oten 10 (!d)) (ordered d (ogroup d 12 1) (ordered d (oten 13 (!d)) (ordered d (ogroup d 15 1) (ordered d (oten 16 (!d)) (ordered d (ogroup d 18 1) (ordered d (oten 19 (!d)) (ordered d (ogroup d 21 1) (ordered d (oten 22 (!d)) (ordered d (ogroup d 24 1) (ordered d (oten 25 (!d)) (ordered d (ogroup d 27 1) (ordered d (oten 28 (!d)) (ordered d (ogroup d 30 1) (ordered d (oten 31 (!d)) (ordered d (ogroup d 33 2) (ordered d (oten 35 (!d)) (ordered d (ogroup d 37 2) (ordered d (oten 39 (!d)) (ordered d (ogroup d 41 2) (ordered d (oten 43 (!d)) (ordered d (ogroup d 45 2) (ordered d (oten 47 (!d)) (ordered d (ogroup d 49 2) (ordered d (oten 51 (!d)) (ordered d (ogroup d 53 2) (ordered d (oten 55 (!d)) (ordered d (ogroup d 57 2) (ordered d (oten 59 (!d)) (ordered d (ogroup d 61 2) (ordered d (oten 63 (!d)) (ordered d (ogroup d 65 2) (ordered d (oten 67 (!d)) (ordered d (ogroup d 69 1) (ordered d (oten 70 (!d)) (ordered d (ogroup d 72 1) (ordered d (oten 73 (!d)) (ordered d (ogroup d 75 1) (ordered d (oten 76 (!d)) (ordered d (ogroup d 78 1) (ordered d (oten 79 (!d)) (ordered d (ogroup d 81 1) (ordered d (oten 82 (!d)) ((ogroup d 84 1))))))))))))))))))))))))))))))))))))))))))))

/-- Unbracketed 1543-tag field group (kept for reference in `WindowFieldJourney`). -/
def group84Raw (d : Bool) : Program :=
  ordered d (ogroup d 1 9) (group84Body d)

/-- The 1542-qubit field group: `group84Body d` has its archive tag `base 720` swapped onto
    `sLetter 435` (`rest87A[6]`), bracketed by `packTag` (99 T, 46 M) and `unpackTag` (99 T, 42 M). -/
def group84 (d : Bool) : Program :=
  ordered d (ogroup d 1 9) (packTag ++ renameProgram tagSwap (group84Body d) ++ unpackTag)

theorem oddPk_mid (d : Bool) (k : Nat) (h1 : 1≤k) (h2 : k<84) : oddPk d k=RouteA.Rolling1588.packet d k := by
  unfold oddPk; rw [if_pos ⟨h1,h2⟩]
theorem oddPk_end (d : Bool) :
    oddPk d 84=OddFullPass.P1LifeLoan.packet d 0 84 := by
  unfold oddPk; rw [if_neg (by decide),if_pos rfl]
theorem oddPk_std (d : Bool) (k : Nat) (h : 84<k) : oddPk d k=ECDSAAdd.Entrant.Rolling1588.packet d k := by
  unfold oddPk; rw [if_neg (by omega),if_neg (by omega)]

/-- every packet of the family uses only wires of the record packet at its place (no new wire). -/
theorem oddPk_sub (d : Bool) (k : Nat) : wires (oddPk d k) ⊆ wires (ECDSAAdd.Entrant.Rolling1588.packet d k) := by
  by_cases h12 : 1≤k ∧ k<84
  · rw [oddPk_mid d k h12.1 h12.2]
    cases d
    · exact StairLoanGroupSupport.c45_oddPacket_sub_false k
    · exact StairLoanGroupSupport.c45_oddPacket_sub k
  by_cases h3 : k=84
  · subst h3
    rw [oddPk_end]
    have h0 := OddFullPass.P1LifeLoan.packet_wires_sub d 0 84 (by decide)
    simpa only [StairGroups.packet_zero] using h0
  · intro q hq
    unfold oddPk at hq
    rwa [if_neg h12,if_neg h3] at hq

/-- the odd packets are physical. -/
theorem oddPk_physical (d : Bool) (k : Nat) (hlo : 1≤k) (hk : k≤84) : GatePhysical (oddPk d k) := by
  by_cases h2 : k<84
  · rw [oddPk_mid d k hlo h2]
    exact RouteA.Rolling1588.packet_physical d k (by omega)
  · have h3 : k=84 := by omega
    subst h3
    rw [oddPk_end]
    exact OddFullPass.P1LifeLoan.packet_physical d 0 84 (by decide)

theorem ot_opk_sub (d : Bool) (k : Nat) : wires (opk d k) ⊆ wires (StairArchiveInactive.packet d k) := by
  simp only [opk,StairArchiveInactive.packet,StairArchiveInactive.hosts_eq,StairGroups.packet_zero]
  exact StairLoanGroupSupport.rename_sub _ _ _ (StairLoanGroupSupport.rename_sub _ _ _ (oddPk_sub d k))

theorem ot_opk_std (d : Bool) (k : Nat) (h : 84<k) : opk d k=StairArchiveInactive.packet d k := by
  simp only [opk,StairArchiveInactive.packet,StairGroups.packet_zero,oddPk_std d k h]

theorem ot_group_eq (d : Bool) (j n : Nat) : group d j n=StairLoan.rebindMany StairSchedule.exclusiveRoles
    (StairPhysicalLayout.hosts 87) (renameProgram (OB5.sig 511) (PacketSequence.program d (StairGroups.packet d 0) j n)) :=
  rfl

theorem ot_ogroup_sub (d : Bool) (j n : Nat) : wires (ogroup d j n) ⊆ wires (group d j n) := by
  rw [group,distribute]
  exact StairLoanGroupSupport.sequence_sub d _ _ (fun k => ot_opk_sub d k) j n

theorem ot_oten_sub (j : Nat) (rev : Bool) : wires (oten j rev) ⊆ wires (ten j rev) := by
  simp only [oten,ten,ofirst,osecond,StairArchiveTen.first,StairArchiveTen.second]
  exact StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
    (StairLoanGroupSupport.append_sub _ _ _ _ (ot_opk_sub _ _)
      (StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
        (StairLoanGroupSupport.append_sub _ _ _ _ (ot_opk_sub _ _) (Finset.Subset.refl _))))
-- oddten:end WDEF

/-- the tape of the reference run is the actual tape (no cell any more). -/
def cellTape (_d : Bool) (m : List Bool) : List Bool := m




theorem ord (c : Cost) (d : Bool) (a b : Program) :
    c.measure (ordered d a b)=c.measure a+c.measure b := by
  cases d <;> simp [ordered,c.append,Nat.add_comm]

/-- every cost measure of a hosted record group is that of the record group. -/
theorem group_measure (c : Cost) (d : Bool) (j n : Nat) :
    c.measure (group d j n) = c.measure (ECDSAAdd.Entrant.Rolling1588.groups d j n) := by
  rw [group, distribute]
  unfold distributed ECDSAAdd.Entrant.Rolling1588.groups
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program, if_true, if_false, Bool.false_eq_true, c.append, ih,
      StairArchiveInactive.packet, StairArchiveInactive.hosts_eq, c.rename, StairGroups.packet_zero]

attribute [local irreducible] opk

theorem opk_measure (c : Cost) (d : Bool) (k : Nat) : c.measure (opk d k)=c.measure (oddPk d k) := by
  simp only [opk,StairArchiveInactive.hosts_eq,c.rename]

theorem ogroup_measure (c : Cost) (d : Bool) (j n : Nat) :
    c.measure (ogroup d j n)=c.measure (PacketSequence.program d (oddPk d) j n) := by
  unfold ogroup
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,c.append,ih,opk_measure]

private theorem gsplit (c : Cost) (d : Bool) (p : Nat→Program) (j n k : Nat) :
    c.measure (PacketSequence.program d p j (n+k))=
      c.measure (PacketSequence.program d p j n)+c.measure (PacketSequence.program d p (j+n) k) := by
  cases d
  · rw [RouteA.Rolling1588.odd45_program_false_add,c.append]; omega
  · rw [RouteA.Rolling1588.odd45_program_true_add,c.append]

private theorem oneP (c : Cost) (d : Bool) (p : Nat→Program) (j : Nat) :
    c.measure (PacketSequence.program d p j 1)=c.measure (p j) := by
  cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,List.append_nil,List.nil_append]

private theorem oseq_congr (d : Bool) (p q : Nat→Program) :
    ∀ (n j : Nat), (∀ k, j≤k → k<j+n → p k=q k) →
      PacketSequence.program d p j n=PacketSequence.program d q j n
  | 0, _, _ => rfl
  | n+1, j, h => by
    have hj := h j (Nat.le_refl j) (by omega)
    have rest := oseq_congr d p q n (j+1) (fun k a b => h k (by omega) (by omega))
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,hj,rest]

private theorem opartition (c : Cost) (d : Bool) :
    c.measure (ogroup d 1 84) = c.measure (ogroup d 1 9)+c.measure (ogroup d 10 2)+c.measure (ogroup d 12 1)+c.measure (ogroup d 13 2)+c.measure (ogroup d 15 1)+c.measure (ogroup d 16 2)+c.measure (ogroup d 18 1)+c.measure (ogroup d 19 2)+c.measure (ogroup d 21 1)+c.measure (ogroup d 22 2)+c.measure (ogroup d 24 1)+c.measure (ogroup d 25 2)+c.measure (ogroup d 27 1)+c.measure (ogroup d 28 2)+c.measure (ogroup d 30 1)+c.measure (ogroup d 31 2)+c.measure (ogroup d 33 2)+c.measure (ogroup d 35 2)+c.measure (ogroup d 37 2)+c.measure (ogroup d 39 2)+c.measure (ogroup d 41 2)+c.measure (ogroup d 43 2)+c.measure (ogroup d 45 2)+c.measure (ogroup d 47 2)+c.measure (ogroup d 49 2)+c.measure (ogroup d 51 2)+c.measure (ogroup d 53 2)+c.measure (ogroup d 55 2)+c.measure (ogroup d 57 2)+c.measure (ogroup d 59 2)+c.measure (ogroup d 61 2)+c.measure (ogroup d 63 2)+c.measure (ogroup d 65 2)+c.measure (ogroup d 67 2)+c.measure (ogroup d 69 1)+c.measure (ogroup d 70 2)+c.measure (ogroup d 72 1)+c.measure (ogroup d 73 2)+c.measure (ogroup d 75 1)+c.measure (ogroup d 76 2)+c.measure (ogroup d 78 1)+c.measure (ogroup d 79 2)+c.measure (ogroup d 81 1)+c.measure (ogroup d 82 2)+c.measure (ogroup d 84 1) := by
  have p0 := gsplit c d (opk d) 1 9 75
  have p1 := gsplit c d (opk d) 10 2 73
  have p2 := gsplit c d (opk d) 12 1 72
  have p3 := gsplit c d (opk d) 13 2 70
  have p4 := gsplit c d (opk d) 15 1 69
  have p5 := gsplit c d (opk d) 16 2 67
  have p6 := gsplit c d (opk d) 18 1 66
  have p7 := gsplit c d (opk d) 19 2 64
  have p8 := gsplit c d (opk d) 21 1 63
  have p9 := gsplit c d (opk d) 22 2 61
  have p10 := gsplit c d (opk d) 24 1 60
  have p11 := gsplit c d (opk d) 25 2 58
  have p12 := gsplit c d (opk d) 27 1 57
  have p13 := gsplit c d (opk d) 28 2 55
  have p14 := gsplit c d (opk d) 30 1 54
  have p15 := gsplit c d (opk d) 31 2 52
  have p16 := gsplit c d (opk d) 33 2 50
  have p17 := gsplit c d (opk d) 35 2 48
  have p18 := gsplit c d (opk d) 37 2 46
  have p19 := gsplit c d (opk d) 39 2 44
  have p20 := gsplit c d (opk d) 41 2 42
  have p21 := gsplit c d (opk d) 43 2 40
  have p22 := gsplit c d (opk d) 45 2 38
  have p23 := gsplit c d (opk d) 47 2 36
  have p24 := gsplit c d (opk d) 49 2 34
  have p25 := gsplit c d (opk d) 51 2 32
  have p26 := gsplit c d (opk d) 53 2 30
  have p27 := gsplit c d (opk d) 55 2 28
  have p28 := gsplit c d (opk d) 57 2 26
  have p29 := gsplit c d (opk d) 59 2 24
  have p30 := gsplit c d (opk d) 61 2 22
  have p31 := gsplit c d (opk d) 63 2 20
  have p32 := gsplit c d (opk d) 65 2 18
  have p33 := gsplit c d (opk d) 67 2 16
  have p34 := gsplit c d (opk d) 69 1 15
  have p35 := gsplit c d (opk d) 70 2 13
  have p36 := gsplit c d (opk d) 72 1 12
  have p37 := gsplit c d (opk d) 73 2 10
  have p38 := gsplit c d (opk d) 75 1 9
  have p39 := gsplit c d (opk d) 76 2 7
  have p40 := gsplit c d (opk d) 78 1 6
  have p41 := gsplit c d (opk d) 79 2 4
  have p42 := gsplit c d (opk d) 81 1 3
  have p43 := gsplit c d (opk d) 82 2 1
  simp only [ogroup]
  norm_num only [] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43
  omega


theorem ooverhead (j : Nat) (d : Bool) :
    toffoliCount (oten j (!d)) = toffoliCount (ogroup d j 2)+(if d then 105 else 101) ∧
    measurementCount (oten j (!d)) = measurementCount (ogroup d j 2)+(if d then 106 else 101) := by
  cases d <;>
    simp only [ogroup,PacketSequence.program,Bool.not_true,Bool.not_false,oten,ofirst,osecond,
      enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
      List.append_nil,toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,ReducedWindowArchives.enter0_counts.2.1,ReducedWindowArchives.switch0_counts.2.1,ReducedWindowArchives.leave0_counts.2.1,
      ReducedWindowArchives.enter1_counts.2.1,ReducedWindowArchives.switch1_counts.2.1,ReducedWindowArchives.leave1_counts.2.1,ReducedWindowArchives.enter0_counts.2.2.1,
      ReducedWindowArchives.switch0_counts.2.2.1,ReducedWindowArchives.leave0_counts.2.2.1,ReducedWindowArchives.enter1_counts.2.2.1,
      ReducedWindowArchives.switch1_counts.2.2.1,ReducedWindowArchives.leave1_counts.2.2.1] <;> constructor <;> omega

private theorem ofield_pieces (c : Cost) (d : Bool) :
    c.measure (ogroup d 1 84)=c.measure (RouteA.Rolling1588.groups d 1 83)+
      c.measure (oddPk d 84) := by
  rw [ogroup_measure]
  have b := gsplit c d (oddPk d) 1 83 1
  have p3 := oneP c d (oddPk d) 84
  have p2 := congrArg c.measure (oseq_congr d (oddPk d) (RouteA.Rolling1588.packet d) 83 1
    (fun k l u => oddPk_mid d k l (by omega)))
  norm_num only [] at b
  unfold RouteA.Rolling1588.groups
  omega

private theorem rfield_pieces (c : Cost) (d : Bool) :
    c.measure (group d 1 84)=c.measure (ECDSAAdd.Entrant.Rolling1588.groups d 1 83)+
      c.measure (ECDSAAdd.Entrant.Rolling1588.packet d 84) := by
  rw [group_measure]
  unfold ECDSAAdd.Entrant.Rolling1588.groups
  have b := gsplit c d (ECDSAAdd.Entrant.Rolling1588.packet d) 1 83 1
  have p3 := oneP c d (ECDSAAdd.Entrant.Rolling1588.packet d) 84
  norm_num only [] at b
  omega

/-- the hosted odd field packets 1..84 save 1260 T / 1680 M against the record packets 1..84. -/
theorem ofield_counts (d : Bool) :
    toffoliCount (ogroup d 1 84)+1260=toffoliCount (group d 1 84) ∧
    measurementCount (ogroup d 1 84)+1680=measurementCount (group d 1 84) := by
  have o1 := ofield_pieces tc d
  have o2 := ofield_pieces mc d
  have r1 := rfield_pieces tc d
  have r2 := rfield_pieces mc d
  rw [show tc.measure=toffoliCount from rfl] at o1 r1
  rw [show mc.measure=measurementCount from rfl] at o2 r2
  have g := RouteA.Rolling1588.groups_count_delta d 1 83 (by decide)
  rw [if_neg (by cases d <;> decide)] at g
  have h84 := OddFullPass.P1LifeLoan.packet_counts d 0 84 (by decide)
  rw [StairGroups.packet_zero] at h84
  rw [oddPk_end] at o1 o2
  simp only [show FoldLoanTop.saving 0 = 0 from rfl] at h84
  norm_num only at h84
  simp only [if_true,if_false] at h84
  exact ⟨by omega,by omega⟩

theorem half760OddLoan_zero_eq (d : Bool) :
    OddFullPass.P1LifeLoan.half760OddLoan 0 d = P1Life.half (base 760) d base (base 2409) := by
  cases d <;> simp only [OddFullPass.P1LifeLoan.half760OddLoan,P1Life.half,
    OddFullPass.P1LifeLoan.forwardLoan,P1Life.forward,
    OddFullPass.P1LifeLoan.inverseLoan,P1Life.inverse,
    OddFullPass.P1LifeLoan.p1Seed,P1Life.p1Seed,
    OddFullPass.P1LifeLoan.rawAddLoan,P1Life.rawAdd,
    OddFullPass.P1LifeLoan.foldLoan,FoldLoanTop.choose_zero,FoldLoanTop.stock,P1Life.fold,
    OddFullPass.P1LifeLoan.rawSubLoan,P1Life.rawSub,
    OddFullPass.P1LifeLoan.unfoldLoan,P1Life.unfoldStep,
    OddFullPass.P1LifeLoan.compareBlockLoan,P1Life.compare,
    OddFullPass.P1LifeLoan.short_zero,OddFullPass.P1LifeLoan.previousShort,P1Life.shortConstAdd,
    OddFullPass.P1LifeLoan.orMajor,P1Life.orMajor,
    OddFullPass.P1LifeLoan.orErase,P1Life.orErase,
    OddFullPass.P1LifeLoan.prepareCompare,P1Life.prepareCompare,
    OddFullPass.P1LifeLoan.exposure,P1Life.exposure,
    StairLoan.addPrefixLoan_zero,StairLoan.mappedAddLoan_zero,
    StairLoan.addTopLoan_zero,StairLoan.mappedSubLoan_zero,
    StairLoan.compareLoan_zero,StairLoan.literalConstAddLoan_zero,
    show (0 : Nat) < 6 by decide,if_true,if_false,Bool.false_eq_true]

/-- gate slots of the hosted odd field packets against the record packets 1..84. -/
theorem ofield_slots (d : Bool) :
    slots.measure (ogroup d 1 84)+(if d then 14280 else 11760)=
      slots.measure (group d 1 84)+(if d then 0 else 0) := by
  have o := ofield_pieces slots d
  have r := rfield_pieces slots d
  rw [show slots.measure=Challenge.gateSlots from rfl] at o r ⊢
  have g := RouteA.Rolling1588.groups_slot_delta d 1 83 (by decide)
  rw [if_neg (by cases d <;> decide)] at g
  have h0eq := half760OddLoan_zero_eq d
  have h84sl : Challenge.gateSlots (OddFullPass.P1LifeLoan.packet d 0 84) + 5 * RouteA.Rolling1588.halfSlotSaving d =
      Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet d 84) := by
    have h32 := RouteA.Rolling1588.cell_slot_delta d 84 3 2
    have h42 := RouteA.Rolling1588.cell_slot_delta d 84 4 2
    have hcEq : ∀ a b, OddFullPass.P1LifeLoan.cell d 0 84 a b = RouteA.Rolling1588.cell d 84 a b := by
      intro a b; cases d <;> simp only [OddFullPass.P1LifeLoan.cell,RouteA.Rolling1588.cell,
        OddFullPass.P1LifeLoan.halfWindow,RouteA.Rolling1588.halfWindow,RouteA.Rolling1588.halfWindowWith,
        Bool.false_eq_true,if_false,if_true,h0eq]
    cases d <;> simp only [OddFullPass.P1LifeLoan.packet,ECDSAAdd.Entrant.Rolling1588.packet,
      OddFullPass.P1LifeLoan.basePacket,ECDSAAdd.Entrant.Rolling1588.basePacket,
      Bool.false_eq_true,if_false,if_true,Baselines.rename_gateSlots,Challenge.gateSlots_append,hcEq] at h32 h42 ⊢ <;> omega
  rw [oddPk_end] at o
  cases d <;> simp only [RouteA.Rolling1588.halfSlotSaving,Bool.false_eq_true,if_false,if_true] at g h84sl o ⊢ <;> omega

private theorem osolve (c : Cost) (d : Bool) (delta : Nat)
    (h : ∀j,c.measure (oten j (!d))=c.measure (ogroup d j 2)+delta) :
    c.measure (group84 d)=c.measure (ogroup d 1 84)+22*delta+c.measure packTag+c.measure unpackTag := by
  simp only [group84,group84Body,ord,c.append,c.rename,h,opartition]
  omega

/-- the field group (odd cell on packets 1..84, ten-blocks + packTag/unpackTag included) against the record packets 1..84. -/
theorem group_cost (d : Bool) :
    toffoliCount (group84 d)+0=toffoliCount (group d 1 84)+(if d then 1247 else 1159) ∧
    measurementCount (group84 d)+0=measurementCount (group d 1 84)+(if d then 737 else 627) := by
  have t := osolve tc d (if d then 105 else 101) (fun j => (ooverhead j d).1)
  have m := osolve mc d (if d then 106 else 101) (fun j => (ooverhead j d).2)
  have f := ofield_counts d
  have hp := packTag_counts
  have hu := unpackTag_counts
  rw [show tc.measure = toffoliCount from rfl] at t
  rw [show mc.measure = measurementCount from rfl] at m
  cases d <;> simp only [if_true,if_false,Bool.false_eq_true] at t m ⊢ <;> exact ⟨by omega, by omega⟩

/-- Static syntax counts include both correction lists of every measurement. -/
theorem group_slots (d : Bool) :
    slots.measure (group84 d)+(if d then 14280 else 11760)=
      slots.measure (group d 1 84)+22*(if d then 5322 else 6122)+905 := by
  have hc := ofield_slots d
  have h (j : Nat) : slots.measure (oten j (!d)) =
      slots.measure (ogroup d j 2)+(if d then 5322 else 6122) := by
    rw [show slots.measure=Challenge.gateSlots from rfl]
    cases d <;>
      simp only [ogroup,PacketSequence.program,Bool.not_true,Bool.not_false,oten,ofirst,osecond,
        enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
        List.append_nil,Challenge.gateSlots_append,Baselines.rename_gateSlots,ReducedWindowArchives.enter0_counts.2.2.2,
        ReducedWindowArchives.switch0_counts.2.2.2,ReducedWindowArchives.leave0_counts.2.2.2,ReducedWindowArchives.enter1_counts.2.2.2,ReducedWindowArchives.switch1_counts.2.2.2,ReducedWindowArchives.leave1_counts.2.2.2] <;> omega
  have w := osolve slots d (if d then 5322 else 6122) h
  have hp := packTag_counts.2.2
  have hu := unpackTag_counts.2.2
  rw [show slots.measure = Challenge.gateSlots from rfl] at w hc ⊢
  cases d <;> simp only [if_true,if_false,Bool.false_eq_true] at hc w ⊢ <;> omega

theorem group_cost_div :
    toffoliCount (group84 true) = toffoliCount (group true 1 84)+1247 ∧
    measurementCount (group84 true) = measurementCount (group true 1 84)+737 := by
  have t := (group_cost true).1
  have m := (group_cost true).2
  simp only [if_true] at t m
  exact ⟨by omega,by omega⟩

theorem group_cost_mul :
    toffoliCount (group84 false) = toffoliCount (group false 1 84)+1159 ∧
    measurementCount (group84 false) = measurementCount (group false 1 84)+627 := by
  have t := (group_cost false).1
  have m := (group_cost false).2
  simp only [Bool.false_eq_true,if_false] at t m
  exact ⟨by omega,by omega⟩
-- oddten:end WCOST


-- Static syntax counts include both correction lists of every measurement.
end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

end


section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [45,406); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 29 ++
    Shadow20.MixedWindow.forwardMixedCut d ++ Rolling1588TickGap.forward d 421 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 421 tail ++
    TickCut.Mixed.reverse d ++ Rolling1588.reverse d 16 29) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

private theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (Shadow20.MixedWindow.forwardMixedCut d)+f=c.measure (Rolling1588TickGap.forward d 45 376))
    (hr : c.measure (TickCut.Mixed.reverse d)+r=c.measure (Rolling1588.reverse d 45 376)) :
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

attribute [local irreducible] Shadow20.MixedWindow.forwardMixedCut TickCut.Mixed.reverse Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 39511 else 39511)=
      toffoliCount (Stair44WalkRun.forward d (405+tail)) ∧
    toffoliCount (backward d tail)+(if d then 39640 else 39618)=
      toffoliCount (Stair44WalkRun.backward d (405+tail)) ∧
    measurementCount (forward d tail)+(if d then 17896 else 17874)=measurementCount (Stair44WalkRun.forward d (405+tail)) ∧
    measurementCount (backward d tail)+(if d then 17687 else 17665)=measurementCount (Stair44WalkRun.backward d (405+tail)) := by
  have sf := StockWindowCosts420.stock420from45 d
  have mcw := TickCut.Mixed.mixed_counts d
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at mcw ⊢
    have t := walk tc false tail 39511 39618 (subEq 39511 mcw.1 sf.1 (by omega)) (subEq 39618 mcw.2.1 sf.2.2.1 (by omega))
    have mv := walk mc false tail 17874 17665 (subEq 17874 mcw.2.2.1 sf.2.1 (by omega)) (subEq 17665 mcw.2.2.2 sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,mv⟩
  · simp only [↓reduceIte] at mcw ⊢
    have t := walk tc true tail 39511 39640 (subEq 39511 mcw.1 sf.1 (by omega)) (subEq 39640 mcw.2.1 sf.2.2.1 (by omega))
    have mv := walk mc true tail 17896 17687 (subEq 17896 mcw.2.2.1 sf.2.1 (by omega)) (subEq 17687 mcw.2.2.2 sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,mv⟩

/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 39511 else 39511)=f) (hr : (if d then 39640 else 39618)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+(if d then 17896 else 17874)=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+(if d then 17687 else 17665)=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact exactWalks d tail

theorem instMeasurements (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 17896 else 17874)=f) (hr : (if d then 17687 else 17665)=r) :
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
  WindowFieldCosts.group84 true ++
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
    WindowFieldCosts.group84 false

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
  have hlt : w < 2426 := StairWireCheck.fpSup_lt w h
  have hchk : (List.range 2426).all (fun x : Nat =>
      !StairWireCheck.fpSup x || (decide (16 ≤ x ∧ x < 2330) || decide (x = 2425))) = true := by
    decide +kernel
  have hw := List.all_eq_true.mp hchk w (List.mem_range.mpr hlt)
  simp only [h, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hw
  exact hw

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
  WindowFieldCosts.group84 true ++
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
    (h : tc.measure (WindowFieldCosts.group84 true)=tc.measure (WindowFieldCosts.group true 1 84)+n) :
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
    (h : tc.measure (WindowFieldCosts.group84 false)=tc.measure (WindowFieldCosts.group false 1 84)+n) :
    tc.measure (exitFieldHosted checkpointPrimitives)+728 =
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
    (h : mc.measure (WindowFieldCosts.group84 true)=mc.measure (WindowFieldCosts.group true 1 84)+n) :
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
    (h : mc.measure (WindowFieldCosts.group84 false)=mc.measure (WindowFieldCosts.group false 1 84)+n) :
    mc.measure (exitFieldHosted checkpointPrimitives)+1706 =
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
    (h : slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n) :
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

theorem tailPrefix_rows : entryTailPrefix checkpointPrimitives = WindowFieldCosts.group84 true ++
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

private theorem fieldTcDiv :
    tc.measure (WindowFieldCosts.group84 true)=tc.measure (WindowFieldCosts.group true 1 84)+1247 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_div.1
private theorem fieldMcDiv :
    mc.measure (WindowFieldCosts.group84 true)=mc.measure (WindowFieldCosts.group true 1 84)+737 := by
  rw [show mc.measure=measurementCount from rfl]
  exact WindowFieldCosts.group_cost_div.2
private theorem fieldTcMul :
    tc.measure (WindowFieldCosts.group84 false)=tc.measure (WindowFieldCosts.group false 1 84)+1159 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_mul.1
private theorem fieldMcMul :
    mc.measure (WindowFieldCosts.group84 false)=mc.measure (WindowFieldCosts.group false 1 84)+627 := by
  rw [show mc.measure=measurementCount from rfl]
  exact WindowFieldCosts.group_cost_mul.2
private theorem pair_delta2 {a b x y g h i j t1 t2 f1 f2 r : Nat}
    (l : a+g+h+t1=x+f1) (rr : b+i+j+t2=y+f2) (v : g+h+t1+i+j+t2=r+f1+f2) : a+b+r=x+y := by omega
attribute [local irreducible] Stair44Outer.divide Stair44Outer.multiply divide multiply
  finite Stair44Outer.finite WindowWalkCosts.forward WindowWalkCosts.backward
  WindowFieldCosts.group84 WindowFieldCosts.group Stair44WalkRun.forward Stair44WalkRun.backward
  toffoliCount measurementCount

theorem tc_div : tc.measure divide+39511+39618+681=tc.measure Stair44Outer.divide+1247 := by
  have k := kernels tc 39511 39618 616 1247 (WindowWalkCosts.inst true 4 409 39511 39640 rfl rfl rfl).1
    (WindowWalkCosts.inst false 85 490 39511 39618 rfl rfl rfl).2.1 (field_delta_tc_div 1247 fieldTcDiv)
  have e : tc.measure Rolling1588.ep + tc.measure Rolling1588.dp = 13 := by
    show toffoliCount Rolling1588.ep + toffoliCount Rolling1588.dp = 13
    rw [PackCutCounts.tc_ep, PackCutCounts.tc_dp]
  omega

theorem tc_mul (k : Nat) : tc.measure (multiply k)+39511+39640+728=tc.measure (Stair44Outer.multiply k)+1159 :=
  kernelsM tc k 39511 39640 728 1159 (WindowWalkCosts.inst false 84 489 39511 39618 rfl rfl rfl).1
    (WindowWalkCosts.inst true 4 409 39511 39640 rfl rfl rfl).2.1 (field_delta_tc_mul 1159 fieldTcMul)

theorem mc_div : mc.measure divide+17896+17665+1406=mc.measure Stair44Outer.divide+737 := by
  have k := kernels mc 17896 17665 1381 737 (WindowWalkCosts.instMeasurements true 4 409 17896 17687 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements false 85 490 17874 17665 rfl rfl rfl).2 (field_delta_mc_div 737 fieldMcDiv)
  have e : mc.measure Rolling1588.ep + mc.measure Rolling1588.dp = 5 := by
    show measurementCount Rolling1588.ep + measurementCount Rolling1588.dp = 5
    exact PackCutCounts.mc_epdp
  omega

theorem mc_mul (k : Nat) : mc.measure (multiply k)+17874+17687+1706=mc.measure (Stair44Outer.multiply k)+627 :=
  kernelsM mc k 17874 17687 1706 627 (WindowWalkCosts.instMeasurements false 84 489 17874 17665 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements true 4 409 17896 17687 rfl rfl rfl).2 (field_delta_mc_mul 627 fieldMcMul)

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+157283=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+72870=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 157283
      (OddOuterBridge.entryYAllOdd_tc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_tc_eq layout layout_widths cy)
      (pair_delta2 tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 72870
      (OddOuterBridge.entryYAllOdd_mc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_mc_eq layout layout_widths cy)
      (pair_delta2 mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2010314 ∧
    measurementCount (program C) ≤ 1446651 := by
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

theorem forwardMixed_domain (d : Bool) : Covered (Shadow20.MixedWindow.forwardMixedCut d) := by
  intro q h
  rw [domain_eq]
  exact (Shadow20.MixedWindow.mixedCut_covered d).1 q h
theorem reverseMixed_domain (d : Bool) : Covered (TickCut.Mixed.reverse d) := by
  intro q h
  rw [domain_eq]
  exact TickCut.Mixed.covered d q h

theorem forwardMixed_fits (d : Bool) : ∀ q ∈ wires (Shadow20.MixedWindow.forwardMixedCut d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (forwardMixed_domain d q h)

theorem reverseMixed_fits (d : Bool) : ∀ q ∈ wires (TickCut.Mixed.reverse d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
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
  Rolling1588TickGap.forward Rolling1588.reverse Shadow20.MixedWindow.forwardMixedCut TickCut.Mixed.reverse

theorem walk (c : Cost) (d : Bool) (tail f r n : Nat) (hn : 405+tail=n)
    (hf : c.measure (Shadow20.MixedWindow.forwardMixedCut d) ≤ f) (hr : c.measure (TickCut.Mixed.reverse d) ≤ r) :
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
    (g : slots.measure (WindowFieldCosts.group84 true)=slots.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
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
    (g : slots.measure (WindowFieldCosts.group84 false)=slots.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
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
  (6 * Shadow20.TrimHigh.adjustWidth s + 5 * Shadow20.liveW20 s + 10 * Shadow20.lowsP20 s + 847 +
    3 * Shadow20.nextWp20 s + Shadow20.barrel20Slots s false)

private def b20SR (j : Fin 9) : Nat :=
  let s := Shadow20.start20 j
  36 + 5000 + (if j.val = 0 then 166 else 332) + 12262 + 95000 +
  (6 * Shadow20.TrimHigh.adjustWidth s + 5 * Shadow20.liveW20 s + 11 * Shadow20.lowsP20 s + 805 +
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
      ((6 * CRTBarrel.adjustWidth 45 + 5 * Shadow7.liveW 45 + 10 * Shadow7.lowsP 45 + 646 + 3 * Shadow7.wpP 60 + CRTBarrel.barrelSlots 45 false) + 0)))))) +
    (Shadow20.MixedWindow.prefixPairs.map fun p => b15SF p.2).sum +
    (35 + (5000 + (168 + (15988 + (70000 + (11515 + 0)))))) +
    ((List.finRange 9).map b20SF).sum +
    (35 + (5000 + (168 + (168 + (15988 + (70000 +
      ((6 * CRTBarrel.adjustWidth 345 + 5 * Shadow7.liveW 345 + 10 * Shadow7.lowsP 345 + 646 + 3 * Shadow7.wpP 360 + CRTBarrel.barrelSlots 345 false) + 0))))))) +
    (Shadow20.MixedWindow.suffixPairs.map fun p => b15SF p.2).sum +
    (9 + ((21 * Shadow7.wpP 420 - 7) + (6004 + (168 + (15988 + 0))))) ≤ 2698994 ∧
    (12262 + (166 + (6001 + ((22 * Shadow7.wpP 420 - 9) + (9 + 0))))) +
    (Shadow20.MixedWindow.suffixPairs.reverse.map fun p => b15SR p.2).sum +
    ((6 * CRTBarrel.adjustWidth 345 + 5 * Shadow7.liveW 345 + 11 * Shadow7.lowsP 345 + 616 + 3 * Shadow7.wpP 360 + CRTBarrel.barrelSlots 345 true) +
      (70098 + (12262 + (166 + (166 + (5000 + (36 + 0))))))) +
    ((List.finRange 9).reverse.map b20SR).sum +
    (11506 + (70098 + (12262 + (166 + (5000 + (36 + 0)))))) +
    (Shadow20.MixedWindow.prefixPairs.reverse.map fun p => b15SR p.2).sum +
    ((6 * CRTBarrel.adjustWidth 45 + 5 * Shadow7.liveW 45 + 11 * Shadow7.lowsP 45 + 616 + 3 * Shadow7.wpP 60 + CRTBarrel.barrelSlots 45 true) +
      (70098 + (166 + (5000 + (36 + ((21 * Shadow7.wpP 45 - 7) + 0)))))) ≤ 2598694 := by
  decide +kernel

private theorem tick420_slots_le :
    gateSlots (Shadow20.MixedWindow.tickW 420) ≤ 6004 ∧
    gateSlots (Shadow20.MixedWindow.recvW 420) ≤ 6001 := by
  unfold Shadow20.MixedWindow.tickW Shadow20.MixedWindow.recvW
  rw [rename_gateSlots, rename_gateSlots]
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
    (hn : 22*(if d then 5322 else 6122)+905=n+(if d then 14280 else 11760)) :
    slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  have h := WindowFieldCosts.group_slots d
  omega
theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+2698994+2599891+103709+12660 :=
  kernels 2698994 2599891 103709
    (walk slots true 4 2698994 2599891 409 rfl (casts ((Shadow20.MixedWindow.mixedCut_slots_le true).1.trans (mixed_slots true).1)) (casts ((TickCut.Mixed.slots_le true).trans (Nat.add_le_add_right ((Shadow20.MixedWindow.mixedCut_slots_le true).2.trans (mixed_slots true).2) 1197)))).1
    (walk slots false 85 2698994 2599891 490 rfl (casts ((Shadow20.MixedWindow.mixedCut_slots_le false).1.trans (mixed_slots false).1)) (casts ((TickCut.Mixed.slots_le false).trans (Nat.add_le_add_right ((Shadow20.MixedWindow.mixedCut_slots_le false).2.trans (mixed_slots false).2) 1197)))).2
    (groupCap true 103709 rfl)

theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+2698994+2599891+123829+12920 :=
  kernelsM k 2698994 2599891 123829
    (walk slots false 84 2698994 2599891 489 rfl (casts ((Shadow20.MixedWindow.mixedCut_slots_le false).1.trans (mixed_slots false).1)) (casts ((TickCut.Mixed.slots_le false).trans (Nat.add_le_add_right ((Shadow20.MixedWindow.mixedCut_slots_le false).2.trans (mixed_slots false).2) 1197)))).1
    (walk slots true 4 2698994 2599891 409 rfl (casts ((Shadow20.MixedWindow.mixedCut_slots_le true).1.trans (mixed_slots true).1)) (casts ((TickCut.Mixed.slots_le true).trans (Nat.add_le_add_right ((Shadow20.MixedWindow.mixedCut_slots_le true).2.trans (mixed_slots true).2) 1197)))).2
    (groupCap false 123829 rfl)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+2698994+2599891+103709+12660)
    (hm : b ≤ y+2698994+2599891+123829+12920) : a+b+7144 ≤ x+y+10858032 := by omega

theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+10858032 :=
  finite_upper C cx cy 10858032 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 67209112 := by
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
  have c43 := ord (ot_pair d 82 (by decide) (by decide) (by decide)) (ot_ogroup_sound d 84 1 (by decide) (by decide))
  have c42 := ord (ot_ogroup_sound d 81 1 (by decide) (by decide)) c43
  have c41 := ord (ot_pair d 79 (by decide) (by decide) (by decide)) c42
  have c40 := ord (ot_ogroup_sound d 78 1 (by decide) (by decide)) c41
  have c39 := ord (ot_pair d 76 (by decide) (by decide) (by decide)) c40
  have c38 := ord (ot_ogroup_sound d 75 1 (by decide) (by decide)) c39
  have c37 := ord (ot_pair d 73 (by decide) (by decide) (by decide)) c38
  have c36 := ord (ot_ogroup_sound d 72 1 (by decide) (by decide)) c37
  have c35 := ord (ot_pair d 70 (by decide) (by decide) (by decide)) c36
  have c34 := ord (ot_ogroup_sound d 69 1 (by decide) (by decide)) c35
  have c33 := ord (ot_pair d 67 (by decide) (by decide) (by decide)) c34
  have c32 := ord (ot_ogroup_sound d 65 2 (by decide) (by decide)) c33
  have c31 := ord (ot_pair d 63 (by decide) (by decide) (by decide)) c32
  have c30 := ord (ot_ogroup_sound d 61 2 (by decide) (by decide)) c31
  have c29 := ord (ot_pair d 59 (by decide) (by decide) (by decide)) c30
  have c28 := ord (ot_ogroup_sound d 57 2 (by decide) (by decide)) c29
  have c27 := ord (ot_pair d 55 (by decide) (by decide) (by decide)) c28
  have c26 := ord (ot_ogroup_sound d 53 2 (by decide) (by decide)) c27
  have c25 := ord (ot_pair d 51 (by decide) (by decide) (by decide)) c26
  have c24 := ord (ot_ogroup_sound d 49 2 (by decide) (by decide)) c25
  have c23 := ord (ot_pair d 47 (by decide) (by decide) (by decide)) c24
  have c22 := ord (ot_ogroup_sound d 45 2 (by decide) (by decide)) c23
  have c21 := ord (ot_pair d 43 (by decide) (by decide) (by decide)) c22
  have c20 := ord (ot_ogroup_sound d 41 2 (by decide) (by decide)) c21
  have c19 := ord (ot_pair d 39 (by decide) (by decide) (by decide)) c20
  have c18 := ord (ot_ogroup_sound d 37 2 (by decide) (by decide)) c19
  have c17 := ord (ot_pair d 35 (by decide) (by decide) (by decide)) c18
  have c16 := ord (ot_ogroup_sound d 33 2 (by decide) (by decide)) c17
  have c15 := ord (ot_pair d 31 (by decide) (by decide) (by decide)) c16
  have c14 := ord (ot_ogroup_sound d 30 1 (by decide) (by decide)) c15
  have c13 := ord (ot_pair d 28 (by decide) (by decide) (by decide)) c14
  have c12 := ord (ot_ogroup_sound d 27 1 (by decide) (by decide)) c13
  have c11 := ord (ot_pair d 25 (by decide) (by decide) (by decide)) c12
  have c10 := ord (ot_ogroup_sound d 24 1 (by decide) (by decide)) c11
  have c9 := ord (ot_pair d 22 (by decide) (by decide) (by decide)) c10
  have c8 := ord (ot_ogroup_sound d 21 1 (by decide) (by decide)) c9
  have c7 := ord (ot_pair d 19 (by decide) (by decide) (by decide)) c8
  have c6 := ord (ot_ogroup_sound d 18 1 (by decide) (by decide)) c7
  have c5 := ord (ot_pair d 16 (by decide) (by decide) (by decide)) c6
  have c4 := ord (ot_ogroup_sound d 15 1 (by decide) (by decide)) c5
  have c3 := ord (ot_pair d 13 (by decide) (by decide) (by decide)) c4
  have c2 := ord (ot_ogroup_sound d 12 1 (by decide) (by decide)) c3
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

private theorem opk_avoids_720 (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    base 720 ∉ wires (opk d k) :=
  fun hw => packet_avoids_wire (base 720) (by decide +kernel) d k lo hi (WindowFieldCosts.ot_opk_sub d k hw)

private theorem opk_avoids_435 (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    StairPhysicalLayout.sLetter 435 ∉ wires (opk d k) :=
  fun hw => packet_avoids_wire (StairPhysicalLayout.sLetter 435) (by decide +kernel) d k lo hi (WindowFieldCosts.ot_opk_sub d k hw)

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
      PieceOK Stair44FieldSites.holes TP (ogroup d j n) ∧ StairPhysicalLayout.sLetter 435 ∉ wires (ogroup d j n) :=
    ⟨ot_ogroup_piece43 d j n lo hi, ogroup_avoids_wire (StairPhysicalLayout.sLetter 435) (opk_avoids_435 d) j n lo hi⟩
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
  have g0 := group84_ok true
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
  have g0 := group84_ok false
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
attribute [local irreducible] wires renameProgram Shadow20.MixedWindow.forwardMixedCut TickCut.Mixed.reverse
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
    (new : GoodWindow (Shadow20.MixedWindow.forwardMixedCut d)) :
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
    (new : GoodWindow (TickCut.Mixed.reverse d)) :
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
    (p : GatePhysical (Shadow20.MixedWindow.forwardMixedCut d)) : Sound (WindowWalkCosts.forward d tail) := by
  subst n
  rw [forward_append d 15 1 (405+tail)] at ref_
  obtain ⟨early,late⟩ := parts ref_
  change Sound (Rolling1588TickGap.forward d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,forward_append d 29 16 (376+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 45 (376+tail)) at ms
  rw [forward_append d 376 45 tail] at ms
  have patch : Sound (Shadow20.MixedWindow.forwardMixedCut d) := ⟨p,dom (PartialSites.forwardMixed_domain d)⟩
  have last : Sound (Rolling1588TickGap.forward d 421 tail) := (parts ms).2
  exact sound_append (sound_rename _ first.injective firstDom early)
    (sound_rename _ rest.injective restDom (sound_append (sound_append pre patch) last))

private theorem bw (d : Bool) (tail n : Nat) (hn : 15+(405+tail)=n)
    (ref_ : Sound (Rolling1588.reverse d 1 n))
    (p : GatePhysical (TickCut.Mixed.reverse d)) : Sound (WindowWalkCosts.backward d tail) := by
  subst n
  rw [reverse_append d 15 1 (405+tail)] at ref_
  obtain ⟨late,early⟩ := parts ref_
  change Sound (Rolling1588.reverse d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,reverse_append d 29 16 (376+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 45 (376+tail)) at ms
  rw [reverse_append d 376 45 tail] at ms
  have patch : Sound (TickCut.Mixed.reverse d) := ⟨p,dom (PartialSites.reverseMixed_domain d)⟩
  have last : Sound (Rolling1588.reverse d 421 tail) := (parts ms).1
  exact sound_append (sound_rename _ rest.injective restDom (sound_append (sound_append last patch) pre))
    (sound_rename _ first.injective firstDom early)
theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

variable (ff : ∀d,GatePhysical (Shadow20.MixedWindow.forwardMixedCut d)) (rr : ∀d,GatePhysical (TickCut.Mixed.reverse d))

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
      hs.all (fun h => decide (h ∉ StairSchedule.exclusiveRoles) && StairSiteEasy.tpList.contains h) &&
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
    · exact ⟨tpList_mem_tpi (hnr_h x hh).2, (hnr_h x hh).1⟩
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
    · exact group84_ok true
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
    exact (pieceOK_sub (fun q hq => PackCutOddExit.cutRows_sub hq) hrows).append (group84_ok false)
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

theorem division (f : GoodWindow (Shadow20.MixedWindow.forwardMixedCut true))
    (r : GoodWindow (TickCut.Mixed.reverse false)) :
    PieceOK reserved UG WindowCallerCosts.divide :=
  (((((phase (walkF true 4 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.pack)))).append
    (ok_kernel entryFieldCut)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.reverseTail)))).append
    (phase (walkR false 85 (by decide) r))).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.native)))

theorem multiplication (k : Nat) (f : GoodWindow (Shadow20.MixedWindow.forwardMixedCut false))
    (r : GoodWindow (TickCut.Mixed.reverse true)) :
    PieceOK reserved UG (WindowCallerCosts.multiply k) :=
  (((((phase (walkF false 84 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.forwardTail)))).append
    (ok_kernel exitField)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.unpack)))).append
    (phase (walkR true 4 (by decide) r))).append (weaken (Stair44PhaseSites.exitX k))

theorem program_width (C : Point) (f : ∀d, GoodWindow (Shadow20.MixedWindow.forwardMixedCut d))
    (r : ∀d,GoodWindow (TickCut.Mixed.reverse d)) :
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
  WindowPhysical.physical (fun d => (Shadow20.MixedWindow.mixedCut_physical d).1) (fun d => TickCut.Mixed.physical d) C

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

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem wl35 : (slots 35).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 35 := by
  decide +kernel
theorem wl39 : (slots 39).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 39 := by
  decide +kernel
theorem wl47 : (slots 47).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 47 := by
  decide +kernel
theorem wl51 : (slots 51).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 51 := by
  decide +kernel
theorem wl59 : (slots 59).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 59 := by
  decide +kernel
theorem wl63 : (slots 63).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 63 := by
  decide +kernel
theorem h35_1 : part 35 1 7 = true := by
  rw [part_eq_W 35 1 7 _ wl35]
  exact partW_cells 35 1 7 (by decide) (by decide) (by decide)
theorem h35_8 : part 35 8 7 = true := by
  rw [part_eq_W 35 8 7 _ wl35]
  exact partW_cells 35 8 7 (by decide) (by decide) (by decide)
theorem h35_15 : part 35 15 7 = true := by
  rw [part_eq_W 35 15 7 _ wl35]
  exact partW_cells 35 15 7 (by decide) (by decide) (by decide)
theorem h35_22 : part 35 22 7 = true := by
  rw [part_eq_W 35 22 7 _ wl35]
  exact partW_cells 35 22 7 (by decide) (by decide) (by decide)
theorem h35_29 : part 35 29 7 = true := by
  rw [part_eq_W 35 29 7 _ wl35]
  exact partW_cells 35 29 7 (by decide) (by decide) (by decide)
theorem h35_36 : part 35 36 7 = true := by
  rw [part_eq_W 35 36 7 _ wl35]
  exact partW_cells 35 36 7 (by decide) (by decide) (by decide)
theorem h35_43 : part 35 43 7 = true := by
  rw [part_eq_W 35 43 7 _ wl35]
  exact partW_cells 35 43 7 (by decide) (by decide) (by decide)
theorem h35_50 : part 35 50 7 = true := by
  rw [part_eq_W 35 50 7 _ wl35]
  exact partW_cells 35 50 7 (by decide) (by decide) (by decide)
theorem h35_57 : part 35 57 7 = true := by
  rw [part_eq_W 35 57 7 _ wl35]
  exact partW_cells 35 57 7 (by decide) (by decide) (by decide)
theorem h35_64 : part 35 64 7 = true := by
  rw [part_eq_W 35 64 7 _ wl35]
  exact partW_cells 35 64 7 (by decide) (by decide) (by decide)
theorem h35_71 : part 35 71 7 = true := by
  rw [part_eq_W 35 71 7 _ wl35]
  exact partW_cells 35 71 7 (by decide) (by decide) (by decide)
theorem h35_78 : part 35 78 7 = true := by
  rw [part_eq_W 35 78 7 _ wl35]
  exact partW_cells 35 78 7 (by decide) (by decide) (by decide)
theorem h39_1 : part 39 1 7 = true := by
  rw [part_eq_W 39 1 7 _ wl39]
  exact partW_cells 39 1 7 (by decide) (by decide) (by decide)
theorem h39_8 : part 39 8 7 = true := by
  rw [part_eq_W 39 8 7 _ wl39]
  exact partW_cells 39 8 7 (by decide) (by decide) (by decide)
theorem h39_15 : part 39 15 7 = true := by
  rw [part_eq_W 39 15 7 _ wl39]
  exact partW_cells 39 15 7 (by decide) (by decide) (by decide)
theorem h39_22 : part 39 22 7 = true := by
  rw [part_eq_W 39 22 7 _ wl39]
  exact partW_cells 39 22 7 (by decide) (by decide) (by decide)
theorem h39_29 : part 39 29 7 = true := by
  rw [part_eq_W 39 29 7 _ wl39]
  exact partW_cells 39 29 7 (by decide) (by decide) (by decide)
theorem h39_36 : part 39 36 7 = true := by
  rw [part_eq_W 39 36 7 _ wl39]
  exact partW_cells 39 36 7 (by decide) (by decide) (by decide)
theorem h39_43 : part 39 43 7 = true := by
  rw [part_eq_W 39 43 7 _ wl39]
  exact partW_cells 39 43 7 (by decide) (by decide) (by decide)
theorem h39_50 : part 39 50 7 = true := by
  rw [part_eq_W 39 50 7 _ wl39]
  exact partW_cells 39 50 7 (by decide) (by decide) (by decide)
theorem h39_57 : part 39 57 7 = true := by
  rw [part_eq_W 39 57 7 _ wl39]
  exact partW_cells 39 57 7 (by decide) (by decide) (by decide)
theorem h39_64 : part 39 64 7 = true := by
  rw [part_eq_W 39 64 7 _ wl39]
  exact partW_cells 39 64 7 (by decide) (by decide) (by decide)
theorem h39_71 : part 39 71 7 = true := by
  rw [part_eq_W 39 71 7 _ wl39]
  exact partW_cells 39 71 7 (by decide) (by decide) (by decide)
theorem h39_78 : part 39 78 7 = true := by
  rw [part_eq_W 39 78 7 _ wl39]
  exact partW_cells 39 78 7 (by decide) (by decide) (by decide)
theorem h47_1 : part 47 1 7 = true := by
  rw [part_eq_W 47 1 7 _ wl47]
  exact partW_cells 47 1 7 (by decide) (by decide) (by decide)
theorem h47_8 : part 47 8 7 = true := by
  rw [part_eq_W 47 8 7 _ wl47]
  exact partW_cells 47 8 7 (by decide) (by decide) (by decide)
theorem h47_15 : part 47 15 7 = true := by
  rw [part_eq_W 47 15 7 _ wl47]
  exact partW_cells 47 15 7 (by decide) (by decide) (by decide)
theorem h47_22 : part 47 22 7 = true := by
  rw [part_eq_W 47 22 7 _ wl47]
  exact partW_cells 47 22 7 (by decide) (by decide) (by decide)
theorem h47_29 : part 47 29 7 = true := by
  rw [part_eq_W 47 29 7 _ wl47]
  exact partW_cells 47 29 7 (by decide) (by decide) (by decide)
theorem h47_36 : part 47 36 7 = true := by
  rw [part_eq_W 47 36 7 _ wl47]
  exact partW_cells 47 36 7 (by decide) (by decide) (by decide)
theorem h47_43 : part 47 43 7 = true := by
  rw [part_eq_W 47 43 7 _ wl47]
  exact partW_cells 47 43 7 (by decide) (by decide) (by decide)
theorem h47_50 : part 47 50 7 = true := by
  rw [part_eq_W 47 50 7 _ wl47]
  exact partW_cells 47 50 7 (by decide) (by decide) (by decide)
theorem h47_57 : part 47 57 7 = true := by
  rw [part_eq_W 47 57 7 _ wl47]
  exact partW_cells 47 57 7 (by decide) (by decide) (by decide)
theorem h47_64 : part 47 64 7 = true := by
  rw [part_eq_W 47 64 7 _ wl47]
  exact partW_cells 47 64 7 (by decide) (by decide) (by decide)
theorem h47_71 : part 47 71 7 = true := by
  rw [part_eq_W 47 71 7 _ wl47]
  exact partW_cells 47 71 7 (by decide) (by decide) (by decide)
theorem h47_78 : part 47 78 7 = true := by
  rw [part_eq_W 47 78 7 _ wl47]
  exact partW_cells 47 78 7 (by decide) (by decide) (by decide)
theorem h51_1 : part 51 1 7 = true := by
  rw [part_eq_W 51 1 7 _ wl51]
  exact partW_cells 51 1 7 (by decide) (by decide) (by decide)
theorem h51_8 : part 51 8 7 = true := by
  rw [part_eq_W 51 8 7 _ wl51]
  exact partW_cells 51 8 7 (by decide) (by decide) (by decide)
theorem h51_15 : part 51 15 7 = true := by
  rw [part_eq_W 51 15 7 _ wl51]
  exact partW_cells 51 15 7 (by decide) (by decide) (by decide)
theorem h51_22 : part 51 22 7 = true := by
  rw [part_eq_W 51 22 7 _ wl51]
  exact partW_cells 51 22 7 (by decide) (by decide) (by decide)
theorem h51_29 : part 51 29 7 = true := by
  rw [part_eq_W 51 29 7 _ wl51]
  exact partW_cells 51 29 7 (by decide) (by decide) (by decide)
theorem h51_36 : part 51 36 7 = true := by
  rw [part_eq_W 51 36 7 _ wl51]
  exact partW_cells 51 36 7 (by decide) (by decide) (by decide)
theorem h51_43 : part 51 43 7 = true := by
  rw [part_eq_W 51 43 7 _ wl51]
  exact partW_cells 51 43 7 (by decide) (by decide) (by decide)
theorem h51_50 : part 51 50 7 = true := by
  rw [part_eq_W 51 50 7 _ wl51]
  exact partW_cells 51 50 7 (by decide) (by decide) (by decide)
theorem h51_57 : part 51 57 7 = true := by
  rw [part_eq_W 51 57 7 _ wl51]
  exact partW_cells 51 57 7 (by decide) (by decide) (by decide)
theorem h51_64 : part 51 64 7 = true := by
  rw [part_eq_W 51 64 7 _ wl51]
  exact partW_cells 51 64 7 (by decide) (by decide) (by decide)
theorem h51_71 : part 51 71 7 = true := by
  rw [part_eq_W 51 71 7 _ wl51]
  exact partW_cells 51 71 7 (by decide) (by decide) (by decide)
theorem h51_78 : part 51 78 7 = true := by
  rw [part_eq_W 51 78 7 _ wl51]
  exact partW_cells 51 78 7 (by decide) (by decide) (by decide)
theorem h59_1 : part 59 1 7 = true := by
  rw [part_eq_W 59 1 7 _ wl59]
  exact partW_cells 59 1 7 (by decide) (by decide) (by decide)
theorem h59_8 : part 59 8 7 = true := by
  rw [part_eq_W 59 8 7 _ wl59]
  exact partW_cells 59 8 7 (by decide) (by decide) (by decide)
theorem h59_15 : part 59 15 7 = true := by
  rw [part_eq_W 59 15 7 _ wl59]
  exact partW_cells 59 15 7 (by decide) (by decide) (by decide)
theorem h59_22 : part 59 22 7 = true := by
  rw [part_eq_W 59 22 7 _ wl59]
  exact partW_cells 59 22 7 (by decide) (by decide) (by decide)
theorem h59_29 : part 59 29 7 = true := by
  rw [part_eq_W 59 29 7 _ wl59]
  exact partW_cells 59 29 7 (by decide) (by decide) (by decide)
theorem h59_36 : part 59 36 7 = true := by
  rw [part_eq_W 59 36 7 _ wl59]
  exact partW_cells 59 36 7 (by decide) (by decide) (by decide)
theorem h59_43 : part 59 43 7 = true := by
  rw [part_eq_W 59 43 7 _ wl59]
  exact partW_cells 59 43 7 (by decide) (by decide) (by decide)
theorem h59_50 : part 59 50 7 = true := by
  rw [part_eq_W 59 50 7 _ wl59]
  exact partW_cells 59 50 7 (by decide) (by decide) (by decide)
theorem h59_57 : part 59 57 7 = true := by
  rw [part_eq_W 59 57 7 _ wl59]
  exact partW_cells 59 57 7 (by decide) (by decide) (by decide)
theorem h59_64 : part 59 64 7 = true := by
  rw [part_eq_W 59 64 7 _ wl59]
  exact partW_cells 59 64 7 (by decide) (by decide) (by decide)
theorem h59_71 : part 59 71 7 = true := by
  rw [part_eq_W 59 71 7 _ wl59]
  exact partW_cells 59 71 7 (by decide) (by decide) (by decide)
theorem h59_78 : part 59 78 7 = true := by
  rw [part_eq_W 59 78 7 _ wl59]
  exact partW_cells 59 78 7 (by decide) (by decide) (by decide)
theorem h63_1 : part 63 1 7 = true := by
  rw [part_eq_W 63 1 7 _ wl63]
  exact partW_cells 63 1 7 (by decide) (by decide) (by decide)
theorem h63_8 : part 63 8 7 = true := by
  rw [part_eq_W 63 8 7 _ wl63]
  exact partW_cells 63 8 7 (by decide) (by decide) (by decide)
theorem h63_15 : part 63 15 7 = true := by
  rw [part_eq_W 63 15 7 _ wl63]
  exact partW_cells 63 15 7 (by decide) (by decide) (by decide)
theorem h63_22 : part 63 22 7 = true := by
  rw [part_eq_W 63 22 7 _ wl63]
  exact partW_cells 63 22 7 (by decide) (by decide) (by decide)
theorem h63_29 : part 63 29 7 = true := by
  rw [part_eq_W 63 29 7 _ wl63]
  exact partW_cells 63 29 7 (by decide) (by decide) (by decide)
theorem h63_36 : part 63 36 7 = true := by
  rw [part_eq_W 63 36 7 _ wl63]
  exact partW_cells 63 36 7 (by decide) (by decide) (by decide)
theorem h63_43 : part 63 43 7 = true := by
  rw [part_eq_W 63 43 7 _ wl63]
  exact partW_cells 63 43 7 (by decide) (by decide) (by decide)
theorem h63_50 : part 63 50 7 = true := by
  rw [part_eq_W 63 50 7 _ wl63]
  exact partW_cells 63 50 7 (by decide) (by decide) (by decide)
theorem h63_57 : part 63 57 7 = true := by
  rw [part_eq_W 63 57 7 _ wl63]
  exact partW_cells 63 57 7 (by decide) (by decide) (by decide)
theorem h63_64 : part 63 64 7 = true := by
  rw [part_eq_W 63 64 7 _ wl63]
  exact partW_cells 63 64 7 (by decide) (by decide) (by decide)
theorem h63_71 : part 63 71 7 = true := by
  rw [part_eq_W 63 71 7 _ wl63]
  exact partW_cells 63 71 7 (by decide) (by decide) (by decide)
theorem h63_78 : part 63 78 7 = true := by
  rw [part_eq_W 63 78 7 _ wl63]
  exact partW_cells 63 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end


section


section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h43_1 : part 43 1 7 = true := by
  rw [part_eq_W 43 1 7 _ wl43]
  exact partW_cells 43 1 7 (by decide) (by decide) (by decide)
theorem h43_8 : part 43 8 7 = true := by
  rw [part_eq_W 43 8 7 _ wl43]
  exact partW_cells 43 8 7 (by decide) (by decide) (by decide)
theorem h43_15 : part 43 15 7 = true := by
  rw [part_eq_W 43 15 7 _ wl43]
  exact partW_cells 43 15 7 (by decide) (by decide) (by decide)
theorem h43_22 : part 43 22 7 = true := by
  rw [part_eq_W 43 22 7 _ wl43]
  exact partW_cells 43 22 7 (by decide) (by decide) (by decide)
theorem h43_29 : part 43 29 7 = true := by
  rw [part_eq_W 43 29 7 _ wl43]
  exact partW_cells 43 29 7 (by decide) (by decide) (by decide)
theorem h43_36 : part 43 36 7 = true := by
  rw [part_eq_W 43 36 7 _ wl43]
  exact partW_cells 43 36 7 (by decide) (by decide) (by decide)
theorem h43_43 : part 43 43 7 = true := by
  rw [part_eq_W 43 43 7 _ wl43]
  exact partW_cells 43 43 7 (by decide) (by decide) (by decide)
theorem h43_50 : part 43 50 7 = true := by
  rw [part_eq_W 43 50 7 _ wl43]
  exact partW_cells 43 50 7 (by decide) (by decide) (by decide)
theorem h43_57 : part 43 57 7 = true := by
  rw [part_eq_W 43 57 7 _ wl43]
  exact partW_cells 43 57 7 (by decide) (by decide) (by decide)
theorem h43_64 : part 43 64 7 = true := by
  rw [part_eq_W 43 64 7 _ wl43]
  exact partW_cells 43 64 7 (by decide) (by decide) (by decide)
theorem h43_71 : part 43 71 7 = true := by
  rw [part_eq_W 43 71 7 _ wl43]
  exact partW_cells 43 71 7 (by decide) (by decide) (by decide)
theorem h43_78 : part 43 78 7 = true := by
  rw [part_eq_W 43 78 7 _ wl43]
  exact partW_cells 43 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

end


section

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h55_1 : part 55 1 7 = true := by
  rw [part_eq_W 55 1 7 _ wl55]
  exact partW_cells 55 1 7 (by decide) (by decide) (by decide)
theorem h55_8 : part 55 8 7 = true := by
  rw [part_eq_W 55 8 7 _ wl55]
  exact partW_cells 55 8 7 (by decide) (by decide) (by decide)
theorem h55_15 : part 55 15 7 = true := by
  rw [part_eq_W 55 15 7 _ wl55]
  exact partW_cells 55 15 7 (by decide) (by decide) (by decide)
theorem h55_22 : part 55 22 7 = true := by
  rw [part_eq_W 55 22 7 _ wl55]
  exact partW_cells 55 22 7 (by decide) (by decide) (by decide)
theorem h55_29 : part 55 29 7 = true := by
  rw [part_eq_W 55 29 7 _ wl55]
  exact partW_cells 55 29 7 (by decide) (by decide) (by decide)
theorem h55_36 : part 55 36 7 = true := by
  rw [part_eq_W 55 36 7 _ wl55]
  exact partW_cells 55 36 7 (by decide) (by decide) (by decide)
theorem h55_43 : part 55 43 7 = true := by
  rw [part_eq_W 55 43 7 _ wl55]
  exact partW_cells 55 43 7 (by decide) (by decide) (by decide)
theorem h55_50 : part 55 50 7 = true := by
  rw [part_eq_W 55 50 7 _ wl55]
  exact partW_cells 55 50 7 (by decide) (by decide) (by decide)
theorem h55_57 : part 55 57 7 = true := by
  rw [part_eq_W 55 57 7 _ wl55]
  exact partW_cells 55 57 7 (by decide) (by decide) (by decide)
theorem h55_64 : part 55 64 7 = true := by
  rw [part_eq_W 55 64 7 _ wl55]
  exact partW_cells 55 64 7 (by decide) (by decide) (by decide)
theorem h55_71 : part 55 71 7 = true := by
  rw [part_eq_W 55 71 7 _ wl55]
  exact partW_cells 55 71 7 (by decide) (by decide) (by decide)
theorem h55_78 : part 55 78 7 = true := by
  rw [part_eq_W 55 78 7 _ wl55]
  exact partW_cells 55 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h67_1 : part 67 1 7 = true := by
  rw [part_eq_W 67 1 7 _ wl67]
  exact partW_cells 67 1 7 (by decide) (by decide) (by decide)
theorem h67_8 : part 67 8 7 = true := by
  rw [part_eq_W 67 8 7 _ wl67]
  exact partW_cells 67 8 7 (by decide) (by decide) (by decide)
theorem h67_15 : part 67 15 7 = true := by
  rw [part_eq_W 67 15 7 _ wl67]
  exact partW_cells 67 15 7 (by decide) (by decide) (by decide)
theorem h67_22 : part 67 22 7 = true := by
  rw [part_eq_W 67 22 7 _ wl67]
  exact partW_cells 67 22 7 (by decide) (by decide) (by decide)
theorem h67_29 : part 67 29 7 = true := by
  rw [part_eq_W 67 29 7 _ wl67]
  exact partW_cells 67 29 7 (by decide) (by decide) (by decide)
theorem h67_36 : part 67 36 7 = true := by
  rw [part_eq_W 67 36 7 _ wl67]
  exact partW_cells 67 36 7 (by decide) (by decide) (by decide)
theorem h67_43 : part 67 43 7 = true := by
  rw [part_eq_W 67 43 7 _ wl67]
  exact partW_cells 67 43 7 (by decide) (by decide) (by decide)
theorem h67_50 : part 67 50 7 = true := by
  rw [part_eq_W 67 50 7 _ wl67]
  exact partW_cells 67 50 7 (by decide) (by decide) (by decide)
theorem h67_57 : part 67 57 7 = true := by
  rw [part_eq_W 67 57 7 _ wl67]
  exact partW_cells 67 57 7 (by decide) (by decide) (by decide)
theorem h67_64 : part 67 64 7 = true := by
  rw [part_eq_W 67 64 7 _ wl67]
  exact partW_cells 67 64 7 (by decide) (by decide) (by decide)
theorem h67_71 : part 67 71 7 = true := by
  rw [part_eq_W 67 71 7 _ wl67]
  exact partW_cells 67 71 7 (by decide) (by decide) (by decide)
theorem h67_78 : part 67 78 7 = true := by
  rw [part_eq_W 67 78 7 _ wl67]
  exact partW_cells 67 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h70_1 : part 70 1 7 = true := by
  rw [part_eq_W 70 1 7 _ wl70]
  exact partW_cells 70 1 7 (by decide) (by decide) (by decide)
theorem h70_8 : part 70 8 7 = true := by
  rw [part_eq_W 70 8 7 _ wl70]
  exact partW_cells 70 8 7 (by decide) (by decide) (by decide)
theorem h70_15 : part 70 15 7 = true := by
  rw [part_eq_W 70 15 7 _ wl70]
  exact partW_cells 70 15 7 (by decide) (by decide) (by decide)
theorem h70_22 : part 70 22 7 = true := by
  rw [part_eq_W 70 22 7 _ wl70]
  exact partW_cells 70 22 7 (by decide) (by decide) (by decide)
theorem h70_29 : part 70 29 7 = true := by
  rw [part_eq_W 70 29 7 _ wl70]
  exact partW_cells 70 29 7 (by decide) (by decide) (by decide)
theorem h70_36 : part 70 36 7 = true := by
  rw [part_eq_W 70 36 7 _ wl70]
  exact partW_cells 70 36 7 (by decide) (by decide) (by decide)
theorem h70_43 : part 70 43 7 = true := by
  rw [part_eq_W 70 43 7 _ wl70]
  exact partW_cells 70 43 7 (by decide) (by decide) (by decide)
theorem h70_50 : part 70 50 7 = true := by
  rw [part_eq_W 70 50 7 _ wl70]
  exact partW_cells 70 50 7 (by decide) (by decide) (by decide)
theorem h70_57 : part 70 57 7 = true := by
  rw [part_eq_W 70 57 7 _ wl70]
  exact partW_cells 70 57 7 (by decide) (by decide) (by decide)
theorem h70_64 : part 70 64 7 = true := by
  rw [part_eq_W 70 64 7 _ wl70]
  exact partW_cells 70 64 7 (by decide) (by decide) (by decide)
theorem h70_71 : part 70 71 7 = true := by
  rw [part_eq_W 70 71 7 _ wl70]
  exact partW_cells 70 71 7 (by decide) (by decide) (by decide)
theorem h70_78 : part 70 78 7 = true := by
  rw [part_eq_W 70 78 7 _ wl70]
  exact partW_cells 70 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h73_1 : part 73 1 7 = true := by
  rw [part_eq_W 73 1 7 _ wl73]
  exact partW_cells 73 1 7 (by decide) (by decide) (by decide)
theorem h73_8 : part 73 8 7 = true := by
  rw [part_eq_W 73 8 7 _ wl73]
  exact partW_cells 73 8 7 (by decide) (by decide) (by decide)
theorem h73_15 : part 73 15 7 = true := by
  rw [part_eq_W 73 15 7 _ wl73]
  exact partW_cells 73 15 7 (by decide) (by decide) (by decide)
theorem h73_22 : part 73 22 7 = true := by
  rw [part_eq_W 73 22 7 _ wl73]
  exact partW_cells 73 22 7 (by decide) (by decide) (by decide)
theorem h73_29 : part 73 29 7 = true := by
  rw [part_eq_W 73 29 7 _ wl73]
  exact partW_cells 73 29 7 (by decide) (by decide) (by decide)
theorem h73_36 : part 73 36 7 = true := by
  rw [part_eq_W 73 36 7 _ wl73]
  exact partW_cells 73 36 7 (by decide) (by decide) (by decide)
theorem h73_43 : part 73 43 7 = true := by
  rw [part_eq_W 73 43 7 _ wl73]
  exact partW_cells 73 43 7 (by decide) (by decide) (by decide)
theorem h73_50 : part 73 50 7 = true := by
  rw [part_eq_W 73 50 7 _ wl73]
  exact partW_cells 73 50 7 (by decide) (by decide) (by decide)
theorem h73_57 : part 73 57 7 = true := by
  rw [part_eq_W 73 57 7 _ wl73]
  exact partW_cells 73 57 7 (by decide) (by decide) (by decide)
theorem h73_64 : part 73 64 7 = true := by
  rw [part_eq_W 73 64 7 _ wl73]
  exact partW_cells 73 64 7 (by decide) (by decide) (by decide)
theorem h73_71 : part 73 71 7 = true := by
  rw [part_eq_W 73 71 7 _ wl73]
  exact partW_cells 73 71 7 (by decide) (by decide) (by decide)
theorem h73_78 : part 73 78 7 = true := by
  rw [part_eq_W 73 78 7 _ wl73]
  exact partW_cells 73 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h76_1 : part 76 1 7 = true := by
  rw [part_eq_W 76 1 7 _ wl76]
  exact partW_cells 76 1 7 (by decide) (by decide) (by decide)
theorem h76_8 : part 76 8 7 = true := by
  rw [part_eq_W 76 8 7 _ wl76]
  exact partW_cells 76 8 7 (by decide) (by decide) (by decide)
theorem h76_15 : part 76 15 7 = true := by
  rw [part_eq_W 76 15 7 _ wl76]
  exact partW_cells 76 15 7 (by decide) (by decide) (by decide)
theorem h76_22 : part 76 22 7 = true := by
  rw [part_eq_W 76 22 7 _ wl76]
  exact partW_cells 76 22 7 (by decide) (by decide) (by decide)
theorem h76_29 : part 76 29 7 = true := by
  rw [part_eq_W 76 29 7 _ wl76]
  exact partW_cells 76 29 7 (by decide) (by decide) (by decide)
theorem h76_36 : part 76 36 7 = true := by
  rw [part_eq_W 76 36 7 _ wl76]
  exact partW_cells 76 36 7 (by decide) (by decide) (by decide)
theorem h76_43 : part 76 43 7 = true := by
  rw [part_eq_W 76 43 7 _ wl76]
  exact partW_cells 76 43 7 (by decide) (by decide) (by decide)
theorem h76_50 : part 76 50 7 = true := by
  rw [part_eq_W 76 50 7 _ wl76]
  exact partW_cells 76 50 7 (by decide) (by decide) (by decide)
theorem h76_57 : part 76 57 7 = true := by
  rw [part_eq_W 76 57 7 _ wl76]
  exact partW_cells 76 57 7 (by decide) (by decide) (by decide)
theorem h76_64 : part 76 64 7 = true := by
  rw [part_eq_W 76 64 7 _ wl76]
  exact partW_cells 76 64 7 (by decide) (by decide) (by decide)
theorem h76_71 : part 76 71 7 = true := by
  rw [part_eq_W 76 71 7 _ wl76]
  exact partW_cells 76 71 7 (by decide) (by decide) (by decide)
theorem h76_78 : part 76 78 7 = true := by
  rw [part_eq_W 76 78 7 _ wl76]
  exact partW_cells 76 78 7 (by decide) (by decide) (by decide)
theorem h79_1 : part 79 1 7 = true := by
  rw [part_eq_W 79 1 7 _ wl79]
  exact partW_cells 79 1 7 (by decide) (by decide) (by decide)
theorem h79_8 : part 79 8 7 = true := by
  rw [part_eq_W 79 8 7 _ wl79]
  exact partW_cells 79 8 7 (by decide) (by decide) (by decide)
theorem h79_15 : part 79 15 7 = true := by
  rw [part_eq_W 79 15 7 _ wl79]
  exact partW_cells 79 15 7 (by decide) (by decide) (by decide)
theorem h79_22 : part 79 22 7 = true := by
  rw [part_eq_W 79 22 7 _ wl79]
  exact partW_cells 79 22 7 (by decide) (by decide) (by decide)
theorem h79_29 : part 79 29 7 = true := by
  rw [part_eq_W 79 29 7 _ wl79]
  exact partW_cells 79 29 7 (by decide) (by decide) (by decide)
theorem h79_36 : part 79 36 7 = true := by
  rw [part_eq_W 79 36 7 _ wl79]
  exact partW_cells 79 36 7 (by decide) (by decide) (by decide)
theorem h79_43 : part 79 43 7 = true := by
  rw [part_eq_W 79 43 7 _ wl79]
  exact partW_cells 79 43 7 (by decide) (by decide) (by decide)
theorem h79_50 : part 79 50 7 = true := by
  rw [part_eq_W 79 50 7 _ wl79]
  exact partW_cells 79 50 7 (by decide) (by decide) (by decide)
theorem h79_57 : part 79 57 7 = true := by
  rw [part_eq_W 79 57 7 _ wl79]
  exact partW_cells 79 57 7 (by decide) (by decide) (by decide)
theorem h79_64 : part 79 64 7 = true := by
  rw [part_eq_W 79 64 7 _ wl79]
  exact partW_cells 79 64 7 (by decide) (by decide) (by decide)
theorem h79_71 : part 79 71 7 = true := by
  rw [part_eq_W 79 71 7 _ wl79]
  exact partW_cells 79 71 7 (by decide) (by decide) (by decide)
theorem h79_78 : part 79 78 7 = true := by
  rw [part_eq_W 79 78 7 _ wl79]
  exact partW_cells 79 78 7 (by decide) (by decide) (by decide)
theorem h82_1 : part 82 1 7 = true := by
  rw [part_eq_W 82 1 7 _ wl82]
  exact partW_cells 82 1 7 (by decide) (by decide) (by decide)
theorem h82_8 : part 82 8 7 = true := by
  rw [part_eq_W 82 8 7 _ wl82]
  exact partW_cells 82 8 7 (by decide) (by decide) (by decide)
theorem h82_15 : part 82 15 7 = true := by
  rw [part_eq_W 82 15 7 _ wl82]
  exact partW_cells 82 15 7 (by decide) (by decide) (by decide)
theorem h82_22 : part 82 22 7 = true := by
  rw [part_eq_W 82 22 7 _ wl82]
  exact partW_cells 82 22 7 (by decide) (by decide) (by decide)
theorem h82_29 : part 82 29 7 = true := by
  rw [part_eq_W 82 29 7 _ wl82]
  exact partW_cells 82 29 7 (by decide) (by decide) (by decide)
theorem h82_36 : part 82 36 7 = true := by
  rw [part_eq_W 82 36 7 _ wl82]
  exact partW_cells 82 36 7 (by decide) (by decide) (by decide)
theorem h82_43 : part 82 43 7 = true := by
  rw [part_eq_W 82 43 7 _ wl82]
  exact partW_cells 82 43 7 (by decide) (by decide) (by decide)
theorem h82_50 : part 82 50 7 = true := by
  rw [part_eq_W 82 50 7 _ wl82]
  exact partW_cells 82 50 7 (by decide) (by decide) (by decide)
theorem h82_57 : part 82 57 7 = true := by
  rw [part_eq_W 82 57 7 _ wl82]
  exact partW_cells 82 57 7 (by decide) (by decide) (by decide)
theorem h82_64 : part 82 64 7 = true := by
  rw [part_eq_W 82 64 7 _ wl82]
  exact partW_cells 82 64 7 (by decide) (by decide) (by decide)
theorem h82_71 : part 82 71 7 = true := by
  rw [part_eq_W 82 71 7 _ wl82]
  exact partW_cells 82 71 7 (by decide) (by decide) (by decide)
theorem h82_78 : part 82 78 7 = true := by
  rw [part_eq_W 82 78 7 _ wl82]
  exact partW_cells 82 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h10_1 : part 10 1 7 = true := by
  rw [part_eq_W 10 1 7 _ wl10]
  exact partW_cells 10 1 7 (by decide) (by decide) (by decide)
theorem h10_8 : part 10 8 7 = true := by
  rw [part_eq_W 10 8 7 _ wl10]
  exact partW_cells 10 8 7 (by decide) (by decide) (by decide)
theorem h10_15 : part 10 15 7 = true := by
  rw [part_eq_W 10 15 7 _ wl10]
  exact partW_cells 10 15 7 (by decide) (by decide) (by decide)
theorem h10_22 : part 10 22 7 = true := by
  rw [part_eq_W 10 22 7 _ wl10]
  exact partW_cells 10 22 7 (by decide) (by decide) (by decide)
theorem h10_29 : part 10 29 7 = true := by
  rw [part_eq_W 10 29 7 _ wl10]
  exact partW_cells 10 29 7 (by decide) (by decide) (by decide)
theorem h10_36 : part 10 36 7 = true := by
  rw [part_eq_W 10 36 7 _ wl10]
  exact partW_cells 10 36 7 (by decide) (by decide) (by decide)
theorem h10_43 : part 10 43 7 = true := by
  rw [part_eq_W 10 43 7 _ wl10]
  exact partW_cells 10 43 7 (by decide) (by decide) (by decide)
theorem h10_50 : part 10 50 7 = true := by
  rw [part_eq_W 10 50 7 _ wl10]
  exact partW_cells 10 50 7 (by decide) (by decide) (by decide)
theorem h10_57 : part 10 57 7 = true := by
  rw [part_eq_W 10 57 7 _ wl10]
  exact partW_cells 10 57 7 (by decide) (by decide) (by decide)
theorem h10_64 : part 10 64 7 = true := by
  rw [part_eq_W 10 64 7 _ wl10]
  exact partW_cells 10 64 7 (by decide) (by decide) (by decide)
theorem h10_71 : part 10 71 7 = true := by
  rw [part_eq_W 10 71 7 _ wl10]
  exact partW_cells 10 71 7 (by decide) (by decide) (by decide)
theorem h10_78 : part 10 78 7 = true := by
  rw [part_eq_W 10 78 7 _ wl10]
  exact partW_cells 10 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h13_1 : part 13 1 7 = true := by
  rw [part_eq_W 13 1 7 _ wl13]
  exact partW_cells 13 1 7 (by decide) (by decide) (by decide)
theorem h13_8 : part 13 8 7 = true := by
  rw [part_eq_W 13 8 7 _ wl13]
  exact partW_cells 13 8 7 (by decide) (by decide) (by decide)
theorem h13_15 : part 13 15 7 = true := by
  rw [part_eq_W 13 15 7 _ wl13]
  exact partW_cells 13 15 7 (by decide) (by decide) (by decide)
theorem h13_22 : part 13 22 7 = true := by
  rw [part_eq_W 13 22 7 _ wl13]
  exact partW_cells 13 22 7 (by decide) (by decide) (by decide)
theorem h13_29 : part 13 29 7 = true := by
  rw [part_eq_W 13 29 7 _ wl13]
  exact partW_cells 13 29 7 (by decide) (by decide) (by decide)
theorem h13_36 : part 13 36 7 = true := by
  rw [part_eq_W 13 36 7 _ wl13]
  exact partW_cells 13 36 7 (by decide) (by decide) (by decide)
theorem h13_43 : part 13 43 7 = true := by
  rw [part_eq_W 13 43 7 _ wl13]
  exact partW_cells 13 43 7 (by decide) (by decide) (by decide)
theorem h13_50 : part 13 50 7 = true := by
  rw [part_eq_W 13 50 7 _ wl13]
  exact partW_cells 13 50 7 (by decide) (by decide) (by decide)
theorem h13_57 : part 13 57 7 = true := by
  rw [part_eq_W 13 57 7 _ wl13]
  exact partW_cells 13 57 7 (by decide) (by decide) (by decide)
theorem h13_64 : part 13 64 7 = true := by
  rw [part_eq_W 13 64 7 _ wl13]
  exact partW_cells 13 64 7 (by decide) (by decide) (by decide)
theorem h13_71 : part 13 71 7 = true := by
  rw [part_eq_W 13 71 7 _ wl13]
  exact partW_cells 13 71 7 (by decide) (by decide) (by decide)
theorem h13_78 : part 13 78 7 = true := by
  rw [part_eq_W 13 78 7 _ wl13]
  exact partW_cells 13 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h16_1 : part 16 1 7 = true := by
  rw [part_eq_W 16 1 7 _ wl16]
  exact partW_cells 16 1 7 (by decide) (by decide) (by decide)
theorem h16_8 : part 16 8 7 = true := by
  rw [part_eq_W 16 8 7 _ wl16]
  exact partW_cells 16 8 7 (by decide) (by decide) (by decide)
theorem h16_15 : part 16 15 7 = true := by
  rw [part_eq_W 16 15 7 _ wl16]
  exact partW_cells 16 15 7 (by decide) (by decide) (by decide)
theorem h16_22 : part 16 22 7 = true := by
  rw [part_eq_W 16 22 7 _ wl16]
  exact partW_cells 16 22 7 (by decide) (by decide) (by decide)
theorem h16_29 : part 16 29 7 = true := by
  rw [part_eq_W 16 29 7 _ wl16]
  exact partW_cells 16 29 7 (by decide) (by decide) (by decide)
theorem h16_36 : part 16 36 7 = true := by
  rw [part_eq_W 16 36 7 _ wl16]
  exact partW_cells 16 36 7 (by decide) (by decide) (by decide)
theorem h16_43 : part 16 43 7 = true := by
  rw [part_eq_W 16 43 7 _ wl16]
  exact partW_cells 16 43 7 (by decide) (by decide) (by decide)
theorem h16_50 : part 16 50 7 = true := by
  rw [part_eq_W 16 50 7 _ wl16]
  exact partW_cells 16 50 7 (by decide) (by decide) (by decide)
theorem h16_57 : part 16 57 7 = true := by
  rw [part_eq_W 16 57 7 _ wl16]
  exact partW_cells 16 57 7 (by decide) (by decide) (by decide)
theorem h16_64 : part 16 64 7 = true := by
  rw [part_eq_W 16 64 7 _ wl16]
  exact partW_cells 16 64 7 (by decide) (by decide) (by decide)
theorem h16_71 : part 16 71 7 = true := by
  rw [part_eq_W 16 71 7 _ wl16]
  exact partW_cells 16 71 7 (by decide) (by decide) (by decide)
theorem h16_78 : part 16 78 7 = true := by
  rw [part_eq_W 16 78 7 _ wl16]
  exact partW_cells 16 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h19_1 : part 19 1 7 = true := by
  rw [part_eq_W 19 1 7 _ wl19]
  exact partW_cells 19 1 7 (by decide) (by decide) (by decide)
theorem h19_8 : part 19 8 7 = true := by
  rw [part_eq_W 19 8 7 _ wl19]
  exact partW_cells 19 8 7 (by decide) (by decide) (by decide)
theorem h19_15 : part 19 15 7 = true := by
  rw [part_eq_W 19 15 7 _ wl19]
  exact partW_cells 19 15 7 (by decide) (by decide) (by decide)
theorem h19_22 : part 19 22 7 = true := by
  rw [part_eq_W 19 22 7 _ wl19]
  exact partW_cells 19 22 7 (by decide) (by decide) (by decide)
theorem h19_29 : part 19 29 7 = true := by
  rw [part_eq_W 19 29 7 _ wl19]
  exact partW_cells 19 29 7 (by decide) (by decide) (by decide)
theorem h19_36 : part 19 36 7 = true := by
  rw [part_eq_W 19 36 7 _ wl19]
  exact partW_cells 19 36 7 (by decide) (by decide) (by decide)
theorem h19_43 : part 19 43 7 = true := by
  rw [part_eq_W 19 43 7 _ wl19]
  exact partW_cells 19 43 7 (by decide) (by decide) (by decide)
theorem h19_50 : part 19 50 7 = true := by
  rw [part_eq_W 19 50 7 _ wl19]
  exact partW_cells 19 50 7 (by decide) (by decide) (by decide)
theorem h19_57 : part 19 57 7 = true := by
  rw [part_eq_W 19 57 7 _ wl19]
  exact partW_cells 19 57 7 (by decide) (by decide) (by decide)
theorem h19_64 : part 19 64 7 = true := by
  rw [part_eq_W 19 64 7 _ wl19]
  exact partW_cells 19 64 7 (by decide) (by decide) (by decide)
theorem h19_71 : part 19 71 7 = true := by
  rw [part_eq_W 19 71 7 _ wl19]
  exact partW_cells 19 71 7 (by decide) (by decide) (by decide)
theorem h19_78 : part 19 78 7 = true := by
  rw [part_eq_W 19 78 7 _ wl19]
  exact partW_cells 19 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h22_1 : part 22 1 7 = true := by
  rw [part_eq_W 22 1 7 _ wl22]
  exact partW_cells 22 1 7 (by decide) (by decide) (by decide)
theorem h22_8 : part 22 8 7 = true := by
  rw [part_eq_W 22 8 7 _ wl22]
  exact partW_cells 22 8 7 (by decide) (by decide) (by decide)
theorem h22_15 : part 22 15 7 = true := by
  rw [part_eq_W 22 15 7 _ wl22]
  exact partW_cells 22 15 7 (by decide) (by decide) (by decide)
theorem h22_22 : part 22 22 7 = true := by
  rw [part_eq_W 22 22 7 _ wl22]
  exact partW_cells 22 22 7 (by decide) (by decide) (by decide)
theorem h22_29 : part 22 29 7 = true := by
  rw [part_eq_W 22 29 7 _ wl22]
  exact partW_cells 22 29 7 (by decide) (by decide) (by decide)
theorem h22_36 : part 22 36 7 = true := by
  rw [part_eq_W 22 36 7 _ wl22]
  exact partW_cells 22 36 7 (by decide) (by decide) (by decide)
theorem h22_43 : part 22 43 7 = true := by
  rw [part_eq_W 22 43 7 _ wl22]
  exact partW_cells 22 43 7 (by decide) (by decide) (by decide)
theorem h22_50 : part 22 50 7 = true := by
  rw [part_eq_W 22 50 7 _ wl22]
  exact partW_cells 22 50 7 (by decide) (by decide) (by decide)
theorem h22_57 : part 22 57 7 = true := by
  rw [part_eq_W 22 57 7 _ wl22]
  exact partW_cells 22 57 7 (by decide) (by decide) (by decide)
theorem h22_64 : part 22 64 7 = true := by
  rw [part_eq_W 22 64 7 _ wl22]
  exact partW_cells 22 64 7 (by decide) (by decide) (by decide)
theorem h22_71 : part 22 71 7 = true := by
  rw [part_eq_W 22 71 7 _ wl22]
  exact partW_cells 22 71 7 (by decide) (by decide) (by decide)
theorem h22_78 : part 22 78 7 = true := by
  rw [part_eq_W 22 78 7 _ wl22]
  exact partW_cells 22 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

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

/-- Banks `j ≠ h`: no slot of `h` is a field port of `j` (one `&&&` of two masks per pair). -/
private def distinct (j h : Nat) := j=h ||
  ((maskOf (slots h)) &&& (maskOf ((List.range 121).map (fieldPort j))) == 0)
private theorem distinct_ok : banks.all (fun j=>banks.all (distinct j))=true := by decide +kernel

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

def entryFieldHostedCut : Program :=
  StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

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
  decide +kernel

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

theorem program_eq (C : Point) : program C = WindowCallerCosts.program C := by
  cases C with
  | zero => rfl
  | @some cx cy hc =>
    simp only [program, WindowCallerCosts.program, finite, WindowCallerCosts.finite,
      borrowGeneric, WindowCallerCosts.borrowGeneric, generic, WindowCallerCosts.generic,
      divide, WindowCallerCosts.divide, multiply, WindowCallerCosts.multiply,
      entryFieldHosted, WindowCallerCosts.entryFieldHosted, entryFieldHostedCut,
      WindowCallerCosts.entryFieldHostedCut, exitFieldHosted,
      WindowCallerCosts.exitFieldHosted, setup_eq]

theorem metrics (C : Point) : toffoliCount (program C) ≤ 2010314 ∧
    measurementCount (program C) ≤ 1446651 ∧ gateSlots (program C) ≤ 67209112 := by
  rw [program_eq]
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
theorem physical (C : Point) : GatePhysical (program C) := by
  rw [program_eq]
  exact WindowCallerCosts.physical C
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Challenge Baselines Stair44Outer WindowFieldParity
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
theorem width (C : Point) : qubits (program C) ≤ 1542 := by
  rw [program_eq]
  exact WindowCallerCosts.qubitBound C
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

def entry : Challenge.Entry := fun C => normalizeProgram (WindowParityCaller.program C)
def bounds : Challenge.Bounds := ⟨2010314,1446651,1542,67209112⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowParityCaller.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowParityCaller.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowParityCaller.metrics C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1446651
    rw [normalize_measurements]
    exact (WindowParityCaller.metrics C).2.1
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1542
    rw [normalize_qubits]
    exact WindowParityCaller.width C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 67209112
    rw [normalize_slots]
    exact (WindowParityCaller.metrics C).2.2

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
private theorem physicalHead :
    WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q=>fieldPort j q == wire (histPort j q)))=true := by
  decide +kernel
private theorem physicalTail : ((fieldPort 0 16 == base 720) &&
    (List.range' 17 104).all (fun q=>fieldPort 0 q == wire (base (Placement5.H (8+(q-17))))))=true := by
  decide +kernel
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
  let I := FrontierEntry1591NativeH.inverse base
  have bd := (FrontierEntry1591NativeH.wires_sub base base_pool_nodup).trans
    (FrontierEntry1591Native.native_pool base base_pool_nodup).2
  have keep := byPool bd logical _ hb m
  have orig := FrontierEntry1591NativeH.inverse_roundtrip base hn x y hx s [] m input
  rw [orig] at keep
  have z (j : Nat) (hj : j∈firstSites) : (run I m logical).basis (base j)=false :=
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
theorem reverse_domain (d : Bool) : ∀ q ∈ wires (TickCut.Mixed.reverse d), domain q = true := by
  intro q h
  rw [domain_eq]
  exact TickCut.Mixed.covered d q h

theorem inside (n:Nat) (use:domain n=true):(16:Nat)≤n ∧ n≤1812:=by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at use
  rcases use with ⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩
  all_goals exact ⟨Nat.le_trans (by decide) lo,Nat.le_trans hi (by decide)⟩
theorem range_pool (n:Nat) (lo:16 ≤ n) (hi:n≤1812):n∈skywalkPoolWires base:=by
  have hit:=StackOB5Base.base_pool (n-16) (by omega)
  simpa only [base,Nat.sub_add_cancel lo] using hit
theorem pool_partial (d:Bool):wires (TickCut.Mixed.reverse d)⊆(skywalkPoolWires base).toFinset:=by
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

def forwardEnd (d:Bool) (n:Nat):Program:=Shadow20.MixedWindow.forwardMixedCut d++Rolling1588TickGap.forward d 421 n
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
theorem tagged : (List.range' 1 84).all allowedTag=true := by decide +kernel
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
private theorem portsHead :
    WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q => regular (host.symm (fieldPort j q))))=true := by
  decide +kernel
private theorem portsTail :
    (List.range' 16 105).all (fun q => q==16 || regular (host.symm (fieldPort 0 q)))=true := by
  decide +kernel
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
  | .native j n => ogroup d j n
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
  | .native _ _ => True
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
      | native j n => exact plain _ _ _ _ _ _ initial (ot_groupSafe d j n loc)
      | paired j =>
        exact ot_stepTen j loc.1 row c (!d) (bounded j loc.1) m a r initial loc.2
          (by simpa only [Bool.not_not] using here.1) here.2.1 here.2.2
    rw [oconcatenate,run_append,run_take]
    exact ih _ _ _ _ tail rest one

theorem oemits_raw (d : Bool) : group84Raw d=oconcatenate d (plan d) := by
  cases d <;> simp only [group84Raw,group84Body,ordered,oconcatenate,oemitted,plan,if_true,if_false,Bool.false_eq_true,
    List.append_assoc,List.append_nil]

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
      exact ⟨trivial,ih _ _ _ more post⟩
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
    decide +kernel
  have jm : j ∈ WindowBankCheck.banks := by simpa [bankIds, WindowBankCheck.banks] using hj
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp hchk j jm) i (List.mem_range.mpr (Finset.mem_range.mp hi))
  simp [hq] at h1

private theorem rest87A_p0_avoids_opk_chk :
    let fc := [base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base
    (rest87A ++ p0Sites).all (fun q =>
      (List.range' 10 75).all (fun k =>
        let x := StairArchiveInactive.preimage k q
        !fc.contains x &&
        (List.finRange 10).all (fun j => History5.historyMap base (5 * k) j != x))) = true := by
  decide +kernel

private theorem pkSites_avoids_fixedCover_chk :
    let fc := [base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base
    (List.range 9).all (fun k1 =>
      (List.finRange 8).all (fun p1 =>
        let x := History5.historyMap base (5 * (k1 + 1)) (NewHistory5.payloadPort p1)
        !fc.contains x)) = true := by
  decide +kernel

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

attribute [local irreducible] ECDSAAdd.wires WindowFieldCosts.opk surface oddCutWord

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
    have h1 := List.all_eq_true.mp rest87A_p0_avoids_opk_chk (tagPort i) hmem
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

private theorem tagData_avoids_hook_chk :
    WindowBankCheck.banks.all (fun b =>
      (StairArchiveRelease.fieldSites b).all (fun w =>
        !(rest87A ++ p0Sites).contains w && !pkSites.contains w)) = true := by
  decide +kernel

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
  unfold group84Body
  repeat (first | apply hord | exact hot _ (by decide) | exact hog _ _ (by decide) (by decide) | exact hpk _ (by decide) (by decide))

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
        -- `oreferenceProgram d (planBody d)` is packets 10..84 in order `d`
        have hfull := oreference_eq d
        cases d
        · rw [plan_split_false] at hfull
          have happ : ∀ l1 l2, oreferenceProgram false (l1 ++ l2) = oreferenceProgram false l1 ++ oreferenceProgram false l2 := by
            intro l1 l2; induction l1 with | nil => rfl | cons x xs ih => simp [oreferenceProgram, ih, List.append_assoc]
          rw [happ, show oreferenceProgram false [Leg.native 1 9] = ogroup false 1 9 by simp [oreferenceProgram, oreferenceLeg]] at hfull
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
          exact List.append_cancel_right hfull
        · rw [plan_split_true] at hfull
          simp only [oreferenceProgram, oreferenceLeg] at hfull
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
          exact List.append_cancel_left hfull
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

end

end


section

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify WindowParityDirty
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
def addr (i : Nat) := OB5.sig 511 (NewHistory5.payloadWire base i)
def block (j : Nat) := (List.range 16).map (8*j+·)
private def stable0 := List.range 80
private def stable1 := List.range' 96 8
private def stable2 := List.range' 120 8
private def stable3 := List.range' 144 8
private def stable4 := List.range' 168 8
private def stable5 := List.range' 192 8
private def stable6 := List.range' 216 8
private def stable7 := List.range' 240 8
private def stable8 := List.range' 264 16
private def stable9 := List.range' 296 16
private def stable10 := List.range' 328 16
private def stable11 := List.range' 360 16
private def stable12 := List.range' 392 16
private def stable13 := List.range' 424 16
private def stable14 := List.range' 456 16
private def stable15 := List.range' 488 16
private def stable16 := List.range' 520 16
private def stable17 := List.range' 552 8
private def stable18 := List.range' 576 8
private def stable19 := List.range' 600 8
private def stable20 := List.range' 624 8
private def stable21 := List.range' 648 8
private def stable22 := List.range' 672 144
theorem split : List.range 816 = stable0 ++ block 10 ++ stable1 ++ block 13 ++ stable2 ++ block 16 ++ stable3 ++ block 19 ++ stable4 ++ block 22 ++ stable5 ++ block 25 ++ stable6 ++ block 28 ++ stable7 ++ block 31 ++ stable8 ++ block 35 ++ stable9 ++ block 39 ++ stable10 ++ block 43 ++ stable11 ++ block 47 ++ stable12 ++ block 51 ++ stable13 ++ block 55 ++ stable14 ++ block 59 ++ stable15 ++ block 63 ++ stable16 ++ block 67 ++ stable17 ++ block 70 ++ stable18 ++ block 73 ++ stable19 ++ block 76 ++ stable20 ++ block 79 ++ stable21 ++ block 82 ++ stable22 := by decide +kernel
private theorem join (l r : List Bool) : TraceParity5.parity (l++r) = (TraceParity5.parity l ^^ TraceParity5.parity r) := by
  induction l with
  | nil => simp [TraceParity5.parity]
  | cons x xs ih => simp only [List.cons_append,TraceParity5.parity,ih,Bool.xor_assoc]
theorem reduce (cs : Cols) (r : Nat) (l : List Nat) :
    TraceParity5.parity (l.map (fun i=>(get cs i).testBit r)) =
    (((l.map (get cs)).foldr (· ^^^ ·) 0).testBit r) := by
  induction l with
  | nil => simp [TraceParity5.parity]
  | cons i xs ih => simp only [List.map_cons,List.foldr_cons,TraceParity5.parity,ih,Nat.testBit_xor]
private def sum (l : List Nat) (s : State) := TraceParity5.parity (l.map (fun i=>s.basis (addr i)))
private theorem fromData (s : State) (j : Nat) (cs : Cols) (r : Nat)
    (bits : ∀ i<16,s.basis (site j i)=(get cs i).testBit r) :
    sum (block j) s=(parity cs).testBit r := by
  unfold sum block parity
  rw [List.map_map,←reduce]
  congr 1
  apply List.map_congr_left
  intro i hi; exact bits i (List.mem_range.mp hi)
private theorem stable_sum (l : List Nat) (a b : State)
    (eq : ∀i∈l,a.basis (addr i)=b.basis (addr i)) : sum l a=sum l b :=
  congrArg TraceParity5.parity (List.map_congr_left eq)
def Elsewhere (i : Nat) := i<80 ∨ (96 ≤ i ∧ i<104) ∨ (120 ≤ i ∧ i<128) ∨ (144 ≤ i ∧ i<152) ∨ (168 ≤ i ∧ i<176) ∨ (192 ≤ i ∧ i<200) ∨ (216 ≤ i ∧ i<224) ∨ (240 ≤ i ∧ i<248) ∨ (264 ≤ i ∧ i<280) ∨ (296 ≤ i ∧ i<312) ∨ (328 ≤ i ∧ i<344) ∨ (360 ≤ i ∧ i<376) ∨ (392 ≤ i ∧ i<408) ∨ (424 ≤ i ∧ i<440) ∨ (456 ≤ i ∧ i<472) ∨ (488 ≤ i ∧ i<504) ∨ (520 ≤ i ∧ i<536) ∨ (552 ≤ i ∧ i<560) ∨ (576 ≤ i ∧ i<584) ∨ (600 ≤ i ∧ i<608) ∨ (624 ≤ i ∧ i<632) ∨ (648 ≤ i ∧ i<656) ∨ (672 ≤ i ∧ i<816)
def stockParity (s : State) := TraceParity5.parity (FrontierEntry1591Field.controls.map s.basis)
private theorem allSum (s : State) : stockParity s=
    ((((((((((((((((((((((((((((((((((((((((((((sum stable0 s ^^ sum (block 10) s) ^^ sum stable1 s) ^^ sum (block 13) s) ^^ sum stable2 s) ^^ sum (block 16) s) ^^ sum stable3 s) ^^ sum (block 19) s) ^^ sum stable4 s) ^^ sum (block 22) s) ^^ sum stable5 s) ^^ sum (block 25) s) ^^ sum stable6 s) ^^ sum (block 28) s) ^^ sum stable7 s) ^^ sum (block 31) s) ^^ sum stable8 s) ^^ sum (block 35) s) ^^ sum stable9 s) ^^ sum (block 39) s) ^^ sum stable10 s) ^^ sum (block 43) s) ^^ sum stable11 s) ^^ sum (block 47) s) ^^ sum stable12 s) ^^ sum (block 51) s) ^^ sum stable13 s) ^^ sum (block 55) s) ^^ sum stable14 s) ^^ sum (block 59) s) ^^ sum stable15 s) ^^ sum (block 63) s) ^^ sum stable16 s) ^^ sum (block 67) s) ^^ sum stable17 s) ^^ sum (block 70) s) ^^ sum stable18 s) ^^ sum (block 73) s) ^^ sum stable19 s) ^^ sum (block 76) s) ^^ sum stable20 s) ^^ sum (block 79) s) ^^ sum stable21 s) ^^ sum (block 82) s) ^^ sum stable22 s) := by
  unfold stockParity FrontierEntry1591Field.controls ParityHost5.payloadControls
  rw [split]
  simp only [List.map_append,List.map_map,join,sum,Function.comp_def,addr]
private theorem pair_step (p q s x y : Bool) : (((p ^^ x) ^^ s) ^^ ((q ^^ y) ^^ s)) = ((p ^^ q) ^^ (x ^^ y)) := by
  cases p <;> cases q <;> cases s <;> cases x <;> cases y <;> rfl
theorem fold_pair (rows : Nat→Nat) (dirs : Nat→Bool) (a b : State)
    (rest : ∀i,Elsewhere i→a.basis (addr i)=b.basis (addr i))
    (custom : ∀j,j=10 ∨ j=13 ∨ j=16 ∨ j=19 ∨ j=22 ∨ j=25 ∨ j=28 ∨ j=31 ∨ j=35 ∨ j=39 ∨ j=43 ∨ j=47 ∨ j=51 ∨ j=55 ∨ j=59 ∨ j=63 ∨ j=67 ∨ j=70 ∨ j=73 ∨ j=76 ∨ j=79 ∨ j=82 → ∀i<16,a.basis (site j i)=(get (ArchivePortAction.code (dirs j)) i).testBit (rows j))
    (stock : ∀j,j=10 ∨ j=13 ∨ j=16 ∨ j=19 ∨ j=22 ∨ j=25 ∨ j=28 ∨ j=31 ∨ j=35 ∨ j=39 ∨ j=43 ∨ j=47 ∨ j=51 ∨ j=55 ∨ j=59 ∨ j=63 ∨ j=67 ∨ j=70 ∨ j=73 ∨ j=76 ∨ j=79 ∨ j=82 → ∀i<16,b.basis (site j i)=(get (StairArchiveNativeCut.canonical (dirs j) (dirs j)) i).testBit (rows j)) :
    (stockParity a ^^ stockParity b) =
    (((((((((((((((((((((((parity (ArchivePortAction.code (dirs 10))).testBit (rows 10) ^^ (parity (StairArchiveNativeCut.canonical (dirs 10) (dirs 10))).testBit (rows 10)) ^^ ((parity (ArchivePortAction.code (dirs 13))).testBit (rows 13) ^^ (parity (StairArchiveNativeCut.canonical (dirs 13) (dirs 13))).testBit (rows 13))) ^^ ((parity (ArchivePortAction.code (dirs 16))).testBit (rows 16) ^^ (parity (StairArchiveNativeCut.canonical (dirs 16) (dirs 16))).testBit (rows 16))) ^^ ((parity (ArchivePortAction.code (dirs 19))).testBit (rows 19) ^^ (parity (StairArchiveNativeCut.canonical (dirs 19) (dirs 19))).testBit (rows 19))) ^^ ((parity (ArchivePortAction.code (dirs 22))).testBit (rows 22) ^^ (parity (StairArchiveNativeCut.canonical (dirs 22) (dirs 22))).testBit (rows 22))) ^^ ((parity (ArchivePortAction.code (dirs 25))).testBit (rows 25) ^^ (parity (StairArchiveNativeCut.canonical (dirs 25) (dirs 25))).testBit (rows 25))) ^^ ((parity (ArchivePortAction.code (dirs 28))).testBit (rows 28) ^^ (parity (StairArchiveNativeCut.canonical (dirs 28) (dirs 28))).testBit (rows 28))) ^^ ((parity (ArchivePortAction.code (dirs 31))).testBit (rows 31) ^^ (parity (StairArchiveNativeCut.canonical (dirs 31) (dirs 31))).testBit (rows 31))) ^^ ((parity (ArchivePortAction.code (dirs 35))).testBit (rows 35) ^^ (parity (StairArchiveNativeCut.canonical (dirs 35) (dirs 35))).testBit (rows 35))) ^^ ((parity (ArchivePortAction.code (dirs 39))).testBit (rows 39) ^^ (parity (StairArchiveNativeCut.canonical (dirs 39) (dirs 39))).testBit (rows 39))) ^^ ((parity (ArchivePortAction.code (dirs 43))).testBit (rows 43) ^^ (parity (StairArchiveNativeCut.canonical (dirs 43) (dirs 43))).testBit (rows 43))) ^^ ((parity (ArchivePortAction.code (dirs 47))).testBit (rows 47) ^^ (parity (StairArchiveNativeCut.canonical (dirs 47) (dirs 47))).testBit (rows 47))) ^^ ((parity (ArchivePortAction.code (dirs 51))).testBit (rows 51) ^^ (parity (StairArchiveNativeCut.canonical (dirs 51) (dirs 51))).testBit (rows 51))) ^^ ((parity (ArchivePortAction.code (dirs 55))).testBit (rows 55) ^^ (parity (StairArchiveNativeCut.canonical (dirs 55) (dirs 55))).testBit (rows 55))) ^^ ((parity (ArchivePortAction.code (dirs 59))).testBit (rows 59) ^^ (parity (StairArchiveNativeCut.canonical (dirs 59) (dirs 59))).testBit (rows 59))) ^^ ((parity (ArchivePortAction.code (dirs 63))).testBit (rows 63) ^^ (parity (StairArchiveNativeCut.canonical (dirs 63) (dirs 63))).testBit (rows 63))) ^^ ((parity (ArchivePortAction.code (dirs 67))).testBit (rows 67) ^^ (parity (StairArchiveNativeCut.canonical (dirs 67) (dirs 67))).testBit (rows 67))) ^^ ((parity (ArchivePortAction.code (dirs 70))).testBit (rows 70) ^^ (parity (StairArchiveNativeCut.canonical (dirs 70) (dirs 70))).testBit (rows 70))) ^^ ((parity (ArchivePortAction.code (dirs 73))).testBit (rows 73) ^^ (parity (StairArchiveNativeCut.canonical (dirs 73) (dirs 73))).testBit (rows 73))) ^^ ((parity (ArchivePortAction.code (dirs 76))).testBit (rows 76) ^^ (parity (StairArchiveNativeCut.canonical (dirs 76) (dirs 76))).testBit (rows 76))) ^^ ((parity (ArchivePortAction.code (dirs 79))).testBit (rows 79) ^^ (parity (StairArchiveNativeCut.canonical (dirs 79) (dirs 79))).testBit (rows 79))) ^^ ((parity (ArchivePortAction.code (dirs 82))).testBit (rows 82) ^^ (parity (StairArchiveNativeCut.canonical (dirs 82) (dirs 82))).testBit (rows 82))) := by
  have h0 := stable_sum stable0 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable0,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h1 := stable_sum stable1 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable1,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h2 := stable_sum stable2 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable2,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h3 := stable_sum stable3 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable3,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h4 := stable_sum stable4 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable4,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h5 := stable_sum stable5 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable5,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h6 := stable_sum stable6 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable6,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h7 := stable_sum stable7 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable7,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h8 := stable_sum stable8 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable8,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h9 := stable_sum stable9 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable9,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h10 := stable_sum stable10 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable10,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h11 := stable_sum stable11 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable11,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h12 := stable_sum stable12 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable12,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h13 := stable_sum stable13 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable13,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h14 := stable_sum stable14 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable14,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h15 := stable_sum stable15 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable15,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h16 := stable_sum stable16 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable16,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h17 := stable_sum stable17 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable17,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h18 := stable_sum stable18 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable18,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h19 := stable_sum stable19 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable19,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h20 := stable_sum stable20 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable20,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h21 := stable_sum stable21 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable21,List.mem_range,List.mem_range'_1] at hi
    omega))
  have h22 := stable_sum stable22 a b (fun i hi=>rest i (by
    unfold Elsewhere
    simp only [stable22,List.mem_range,List.mem_range'_1] at hi
    omega))
  rw [allSum a,
    allSum b,
    h0,
    h1,
    h2,
    h3,
    h4,
    h5,
    h6,
    h7,
    h8,
    h9,
    h10,
    h11,
    h12,
    h13,
    h14,
    h15,
    h16,
    h17,
    h18,
    h19,
    h20,
    h21,
    h22,
    fromData _ _ _ _ (custom 10 (by decide)),
    fromData _ _ _ _ (custom 13 (by decide)),
    fromData _ _ _ _ (custom 16 (by decide)),
    fromData _ _ _ _ (custom 19 (by decide)),
    fromData _ _ _ _ (custom 22 (by decide)),
    fromData _ _ _ _ (custom 25 (by decide)),
    fromData _ _ _ _ (custom 28 (by decide)),
    fromData _ _ _ _ (custom 31 (by decide)),
    fromData _ _ _ _ (custom 35 (by decide)),
    fromData _ _ _ _ (custom 39 (by decide)),
    fromData _ _ _ _ (custom 43 (by decide)),
    fromData _ _ _ _ (custom 47 (by decide)),
    fromData _ _ _ _ (custom 51 (by decide)),
    fromData _ _ _ _ (custom 55 (by decide)),
    fromData _ _ _ _ (custom 59 (by decide)),
    fromData _ _ _ _ (custom 63 (by decide)),
    fromData _ _ _ _ (custom 67 (by decide)),
    fromData _ _ _ _ (custom 70 (by decide)),
    fromData _ _ _ _ (custom 73 (by decide)),
    fromData _ _ _ _ (custom 76 (by decide)),
    fromData _ _ _ _ (custom 79 (by decide)),
    fromData _ _ _ _ (custom 82 (by decide)),
    fromData _ _ _ _ (stock 10 (by decide)),
    fromData _ _ _ _ (stock 13 (by decide)),
    fromData _ _ _ _ (stock 16 (by decide)),
    fromData _ _ _ _ (stock 19 (by decide)),
    fromData _ _ _ _ (stock 22 (by decide)),
    fromData _ _ _ _ (stock 25 (by decide)),
    fromData _ _ _ _ (stock 28 (by decide)),
    fromData _ _ _ _ (stock 31 (by decide)),
    fromData _ _ _ _ (stock 35 (by decide)),
    fromData _ _ _ _ (stock 39 (by decide)),
    fromData _ _ _ _ (stock 43 (by decide)),
    fromData _ _ _ _ (stock 47 (by decide)),
    fromData _ _ _ _ (stock 51 (by decide)),
    fromData _ _ _ _ (stock 55 (by decide)),
    fromData _ _ _ _ (stock 59 (by decide)),
    fromData _ _ _ _ (stock 63 (by decide)),
    fromData _ _ _ _ (stock 67 (by decide)),
    fromData _ _ _ _ (stock 70 (by decide)),
    fromData _ _ _ _ (stock 73 (by decide)),
    fromData _ _ _ _ (stock 76 (by decide)),
    fromData _ _ _ _ (stock 79 (by decide)),
    fromData _ _ _ _ (stock 82 (by decide))]
  rw [pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,Bool.xor_self,Bool.false_xor]
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.Stair44Kernel
open Arithmetic MappedCompressed Secp256k1 DirectSkywalk StairConcreteAssembly
open Rolling1588Lifetime
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount wires renameProgram

abbrev divLead := renameProgram phaseHost (openR true 409 ++ checkpointPrimitives.firstPack)
abbrev fieldD := StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan
def division := (divLead ++ fieldD) ++ renameProgram phaseHost Stair44DivTerm.routedClose

private theorem reallead : StairSchedule.firstPhase checkpointPrimitives =
    openS true 409 ++ checkpointPrimitives.firstPack := by
  simp only [openS,StairSchedule.firstPhase,StairSchedule.stackForward6,List.append_assoc]

private theorem leadCount : measurementCount divLead =
    measurementCount (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)) := by
  rw [reallead,(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,open_count]

private theorem leadRun {t : State} (F : EntryFrame t) (m : List Bool) :
    run divLead m t=run (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)) m t := by
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,
    StairField13V3Clean.pull_phaseHost_entry F,reallead]
  exact with_tail true 409 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup t (StairField13V3Clean.entryInput F) _ m

private theorem transferPool (v old target : State) (e : pullState phaseHost old=target)
    (h : v.phase=old.phase ∧ ∀q∈skywalkPoolWires base,v.basis q=old.basis q) :
    (pullState phaseHost v).phase=target.phase ∧
      ∀q∈skywalkPoolWires base,(pullState phaseHost v).basis q=target.basis q := by
  subst target
  exact ⟨h.1,fun q hq => h.2 _ (Stair44DivTerm.host_pool q hq)⟩

theorem division_run {t : State} (F : EntryFrame t) (m : List Bool) :
    run division m t = run (StairHostsSchedule.entryKernel checkpointPrimitives hostPlan) m t := by
  let A := Stair44DivisionCut.beforeClose checkpointPrimitives hostPlan
  let L := renameProgram phaseHost (InverseFive23.lastPhase15 false)
  have stock : StairHostsSchedule.entryKernel checkpointPrimitives hostPlan=A++L := rfl
  have same (u : List Bool) : run (divLead ++ fieldD) u t=run A u t := by
    change _=run (_++_) u t
    rw [run_append,run_append,leadCount,leadRun F]
  have cnt : measurementCount (divLead++fieldD)=measurementCount A := by
    change _=measurementCount (_++_)
    rw [measurementCount_append,measurementCount_append,leadCount]
  rw [division,stock,run_append (divLead++fieldD),run_append A,cnt,same]
  obtain ⟨v,ev⟩ : ∃ v : State,run A (m.take (measurementCount A)) t=v := ⟨_,rfl⟩
  rw [ev]
  have h := Stair44DivisionCut.pool F (m.take (measurementCount A))
  change (run A _ t).phase=_ ∧ ∀q∈skywalkPoolWires base,(run A _ t).basis q=_ at h
  rw [ev] at h
  let P := Rolling1588TickGap.firstPhase false
  have first := StairLoanField7Values.first_phase_hosted false F.sharedNodup F.historyAbove F.x _
    F.x_pos F.x_lt t [] (StairField13V3Clean.entryInput F)
  have before := run_rename phaseHost phaseHost.injective P [] t
  change pullState phaseHost (run (renameProgram phaseHost (Rolling1588TickGap.firstPhase false)) [] t)=_ at before
  rw [first,StairField13V3Clean.pull_phaseHost_entry F] at before
  apply MappedCompressed.pullState_perm_injective phaseHost
  change pullState phaseHost (run (renameProgram phaseHost _) _ v)=pullState phaseHost (run (renameProgram phaseHost _) _ v)
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  have good := transferPool v _ _ before h
  exact Stair44DivTerm.close F.x _ F.x_pos F.x_lt F.sharedNodup t _ (StairField13V3Clean.entryInput F) good.1 good.2 _

theorem hostReplay : ∀ k,StairSemanticComposition.HostedReplayInterface k :=
  StairSemanticComposition.hostedReplayInterface_of
    (StairHostReplayField.hostReplay_of_field (StairOpenWiring.host_replay_of StairOpenWiring.remaining))
    (StairCertificate.replay_interfaces (StairOpenWiring.stairOpen_of_remaining StairOpenWiring.remaining))

theorem division_correct : FrontierEntry1591Callers.EntryCorrect division := by
  intro hn hl ho hf x Y hx0 hx s t m input hg hs phase eq val
  let F : EntryFrame t := ⟨hn,hl,ho,hf,x,Y,hx0,hx,s,input,hg,hs,phase,eq,val⟩
  have old := StairCallerReplay.hostedEntry_correct hostReplay hn hl ho hf x Y hx0 hx s t m input hg hs phase eq val
  dsimp only at old ⊢
  rw [division_run F]
  exact old

end ECDSAAdd.Entrant.Stair44Kernel

end

section

namespace ECDSAAdd.Entrant.Stair44Kernel
open Arithmetic MappedCompressed Stair44WalkMap
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def rawOut := Stair44PointMap.chain [(base 1542,base 500),(base 1026,base 501),(base 1541,base 502),
  (base 723,base 503),(base 724,base 504)]
def rawX := rawOut.trans (Equiv.swap (base 501) (base 514))
def changeList := [1542,1026,1541,723,724,500,501,502,503,504,514].map base

theorem off (w : Wire) (h : w∉changeList) : rawOut.symm w=w ∧ rawX.symm w=w ∧ first.symm w=w := by
  simp only [changeList,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  obtain ⟨a,b,c,d,e,f,g,i,j,k,l⟩ := h
  simp [rawOut,rawX,Stair44PointMap.chain,first,shared,Equiv.swap_apply_def,a,b,c,d,e,f,g,i,j,k,l]

private theorem encode_eq (f g : Equiv.Perm Wire) (z : List Wire)
    (chk : ∀q∈changeList,f.symm q=g.symm q ∨ f.symm q∈z ∧ g.symm q∈z)
    (far : ∀q,q∉changeList → f.symm q=g.symm q) (u : State) (hu : ∀q∈z,u.basis q=false) :
    pullState f.symm u = pullState g.symm u := by
  apply State.extensionality
  · rfl
  · funext q;change u.basis (f.symm q)=u.basis (g.symm q)
    by_cases h : q∈changeList
    · rcases chk q h with eq|⟨a,b⟩
      · rw [eq]
      · rw [hu _ a,hu _ b]
    · rw [far q h]

theorem xBefore (u : State) (hz : ∀j∈Stair44WalkExit.firstClean,u.basis (base j)=false) :
    pullState first.symm u=pullState rawX.symm u := by
  apply encode_eq first rawX (Stair44WalkExit.firstClean.map base) (by decide +kernel)
    (fun q h => (off q h).2.2.trans (off q h).2.1.symm)
  intro q h
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
  exact hz _ hj

theorem xAfter (u : State) (a : u.basis (base 1026)=false) (b : u.basis (base 514)=false) :
    pullState rawX.symm u=pullState rawOut.symm u := by
  apply encode_eq rawX rawOut [base 1026,base 514] (by decide +kernel)
    (fun q h => (off q h).2.1.trans (off q h).1.symm)
  intro q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl
  · exact a
  · exact b

attribute [local irreducible] run wires measurementCount Rolling1588.reverse Rolling1588TickGap.forward
  Rolling1588.Integer.regularForward Stair44WalkRun.backward ParityXExitInverse23Kernel.x1N

theorem routed_at_X (a x : Nat) (cut : 16+a∈[425,505,506]) (hx0 : 0<x) (hx : x<p) (s1 : State) (firstStage :
    W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t : State) (enc : List Bool) (atCut : t=run (Rolling1588TickGap.forward true 1 (15+a)) enc s1)
    (mr : List Bool) :
    run (Stair44WalkRun.backward true a) mr t = pullState rawX.symm (run (Rolling1588.reverse true 1 (15+a)) mr t) := by
  have r := Rolling1588TickGap.forward_gen true x hx0 hx (15+a) 1 (by decide) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at cut;omega) s1 enc
    (Rolling1588.Integer.stage_one base true x p s1 firstStage)
  have init : pullState (OB5.sig 0) s1=s1 := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg s1.basis (OB5.sig_zero q)
  rw [show 1-1=0 by decide,init] at r
  obtain ⟨raw,er⟩ : ∃ u : State,run (Rolling1588.Integer.regularForward base true 1 (15+a)) enc s1=u := ⟨_,rfl⟩
  rw [er] at r
  have et : t=pullState (OB5.sig (16+a-1)) raw := atCut.trans (by simpa only [show 1+(15+a)=16+a by omega] using r)
  have h1 := Rolling1588.Integer.stage_one base true x p s1 firstStage
  have eqb (q : Wire) (_ : q∈skywalkPoolWires base) := (congrArg (fun u : State => u.basis q) er).symm
  let R := Rolling1588.reverse true 1 (15+a)
  obtain ⟨v,ev⟩ : ∃ w,run R mr t=w := ⟨_,rfl⟩
  obtain ⟨act,ea⟩ : ∃ w,run (Stair44WalkRun.backward true a) mr t=w := ⟨_,rfl⟩
  have dec : pullState first act=v := by
    rw [←ea,←ev,et]
    exact Stair44WalkCuts.backward_record true a x cut hx0 hx s1 raw enc mr h1 eqb
  have pool : ∀q∈skywalkPoolWires base,v.basis q = s1.basis q := by
    rw [←ev,et]
    exact Stair44WalkCuts.restore_raw true a x cut hx0 hx s1 raw enc mr h1 eqb
  have z (j : Nat) (hj : j∈Stair44WalkExit.firstClean) : v.basis (base j)=false :=
    (pool _ (OB5.base_pool _ (by simp [Stair44WalkExit.firstClean] at hj; omega))).trans
      (Stair44WalkExit.first_ready true x p s1 h1 j hj)
  have revertEq (e : Equiv.Perm Wire) (u : State) : pullState e.symm (pullState e u)=u := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg u.basis (e.apply_symm_apply q)
  have registered := congrArg (pullState first.symm) dec
  rw [revertEq,xBefore v z] at registered
  change run (Stair44WalkRun.backward true a) mr t=pullState rawX.symm (run R mr t)
  rw [ea,ev]; exact registered

theorem reverseX (k x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (firstStage :
    W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t : State) (enc : List Bool) (atCut : t=run (Rolling1588TickGap.forward true 1 424) enc s1)
    (m : List Bool) :
    let R := Rolling1588.reverse true 1 424
    let X := ParityXExitInverse23Kernel.x1N k
    let old := run (R++X) m t
    run (Stair44WalkRun.backward true 409 ++ renameProgram rawX X) m t = pullState rawX.symm old := by
  dsimp only
  rw [run_append,run_append,(Stair44WalkRun.metrics true 409).2.2.1,
    routed_at_X 409 x (by decide) hx0 hx s1 firstStage t enc atCut]
  apply MappedCompressed.pullState_perm_injective rawX
  rw [run_rename _ rawX.injective]
  have flip (u : State) : pullState rawX (pullState rawX.symm u)=u := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg u.basis (rawX.symm_apply_apply q)
  rw [flip,flip]

end ECDSAAdd.Entrant.Stair44Kernel

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChain
open Arithmetic MappedCompressed WideReference IntegerPacket ArchiveHistoryCompare
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
theorem early (i q:Nat) (h:oldRange i q):Earlier i q := by
  obtain a|b:=h
  · exact ⟨q-16,by omega,Or.inl (by simp only [base,Wire];omega)⟩
  · exact ⟨q-1044,by omega,Or.inr (by simp only [base,Wire];omega)⟩
end ECDSAAdd.Entrant.StairPacket.OrdinaryChain

end

-- ==== w4: step 9: build-w4b drop-ins StockWindowW, FinalW_inst, OrdinaryChainW (+ holes) ====
-- BEGIN par-d2 StockWindowW (parallel chain: Tail752; needs Tail10d9 (WideReference, ArchiveStockRows), HBJ/FirstHit, PointMap/QTop; no Stair44Stock/BO)
section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowGeo
open Arithmetic MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2 (job D2): geometry of the stock comparison over an `n`-block window, generic in the first block
start `s1` and `n`. The blocks start at `s1, s1+15, ..., s1+15(n-1)` and the exit is at `e = s1+15n`.
- The stock walk over the window packs `3n+1` groups at ticks `s1-5, s1, ..., e-5` (`gstart`).
- The window packs the `plain` groups itself: the pre-window letters, then each block's own pack.
- Bank `b`'s archive holds the two `packed` groups `2+3b` and `3+3b`. Their letters 5 and 9 are the `holes`; the
  other 16 letters are the bank's 16 code cells.
This replaces dadon's `decide +kernel` checks over `Fin 13` and `Fin 4 × Fin 16` (`StockGroups.sparse/distinct/
holeSlot`, `StockArchiveBanks.chart`, `ArchiveStockSuffix.sites*`). Every lemma is a 16-way or 10-way case split
plus `omega`, so the cost is O(1) in `n`. -/

/-- Start tick of pack group `i` of the window. -/
def gstart (s1 i : Nat) : Nat := s1-5+5*i
def slot (s1 i : Nat) : Fin 10 → Wire := History5.historyMap base (gstart s1 i)
/-- Groups the window packs itself: the five pre-window letters, then the pack of each block. -/
def plain (n : Nat) : List Nat := 0 :: (List.range n).map (fun b => 1+3*b)
/-- Groups the archives hold: two per bank. -/
def packed (n : Nat) : List Nat := (List.range n).flatMap (fun b => [2+3*b, 3+3*b])
/-- The two letters of each archived group that no code cell keeps (letters 5 and 9). -/
def holes (s1 n : Nat) : List Wire :=
  (packed n).flatMap (fun i => [base (1028+gstart s1 i+2), base (1028+gstart s1 i+4)])

def logical (sw : Bool) (r : Nat) : Wire := if sw then base (1028+r) else base r
/-- A history cell of tick `r < e` in the exit-tick frame. -/
def site (e : Nat) (sw : Bool) (r : Nat) : Wire := OB5.sig e (logical sw r)
def offset (j : Fin 16) : Nat := 5*(j.val/8)+[0,0,1,1,2,3,3,4].getD (j.val%8) 0
def swap (j : Fin 16) : Bool := j.val%8∈[1,3,6]
def index (j : Fin 16) : Fin 10 := ⟨if j.val%8<5 then j.val%8 else j.val%8+1,by split <;> omega⟩
def group (b : Nat) (j : Fin 16) : Nat := 2+3*b+j.val/8
/-- Block start of bank `b` (the archive of block `j1+b`, or the exit archive for `b = n-1`). -/
def tick (s1 b : Nat) : Nat := s1+15*b
/-- Code cell `j` of bank `b`: the first 16 code ports of the archive at tick `tick s1 b+15`. -/
def bankSite (s1 b : Nat) (j : Fin 16) : Wire := (Partial.cellsRestoreP (tick s1 b+15)).getD j 0
def packet (s1 i : Nat) : Nat := s1+15*((i-2)/3)
def high (i : Nat) : Bool := decide ((i-2)%3=1)
/-- `StockArchiveTruth.tile` (same body, so the two agree by `rfl`). -/
def tile (k : Nat) (hi : Bool) : Nat := k+5+(if hi then 5 else 0)
/-- All archive cells of the window. -/
def archives (s1 n : Nat) : List Wire := (List.range n).flatMap (fun b => (List.finRange 16).map (bankSite s1 b))

/-- `OB5.sig` keeps the history cell of tick `r` fixed in every frame later than `r`. -/
theorem stable (i e r : Nat) (hi : i ≤ 511) (he : e ≤ 511) (ri : r < i) (re : r < e) (sw : Bool) :
    OB5.sig i (logical sw r)=site e sw r := by
  show OB5.sigNat i (logical sw r)=OB5.sigNat e (logical sw r)
  cases sw <;> simp only [logical,base,Bool.false_eq_true,if_false,if_true,OB5.sigNat] <;>
    split_ifs with h1 h2 h2 <;> (try rcases h1 with h1|h1) <;> (try rcases h2 with h2|h2) <;> omega

/-- The 16 code cells of the archive at tick `t` are the history cells of ticks `t-10..t-1`. -/
theorem cells (t : Nat) (lo : 10≤t) (hi : t≤511) (j : Fin 16) :
    (Partial.cellsRestoreP t).getD j 0=OB5.sig t (logical (swap j) (t-10+offset j)) := by
  show _=OB5.sigNat t (logical (swap j) (t-10+offset j))
  rcases j with ⟨j,hj⟩
  interval_cases j <;>
    simp only [Partial.cellsRestoreP,List.getD_cons_zero,List.getD_cons_succ,logical,swap,offset,base,
      OB5.sig_nat,List.mem_cons,List.not_mem_nil,or_false,List.getD,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] <;>
    first | rfl | (simp only [OB5.sigNat]; split_ifs with h1 h2 <;> (try rcases h1 with h1|h1) <;>
      (try rcases h2 with h2|h2) <;> omega) | (norm_num [OB5.sigNat]; split_ifs <;> omega)

/-- Bank cells in the exit frame: tick `tick s1 b+5+offset j`, older than the exit. -/
theorem bank_site (s1 b e : Nat) (lo : 5≤s1) (hb : tick s1 b+15≤e) (he : e≤511) (j : Fin 16) :
    bankSite s1 b j=site e (swap j) (tick s1 b+5+offset j) ∧ tick s1 b+5+offset j<e := by
  have ho:offset j≤9:=by
    rcases j with ⟨j,hj⟩; interval_cases j <;> simp [offset]
  refine ⟨?_,by omega⟩
  rw [bankSite,cells _ (by simp only [tick]; omega) (by omega)]
  rw [show tick s1 b+15-10+offset j=tick s1 b+5+offset j by omega]
  exact stable _ e _ (by omega) he (by omega) (by omega) _

/-- `StockArchiveBanks.chart`, generic: bank cell `j` of bank `b` is letter `index j` of group `group b j`, a
packed group whose packet tick is the bank's block start. -/
theorem chart (s1 n b e : Nat) (lo : 5≤s1) (hb : b<n) (he : e=s1+15*n) (le : e≤511) (j : Fin 16) :
    bankSite s1 b j=OB5.sig e (slot s1 (group b j) (index j)) ∧ packet s1 (group b j)=tick s1 b ∧
      group b j∈packed n ∧ high (group b j)=decide (8≤j.val) := by
  have bs:=(bank_site s1 b e lo (by simp only [tick]; omega) le j).1
  refine ⟨?_,?_,?_,?_⟩
  · rw [bs,site]
    congr 1
    rcases j with ⟨j,hj⟩
    interval_cases j <;> simp [logical,swap,offset,slot,History5.historyMap,History5.historyId,index,group,
      gstart,tick,base] <;> omega
  · simp only [packet,group]; rw [show (2+3*b+j.val/8-2)/3=b by have:=j.isLt; omega]; rfl
  · simp only [packed,group,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨b,hb,by have:=j.isLt; omega⟩
  · simp only [high,group]; have:=j.isLt; congr 1; apply propext; omega

theorem bank_mem (s1 n b : Nat) (hb : b<n) (j : Fin 16) : bankSite s1 b j∈archives s1 n := by
  simp only [archives,List.mem_flatMap,List.mem_range,List.mem_map,List.mem_finRange,true_and]
  exact ⟨b,hb,j,rfl⟩

/-- Every archive cell is a history cell of a tick older than the exit (the stock suffix never touches it). -/
theorem archive_old (s1 n e : Nat) (lo : 5≤s1) (he : e=s1+15*n) (le : e≤511) :
    ∀q∈archives s1 n,∃sw r,r<e ∧ q=site e sw r := by
  intro q hq
  simp only [archives,List.mem_flatMap,List.mem_range,List.mem_map,List.mem_finRange,true_and] at hq
  obtain ⟨b,hb,j,rfl⟩:=hq
  obtain ⟨eq,lt⟩:=bank_site s1 b e lo (by simp only [tick]; omega) le j
  exact ⟨_,_,lt,eq⟩

/-- `StockGroups.sparse`, generic: each letter of an archived group is a hole (letters 5, 9) or, in the exit
frame, an archive cell. -/
theorem sparse (s1 n e : Nat) (lo : 5≤s1) (he : e=s1+15*n) (le : e≤511) :
    ∀i∈packed n,∀j:Fin 10,(j=5 ∨ j=9) ∧ slot s1 i j∈holes s1 n ∨ OB5.sig e (slot s1 i j)∈archives s1 n := by
  intro i hi j
  have hi':=hi
  simp only [packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hi'
  obtain ⟨b,hb,hib⟩:=hi'
  by_cases hole:j=5 ∨ j=9
  · left
    refine ⟨hole,?_⟩
    simp only [holes,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
    refine ⟨i,hi,?_⟩
    rcases hole with rfl|rfl
    · left; simp [slot,History5.historyMap,History5.historyId,base] <;> omega
    · right; simp [slot,History5.historyMap,History5.historyId,base] <;> omega
  · right
    -- the bank cell holding letter `j` of group `i`
    let k:Nat:=8*(i-2-3*b)+(if j.val<5 then j.val else j.val-1)
    have hk:k<16:=by have:=j.isLt; simp only [k]; split <;> omega
    have gi:group b ⟨k,hk⟩=i:=by simp only [group,k]; split <;> omega
    have ij:index ⟨k,hk⟩=j:=by
      apply Fin.ext; simp only [index,k]
      have:=j.isLt
      have h5:j.val≠5:=fun h=>hole (Or.inl (Fin.ext h))
      have h9:j.val≠9:=fun h=>hole (Or.inr (Fin.ext h))
      split <;> split <;> omega
    have c:=(chart s1 n b e lo hb he le ⟨k,hk⟩).1
    rw [gi,ij] at c
    rw [←c]
    exact bank_mem s1 n b hb _

theorem hole_slot (s1 n : Nat) : ∀q∈holes s1 n,∃i∈packed n,∃j:Fin 10,q=slot s1 i j := by
  intro q hq
  simp only [holes,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hq
  obtain ⟨i,hi,e|e⟩:=hq
  · exact ⟨i,hi,5,by simp [e,slot,History5.historyMap,History5.historyId,base] <;> omega⟩
  · exact ⟨i,hi,9,by simp [e,slot,History5.historyMap,History5.historyId,base] <;> omega⟩

/-- `StockGroups.distinct`, generic: different groups use different history cells. -/
theorem distinct (s1 : Nat) (lo : 5≤s1) (i h : Nat) (hi : gstart s1 i+5≤1028) (hh : gstart s1 h+5≤1028)
    (ne : i≠h) (a b : Fin 10) : slot s1 i a≠slot s1 h b := by
  have:=a.isLt; have:=b.isLt
  intro eq
  have e2:History5.historyId (gstart s1 i) a+16=History5.historyId (gstart s1 h) b+16:=eq
  simp only [History5.historyId,gstart] at e2 hi hh
  split_ifs at e2 <;> omega

theorem split (n i : Nat) (hi : i<3*n+1) : i∈plain n ∨ i∈packed n := by
  simp only [plain,packed,List.mem_cons,List.mem_map,List.mem_range,List.mem_flatMap,List.not_mem_nil,or_false]
  rcases Nat.lt_or_ge i 1 with h|h
  · left; left; omega
  · have:=Nat.mod_lt (i-1) (show 0<3 by decide)
    rcases (show (i-1)%3=0 ∨ (i-1)%3=1 ∨ (i-1)%3=2 by omega) with r|r|r
    · left; right; exact ⟨(i-1)/3,by omega,by omega⟩
    · right; exact ⟨(i-1)/3,by omega,by omega⟩
    · right; exact ⟨(i-1)/3,by omega,by omega⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowGeo

end

-- ArchiveStockRows.FinalW / bankPorts / FinalW.bank: in Window (build-chain switch)

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffixW
open Arithmetic MappedCompressed StockWindowGeo
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2: `ArchiveStockSuffix`, generic in the exit tick `e` (dadon: 270, a multiple of 5) and over the
window's archive cells `StockWindowGeo.archives s1 n` (dadon: four banks). The stock suffix ticks after `e`
never touch an archive cell. The proofs are dadon's with 270/271 replaced by `e`/`e+1`. Ticks `e+1..e+4` are not
due, which dadon special-cased as `i < 275`; here the `packDue` split alone handles them. -/

private theorem no_pack (e i:Nat) (e5:e%5=0) (lo:e+1 ≤ i) (hi:i < 512) (r:Nat) (old:r < e) (d sw:Bool):
    logical sw r∉wires (Rolling1588.Integer.packFirst base d i) ∧
    logical sw r∉wires (Rolling1588.unpackAtTick d i):=by
  have disjoint (due:History5.packDue i=true) (j:Fin 10):logical sw r≠History5.historyMap base (i-5) j:=by
    simp only [History5.packDue,decide_eq_true_eq] at due
    have lim:=j.isLt
    cases sw <;> simp only [logical,Bool.false_eq_true,if_false,if_true,History5.historyMap,History5.historyId,base,Wire]
    all_goals split_ifs <;> omega
  constructor
  · intro h
    rw [Rolling1588.Integer.packFirst,if_neg (show i≠5 by omega),Rolling1588.Integer.pack_support_eq] at h
    unfold History5.packAfter at h
    split at h
    · rename_i due
      obtain ⟨j,eq⟩:=History5.history_gate_mem base (i-5) _ (Or.inl rfl) _ h
      exact disjoint due j eq
    · simp [wires] at h
  · intro h
    rw [←Rolling1588.Integer.unpackFirst_base,Rolling1588.Integer.unpackFirst,if_neg (show i≠5 by omega),
      Rolling1588.Integer.decodeBefore_support_eq] at h
    unfold History5.decodeBefore at h
    split at h
    · rename_i due
      obtain ⟨j,eq⟩:=History5.history_gate_mem base (i-5) _ (Or.inr rfl) _ h
      exact disjoint due j eq
    · simp [wires] at h

theorem one (e:Nat) (e5:e%5=0) (he:e≤511) (d sw:Bool) (r i:Nat) (old:r < e) (lo:e+1 ≤ i) (hi:i < 512):
    site e sw r∉wires (renameProgram (OB5.sig i) (TickRanges.tick base i ++ Rolling1588.Integer.packFirst base d i)) ∧
    site e sw r∉wires (renameProgram (OB5.sig i) (Rolling1588.unpackAtTick d i ++ W.ReverseCarry.compactReceiverTick base i)):=by
  have past:WideReference.Earlier i (logical sw r):=⟨r,by omega,by cases sw <;> simp [logical]⟩
  have off:=WideReference.away hi past
  have pack:=no_pack e i e5 lo hi r old d sw
  have pre (q:Wire) (eq:OB5.sig i q=site e sw r):q=logical sw r:=by
    -- `StairPacket.stable` (parent) hides the opened name
    rw [←StockWindowGeo.stable i e r (by omega) he (by omega) old sw] at eq
    have inj:Function.Injective (OB5.sig i):=(OB5.sig_injective i (by omega))
    exact inj eq
  constructor <;> intro h <;> rw [renameProgram_support] at h <;>
    obtain ⟨q,mem,eq⟩:=Finset.mem_image.mp h <;> rw [pre q eq,wires_append,Finset.mem_union] at mem
  · rcases mem with tick|packet
    · exact off (List.mem_toFinset.mp (W.repairedTick_support base i hi base_pool_nodup (TickRanges.tick_support base i hi base_pool_nodup tick)))
    · exact pack.1 packet
  · rcases mem with packet|tick
    · exact pack.2 packet
    · exact off (List.mem_toFinset.mp (W.ReverseCarry.compactReceiverTick_support base i hi base_pool_nodup tick))

theorem suffix (e:Nat) (e5:e%5=0) (he:e≤511) (d sw:Bool) (r i n:Nat) (old:r < e) (lo:e+1 ≤ i) (hi:i+n≤512):
    site e sw r∉wires (Rolling1588TickGap.forward d i n) ∧ site e sw r∉wires (Rolling1588.reverse d i n):=by
  induction n generalizing i with
  | zero=>simp [Rolling1588TickGap.forward,Rolling1588.reverse,wires]
  | succ n ih=>
    have a:=one e e5 he d sw r i old lo (by omega)
    have b:=ih (i+1) (by omega) (by omega)
    simp only [Rolling1588TickGap.forward,Rolling1588.reverse,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨a.1,b.1⟩,⟨b.2,a.2⟩⟩

/-- `ArchiveStockSuffix.safe`, generic over the window's archive cells. -/
theorem safe (s1 n e:Nat) (lo5:5≤s1) (he:e=s1+15*n) (le:e≤511) (e5:e%5=0) (d:Bool) (i m:Nat) (lo:e+1 ≤ i)
    (hi:i+m≤512) (q:Wire) (mem:q∈archives s1 n):
    q∉wires (Rolling1588TickGap.forward d i m) ∧ q∉wires (Rolling1588.reverse d i m):=by
  obtain ⟨sw,r,old,rfl⟩:=archive_old s1 n e lo5 he le q mem
  exact suffix e e5 le d sw r i m old lo hi

def Same (s1 n:Nat) (a b:State):Prop:=a.phase=b.phase ∧ ∀q,q∉archives s1 n → a.basis q=b.basis q
theorem independent (s1 n:Nat) (P:Program) (off:∀q∈archives s1 n,q∉wires P)
    (m:List Bool) (s t:State) (same:Same s1 n s t):
    Same s1 n (run P m s) (run P m t) ∧ ∀q∈archives s1 n,(run P m s).basis q=s.basis q:=by
  have eqs:=pool_run_agrees P (wires P) (Finset.Subset.refl _) m s t same.1
    (fun q h=>same.2 q (fun mem=>off q mem h))
  refine ⟨⟨eqs.1,?_⟩,fun q mem=>run_preserves_outside _ m s _ (off q mem)⟩
  intro q ext
  by_cases use:q∈wires P
  · exact eqs.2 q use
  · rw [run_preserves_outside _ m s _ use,run_preserves_outside _ m t _ use]
    exact same.2 q ext
end ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffixW

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockGroupsW
open Arithmetic MappedCompressed StockWindowGeo
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2: `StockGroups` for the `n`-block window from `s1`. Group `i < 3n+1` packs ticks `gstart s1 i .. +4`.
Groups are `Nat` indices; dadon used `Fin 13`. dadon's `stockEq` was `rfl` at 210/61; here it is an induction
over the window's due ticks. -/

def ports (s1 i:Nat):Finset Wire:=Finset.univ.image (slot s1 i)
def one (s1:Nat) (d:Bool) (i:Nat):Program:=Rolling1588.encodeAt base d (gstart s1 i)
def batch (s1:Nat) (d:Bool) (seq:List Nat):Program:=seq.flatMap (one s1 d)
def all (n:Nat):List Nat:=List.range (3*n+1)
/-- `packs`, restated here (parallel chain); `StockTailW.packs_bridge` equates the two. -/
def packs (d:Bool) (i:Nat):Nat→Program
  | 0=>[]
  | n+1=>Rolling1588.Integer.packAfter base d i ++ packs d (i+1) n

theorem packs_add (d:Bool) (i a b:Nat):
    packs d i (a+b)=packs d i a++packs d (i+a) b:=by
  induction a generalizing i with
  | zero=>simp [packs]
  | succ a ih=>
    rw [show a+1+b=(a+b)+1 by omega,packs,packs,ih (i+1),List.append_assoc,
      show i+1+a=i+(a+1) by omega]

theorem pack_idle (d:Bool) (k:Nat) (hk:k%5≠0):Rolling1588.Integer.packAfter base d k=[]:=by
  unfold Rolling1588.Integer.packAfter
  rw [if_neg (by simp only [History5.packDue,decide_eq_true_eq]; omega)]

theorem packs_idle (d:Bool) (i:Nat) (h:i%5=1):packs d i 4=[]:=by
  simp only [packs,List.append_nil]
  rw [pack_idle d i (by omega),pack_idle d (i+1) (by omega),pack_idle d (i+1+1) (by omega),
    pack_idle d (i+1+1+1) (by omega)]
  rfl

theorem packs_due (d:Bool) (i:Nat) (h5:10≤ i) (h:i%5=0):
    packs d i 1=Rolling1588.encodeAt base d (i-5):=by
  simp only [packs,List.append_nil]
  unfold Rolling1588.Integer.packAfter Rolling1588.Integer.encode
  rw [if_pos (by simp only [History5.packDue,decide_eq_true_eq]; omega),if_neg (by omega)]

/-- `StockGroups.stockEq`, generic: the stock walk's packs over the window are the batch of its `3n+1` groups. -/
theorem stockEq (d:Bool) (s1 n:Nat) (lo:10≤s1) (h5:s1%5=0):
    packs d s1 (15*n+1)=batch s1 d (all n):=by
  have g:∀ m k,packs d (s1+5*k) (5*m+1)=(List.range' k (m+1)).flatMap (one s1 d):=by
    intro m
    induction m with
    | zero=>
      intro k
      rw [show 5*0+1=1 by rfl,packs_due d _ (by omega) (by omega)]
      simp only [List.range'_succ,List.range'_zero,List.flatMap_cons,List.flatMap_nil,List.append_nil,one,gstart]
      congr 1; omega
    | succ m ih=>
      intro k
      rw [show 5*(m+1)+1=1+(4+(5*m+1)) by omega,packs_add,packs_add,packs_due d _ (by omega) (by omega),
        packs_idle d _ (by omega),show s1+5*k+1+4=s1+5*(k+1) by omega,ih (k+1)]
      -- unfold both sides together; a `rw` of `range'_succ` hits only the left copy
      simp only [List.append_nil,List.range'_succ,List.flatMap_cons,List.nil_append,one,gstart]
      rw [show s1 - 5 + 5 * k = s1 + 5 * k - 5 by omega]
  have e:=g (3*n) 0
  rw [show 5*(3*n)+1=15*n+1 by omega,show s1+5*0=s1 by omega] at e
  rw [e,batch,all,List.range_eq_range']

theorem allNodup (n:Nat):(all n).Nodup:=List.nodup_range
theorem inAll {n i:Nat} (h:i<3*n+1):i∈all n:=List.mem_range.mpr h
theorem plainNodup (n:Nat):(plain n).Nodup:=by
  simp only [plain,List.nodup_cons,List.mem_map,List.mem_range,not_exists,not_and]
  refine ⟨fun b _ e=>by omega,?_⟩
  exact (List.nodup_range).map (fun a b e=>by omega)

theorem cover (s1:Nat) (d:Bool) (i:Nat):wires (one s1 d i)⊆ports s1 i:=by
  intro q h
  change q∈wires (renameProgram (MeasuredCodec5.label (slot s1 i)) (Rolling1588.codeEncode d)) at h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
  rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
  exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,by simp [MeasuredCodec5.label,ha]⟩

private theorem distant (s1:Nat) (lo:5≤s1) {i h:Nat} (hi:gstart s1 i+5≤1028) (hh:gstart s1 h+5≤1028) (ne:i≠h)
    {q:Wire} (mem:q∈ports s1 i):q∉ports s1 h:=by
  intro hit
  obtain ⟨a,_,ea⟩:=Finset.mem_image.mp mem
  obtain ⟨b,_,eb⟩:=Finset.mem_image.mp hit
  exact distinct s1 lo i h hi hh ne a b (ea.trans eb.symm)

theorem batch_cover (s1:Nat) (d:Bool) (seq:List Nat) (q:Wire) (hit:q∈wires (batch s1 d seq)):
    ∃i∈seq,q∈ports s1 i:=by
  induction seq with
  | nil=>simp [batch,wires] at hit
  | cons h t ih=>
    change q∈wires (one s1 d h++batch s1 d t) at hit
    rw [wires_append,Finset.mem_union] at hit
    rcases hit with a|b
    · exact ⟨h,by simp,cover _ _ _ a⟩
    · obtain ⟨i,ii,v⟩:=ih b
      exact ⟨i,by simp [ii],v⟩
theorem outside (s1:Nat) (d:Bool) (seq:List Nat) (s:State) (q:Wire) (off:∀i∈seq,q∉ports s1 i):
    (run (batch s1 d seq) [] s).basis q=s.basis q:=by
  apply run_preserves_outside
  intro hit;obtain ⟨i,mem,h⟩:=batch_cover s1 d seq q hit;exact off i mem h
theorem isolated (s1:Nat) (lo:5≤s1) (d:Bool) (seq:List Nat) (nd:seq.Nodup) (small:∀i∈seq,gstart s1 i+5≤1028)
    (s:State) (i:Nat) (mem:i∈seq) (q:Wire) (hq:q∈ports s1 i):
    (run (batch s1 d seq) [] s).basis q=(run (one s1 d i) [] s).basis q:=by
  induction seq generalizing s with
  | nil=>simp at mem
  | cons h t ih=>
    change (run (one s1 d h++batch s1 d t) [] s).basis q=_
    rw [run_append,run_take,List.drop_nil]
    obtain ⟨not,unique⟩:=List.nodup_cons.mp nd
    have sh:gstart s1 h+5≤1028:=small h (by simp)
    have st:∀k∈t,gstart s1 k+5≤1028:=fun k hk=>small k (by simp [hk])
    rcases List.mem_cons.mp mem with rfl|im
    · exact outside s1 d t _ q (fun j jj=>distant s1 lo sh (st j jj) (fun eq=>not (eq.symm ▸ jj)) hq)
    · have ne:i≠h:=fun eq=>not (eq ▸ im)
      have si:=st i im
      have hd:Disjoint (wires (one s1 d i)) (wires (one s1 d h)):=by
        rw [Finset.disjoint_left]
        intro q' a b
        exact distant s1 lo si sh ne (cover _ _ _ a) (cover _ _ _ b)
      rw [ih unique st (run (one s1 d h) [] s) im,run_disjoint_commute _ _ hd]
      exact run_preserves_outside _ _ _ _ (fun bad=>distant s1 lo si sh ne hq (cover _ _ _ bad))

/-- Window groups stay inside the history pool. -/
theorem small_all (s1 n:Nat) (ge:5≤s1) (le:s1+15*n≤511) :∀i∈all n,gstart s1 i+5≤1028:=by
  intro i hi; have:=List.mem_range.mp hi; simp only [gstart]; omega
theorem small_plain (s1 n:Nat) (ge:5≤s1) (le:s1+15*n≤511) :∀i∈plain n,gstart s1 i+5≤1028:=by
  intro i hi
  simp only [plain,List.mem_cons,List.mem_map,List.mem_range] at hi
  rcases hi with rfl|⟨b,hb,rfl⟩ <;> simp only [gstart] <;> omega

/-- dadon's instance: the 13 groups of 210..270. -/
example (d:Bool) : packs d 210 61=batch 210 d (all 4) := stockEq d 210 4 (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.StockGroupsW

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveReferenceW
open Arithmetic MappedCompressed WideReference StockWindowGeo
set_option linter.unusedVariables false
/-- par-d2: `StockArchiveReference.common` for the `n`-block window from `s1` (exit `s1+15n`). The native packs
of the window are the batch of its `plain` groups. -/
def ordinary (s1 n:Nat) (d:Bool):Program:=StockGroupsW.batch s1 d (plain n)
def common (s1 n:Nat) (d:Bool) (raw:State):State:=
  pullState (OB5.sig (s1+15*n)) (eraseSites (holes s1 n) (run (ordinary s1 n d) [] (run (span s1 (15*n+1)) [] raw)))
end ECDSAAdd.Entrant.StairPacket.StockArchiveReferenceW


namespace ECDSAAdd.Entrant.StairPacket.StockBaselineW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span WideReference.canonical

theorem high_lo (b:Nat):high (2+3*b)=false:=by simp only [high]; rw [decide_eq_false_iff_not]; omega
theorem high_hi (b:Nat):high (3+3*b)=true:=by simp only [high]; rw [decide_eq_true_eq]; omega
theorem packed_lt {n i:Nat} (h:i∈StockWindowGeo.packed n):i<3*n+1:=by
  -- `StairPacket.packed` (parent) hides `StockWindowGeo.packed`
  simp only [StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at h
  obtain ⟨b,hb,h|h⟩:=h <;> omega
theorem plain_lt {n i:Nat} (h:i∈plain n):i<3*n+1:=by
  simp only [plain,List.mem_cons,List.mem_map,List.mem_range] at h
  rcases h with rfl|⟨b,hb,rfl⟩ <;> omega

/-- `StockBaseline.chart`, generic: an archived group is the young/old half of its bank's tile. -/
theorem chart (s1 n i:Nat) (lo:5≤s1) (hi:i∈StockWindowGeo.packed n):gstart s1 i=tile (packet s1 i) (high i) ∧
    s1≤packet s1 i ∧ packet s1 i+15≤s1+15*n ∧ ∃b<n,packet s1 i=s1+15*b:=by
  simp only [StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hi
  obtain ⟨b,hb,h|h⟩:=hi <;> subst h
  · rw [high_lo]
    simp only [gstart,tile,packet,Bool.false_eq_true,if_false]
    exact ⟨by omega,by omega,by omega,b,hb,by omega⟩
  · rw [high_hi]
    simp only [gstart,tile,packet,if_true]
    exact ⟨by omega,by omega,by omega,b,hb,by omega⟩

theorem small512 (s1 n:Nat) (ge:5≤s1) (le:s1+15*n≤511) (seq:List Nat) (bound:∀i∈seq,i<3*n+1):∀i∈seq,gstart s1 i+5≤512:=by
  intro i hi; have:=bound i hi; simp only [gstart]; omega

theorem phase_batch (s1:Nat) (d:Bool) (seq:List Nat) (small:∀i∈seq,gstart s1 i+5≤512) (s:State):
    (run (batch s1 d seq) [] s).phase=s.phase:=by
  induction seq generalizing s with
  | nil=>simp only [batch,List.flatMap_nil,run]
  | cons h t ih=>
    change (run (one s1 d h++batch s1 d t) [] s).phase=_
    rw [run_append,run_take,List.drop_nil,ih (fun k hk=>small k (by simp [hk]))]
    exact Rolling1588.codeEncodeAt_zero_phase d (slot s1 h)
      (History5.historyMap_injective base base_pool_nodup (gstart s1 h) (small h (by simp))) s

end ECDSAAdd.Entrant.StairPacket.StockBaselineW

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span

/-! par-d2: `StockArchiveBanks` for the window of blocks `j1 .. jn` (`n = jn-j1+1` banks, exit at
`start j1+15n`). Bank `b < n` is the archive of block `j1+b`, or the exit archive for the last bank.
`exitCells` is the one fact needed from par-c2's exit form: its first 16 code ports are the cells of the exit
tick. `ArchiveBoundary270.codePortsList` starts with `cellsRestoreP 270`, as the generic exit form will. -/

theorem window_cells (k:Fin 26) (j:Fin 16):
    ArchiveJ7.codePorts k ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start k+15)).getD j 0:=by
  rw [ArchiveJ7.codePorts,ArchiveJ7.code_split,List.append_assoc,
    List.getD_append _ _ _ _ (by simp [Partial.cellsRestoreP])]

def siteAt (j1 jn:Fin 26) (exitPorts:Ports) (b:Nat) (j:Fin 16):Wire:=
  ArchiveStockRows.bankPorts j1 jn exitPorts b ⟨j.val,by omega⟩

theorem site_eq (j1 jn:Fin 26) (exitPorts:Ports)
    (exitCells:∀j:Fin 16,exitPorts ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start jn+15)).getD j 0)
    (b:Nat) (hb:j1.val+b≤jn.val) (j:Fin 16):siteAt j1 jn exitPorts b j=bankSite (start j1) b j:=by
  simp only [siteAt,ArchiveStockRows.bankPorts,bankSite,tick]
  split
  · rw [ArchiveJ7.head_port_eq _ j, window_cells]; congr 2; simp only [start]; omega
  · rw [exitCells]; congr 2; simp only [start]; omega

/-- dadon's `byte`, now independent of the bank: one small decide over `Bool × Fin 16`. -/
theorem byte:∀(d:Bool)(j:Fin 16),
    get (storage (native d (decide (8≤j.val)))) (index j)=get (StairArchiveNativeCut.canonical d d) j:=by decide +kernel

def nativeAt (ps:Fin 16→Wire) (d:Bool) (r:Nat) (s:State):Prop:=
  ∀j:Fin 16,s.basis (ps j)=(get (StairArchiveNativeCut.canonical d d) j).testBit r

theorem readback (e:Nat) (he:e≤511) (z:State) (q w:Wire) (eq:q=OB5.sig e w):
    (pullState (OB5.sig e) z).basis q=z.basis w:=by
  change z.basis (OB5.sig e q)=z.basis w
  rw [eq,OB5.sig_invol e he]

end ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW

end
-- END par-d2 StockWindowW

-- BEGIN par-d2 OrdinaryChainW (Tail8dd, serial tail; after ArchiveHistoryCompare)
section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainW
open Arithmetic MappedCompressed WideReference ArchiveHistoryCompare
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run

/-! par-d2: the mask/program half of dadon's `OrdinaryChain` (`mask{s}`, `progW{s}`, `add{s}`), as a fold over the
window's blocks from `s1`. Block `k` (start `s1+15k`) has two parts:
- its exit hands the previous block's archive cells (ticks `s-10..s-1`) to the stock frame (`newBank`, empty for
  the first block; dadon's `Logical{s}Exit.newBank`);
- its ordinary program is the stock encoder of its plain group (`s1-5` for the first block, `s-15` after).
dadon's three per-step decides over the growing masks (`maskEarly`, `progEarly`, `apart`) become `omega` bounds:
mask cells are older than `s-15`, and program cells are older than `s-10`. -/

/-- History cells of ticks `t .. t+9`. -/
def cells10 (t:Nat):List Wire:=(List.range' t 10).flatMap (fun r=>[base r,base (1028+r)])
def newBank (s1 s:Nat):List Wire:=if s=s1 then [] else cells10 (s-10)
/-- Plain group of block `k`. -/
def group (s1 k:Nat):Nat:=if k=0 then s1-5 else s1+15*k-15
def mask (s1:Nat):Nat→List Wire
  | 0=>[]
  | k+1=>mask s1 k++newBank s1 (s1+15*k)
def progW (s1:Nat) (d:Bool):Nat→Program
  | 0=>[]
  | k+1=>progW s1 d k++Rolling1588.encodeAt base d (group s1 k)

theorem mask_cells (s1:Nat) (lo:10≤s1) : ∀k,∀q∈mask s1 k,∃r,r+16≤s1+15*k ∧ (q=base r ∨ q=base (1028+r))
  | 0,q,h=>by simp [mask] at h
  | k+1,q,h=>by
    simp only [mask,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨r,hr,e⟩:=mask_cells s1 lo k q h
      exact ⟨r,by omega,e⟩
    · unfold newBank at h
      split at h
      · simp at h
      · simp only [cells10,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at h
        obtain ⟨r,⟨r1,r2⟩,e⟩:=h
        exact ⟨r,by omega,e⟩

theorem encode_cells (d:Bool) (t:Nat) : ∀q∈wires (Rolling1588.encodeAt base d t),
    ∃r,t≤r ∧ r≤t+4 ∧ (q=base r ∨ q=base (1028+r)) := by
  intro q h
  change q∈wires (renameProgram (MeasuredCodec5.label (History5.historyMap base t)) (Rolling1588.codeEncode d)) at h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
  rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
  refine ⟨t+a/2,by omega,by omega,?_⟩
  simp only [MeasuredCodec5.label,ha,dif_pos,History5.historyMap,History5.historyId]
  split
  · left; rfl
  · right; congr 1; omega

theorem prog_cells (s1:Nat) (lo:10≤s1) (d:Bool) : ∀k,∀q∈wires (progW s1 d k),∃r,r+11≤s1+15*k ∧ (q=base r ∨ q=base (1028+r))
  | 0,q,h=>by simp [progW,wires] at h
  | k+1,q,h=>by
    simp only [progW,wires_append,Finset.mem_union] at h
    rcases h with h|h
    · obtain ⟨r,hr,e⟩:=prog_cells s1 lo d k q h
      exact ⟨r,by omega,e⟩
    · obtain ⟨r,r1,r2,e⟩:=encode_cells d _ q h
      refine ⟨r,?_,e⟩
      simp only [group] at r1 r2
      split at r1 <;> split at r2 <;> omega

/-- `OrdinaryChain.add{s}`, generic: block `k ≥ 1` extends the mask and the ordinary program by one block. -/
theorem add (s1:Nat) (lo:10≤s1) (k:Nat) (hk:1≤k) (lim:s1+15*k+15≤512) (d:Bool) (raw baseRaw out:State)
    (old:Except (mask s1 k) raw (run (progW s1 d k) [] (run (span s1 (15*k)) [] baseRaw)))
    (step:Except (newBank s1 (s1+15*k)) out
      (run (Rolling1588.encodeAt base d (group s1 k)) [] (run (span (s1+15*k) 15) [] raw))) :
    Except (mask s1 (k+1)) out (run (progW s1 d (k+1)) [] (run (span s1 (15*(k+1))) [] baseRaw)) := by
  have h:=extend (s1+15*k) 15 lim _ _ _ _ raw (run (span s1 (15*k)) [] baseRaw) out old step
    (fun q hit=>by obtain ⟨r,hr,e⟩:=mask_cells s1 lo k q hit; exact ⟨r,by omega,e⟩)
    (fun q hit=>by obtain ⟨r,hr,e⟩:=prog_cells s1 lo d k q hit; exact ⟨r,by omega,e⟩)
    (fun q hit used=>by
      obtain ⟨r,hr,e⟩:=mask_cells s1 lo k q hit
      obtain ⟨r',r1,r2,e'⟩:=encode_cells d _ q used
      simp only [group,if_neg (show k≠0 by omega)] at r1 r2
      rcases e with rfl|rfl <;> rcases e' with e'|e' <;> simp only [base,Wire] at e' <;> omega)
  have chronology:run (span s1 (15*(k+1))) [] baseRaw=run (span (s1+15*k) 15) [] (run (span s1 (15*k)) [] baseRaw):=by
    rw [show 15*(k+1)=15*k+15 by omega,spanAppend s1 (15*k) 15,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h

/-- The exit tick (`OrdinaryChain.add270`, generic): the stock tick `e` itself and the last archive's cells. -/
theorem add_last (s1:Nat) (lo:10≤s1) (n:Nat) (hn:1≤n) (lim:s1+15*n+1≤512) (d:Bool) (raw baseRaw out:State)
    (old:Except (mask s1 n) raw (run (progW s1 d n) [] (run (span s1 (15*n)) [] baseRaw)))
    (step:Except (cells10 (s1+15*n-10)) out
      (run (Rolling1588.encodeAt base d (s1+15*n-15)) [] (run (span (s1+15*n) 1) [] raw))) :
    Except (mask s1 n++cells10 (s1+15*n-10)) out
      (run (progW s1 d n++Rolling1588.encodeAt base d (s1+15*n-15)) [] (run (span s1 (15*n+1)) [] baseRaw)) := by
  have h:=extend (s1+15*n) 1 lim _ _ _ _ raw (run (span s1 (15*n)) [] baseRaw) out old step
    (fun q hit=>by obtain ⟨r,hr,e⟩:=mask_cells s1 lo n q hit; exact ⟨r,by omega,e⟩)
    (fun q hit=>by obtain ⟨r,hr,e⟩:=prog_cells s1 lo d n q hit; exact ⟨r,by omega,e⟩)
    (fun q hit used=>by
      obtain ⟨r,hr,e⟩:=mask_cells s1 lo n q hit
      obtain ⟨r',r1,r2,e'⟩:=encode_cells d _ q used
      rcases e with rfl|rfl <;> rcases e' with e'|e' <;> simp only [base,Wire] at e' <;> omega)
  have chronology:run (span s1 (15*n+1)) [] baseRaw=run (span (s1+15*n) 1) [] (run (span s1 (15*n)) [] baseRaw):=by
    rw [spanAppend s1 (15*n) 1,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h

/-! First ship 120..255 (s1 = 120, n = 10 blocks, exit 270). -/
example : group 120 0=115 ∧ group 120 9=240 ∧ newBank 120 120=[] ∧ newBank 120 135=cells10 125 := ⟨rfl,rfl,rfl,rfl⟩

-- needs par-a WideReference patch (oldSites, endRaw_inside_gen/outside_gen); goes inside OrdinaryChainW after `add_last`
/-! Hole carry, generic (`OrdinaryChain.carry240/255` and `holes225/240/255`).
dadon decided `q∉sites` and `oldRange` per block. Here both are hypotheses, so the proof
does not grow with the window. `clear` is par-c2's `cleared_holes` (still per block).
`endRaw_inside_gen` reads the snapshot through `OB5.sig (s+14)`, which is the identity
on these wires only while `Fixed s` holds; the statement does not assume that. -/

theorem carry (s:Nat) (hs:s+14≤511) (holes:List Wire)
    (off:∀q∈holes,q∉oldSites s) (aged:∀q∈holes,oldRange s q)
    (raw history:State) (clear:∀q∈holes,raw.basis q=false) :
    ∀q∈holes,(endRaw s raw history).basis q=false := by
  intro q hq
  rw [endRaw_outside_gen s hs raw history q (off q hq)]
  rw [run_preserves_outside (span s 15) [] raw q
    (pastOffSpan s 15 q (by omega) (OrdinaryChain.early s q (aged q hq)))]
  exact clear q hq

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainW

end
-- END par-d2 OrdinaryChainW

-- ==== w4: build-w4b StockTailW + StockRowVectorW ====
-- BEGIN par-d2 StockTailW (serial tail: Tail8dd; only what needs StockDelayed.window / StockArchiveByte)
section

namespace ECDSAAdd.Entrant.StairPacket.StockGroupsW
set_option linter.unusedVariables false
/-- The parallel chain's `packs` is dadon's `StockDelayed.packs`. -/
theorem packs_bridge (d:Bool) (i n:Nat):StockDelayed.packs d i n=packs d i n:=by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=>rw [StockDelayed.packs,packs,ih]
end ECDSAAdd.Entrant.StairPacket.StockGroupsW

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveTruthW
open Arithmetic MappedCompressed WideReference SkywalkRails StairArchiveTrace StairArchiveRaw StairArchiveNativeRows CodecBitSliceVerify
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run SkywalkNat.step span WideReference.canonical StairArchiveRaw.rawCol SkywalkTrace.trace

private theorem observeSite (b:BasisState) (t:Nat) (q:Fin 10) (v:Bool×Bool)
    (a:b (base (t+q.val/2))=v.1) (c:b (base (1028+(t+q.val/2)))=v.2):
    b (History5.historyMap base t q)=letterBit v q:=by
  unfold History5.historyMap History5.historyId letterBit
  by_cases h:q.val%2=0
  · simpa only [if_pos h] using a
  · simpa only [if_neg h,Nat.add_assoc] using c

/-- `StockArchiveTruth.raw_for`, generic in the window start `s1` and length `len` (dadon: 210, 61). -/
theorem raw_for (s1 len x p:Nat) (lim:s1+len≤512) (good:Bounds x p) (s:State) (dom:Domain s1 x p s)
    (k:Nat) (start:s1≤k) (stop:k+15≤s1+len)
    (row:Nat) (truth:ArchiveStockRows.Chronology k x p row) (hi:Bool) (q:Fin 10):
    (run (span s1 len) [] s).basis (History5.historyMap base (StockWindowGeo.tile k hi) q)=
      (rawCol ((if hi then 10 else 0)+q.val)).testBit row:=by
  let e:Nat:=(if hi then 10 else 0)+q.val
  have bound:e<20:=by cases hi <;> simp [e] <;> omega
  have lo:s1≤StockWindowGeo.tile k hi+q.val/2:=by unfold StockWindowGeo.tile;omega
  have lim':StockWindowGeo.tile k hi+q.val/2<s1+len:=by cases hi <;> simp [StockWindowGeo.tile] <;> omega
  have obs:=trace_sites s1 len x p lim good s [] dom (StockWindowGeo.tile k hi+q.val/2) lo lim'
  have exactBit:=observeSite (run (span s1 len) [] s).basis (StockWindowGeo.tile k hi) q _ obs.1 obs.2
  have label:=StockArchiveTruth.observedLabel k x p row truth ⟨e,bound⟩
  change (rawCol e).testBit row=letterBit (SkywalkTrace.code (WideReference.canonical (k+(5+e/2)) x p)) e at label
  have shift : k+(5+e/2)=StockWindowGeo.tile k hi+q.val/2:=by cases hi <;> simp [StockWindowGeo.tile,e] <;> omega
  have parity:e%2=q.val%2:=by
    cases hi <;> simp [e]
    omega
  rw [shift] at label
  have bit (v:Bool×Bool):letterBit v e=letterBit v q:=by simp only [letterBit,parity]
  exact exactBit.trans ((bit _).symm.trans label.symm)

theorem native_byte (s1 len x p:Nat) (lim:s1+len≤512) (good:Bounds x p) (s:State) (dom:Domain s1 x p s)
    (k:Nat) (start:s1≤k) (stop:k+15≤s1+len)
    (row:Nat) (lm:row<63145) (truth:ArchiveStockRows.Chronology k x p row) (d hi:Bool) (m:List Bool):
    let raw:=run (span s1 len) [] s
    let f:=History5.historyMap base (StockWindowGeo.tile k hi)
    let out:=run (Rolling1588.codeEncodeAt d f) m raw
    out.phase=raw.phase ∧ ∀q:Fin 10,out.basis (f q)=(get (storage (native d hi)) q).testBit row:=by
  exact StockArchiveByte.run_byte d hi row lm _ (History5.historyMap_injective base base_pool_nodup _
    (by cases hi <;> simp [StockWindowGeo.tile] <;> omega)) _ m
    (raw_for s1 len x p lim good s dom k start stop row truth hi)
end ECDSAAdd.Entrant.StairPacket.StockArchiveTruthW


namespace ECDSAAdd.Entrant.StairPacket.StockBaselineW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span WideReference.canonical

theorem receipt (s1 n:Nat) (lo:10≤s1) (le:s1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p) (s:State)
    (dom:Domain s1 x p s) (i:Nat) (active:i∈StockWindowGeo.packed n) (row:Nat) (lim:row<63145)
    (truth:ArchiveStockRows.Chronology (packet s1 i) x p row) (j:Fin 10):
    let raw:=run (span s1 (15*n+1)) [] s
    (run (batch s1 d (all n)) [] raw).basis (slot s1 i j)=(get (storage (native d (high i))) j).testBit row:=by
  have ⟨shape,lo',hi',_⟩:=chart s1 n i (by omega) active
  let raw:=run (span s1 (15*n+1)) [] s
  have obs:=StockArchiveTruthW.native_byte s1 (15*n+1) x p (by omega) good s dom (packet s1 i) lo' (by omega)
    row lim truth d (high i) []
  have bit:=obs.2 j
  change (run (batch s1 d (all n)) [] raw).basis (slot s1 i j)=_
  rw [isolated s1 (by omega) d (all n) (allNodup n) (small_all s1 n (by omega) le) raw i (inAll (packed_lt active)) (slot s1 i j)
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)]
  change (run (Rolling1588.codeEncodeAt d (History5.historyMap base (gstart s1 i))) [] raw).basis
    (History5.historyMap base (gstart s1 i) j)=_
  rwa [shape]

/-- `StockBaseline.from_final`, generic over the window's banks. -/
theorem from_final {j1 jn:Fin 26} {exitPorts:ArchivePortAction.Ports} (n:Nat) (hn:jn.val+1=j1.val+n) (d:Bool)
    (x:Nat) (a:State) (results:ArchiveStockRows.FinalW j1 jn exitPorts d x p a) (i:Nat) (active:i∈StockWindowGeo.packed n) :
    ∃row<63145,ArchiveStockRows.Chronology (packet (start j1) i) x p row:=by
  obtain ⟨-,-,-,b,hb,eq⟩:=chart (start j1) n i (by simp only [start]; omega) active
  obtain ⟨r,l,t,_⟩:=results.bank b (by omega)
  exact ⟨r,l,by rw [eq]; exact t⟩

/-- `StockBaseline.comparison`, generic: after the window, the stock walk and the window's reference state agree
off the archive cells. -/
theorem comparison {j1 jn:Fin 26} {exitPorts:ArchivePortAction.Ports} (n:Nat) (hn:jn.val+1=j1.val+n)
    (le:start j1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start j1) s.basis)
    (results:ArchiveStockRows.FinalW j1 jn exitPorts d x p a):
    ArchiveStockSuffixW.Same (start j1) n
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) s))
      (StockArchiveReferenceW.common (start j1) n d s):=by
  have lo:10≤start j1:=by simp only [start]; omega
  have h5:start j1%5=0:=by simp only [start]; omega
  let s1:=start j1
  let raw:=run (span s1 (15*n+1)) [] s
  have stock:=StockDelayed.window d x good.nonzero good.small s1 (15*n+1) (by omega) (by omega) s m stage
  rw [show s1+(15*n+1)-1=s1+15*n by omega] at stock
  change run (Rolling1588TickGap.forward d s1 (15*n+1)) m (pullState (OB5.sig (s1-1)) s)=
    pullState (OB5.sig (s1+15*n)) (run (StockDelayed.packs d s1 (15*n+1)) [] raw) at stock
  rw [stock,packs_bridge,stockEq d s1 n lo h5,StockArchiveReferenceW.common,StockArchiveReferenceW.ordinary]
  refine ⟨(phase_batch s1 d (all n) (small512 s1 n (by omega) le _ (fun i hi=>List.mem_range.mp hi)) raw).trans
    (phase_batch s1 d (plain n) (small512 s1 n (by omega) le _ (fun i hi=>plain_lt hi)) raw).symm,?_⟩
  intro q safe
  let y:=OB5.sig (s1+15*n) q
  change (run (batch s1 d (all n)) [] raw).basis y=
    (if y∈holes s1 n then false else (run (batch s1 d (plain n)) [] raw).basis y)
  have away:OB5.sig (s1+15*n) y∉archives s1 n:=by simpa only [y,OB5.sig_invol (s1+15*n) (by omega)] using safe
  by_cases old:∃i∈StockWindowGeo.packed n,y∈ports s1 i
  · obtain ⟨i,used,inside⟩:=old
    obtain ⟨j,_,atSite⟩:=Finset.mem_image.mp inside
    have hs:=sparse s1 n (s1+15*n) (by omega) rfl le i used j
    rcases hs with ⟨blank,hit⟩|covered
    · rw [←atSite,if_pos hit]
      obtain ⟨row,lim,history⟩:=from_final n hn d x a results i used
      have dom:=WideReference.initial s1 x p (by omega) d s stage
      have bit:=receipt s1 n lo le d x good s dom i used row lim history j
      have cleared (k:Nat) (ok:k=5 ∨ k=9):CodecBitSliceVerify.get (storage (native d (high i))) k=0:=by
        rcases ok with rfl|rfl <;> rfl
      exact bit.trans ((congrArg (fun a:Nat=>a.testBit row) (cleared j (by rcases blank with rfl|rfl <;> decide))).trans
        (Nat.zero_testBit row))
    · exact (away (atSite ▸ covered)).elim
  · have nh:y∉holes s1 n:=by
      intro h;obtain ⟨i,used,j,e⟩:=hole_slot s1 n y h
      exact old ⟨i,used,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm⟩⟩
    rw [if_neg nh]
    by_cases saved:∃i∈plain n,y∈ports s1 i
    · obtain ⟨i,mem,h⟩:=saved
      exact (isolated s1 (by omega) d (all n) (allNodup n) (small_all s1 n (by omega) le) raw i (inAll (plain_lt mem)) y h).trans
        (isolated s1 (by omega) d (plain n) (plainNodup n) (small_plain s1 n (by omega) le) raw i mem y h).symm
    · have off (i:Nat) (hi:i<3*n+1):y∉ports s1 i:=by
        intro h;rcases StockWindowGeo.split n i hi with m|m
        · exact saved ⟨i,m,h⟩
        · exact old ⟨i,m,h⟩
      exact (outside s1 d (all n) raw y (fun i hi=>off i (List.mem_range.mp hi))).trans
        (outside s1 d (plain n) raw y (fun i hi=>off i (plain_lt hi))).symm

end ECDSAAdd.Entrant.StairPacket.StockBaselineW

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span

/-! par-d2: `StockArchiveBanks` for the window of blocks `j1 .. jn` (`n = jn-j1+1` banks, exit at
`start j1+15n`). Bank `b < n` is the archive of block `j1+b`, or the exit archive for the last bank.
`exitCells` is the one fact needed from par-c2's exit form: its first 16 code ports are the cells of the exit
tick. `ArchiveBoundary270.codePortsList` starts with `cellsRestoreP 270`, as the generic exit form will. -/

theorem stock_state (s1 n:Nat) (lo:10≤s1) (h5:s1%5=0) (le:s1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p)
    (s:State) (m:List Bool) (stage:Rolling1588.Integer.Stage base d x p s1 s.basis):
    run (Rolling1588TickGap.forward d s1 (15*n+1)) m (pullState (OB5.sig (s1-1)) s)=
    pullState (OB5.sig (s1+15*n)) (run (batch s1 d (all n)) [] (run (span s1 (15*n+1)) [] s)):=by
  rw [←stockEq d s1 n lo h5,←packs_bridge]
  have w:=StockDelayed.window d x good.nonzero good.small s1 (15*n+1) (by omega) (by omega) s m stage
  rwa [show s1+(15*n+1)-1=s1+15*n by omega] at w

theorem stored (j1 jn:Fin 26) (exitPorts:Ports)
    (exitCells:∀j:Fin 16,exitPorts ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start jn+15)).getD j 0)
    (n:Nat) (hn:jn.val+1=j1.val+n) (le:start j1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p) (s:State)
    (m:List Bool) (stage:Rolling1588.Integer.Stage base d x p (start j1) s.basis) (b:Nat) (hb:b<n) (row:Nat)
    (lim:row<63145) (truth:ArchiveStockRows.Chronology (start j1+15*b) x p row):
    nativeAt (siteAt j1 jn exitPorts b) d row
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) s)):=by
  have lo:10≤start j1:=by simp only [start]; omega
  have h5:start j1%5=0:=by simp only [start]; omega
  intro j
  obtain ⟨addr,clock,used,hj⟩:=chart (start j1) n b (start j1+15*n) (by omega) hb rfl le j
  have dom:=WideReference.initial (start j1) x p (by omega) d s stage
  have bit:=StockBaselineW.receipt (start j1) n lo le d x good s dom (group b j) used row lim
    (by rw [clock]; exact truth) (index j)
  rw [stock_state (start j1) n lo h5 le d x good s m stage,
    readback _ (by omega) _ _ _ ((site_eq j1 jn exitPorts exitCells b (by omega) j).trans addr)]
  exact bit.trans (congrArg (fun a:Nat=>a.testBit row) (by rw [hj]; exact byte d j))

structure Paired (j1 jn:Fin 26) (exitPorts:Ports) (n:Nat) (d:Bool) (x:Nat) (a s:State) (rows:Nat→Nat):Prop where
  equality:ArchiveStockSuffixW.Same (start j1) n a s
  labels:∀b<n,rows b<63145 ∧ ArchiveStockRows.Chronology (start j1+15*b) x p (rows b)
  custom:∀b<n,Kept (ArchiveStockRows.bankPorts j1 jn exitPorts b) d (rows b) a
  stock:∀b<n,nativeAt (siteAt j1 jn exitPorts b) d (rows b) s

theorem Paired.through {j1 jn exitPorts n d x a s rows}
    (exitCells:∀j:Fin 16,exitPorts ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start jn+15)).getD j 0)
    (hn:jn.val+1=j1.val+n) (le:start j1+15*n≤511)
    (pair:Paired j1 jn exitPorts n d x a s rows) (P:Program)
    (off:∀q∈archives (start j1) n,q∉wires P) (m:List Bool):Paired j1 jn exitPorts n d x (run P m a) (run P m s) rows:=by
  have h:=ArchiveStockSuffixW.independent (start j1) n P off m a s pair.equality
  have mem (b:Nat) (hb:b<n) (j:Fin 16):siteAt j1 jn exitPorts b j∈archives (start j1) n:=by
    rw [site_eq j1 jn exitPorts exitCells b (by omega) j]; exact bank_mem _ n b hb j
  refine ⟨h.1,pair.labels,?_,?_⟩
  · intro b hb j
    exact (h.2 (siteAt j1 jn exitPorts b j) (mem b hb j)).trans (pair.custom b hb j)
  · intro b hb j
    exact (run_preserves_outside P m s (siteAt j1 jn exitPorts b j) (off _ (mem b hb j))).trans (pair.stock b hb j)
end ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW

end
-- END par-d2 StockTailW

-- BEGIN build-w4b StockRowVectorW (B2-a)
-- Main (w4r): after par-d2's StockTailW section (StockArchiveBanksW) and after dadon's StockRowVector (uses its
-- `historical`, generic already).
section

namespace ECDSAAdd.Entrant.StairPacket.StockRowVectorW
open Arithmetic MappedCompressed Secp256k1 StockCanonicalRow StockStrongChain StockArchiveBanksW
open StairArchiveRaw WideReference ArchivePortAction Partial
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-- dadon's `cross{s}`, for every block: the bank-high crossing bit of the leave's true middle. -/
def crossW (j : Fin 26) (z : SkywalkNat.State) : Bool := HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j z)
/-- dadon's `StockRowVector.keys`, for the window of blocks `j1, j1+1, …`: bank `b` is block `j1+b`'s archive key. -/
noncomputable def keys (j1 : Fin 26) (x p b : Nat) : Nat → Bool :=
  if h : j1.val + b < 26 then value x p (start j1 + 15*b) (Shadow7.sbP (start j1 + 15*b)) (crossW ⟨j1.val+b, h⟩)
  else fun _ => false
/-- dadon's `StockRowVector.rows`: a function of `(x, p)` only (the pairing across runs needs that). -/
noncomputable def rows (j1 : Fin 26) (x p : Nat) (b : Nat) : Nat := select (keys j1 x p b)

/-- dadon's `StockStrongChain.final`, generic: every bank holds its key-selected row. -/
def final (j1 jn : Fin 26) (exitPorts : Ports) (d : Bool) (x p : Nat) (s : State) : Prop :=
  ∀ b, j1.val + b ≤ jn.val → SavedKey (keys j1 x p b) (ArchiveStockRows.bankPorts j1 jn exitPorts b) d s

theorem trace {j1 jn exitPorts d x p s} (h : final j1 jn exitPorts d x p s) (b : Nat) (hb : j1.val + b ≤ jn.val) :
    ArchiveStockRows.Chronology (start j1 + 15*b) x p (rows j1 x p b) := by
  have k := (h b hb).2.1
  have lt : j1.val + b < 26 := by have := jn.isLt; omega
  simp only [rows, keys, dif_pos lt] at k ⊢
  exact StockRowVector.historical _ _ x p _ _ k

/-- dadon's `StockRowVector.binding`, generic over the window's banks. -/
theorem binding (j1 jn : Fin 26) (exitPorts : Ports)
    (exitCells : ∀ j : Fin 16, exitPorts ⟨j.val, by omega⟩ = (Partial.cellsRestoreP (start jn+15)).getD j 0)
    (n : Nat) (hn : jn.val+1 = j1.val+n) (le : start j1+15*n ≤ 511) (d : Bool) (x : Nat) (good : Bounds x p)
    (raw a : State) (m : List Bool) (stage : Rolling1588.Integer.Stage base d x p (start j1) raw.basis)
    (stored : final j1 jn exitPorts d x p a)
    (same : ArchiveStockSuffixW.Same (start j1) n a
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) raw))) :
    Paired j1 jn exitPorts n d x a
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) raw)) (rows j1 x p) := by
  refine ⟨same, fun b hb => ⟨(stored b (by omega)).1, trace stored b (by omega)⟩, fun b hb => (stored b (by omega)).2.2,
    fun b hb => ?_⟩
  exact StockArchiveBanksW.stored j1 jn exitPorts exitCells n hn le d x good raw m stage b hb _ (stored b (by omega)).1
    (trace stored b (by omega))

end ECDSAAdd.Entrant.StairPacket.StockRowVectorW

end
-- END build-w4b StockRowVectorW
-- ==== w4: end stocktail ====

-- ==== build-main2: generic OrdinaryChain (build-leaves OrdW) ====
/-! build-ordinary (build-leaves): the generic `OrdinaryChain` Ref half for the window 120..255 (exit 270).
Replaces dadon's literal `OrdinaryChain` (`Ref240/255/270`, `begin225`, `next240/255`, `last270`, `terminal`, `finish`,
`project`, `readOld`, `keepTick`, `keepEncode`, `holes240/255`, `carry255`, `seven`, `wires`) by one induction over
the fold's blocks. Every proof here is O(1) in the number of blocks: no decide over the window's growing lists. -/

-- ===== Part 1: generic list facts and the finish (any window `s1`, `n` blocks, exit `s1+15n`) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed WideReference ArchiveHistoryCompare
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

theorem plain_succ (n : Nat) : StockWindowGeo.plain (n+1)=StockWindowGeo.plain n++[1+3*n] := by
  simp only [StockWindowGeo.plain,List.range_succ,List.map_append,List.map_cons,List.map_nil,List.cons_append]

theorem packed_succ (n : Nat) : StockWindowGeo.packed (n+1)=StockWindowGeo.packed n++[2+3*n,3+3*n] := by
  simp only [StockWindowGeo.packed,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil]

theorem holes_succ (s1 n : Nat) : StockWindowGeo.holes s1 (n+1)=StockWindowGeo.holes s1 n++
    [base (1028+StockWindowGeo.gstart s1 (2+3*n)+2),base (1028+StockWindowGeo.gstart s1 (2+3*n)+4),
     base (1028+StockWindowGeo.gstart s1 (3+3*n)+2),base (1028+StockWindowGeo.gstart s1 (3+3*n)+4)] := by
  simp only [StockWindowGeo.holes,packed_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.cons_append,List.nil_append]

theorem batch_append (s1 : Nat) (d : Bool) (a b : List Nat) :
    StockGroupsW.batch s1 d (a++b)=StockGroupsW.batch s1 d a++StockGroupsW.batch s1 d b := by
  simp only [StockGroupsW.batch,List.flatMap_append]

/-- The window's ordinary program after `n+1` blocks is the reference's batch of the `plain` groups. -/
theorem progW_plain (s1 : Nat) (lo : 5≤s1) (d : Bool) :
    ∀n,OrdinaryChainW.progW s1 d (n+1)=StockGroupsW.batch s1 d (StockWindowGeo.plain n)
  | 0=>by
    show []++Rolling1588.encodeAt base d (OrdinaryChainW.group s1 0)=_
    simp only [OrdinaryChainW.group,↓reduceIte,List.nil_append,StockWindowGeo.plain,List.range_zero,List.map_nil,
      StockGroupsW.batch,List.flatMap_cons,List.flatMap_nil,List.append_nil,StockGroupsW.one,StockWindowGeo.gstart,
      Nat.mul_zero,Nat.add_zero]
  | n+1=>by
    have e:OrdinaryChainW.progW s1 d (n+1+1)=OrdinaryChainW.progW s1 d (n+1)++
      Rolling1588.encodeAt base d (OrdinaryChainW.group s1 (n+1)):=rfl
    rw [e,progW_plain s1 lo d n,plain_succ,batch_append]
    congr 1
    simp only [StockGroupsW.batch,List.flatMap_cons,List.flatMap_nil,List.append_nil,StockGroupsW.one,
      OrdinaryChainW.group,if_neg (show n+1≠0 by omega),StockWindowGeo.gstart]
    congr 1; omega

theorem progW_last (s1 n : Nat) (lo : 5≤s1) (hn : 1≤n) (d : Bool) :
    OrdinaryChainW.progW s1 d n++Rolling1588.encodeAt base d (s1+15*n-15)=
      StockGroupsW.batch s1 d (StockWindowGeo.plain n) := by
  rw [←progW_plain s1 lo d n]
  show _=OrdinaryChainW.progW s1 d n++Rolling1588.encodeAt base d (OrdinaryChainW.group s1 n)
  rw [OrdinaryChainW.group,if_neg (by omega)]

/-- Every hole is a B-side history cell of a tick inside the window (after its first five ticks). -/
theorem hole_cell (s1 n : Nat) (lo : 5≤s1) :
    ∀w∈StockWindowGeo.holes s1 n,∃r:Nat,s1+7≤r ∧ r+1≤s1+15*n ∧ w=base (1028+r) := by
  intro w hw
  simp only [StockWindowGeo.holes,StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false] at hw
  obtain ⟨i,⟨b,hb,hi⟩,e⟩:=hw
  simp only [StockWindowGeo.gstart] at e
  rcases hi with rfl|rfl <;> rcases e with rfl|rfl
  · exact ⟨s1-5+5*(2+3*b)+2,by omega,by omega,by congr 1⟩
  · exact ⟨s1-5+5*(2+3*b)+4,by omega,by omega,by congr 1⟩
  · exact ⟨s1-5+5*(3+3*b)+2,by omega,by omega,by congr 1⟩
  · exact ⟨s1-5+5*(3+3*b)+4,by omega,by omega,by congr 1⟩

/-- Letter `a` of bank `b`'s ten ticks is a letter of one of its two archived groups. -/
theorem cell_letter (s1 b a : Nat) (lo : 5≤s1) (ha : a<10) :
    base (s1+15*b+5+a)=StockWindowGeo.slot s1 (2+3*b+a/5) ⟨2*(a%5),by omega⟩ ∧
    base (1028+(s1+15*b+5+a))=StockWindowGeo.slot s1 (2+3*b+a/5) ⟨2*(a%5)+1,by omega⟩ := by
  simp only [StockWindowGeo.slot,History5.historyMap,History5.historyId,StockWindowGeo.gstart,Fin.val_mk]
  constructor
  · rw [if_pos (by omega)]; congr 1; omega
  · rw [if_neg (by omega)]; congr 1; omega

/-- `StockGroups.sparse` read on bank `b`'s ten ticks: each cell is a hole or, in the exit frame, an archive cell. -/
theorem cells_census (s1 n b : Nat) (lo : 5≤s1) (hb : b<n) (le : s1+15*n≤511) :
    ∀w∈OrdinaryChainW.cells10 (s1+15*b+5),
      w∈StockWindowGeo.holes s1 n ∨ OB5.sig (s1+15*n) w∈StockWindowGeo.archives s1 n := by
  intro w hw
  simp only [OrdinaryChainW.cells10,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
    or_false] at hw
  obtain ⟨r,⟨r1,r2⟩,e⟩:=hw
  have hi:2+3*b+(r-(s1+15*b+5))/5∈StockWindowGeo.packed n:=by
    simp only [StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨b,hb,by omega⟩
  have hr:s1+15*b+5+(r-(s1+15*b+5))=r:=by omega
  have cl:=cell_letter s1 b (r-(s1+15*b+5)) lo (by omega)
  rw [hr] at cl
  have sp:=StockWindowGeo.sparse s1 n (s1+15*n) lo rfl le _ hi
  rcases e with rfl|rfl
  · rw [cl.1]
    rcases sp ⟨2*((r-(s1+15*b+5))%5),by omega⟩ with ⟨_,h⟩|h
    · exact Or.inl h
    · exact Or.inr h
  · rw [cl.2]
    rcases sp ⟨2*((r-(s1+15*b+5))%5)+1,by omega⟩ with ⟨_,h⟩|h
    · exact Or.inl h
    · exact Or.inr h

theorem mask_mem (s1 : Nat) : ∀k,∀w∈OrdinaryChainW.mask s1 k,∃b,b+1<k ∧ w∈OrdinaryChainW.cells10 (s1+15*b+5)
  | 0,w,h=>by simp [OrdinaryChainW.mask] at h
  | k+1,w,h=>by
    have e:OrdinaryChainW.mask s1 (k+1)=OrdinaryChainW.mask s1 k++OrdinaryChainW.newBank s1 (s1+15*k):=rfl
    rw [e,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨b,hb,m⟩:=mask_mem s1 k w h
      exact ⟨b,by omega,m⟩
    · unfold OrdinaryChainW.newBank at h
      split at h
      · simp at h
      · rename_i hne
        refine ⟨k-1,by omega,?_⟩
        have e2:s1+15*k-10=s1+15*(k-1)+5:=by omega
        rw [←e2]; exact h

/-- dadon's `census` (`finish`), generic: the masked cells are holes or archive cells in the exit frame. -/
theorem census (s1 n : Nat) (lo : 5≤s1) (hn : 1≤n) (le : s1+15*n≤511) :
    ∀w∈OrdinaryChainW.mask s1 n++OrdinaryChainW.cells10 (s1+15*n-10),
      w∈StockWindowGeo.holes s1 n ∨ OB5.sig (s1+15*n) w∈StockWindowGeo.archives s1 n := by
  intro w hw
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨b,hb,m⟩:=mask_mem s1 n w h
    exact cells_census s1 n b lo (by omega) le w m
  · have e:s1+15*n-10=s1+15*(n-1)+5:=by omega
    rw [e] at h
    exact cells_census s1 n (n-1) lo (by omega) le w h

/-- dadon's `OrdinaryChain.finish`, generic: the stock-masked exit state plus clear holes is the reference off the
archive cells. -/
theorem finishW (s1 n : Nat) (lo : 5≤s1) (hn : 1≤n) (le : s1+15*n≤511) (d:Bool) (out initial:State)
    (all:Except (OrdinaryChainW.mask s1 n++OrdinaryChainW.cells10 (s1+15*n-10)) (pullState (OB5.sig (s1+15*n)) out)
      (run (OrdinaryChainW.progW s1 d n++Rolling1588.encodeAt base d (s1+15*n-15)) [] (run (span s1 (15*n+1)) [] initial)))
    (zero:∀w∈StockWindowGeo.holes s1 n,out.basis (OB5.sig (s1+15*n) w)=false) :
    ∀q∉StockWindowGeo.archives s1 n,out.basis q=(StockArchiveReferenceW.common s1 n d initial).basis q := by
  intro q away
  have inv:OB5.sig (s1+15*n) (OB5.sig (s1+15*n) q)=q:=OB5.sig_invol (s1+15*n) le q
  generalize ey:OB5.sig (s1+15*n) q=y at inv
  have goal:(StockArchiveReferenceW.common s1 n d initial).basis q=(eraseSites (StockWindowGeo.holes s1 n)
      (run (StockArchiveReferenceW.ordinary s1 n d) [] (run (span s1 (15*n+1)) [] initial))).basis y:=by
    rw [←ey]; rfl
  rw [goal]
  by_cases hole:y∈StockWindowGeo.holes s1 n
  · simp only [eraseSites,if_pos hole]
    have z:=zero y hole
    rw [inv] at z
    exact z
  · have free:y∉OrdinaryChainW.mask s1 n++OrdinaryChainW.cells10 (s1+15*n-10):=by
      intro hit
      rcases census s1 n lo hn le y hit with h|h
      · exact hole h
      · rw [inv] at h; exact away h
    have value:=all y free
    change out.basis (OB5.sig (s1+15*n) y)=_ at value
    rw [inv,progW_last s1 n lo hn d] at value
    simpa only [eraseSites,if_neg hole,StockArchiveReferenceW.ordinary] using value

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 2: the exit at 270 (dadon's `terminal`, without `At270`'s saved keys) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic IntegerPacket MappedCompressed Secp256k1 WideReference SkywalkRails NativePack270 Partial ParkEndpoint StockWindowTicket
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 3: the window's reference hand-off `RefW` and the exit block (dadon's `Ref270`, `last270`) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 ArchiveHistoryCompare StockWindowW7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount

/-- dadon's `Ref240/255/270` for any block `j` of the window from block `f` (tick `start f`): the block's stock hand-off (build-chain's
`AtJ`), the logical state agrees with the stock run of `j-3` blocks off the archived cells (par-d2's `mask`/`progW`),
and the holes of the banks of blocks `3..j-2` (cleared by blocks `4..j-1`) are zero. -/
def RefW (f j : Fin 26) (d:Bool) (x:Nat) (initial s:State) : Prop :=
  ∃raw g sg pg ps,AtJ j d x p raw s g sg pg ps ∧
    Except (OrdinaryChainW.mask (start f) (j.val-f.val)) raw
      (run (OrdinaryChainW.progW (start f) d (j.val-f.val)) [] (run (span (start f) (15*(j.val-f.val))) [] initial)) ∧
    ∀q∈StockWindowGeo.holes (start f) (j.val-f.val-1),raw.basis q=false

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 4: interior blocks 4..12 (dadon's `next240/255`), first block (`begin225`), the fold, `wiresW` =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 ArchiveHistoryCompare StockWindowW7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount Shadow7.body

/-- L11 (new, first form at 90 (block 1); dadon's `StockWindowTicket.ordinary225`): the first block's logical end state is
the stock run of its 15 ticks with the five pre-window letters (group 85) encoded. -/
abbrev FirstOrdinarySpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis),
    Except [] (endRaw 45 raw (run (Shadow7.portalP 45 ++ NativeFirstJ7.enteredWindow WindowParams.first d) m
        (pullState (OB5.sig 44) raw)))
      (run (Rolling1588.encodeAt base d 40) [] (run (span 45 15) [] raw))

theorem not_firstF (f k : Fin 26) (hfb : start f=firstBlock) (hk : f.val<k.val) : start k≠firstBlock := by
  rw [←hfb]; simp only [StairPacket.start]; omega

/-- build-chain's `FirstSpec` for any first block `f` (next block `k1`); `FirstSpec = FirstSpecF first ⟨4⟩`. -/
abbrev FirstSpecF (f k1 : Fin 26) : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis),
    ∃g s:Bool,
      InputAt (start f) (encode g s (unsigned (start f) x p).u (unsigned (start f) x p).v) raw ∧
      LeaveJ7.Admission.Inputs f
        (run (Shadow7.portalP (start f) ++ NativeFirstJ7.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw))
        (unsigned (start f) x p) g s ∧
      PackedCut (EnterJ7.lowerPairs k1) (EnterJ7.upperPairs k1) (EnterJ7.gate k1)
        (EnterJ7.flagN k1) (EnterJ7.flagF k1) (EnterJ7.flagU k1)
        (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start f) x p) g s).2 (unsigned (start f+15) x p).u)
        (decide (Shadow.far (Shadow7.sbP (start f+15)) 15 (unsigned (start f+15) x p)))
        (decide (Shadow.far (Shadow7.sbP (start f+15)) 15 (unsigned (start f+15) x p) ∧ 2^(Shadow7.sbP (start f+15))≤(unsigned (start f+15) x p).u))
        (pullState (EnterJ7.pull k1)
          (endRaw (start f) raw (run (Shadow7.portalP (start f) ++ NativeFirstJ7.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw))))
        (eraseSites (EnterJ7.pending k1) (run (Shadow7.leaveP f) n
          (run (Shadow7.portalP (start f) ++ NativeFirstJ7.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)))) ∧
      PastFacts f (ArchiveJ7.rawPorts f) (Shadow7.sbP (start f)) (unsigned (start f) x p) g s
        (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d f (unsigned (start f) x p)))
        (run (Shadow7.leaveP f) n
          (run (Shadow7.portalP (start f) ++ NativeFirstJ7.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)))

theorem first_ship (F:FirstSpec) : FirstSpecF WindowParams.first ⟨1,by decide⟩ := F

/-- `FirstOrdinarySpec` for any first block `f`. -/
abbrev FirstOrdinarySpecF (f : Fin 26) : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis),
    Except [] (endRaw (start f) raw (run (Shadow7.portalP (start f) ++ NativeFirstJ7.enteredWindow f d) m
        (pullState (OB5.sig (start f-1)) raw)))
      (run (Rolling1588.encodeAt base d (start f-5)) [] (run (span (start f) 15) [] raw))

theorem firstOrdinary_ship (FO:FirstOrdinarySpec) : FirstOrdinarySpecF WindowParams.first := FO

theorem first_eqF (d:Bool) (f:Fin 26) :
    (CRTBarrel.params.portal (start f) :: firstF CRTBarrel.params d f).flatten=
      (Shadow7.portalP (start f)++NativeFirstJ7.enteredWindow f d)++CRTBarrel.leave f := by
  simp only [firstF,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeFirstJ7.enteredWindow,NativeFirstJ7.window,Shadow7.body,NativeFirstJ7.program,List.append_assoc]

/-- The move leave of the first block `f` runs like its reference leave (`FirstSpecF` gives the leave input). -/
theorem firstSameF (f k1:Fin 26) (hf1:0≤f.val) (hf20:f.val≤24) (hk1:k1.val=f.val+1) (F:FirstSpecF f k1) (d:Bool) (x p:Nat)
    (good:Bounds x p) (raw:State) (m n:List Bool) (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis) :
    run (CRTBarrel.leave f) n (run (Shadow7.portalP (start f)++NativeFirstJ7.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw))=
      run (Shadow7.leaveP f) n (run (Shadow7.portalP (start f)++NativeFirstJ7.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)) := by
  obtain ⟨g,sg,input,hin,cut,facts⟩:=F d x p good raw m n stage
  exact (LeaveJ7.Admission.Inputs.crt_pair (by omega) hf20 hin).1 n

theorem run_nil_eq (m:List Bool) (s:State) : run [] m s=s := by
  with_unfolding_all rfl


end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 5: the first block's ordinary (`FirstOrdinarySpec`) from the portal frame at 120 =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction
open StockWindowTicket Secp256k1 ArchiveHistoryCompare StockWindowW7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.body Shadow7.routed measurementCount

/-- The five pre-window letters of the first block `j` (group `start j-5`). -/
def plainF (j : Fin 26) : Fin 10 → Wire := History5.historyMap base (start j-5)

theorem plainF_cell (j : Fin 26) (i : Fin 10) :
    (i.val%2=0 ∧ (plainF j i:Nat)=start j-5+i.val/2+16) ∨ (i.val%2≠0 ∧ (plainF j i:Nat)=start j-5+i.val/2+1044) := by
  simp only [plainF,History5.historyMap,History5.historyId,base,Wire]
  split
  · left; constructor; assumption; omega
  · right; constructor; assumption; omega

theorem plainF_inj (j : Fin 26) : Function.Injective (plainF j) := by
  intro a b e
  have ha:=a.isLt; have hb:=b.isLt
  have ca:=plainF_cell j a; have cb:=plainF_cell j b
  have e':(plainF j a:Nat)=plainF j b:=e
  apply Fin.ext
  simp only [Wire] at ca cb e'
  omega

/-- `OB5.sig s` and `OB5.sig (s+14)` agree on the first block's letters. -/
theorem sigF_same (j : Fin 26) (i : Fin 10) :
    (OB5.sig (start j) (plainF j i):Nat)=OB5.sig (start j+14) (plainF j i) := by
  have c:=plainF_cell j i
  have hj:=j.isLt; have hi:=i.isLt
  simp only [OB5.sig,Wire]
  simp only [start,Wire] at *
  split <;> split <;> omega

theorem pastInputF (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (x p:Nat) (good:Bounds x p) (raw:State)
    (dom:Domain (start j) x p raw) (i:Fin 10) :
    raw.basis (plainF j i)=(run (span (start j) 15) [] raw).basis (plainF j i) := by
  have pp:=preservePast (start j) 15 x p (start j-5+i.val/2) (by simp only [start]; omega) good raw dom
    (by simp only [start]; omega) []
  rcases plainF_cell j i with ⟨-,e⟩|⟨-,e⟩
  · rw [e]; exact pp.1.symm
  · rw [e,show start j-5+i.val/2+1044=base (1028+(start j-5+i.val/2)) by simp only [base]; omega]; exact pp.2.symm

theorem encodeF (j : Fin 26) (h1 : 0≤j.val) (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (NativeFirstJ7.history j i)=b.basis (plainF j i)) (i:Fin 10) :
    (run (NativeFirstJ7.program j d) tape a).basis (NativeFirstJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-5)) [] b).basis (plainF j i) := by
  rw [(NativeFirstJ7.equals j h1 d).1]
  exact ArchiveOrdinaryFive.stock_relocated d (NativeFirstJ7.history j) (plainF j) (NativeFirstJ7.histInj j)
    (plainF_inj j) a b tape [] agree i

/-- `Ordinary225Exit.result` for the first block `j`. -/
theorem resultF (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24)
    (old:∀i,oldRange (start j+1) (windowNet j (NativeFirstJ7.history j i))) (d:Bool) (raw s:State) (m:List Bool)
    (x p:Nat) (good:Bounds x p) (dom:Domain (start j) x p raw)
    (input:∀i,(run (Shadow7.routed j 0 1) m s).basis (NativeFirstJ7.history j i)=raw.basis (plainF j i)) :
    ∀i,(run (Shadow7.body j (NativeFirstJ7.program j d)) m s).basis (NativeFirstJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-5)) [] (run (span (start j) 15) [] raw)).basis (plainF j i) := by
  intro i
  rw [OrdinaryJ.kept j _ m s _ (old i)]
  exact encodeF j h1 d _ _ _ (fun k=>(input k).trans (pastInputF j h1 h21 x p good raw dom k)) i

/-- `Logical225Exit.window` for the first block `j` (old cells = the five ticks before it). -/
theorem windowF (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24)
    (first:oldStart (start j)=start j-5 ∧ oldCount (start j)=5) (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,historyState.basis (NativeFirstJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-5)) [] (run (span (start j) 15) [] raw)).basis (plainF j i))
    (q:Wire) :
    (endRaw (start j) raw historyState).basis q=
      (run (Rolling1588.encodeAt base d (start j-5)) [] (run (span (start j) 15) [] raw)).basis q := by
  have bound:start j+14≤511:=by simp only [start]; omega
  have s5:5≤start j:=by simp only [start]; omega
  by_cases inside:q∈oldSites (start j)
  · obtain ⟨r,r1,r2,hq⟩:=old_cell inside
    rw [first.1] at r1 r2
    rw [first.2] at r2
    have ex:∃i:Fin 10,q=plainF j i:=by
      simp only [Wire] at *
      rcases hq with hq|hq
      · refine ⟨⟨2*(r-(start j-5)),by omega⟩,?_⟩
        rcases plainF_cell j ⟨2*(r-(start j-5)),by omega⟩ with ⟨-,e⟩|⟨od,-⟩
        · rw [e]; dsimp only; omega
        · exfalso; simp only at od; omega
      · refine ⟨⟨2*(r-(start j-5))+1,by omega⟩,?_⟩
        rcases plainF_cell j ⟨2*(r-(start j-5))+1,by omega⟩ with ⟨ev,-⟩|⟨-,e⟩
        · exfalso; simp only at ev; omega
        · rw [e]; dsimp only; omega
    obtain ⟨i,rfl⟩:=ex
    rw [endRaw_inside_gen _ bound _ _ _ inside,← sigF_same j i]
    exact ordinaryBits i
  · rw [endRaw_outside_gen _ bound _ _ _ inside]
    apply (run_preserves_outside _ _ _ q _).symm
    intro used
    obtain ⟨r,r1,r2,hq⟩:=OrdinaryJ.encode_cells d _ q used
    apply inside
    simp only [oldSites,first.1,first.2,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
      or_false,base]
    simp only [Wire] at *
    exact ⟨r,⟨by omega,by omega⟩,by omega⟩

theorem old_first : ∀i:Fin 10,oldRange (start WindowParams.first+1)
    (windowNet WindowParams.first (NativeFirstJ7.history WindowParams.first i)) := by decide +kernel

/-- `FirstOrdinarySpec` (dadon's `ordinary225` at 120), from build-chain's `NativeFirstJ7.first_core` (portal frame). -/
theorem firstOrdinary : FirstOrdinarySpec := by
  intro d x p good raw m stage
  let j:=WindowParams.first
  let z:=unsigned 45 x p
  let origin:=pullState (OB5.sig 44) raw
  let cut:=run (Shadow7.portalP 45) m origin
  let n:=m.drop (measurementCount (Shadow7.portalP 45))
  let pre:=run (Shadow7.enterP j) n cut
  let tape:=n.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP 45) 15 z
  obtain ⟨G,S,inputAt,frame,-⟩:=NativeFirstJ7.first_core d x p good raw m stage
  have eqg:(SkywalkRails.encode G S (unsigned 45 x p).u (unsigned 45 x p).v).g=G:=by cases G <;> rfl
  have input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 45)
      (SkywalkRails.encode G S (unsigned 45 x p).u (unsigned 45 x p).v).a
      (SkywalkRails.encode G S (unsigned 45 x p).u (unsigned 45 x p).v).b G raw.basis:=by
    unfold InputAt at inputAt; rwa [eqg] at inputAt
  have nums:=LeaveJ7.Admission.actualNumbers j (by decide) (by decide) x p good
  have dom:=initial 45 x p (by decide) d raw stage
  have hist:=pulled_history j rfl dom
  have sh:∀r:Fin 15,(IntegerPacket.ports (Shadow7.shape j) ↑r).history=(IntegerPacket.ports (StairPacket.shape j) ↑r).history:=by
    decide +kernel
  have hist':∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) ↑r).history))=false:=by
    intro r; rw [sh r]; exact hist r
  have ready:=EnterJ7.ready_from_cut_at j raw cut z G S n nums.farSmall frame input hist'
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP 45) z nums.farSmall nums.odd
  have parity:((encode G S T.u T.v).a+(encode G S T.u T.v).b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have inp:=NativeFirstJ7.history_from_stock j (by decide) (by decide) raw cut pre frame n tape rfl _ parity ready.2
  have res:=resultF j (by decide) (by decide) old_first d raw pre tape x p good dom inp
  have fb:start j=firstBlock:=rfl
  have firstB:oldStart (start j)=start j-5 ∧ oldCount (start j)=5:=by
    rw [fb]; exact ⟨oldStart_first,oldCount_first⟩
  intro q _
  have w:=windowF j (by decide) (by decide) firstB d raw _ res q
  have e:run (Shadow7.portalP 45++NativeFirstJ7.enteredWindow WindowParams.first d) m origin=
      run (Shadow7.body j (NativeFirstJ7.program j d)) tape pre:=by
    simp only [NativeFirstJ7.enteredWindow,NativeFirstJ7.window,run_append,run_take]; rfl
  rw [e]
  exact w

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowW7

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end



-- ==== window405: Main's exit-270 pieces at the exit 405 (build-chain's exit360/renderM360.py via helpers/window405/main/renderM_x.py, from Main 74aa223): the exit's
-- blank holes, dadon's finalBank receipt (selected_*), the terminal bank (Ordinary420Terminal) and resultW405. ====
section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
attribute [local irreducible] run routed measurementCount body
namespace NativePack4207
open ArchiveBoundary4207
def fourHoles : List Wire := [1657,1655,1652,1650]
theorem blank_slots : ∀q∈fourHoles,∃i:Fin 157,16 ≤ i.val ∧ codePorts i=q := by decide +kernel
theorem cleared_holes (d:Bool) (row:Nat) (s:State) (frame:Frame codePorts (code d) row s) :
    ∀q∈fourHoles,s.basis q=false := by
  intro q hq
  obtain ⟨i,hi,rfl⟩:=blank_slots q hq
  rw [frame,archive_blank d i hi,Nat.zero_testBit]
end NativePack4207
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack4207
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary4207
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open StockCanonicalRow ArchiveBoundary4207 ParkEndpoint4207 Portal420Flag7 Secp256k1 SkywalkRails StairArchiveTrace
theorem selected_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:Shadow7.SmallIfFar 46 15 past)
    (prior:PastFacts sourceIdx rawPorts 46 past G S cross s) :
    let out:=run (p ++ (program d ++ (Shadow7.exitLoadP 420) d)) m s
    out.phase=s.phase ∧ (let v:=key 46 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run ((Shadow7.exitRestoreP 420) d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=frame_key sourceIdx rawPorts chronological row 46 past G S cross s pre prior
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have spec:=select_spec ⟨row,limit,truth⟩
  have fresh:=reframe limit truth rawPorts pre frame
  have enc:=source_law d tick e legal
  have act:=load_run d _ spec.1 pre f fresh
  exact sequence_law p (program d) ((Shadow7.exitLoadP 420) d) ((Shadow7.exitRestoreP 420) d)
    (reverse d) q s m (fun out=>let v:=key 46 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run ((Shadow7.exitLoadP 420) d) f pre) rfl act.1
    ⟨spec.1,spec.2,act.2.1⟩ (fun n=>roundtrip d _ spec.1 pre f n fresh)

theorem selected_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick4207.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:Shadow7.SmallIfFar 46 15 past)
    (prior:PastFacts sourceIdx rawPorts 46 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (let v:=key 46 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run (endUndo d) n out=s :=
  selected_generic EndTick4207.physP EndTick4207.physQ d s m step past G S cross odd small prior
theorem selected_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick4207.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 420 original.basis)
    (hist:raw.basis (base (1028+420))=false) (swapSlot:raw.basis (base (2053-420))=false)
    (hosts:∀k:Fin 134,512≤k.val+420 → raw.basis (790+k.val)=false)
    (z:SkywalkNat.State) (small:Shadow7.SmallIfFar 39 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick4207.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 (PortalValues.negative S z.u)
      (decide (2*2^54≤z.u+z.v)) (decide (2*2^54≤z.u+z.v ∧ 2^39≤z.u)) (pullState (OB5.sig 419) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:Shadow7.SmallIfFar 46 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1619=decide (Shadow.far 46 15 past))
    (angle:s.basis 1620=(decide (Shadow.far 46 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1621=(decide (Shadow.far 46 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 46 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount (Shadow7.parkP 420))
  let one:=run (Shadow7.portalInvP 420) n (run (Shadow7.parkP 420) m s)
  let tape:=n.drop (measurementCount (Shadow7.portalInvP 420))
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot hosts tape
  have eqOne:one=stash s (pullState (OB5.sig 419) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 46 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick4207.physP tape one):=by rw [eqOne];exact tick
  have body:=selected_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem selected_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 420 x p raw) (z:SkywalkNat.State) (small:Shadow7.SmallIfFar 39 15 z) (G S:Bool)
    (input:SkywalkIntegerInput EndTick4207.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 435 1618 1616 1617 (PortalValues.negative S z.u)
      (decide (2*2^54≤z.u+z.v)) (decide (2*2^54≤z.u+z.v ∧ 2^39≤z.u)) (pullState (OB5.sig 419) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:Shadow7.SmallIfFar 46 15 past)
    (records:Shadow7.physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1619=decide (Shadow.far 46 15 past))
    (angle:s.basis 1620=(decide (Shadow.far 46 15 past) && afterFlags (decide (past.v<past.u)) ((Shadow7.physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1621=(decide (Shadow.far 46 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 46 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty,hosts⟩:=WideReference.terminal4207 d x raw domain
  exact selected_last d x hx0 hx raw ref s m read stage history swapSlot hosts z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack4207

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary420Terminal
open Arithmetic MappedCompressed NativePack4207 ArchivePortAction ArchiveBoundary4207 ParkEndpoint4207 CodecBitSliceVerify
set_option maxRecDepth 40000
set_option maxHeartbeats 3800000
attribute [local irreducible] run
def newBank := (List.range' 410 10).flatMap (fun r=>[OB5.sig 420 (base r), OB5.sig 420 (base (1028+r))])
def ordinary := (List.finRange 10).map history
def zeros:=(List.range 134).map (Shadow7.scratchX 420)++dst

theorem basis (d:Bool) (raw payload:State) (m n:List Bool)
    (row:Nat)
    (clear:∀q∈zeros,raw.basis (OB5.sig 420 q)=false)
    (frame:Frame codePorts (code d) row (run ((Shadow7.exitLoadP 420) d) n
      (run (program d) m (stash payload (pullState (OB5.sig 420) raw))))) :
    let out:=run ((Shadow7.exitLoadP 420) d) n (run (program d) m (stash payload (pullState (OB5.sig 420) raw)))
    let wide:=run (Rolling1588.encodeAt base d 405) [] raw
    ∀q∉newBank,out.basis q=wide.basis (OB5.sig 420 q) := by
  let inp:=stash payload (pullState (OB5.sig 420) raw)
  let mid:=run (program d) m inp
  let wide:=run (Rolling1588.encodeAt base d 405) [] raw
  let coords:=History5.historyMap base 405
  have geom:∀i:Fin 10,history i∉dst ∧ OB5.sig 420 (history i)=coords i ∧ history i∉rawPortsList := by dsimp only [coords];decide +kernel
  have agree (i:Fin 10):inp.basis (history i)=raw.basis (coords i):=by
    simp only [inp,stash,if_neg (geom i).1,pullState,(geom i).2.1]
  have injected:Function.Injective coords:=by dsimp only [coords];decide +kernel
  have keep (q:Wire) (no:q∉ordinary) : wide.basis (OB5.sig 420 q)=raw.basis (OB5.sig 420 q) := by
    have cover:wires (Rolling1588.encodeAt base d 405) ⊆ ((List.finRange 10).map coords).toFinset:=by dsimp only [coords];cases d <;> decide +kernel
    apply run_preserves_outside
    intro h
    obtain ⟨i,_,e⟩:=List.mem_map.mp (List.mem_toFinset.mp (cover h))
    have e':OB5.sig 420 (history i)=OB5.sig 420 q:=(geom i).2.1.trans e
    have unique:history i=q:=by simpa only [OB5.sig_invol 420 (by decide)] using congrArg (OB5.sig 420) e'
    exact no (List.mem_map.mpr ⟨i,List.mem_finRange i,unique⟩)
  dsimp only
  intro q outside
  by_cases normal:q∈ordinary
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp normal
    rw [run_preserves_outside ((Shadow7.exitLoadP 420) d) _ _ _ (fun h=>(geom i).2.2 (List.mem_toFinset.mp (load_cover d h))), (geom i).2.1]
    have encoded:=ArchiveOrdinaryFive.stock_relocated d history coords histInj injected inp raw m [] agree i
    rw [←(equals d).1] at encoded
    exact encoded
  rw [keep q normal]
  by_cases touched:q∈rawPortsList
  · have mask:∀q∈rawPortsList,q∈newBank ∨ (q∈zeros ∧ ∃i:Fin 157,16≤ i.val ∧ codePorts i=q) := by decide +kernel
    obtain ⟨blank,i,hi,slot⟩:=(mask q touched).resolve_left outside
    rw [clear q blank,←slot,frame,archive_blank _ _ hi,Nat.zero_testBit]
  · have no:q∉wires ((Shadow7.exitLoadP 420) d):=fun h=>touched (List.mem_toFinset.mp (load_cover d h))
    have mask:∀q∈dst,q∈rawPortsList:=by decide +kernel
    have notDst:q∉dst:=fun h=>touched (mask q h)
    rw [run_preserves_outside _ _ _ _ no]
    exact (NativePack4207.outside d q (fun i e=>normal (List.mem_map.mpr ⟨i,List.mem_finRange i,e.symm⟩)) _ _).trans
      (by simp only [stash,if_neg notDst,pullState])
end ECDSAAdd.Entrant.StairPacket.Ordinary420Terminal

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic IntegerPacket MappedCompressed Secp256k1 WideReference SkywalkRails NativePack4207 Partial ParkEndpoint4207 StockWindowTicket
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

/-- `Ordinary270Native.result` with the exit frame as a hypothesis (dadon took it from `step270`, which needs
`At270.saved225/240`; the generic hand-off `AtJ 13` has no saved keys). Proof otherwise dadon's. -/
theorem resultW420 (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg:Bool) (m:List Bool)
    (domain:Domain 420 x p raw) (input:InputAt 420 (signedAt 420 x p g sg) raw)
    (cut:PackedCut Portal420Flag7.loPairs Portal420Flag7.hiPairs 435 1618 1616 1617 (flagNeg 420 x p sg)
      (decide (farAt 39 420 x p)) (decide (farAt 39 420 x p ∧ 2^39≤(unsigned 420 x p).u))
      (pullState (OB5.sig 419) raw) (eraseSites ParkEndpoint4207.src s))
    (last:StockWindowW7.LastAt ArchiveBoundary4207.codePorts ⟨24,by decide⟩ d x p (run (lastWindow d) m s)) :
    ArchiveHistoryCompare.Except Ordinary420Terminal.newBank (run (lastWindow d) m s)
      (pullState (OB5.sig 420) (run (Rolling1588.encodeAt base d 405) [] (run EndTick4207.canonical [] raw))) := by
  obtain ⟨ref,stage,read,hist,spare,spaces,hosts⟩:=WideReference.terminal4207 d x raw domain
  let z:=unsigned 420 x p
  let v:=run EndTick4207.canonical [] raw
  let p1:=m.drop (measurementCount (Shadow7.parkP 420))
  let p2:=p1.drop (measurementCount (Shadow7.portalInvP 420))
  let p3:=p2.drop (measurementCount EndTick4207.physP)
  let p4:=p3.drop (measurementCount (program d))
  have lim:Shadow7.SmallIfFar 39 15 z:=(Shadow7.Envelope.inputs x p 420 (lt_trans good.small good.cap) good.cap (by decide)).1
  have mode:farAt 39 420 x p=(2*2^54≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have first:=parked_release z lim raw s m p1 g sg (readInput 420 x p raw g sg input)
    (by simpa only [mode] using cut) (empty_from_cut _ _ _ _ _ cut spaces)
  have tick:=EndTick4207.physical d x good.nonzero good.small raw ref s read stage hist spare p2
  let loaded:=run ((Shadow7.exitLoadP 420) d) p4 (run (program d) p3 (stash s (pullState (OB5.sig 420) v)))
  have actual:run (lastWindow d) m s=loaded := by
    simp only [lastWindow,endSlice,run_append,run_take]
    change run ((Shadow7.exitLoadP 420) d) p4 (run (program d) p3 (run EndTick4207.physP p2 (run (Shadow7.portalInvP 420) p1 (run (Shadow7.parkP 420) m s))))=_
    rw [first.1,tick.1]
  obtain ⟨row,_,_,frame⟩:=last
  rw [actual] at frame
  have zeros (q:Wire) (h:q∈Ordinary420Terminal.zeros) : v.basis (OB5.sig 420 q)=false:=by
    rcases List.mem_append.mp h with carryLane|tag
    · have table:∀q∈(List.range 134).map (Shadow7.scratchX 420),∃k:Fin 134,OB5.sig 420 q=Shadow7.scratchX 420 k.val:=by decide +kernel
      obtain ⟨k,eq⟩:=table _ carryLane
      rw [eq];exact (EndTick4207.after_cells d x good.nonzero good.small raw ref read stage hosts).2 k
    · have coords:∀q∈dst,OB5.sig 420 q=OB5.sig 419 q := by decide +kernel
      have nocell:=EndTick4207.spared q tag
      have cover:=W.compactSkywalkTick_support base 420 (by decide) base_pool_nodup
      have no:OB5.sig 420 q∉wires EndTick4207.canonical:=fun used=>nocell (List.mem_toFinset.mp (cover used))
      exact (run_preserves_outside _ _ _ _ no).trans (by rw [coords q tag];exact spaces q tag)
  rw [actual]
  exact Ordinary420Terminal.basis d v s p3 p4 row zeros frame

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG

end

-- ==== end window405 Main exit pieces ====

section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic IntegerPacket MappedCompressed Secp256k1 WideReference SkywalkRails Partial StockWindowTicket StockWindowW7
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

/-- The generic hand-off at block 21 is the exit-405 cut (build-chain's (at 375) `exitBridge405`). -/
theorem exitCut420 (d:Bool) (x:Nat) (raw s:State) (g sg pg ps:Bool)
    (pre:AtJ ⟨25,by decide⟩ d x p raw s g sg pg ps) :
    PackedCut Portal420Flag7.loPairs Portal420Flag7.hiPairs 435 1618 1616 1617 (flagNeg 420 x p sg)
      (decide (farAt 39 420 x p)) (decide (farAt 39 420 x p ∧ 2^39≤(unsigned 420 x p).u))
      (pullState (OB5.sig 419) raw) (eraseSites ParkEndpoint4207.src s) := by
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,-,-,-⟩:=StockWindowW7.exitBridge420
  have cut:=pre.cut
  rw [bl,bu,bg,bn,bf,bu',bp] at cut
  have e19:start (⟨25,by decide⟩:Fin 26)=420:=rfl
  have sb:Shadow7.sbP 420=39:=by decide
  have pl:EnterJ7.pull ⟨25,by decide⟩=OB5.sig 419:=rfl
  simp only [e19,sb,pl] at cut
  exact cut

/-- The exit frame at 420 from the generic hand-off (build-chain's (at 375) `exitStep420`, its `LastAt` part). -/
theorem exitLast420 (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool)
    (pre:AtJ ⟨25,by decide⟩ d x p raw s g sg pg ps) (m:List Bool) :
    LastAt ArchiveBoundary4207.codePorts ⟨24,by decide⟩ d x p (run (NativePack4207.lastWindow d) m s) := by
  have h:=StockWindowW7.exitStep420 d x good s m ⟨⟨25,by decide⟩,rfl,raw,g,sg,pg,ps,pre⟩
  have e420:start (⟨24,by decide⟩:Fin 26)+15=420:=rfl
  rw [e420,(StockWindowW7.exitProg420 d).1] at h
  exact h.2.1

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 6: generic over the window's length (blocks 4..J, exit e = 120+15n) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 ArchiveHistoryCompare StockWindowW7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount Shadow7.body

/-- build-chain's `EndpointSpec` for interior blocks `I..J` (`EndpointSpec = EndpointBetween 4 12`). -/
abbrev EndpointBetween (I J : Nat) : Prop :=
  ∀ (j k : Fin 26), k.val=j.val+1 → I≤j.val → j.val≤J → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:ScratchAt j d m s) (pg ps cross:Bool)
    (prior:PastFacts (NativeJ7.prev j) (ArchiveJ7.rawPorts (NativeJ7.prev j)) (Shadow7.sbP (start (NativeJ7.prev j)))
      (unsigned (start (NativeJ7.prev j)) x p) pg ps cross s),
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (NativeJ7.nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))

/-- dadon's `pinned{s}` for block `k ≤ J`. -/
theorem pinnedG (I J:Nat) (hI2:1≤I) (hJ:J≤24) (L1:EndpointBetween I J) (L2:ScratchSpec) (k k1:Fin 26)
    (hk:k1.val=k.val+1) (hIk:I≤k.val) (hkJ:k.val≤J) (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool)
    (pre:AtJ k d x p raw s g sg pg ps) :
    ∃a b c e,AtJ k1 d x p (endRaw (start k) raw (run (NativeJ7.nextWindow k d) m s))
      (run (Shadow7.leaveP k) (m.drop (measurementCount (NativeJ7.nextWindow k d))) (run (NativeJ7.nextWindow k d) m s)) a b c e := by
  let v:=run (NativeJ7.nextWindow k d) m s
  let n:=m.drop (measurementCount (NativeJ7.nextWindow k d))
  have p1:NativeJ7.prev k1=k:=prev_of k k1 hk
  have s1:start k1=start k+15:=start_succ k k1 hk
  let flags:=LeaveJ7.Admission.flags (unsigned (start k) x p) g sg
  have h2 : 1≤k.val := by omega
  have h19 : k.val≤24 := by omega
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k h2 h19 d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k h2 h19 d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨cut,facts⟩:=L1 k k1 hk hIk hkJ d x p good raw s m n pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  have hin:=native.1
  have carried:=stepInput_gen_shadow7 (start k) (Shadow7.sbP (start k)) x p (by simp only [StairPacket.start]; omega)
    (by simp only [StairPacket.start]; omega) good raw v g sg pre.domain pre.input hin.farSmall
  have canon:=unique_input pre.input (fixed_input _ _ _ (by simp only [StairPacket.start]; omega) good raw pre.domain)
  refine ⟨flags.1,flags.2,g,sg,⟨?_,?_,cut,?_,?_⟩⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [p1]; exact facts
  · rw [p1]; exact canon

/-- `OB5.sig s` and `OB5.sig (s+14)` move a B-side cell of the block's last ten ticks alike (any block). -/
theorem sigNat_same (s r : Nat) (hs : s≤405) (h1 : s≤r+8) (h2 : r+1≤s) :
    OB5.sigNat (s+14) (1028+r+16)=OB5.sigNat s (1028+r+16) := by
  unfold OB5.sigNat
  by_cases a : 1301≤1028+r+16
  · rw [if_pos (Or.inl ⟨a,by omega⟩),if_pos (Or.inl ⟨a,by omega⟩)]
  · rw [if_neg (by rintro (⟨x,_⟩|⟨x,_⟩) <;> omega),if_neg (by rintro (⟨x,_⟩|⟨x,_⟩) <;> omega)]

theorem hole_sig (k : Fin 26) (h18 : k.val≤24) (r : Nat) (h1 : start k≤r+8) (h2 : r+1≤start k) :
    OB5.sig (start k+14) (base (1028+r))=OB5.sig (start k) (base (1028+r)) := by
  have s0 : start k≤405 := by simp only [StairPacket.start]; omega
  exact sigNat_same (start k) r s0 h1 h2

theorem hole_four (k : Fin 26) (h1 : 1≤k.val) (h18 : k.val≤24) (r : Nat)
    (hr : r=start k-8 ∨ r=start k-6 ∨ r=start k-3 ∨ r=start k-1) :
    OB5.sig (start k) (base (1028+r))∈NativeJ7.fourHoles k := by
  rw [NativeJ7.fourHoles_eq k h1]
  have s0 : 45 ≤ start k := by simp only [StairPacket.start]; omega
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rcases hr with rfl|rfl|rfl|rfl
  · left; congr 1; simp only [base,Wire]; omega
  · right; left; congr 1; simp only [base,Wire]; omega
  · right; right; left; congr 1; simp only [base,Wire]; omega
  · right; right; right; congr 1; simp only [base,Wire]; omega

/-- dadon's `ordinary{s}` for block `k ≤ 19`. -/
theorem ordinaryG (f:Fin 26) (hfb:start f=firstBlock) (k:Fin 26) (hfk:f.val<k.val) (h18:k.val≤24) (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State)
    (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) :
    Except (OrdinaryJ.newBank k) (endRaw (start k) raw (run (NativeJ7.nextWindow k d) m s))
      (run (Rolling1588.encodeAt base d (start k-15)) [] (run (span (start k) 15) [] raw)) := by
  let z:=unsigned (start k) x p
  let T:=Shadow.reduced (Shadow7.sbP (start k)) 15 z
  have nums:=LeaveJ7.Admission.actualNumbers k (by omega) (by omega) x p good
  have hist:=pulled_history k rfl pre.domain
  have inp:=readInput (start k) x p raw g sg pre.input
  have ready:=EnterJ7.ready_pending_at k raw s z g sg m nums.farSmall pre.cut inp hist
  have odd:T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start k)) z nums.farSmall nums.odd
  have parity:((encode g sg T.u T.v).a+(encode g sg T.u T.v).b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have hne:=not_firstF f k hfb hfk
  have h:=OrdinaryJ.native k (by omega) (by omega) ⟨oldStart_interior hne,oldCount_interior hne⟩ d x p good raw s
    pre.domain m (m.drop (measurementCount (Shadow7.enterP k))) _ _ _ pre.cut _ parity ready.2.1
  simpa only [NativeJ7.nextWindow,NativeJ7.window,run_append,run_take] using h

/-- dadon's `holes{s}` for block `k ≤ 19` (the sig-moved holes of blocks ≥ 270 included). -/
theorem holesG (f:Fin 26) (hfb:start f=firstBlock) (L2:ScratchSpec) (k:Fin 26) (hfk:f.val<k.val) (h2:1≤k.val) (h18:k.val≤24) (d:Bool) (x:Nat) (good:Bounds x p)
    (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) (r:Nat)
    (hr : r=start k-8 ∨ r=start k-6 ∨ r=start k-3 ∨ r=start k-1) :
    (endRaw (start k) raw (run (NativeJ7.nextWindow k d) m s)).basis (base (1028+r))=false := by
  let z:=unsigned (start k) x p
  have nums:=LeaveJ7.Admission.actualNumbers k (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (NativeJ7.prev k) (by simp only [NativeJ7.prev]; omega)
    (by simp only [NativeJ7.prev]; omega) x p good
  have hist:=pulled_history k rfl pre.domain
  have inp:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k (by omega) (by omega) d x p good raw s g sg pg ps m pre
  have clear:=NativeJ7.cleared_holes k (by omega) (by omega) d raw s m z g sg nums.odd nums.farSmall pre.cut inp hist scr
    _ pg ps _ old.odd old.farSmall pre.facts
  have hne:=not_firstF f k hfb hfk
  have s0 : 60 ≤ start k ∧ start k≤405 := by simp only [StairPacket.start]; omega
  have bound:start k+14≤511:=by omega
  have r0 : start k-8≤r ∧ r≤start k-1 := by rcases hr with rfl|rfl|rfl|rfl <;> omega
  have mem:base (1028+r)∈oldSites (start k):=by
    simp only [oldSites,oldStart_interior hne,oldCount_interior hne,List.mem_flatMap,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨r,⟨by omega,by omega⟩,Or.inr rfl⟩
  rw [endRaw_inside_gen _ bound _ _ _ mem,hole_sig k h18 r (by omega) (by omega)]
  exact clear _ (hole_four k (by omega) h18 r hr)

/-- dadon's `next240/next255` for any interior block `k` (`I ≤ k ≤ J`) of the window from block `f`. -/
theorem nextG (f:Fin 26) (hfb:start f=firstBlock) (I J:Nat) (hI2:1≤I) (hIf:f.val+1≤I) (hJ:J≤24)
    (L1:EndpointBetween I J) (L2:ScratchSpec) (d:Bool) (x:Nat) (good:Bounds x p)
    (initial s:State) (k k1:Fin 26) (hk:k1.val=k.val+1) (hIk:I≤k.val) (hkJ:k.val≤J) (m:List Bool)
    (h:RefW f k d x initial s) :
    RefW f k1 d x initial (run (NativeJ7.nextWindow k d++CRTBarrel.leave k) m s) := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  rw [run_append,run_take,sameAt L2 k (by omega) (by omega) d x p good raw s g sg pg ps m pre]
  obtain ⟨a,b,c,e,pre'⟩:=pinnedG I J hI2 hJ L1 L2 k k1 hk hIk hkJ d x good raw s g sg pg ps m pre
  have hfk:f.val<k.val:=by omega
  have hne:=not_firstF f k hfb hfk
  have sf : 45≤start f ∧ start f+15≤start k := by simp only [StairPacket.start]; omega
  have s0 : start k≤405 := by simp only [StairPacket.start]; omega
  have sk:start k=start f+15*(k.val-f.val):=by simp only [StairPacket.start]; omega
  refine ⟨_,a,b,c,e,pre',?_,?_⟩
  · have step:=ordinaryG f hfb k hfk (by omega) d x good raw s g sg pg ps m pre
    have step':Except (OrdinaryChainW.newBank (start f) (start f+15*(k.val-f.val)))
        (endRaw (start k) raw (run (NativeJ7.nextWindow k d) m s))
        (run (Rolling1588.encodeAt base d (OrdinaryChainW.group (start f) (k.val-f.val))) []
          (run (span (start f+15*(k.val-f.val)) 15) [] raw)):=by
      rw [←sk,OrdinaryChainW.newBank,if_neg (by omega),OrdinaryChainW.group,if_neg (by omega),
        show start f+15*(k.val-f.val)-15=start k-15 by omega]
      exact step
    have e1:k1.val-f.val=(k.val-f.val)+1:=by omega
    rw [e1]
    exact OrdinaryChainW.add (start f) (by omega) (k.val-f.val) (by omega) (by omega) d raw initial _ old step'
  · have e1:k1.val-f.val-1=(k.val-f.val-1)+1:=by omega
    rw [e1,holes_succ]
    intro q hq
    rcases List.mem_append.mp hq with h|h
    · apply OrdinaryChainW.carry (start k) (by omega) (StockWindowGeo.holes (start f) (k.val-f.val-1)) ?_ ?_ raw _ zeros q h
      · intro w hw hit
        obtain ⟨r,r1,r2,rfl⟩:=hole_cell (start f) (k.val-f.val-1) (by omega) w hw
        obtain ⟨r',a1,a2,e'⟩:=old_cell hit
        rw [oldStart_interior hne] at a1 a2
        rw [oldCount_interior hne] at a2
        rcases e' with e'|e' <;> simp only [base,Wire] at e' <;> omega
      · intro w hw
        obtain ⟨r,r1,r2,rfl⟩:=hole_cell (start f) (k.val-f.val-1) (by omega) w hw
        right; simp only [base,Wire]; omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      have g0:∀i,StockWindowGeo.gstart (start f) i=start f-5+5*i:=fun i=>by simp only [StockWindowGeo.gstart]
      rcases h with rfl|rfl|rfl|rfl
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-8) (Or.inl rfl)
        rw [show 1028+StockWindowGeo.gstart (start f) (2+3*(k.val-f.val-1))+2=1028+(start k-8) by rw [g0]; omega]; exact this
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-6) (Or.inr (Or.inl rfl))
        rw [show 1028+StockWindowGeo.gstart (start f) (2+3*(k.val-f.val-1))+4=1028+(start k-6) by rw [g0]; omega]; exact this
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-3) (Or.inr (Or.inr (Or.inl rfl)))
        rw [show 1028+StockWindowGeo.gstart (start f) (3+3*(k.val-f.val-1))+2=1028+(start k-3) by rw [g0]; omega]; exact this
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-1) (Or.inr (Or.inr (Or.inr rfl)))
        rw [show 1028+StockWindowGeo.gstart (start f) (3+3*(k.val-f.val-1))+4=1028+(start k-1) by rw [g0]; omega]; exact this

/-- The interior fold over blocks `I..J` of the window from block `f`. -/
theorem chainG (f:Fin 26) (hfb:start f=firstBlock) (I J:Nat) (hI2:1≤I) (hIf:f.val+1≤I) (hJ:J≤24)
    (L1:EndpointBetween I J) (L2:ScratchSpec) (d:Bool) (x:Nat) (good:Bounds x p) (initial:State) :
    ∀(i:Fin 26) (js:List (Fin 26)),Consec i js → (∀k∈js,I≤k.val ∧ k.val≤J) →
    ∀(j j':Fin 26),j.val=i.val+1 → j'.val=(lastBlock i js).val+1 → ∀s m,RefW f j d x initial s →
      RefW f j' d x initial (run (chainF CRTBarrel.params d i js).flatten m s)
  | i,[],_,_,j,j',hj,hj',s,m,h=>by
    have e:j'=j:=Fin.ext (by simp only [lastBlock] at hj'; omega)
    subst e
    rw [chainF,List.flatten_nil,run_nil_eq]
    exact h
  | i,k::js,⟨hk,rest⟩,hb,j,j',hj,hj',s,m,h=>by
    have e:j=k:=Fin.ext (by omega)
    subst e
    have bk:=hb j List.mem_cons_self
    rw [chainF,List.flatten_append,run_append,next_eq d i j hk]
    exact chainG f hfb I J hI2 hIf hJ L1 L2 d x good initial j js rest (fun k hk=>hb k (List.mem_cons_of_mem _ hk))
      ⟨j.val+1,by omega⟩ j' rfl (by simpa only [lastBlock] using hj') _ _
      (nextG f hfb I J hI2 hIf hJ L1 L2 d x good initial s j ⟨j.val+1,by omega⟩ rfl bk.1 bk.2 _ h)

/-- The exit's stock-frame bank: the cells of its last ten ticks in the exit frame. -/
def newBankE (e:Nat) : List Wire := (OrdinaryChainW.cells10 (e-10)).map (OB5.sig e)

/-- The window's exit at `e` (hand-off block `jx`): the exit pieces agree with the stock exit tick off the last
bank, and the last bank's four holes are zero (the exit archive's blank code slots). Ship: `exitShip`. -/
abbrev ExitSpec (e:Nat) (jx:Fin 26) : Prop :=
  ∀ (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool),
    AtJ jx d x p raw s g sg pg ps →
    Except (newBankE e) (run (exitF CRTBarrel.params d e).flatten m s)
      (pullState (OB5.sig e) (run (Rolling1588.encodeAt base d (e-15)) [] (run (span e 1) [] raw))) ∧
    ∀ r, (r=e-8 ∨ r=e-6 ∨ r=e-3 ∨ r=e-1) →
      (run (exitF CRTBarrel.params d e).flatten m s).basis (OB5.sig e (base (1028+r)))=false

theorem projectG (e:Nat) (he:e≤511) (raw out W:State) (direct:Except (newBankE e) out (pullState (OB5.sig e) W)) :
    Except (OrdinaryChainW.cells10 (e-10)) (pullState (OB5.sig e) out) W := by
  intro q absent
  have free:OB5.sig e q∉newBankE e:=by
    intro hit
    obtain ⟨w,hw,ew⟩:=List.mem_map.mp hit
    have := OB5.sig_injective e he ew
    exact absent (this ▸ hw)
  have := direct _ free
  simpa only [pullState,OB5.sig_invol e he] using this

theorem old_hole_G (e:Nat) (he:e+1≤512) (d:Bool) (raw out:State) (r:Nat) (r2:r+16≤e)
    (direct:Except (newBankE e) out
      (pullState (OB5.sig e) (run (Rolling1588.encodeAt base d (e-15)) [] (run (span e 1) [] raw))))
    (clear:raw.basis (base (1028+r))=false) :
    out.basis (OB5.sig e (base (1028+r)))=false := by
  have notNew:OB5.sig e (base (1028+r))∉newBankE e:=by
    intro hit
    obtain ⟨w,hw,ew⟩:=List.mem_map.mp hit
    have ew' := OB5.sig_injective e (by omega) ew
    subst ew'
    simp only [OrdinaryChainW.cells10,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
      or_false] at hw
    obtain ⟨r',⟨a,b⟩,e1|e1⟩:=hw <;> simp only [base,Wire] at e1 <;> omega
  have eq:=direct _ notNew
  change out.basis _=(run (Rolling1588.encodeAt base d (e-15)) [] (run (span e 1) [] raw)).basis
    (OB5.sig e (OB5.sig e (base (1028+r)))) at eq
  rw [OB5.sig_invol e (by omega)] at eq
  have enc:base (1028+r)∉wires (Rolling1588.encodeAt base d (e-15)):=by
    intro used
    obtain ⟨r',a,b,e'|e'⟩:=OrdinaryChainW.encode_cells d (e-15) _ used <;> simp only [base,Wire] at e' <;> omega
  have tick:base (1028+r)∉wires (span e 1):=pastOffSpan e 1 _ he ⟨r,by omega,Or.inr rfl⟩
  rw [eq,run_preserves_outside _ _ _ _ enc,run_preserves_outside _ _ _ _ tick]
  exact clear

/-- dadon's `last270`/`terminal`, generic: window from block `f`, `n` banks, exit `start f+15n` (hand-off `jx`). -/
theorem lastG (f:Fin 26) (n:Nat) (hn:1≤n) (he:start f+15*n+1≤512) (jx:Fin 26) (hjx:jx.val=n+f.val)
    (X:ExitSpec (start f+15*n) jx)
    (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State) (m:List Bool) (h:RefW f jx d x initial s) :
    ∀q∉StockWindowGeo.archives (start f) n,(run (exitF CRTBarrel.params d (start f+15*n)).flatten m s).basis q=
      (StockArchiveReferenceW.common (start f) n d initial).basis q := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  obtain ⟨direct,lastHoles⟩:=X d x good raw s g sg pg ps m pre
  have sf : 45≤start f := by simp only [StairPacket.start]; omega
  have e3:jx.val-f.val=n:=by omega
  have e4:jx.val-f.val-1=n-1:=by omega
  rw [e3] at old
  rw [e4] at zeros
  have all:=OrdinaryChainW.add_last (start f) (by omega) n hn he d raw initial _ old
    (projectG (start f+15*n) (by omega) raw _ _ direct)
  apply finishW (start f) n (by omega) hn (by omega) d _ initial all
  obtain ⟨n',rfl⟩:∃n',n=n'+1:=⟨n-1,by omega⟩
  intro w hw
  rw [holes_succ] at hw
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨r,r1,r2,rfl⟩:=hole_cell (start f) n' (by omega) w h
    exact old_hole_G (start f+15*(n'+1)) he d raw _ r (by omega) direct
      (zeros _ (by simpa only [show n'+1-1=n' by omega] using h))
  · have g0:∀i,StockWindowGeo.gstart (start f) i=start f-5+5*i:=fun i=>by simp only [StockWindowGeo.gstart]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · rw [show 1028+StockWindowGeo.gstart (start f) (2+3*n')+2=1028+(start f+15*(n'+1)-8) by rw [g0]; omega]
      exact lastHoles _ (Or.inl rfl)
    · rw [show 1028+StockWindowGeo.gstart (start f) (2+3*n')+4=1028+(start f+15*(n'+1)-6) by rw [g0]; omega]
      exact lastHoles _ (Or.inr (Or.inl rfl))
    · rw [show 1028+StockWindowGeo.gstart (start f) (3+3*n')+2=1028+(start f+15*(n'+1)-3) by rw [g0]; omega]
      exact lastHoles _ (Or.inr (Or.inr (Or.inl rfl)))
    · rw [show 1028+StockWindowGeo.gstart (start f) (3+3*n')+4=1028+(start f+15*(n'+1)-1) by rw [g0]; omega]
      exact lastHoles _ (Or.inr (Or.inr (Or.inr rfl)))

/-- dadon's `begin225` at the first block `f` (next block `k1`), from the first-form leaves only. -/
theorem beginG (f k1:Fin 26) (hf1:0≤f.val) (hf20:f.val≤24) (hk1:k1.val=f.val+1) (F:FirstSpecF f k1) (FO:FirstOrdinarySpecF f)
    (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis) :
    RefW f k1 d x raw (run ((Shadow7.portalP (start f)++NativeFirstJ7.enteredWindow f d)++
      CRTBarrel.leave f) m (pullState (OB5.sig (start f-1)) raw)) := by
  rw [run_append,run_take,firstSameF f k1 (by omega) hf20 hk1 F d x p good raw m _ stage]
  have sf : 45≤start f ∧ start f≤405 := by simp only [StairPacket.start]; omega
  let v:=run (Shadow7.portalP (start f)++NativeFirstJ7.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)
  let n:=m.drop (measurementCount (Shadow7.portalP (start f)++NativeFirstJ7.enteredWindow f d))
  obtain ⟨g,sg,input,hin,cut,facts⟩:=F d x p good raw m n stage
  let flags:=LeaveJ7.Admission.flags (unsigned (start f) x p) g sg
  have dom:=initial (start f) x p (by omega) d raw stage
  have carried:=stepInput_gen_shadow7 (start f) (Shadow7.sbP (start f)) x p (by omega) (by omega) good raw v g sg dom input hin.farSmall
  have s1:start k1=start f+15:=by simp only [StairPacket.start]; omega
  have p1:NativeJ7.prev k1=f:=Fin.ext (by simp only [NativeJ7.prev]; omega)
  refine ⟨endRaw (start f) raw v,flags.1,flags.2,g,sg,⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [s1]; exact cut
  · rw [p1]; exact facts
  · rw [p1]; exact unique_input input (fixed_input (start f) x p (by omega) good raw dom)
  · rw [show k1.val-f.val=1 by omega]
    have fo:=FO d x p good raw m stage
    simp only [OrdinaryChainW.mask,OrdinaryChainW.progW,OrdinaryChainW.newBank,OrdinaryChainW.group,
      Nat.mul_zero,Nat.add_zero,if_true,List.nil_append,Nat.mul_one]
    exact fo
  · rw [show k1.val-f.val-1=0 by omega]
    intro q hq
    simp [StockWindowGeo.holes,StockWindowGeo.packed] at hq

/-- `OrdinaryChain.wires` for any window over the fold: first block `f` (tick `start f`), interior blocks `I..J`,
`n` banks, exit `start f+15n`. Ship: f = 3, n = 10; 345: f = 3, n = 16; 90..345: f = 1, n = 18; 90..360: f = 1, n = 19. -/
theorem wiresFold (f k1:Fin 26) (hk1:k1.val=f.val+1) (hfb:start f=firstBlock)
    (I J:Nat) (hI2:1≤I) (hIf:f.val+1≤I) (hJ:J≤24)
    (L1:EndpointBetween I J) (L2:ScratchSpec) (F:FirstSpecF f k1) (FO:FirstOrdinarySpecF f)
    (js:List (Fin 26)) (consec:Consec f js) (hb:∀k∈js,I≤k.val ∧ k.val≤J)
    (n:Nat) (hn:1≤n) (he:start f+15*n+1≤512) (hl:(lastBlock f js).val+1=n+f.val)
    (jx:Fin 26) (hjx:jx.val=n+f.val) (X:ExitSpec (start f+15*n) jx)
    (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis) :
    ∀q∉StockWindowGeo.archives (start f) n,
      (run (forwardW CRTBarrel.params d f js) m (pullState (OB5.sig (start f-1)) raw)).basis q=
      (StockArchiveReferenceW.common (start f) n d raw).basis q := by
  have et:exitTick f js=start f+15*n:=by
    simp only [exitTick,lastStart_eq,StairPacket.start]; omega
  have sp:forwardW CRTBarrel.params d f js=
      (((CRTBarrel.params.portal (start f) :: firstF CRTBarrel.params d f).flatten++
        (chainF CRTBarrel.params d f js).flatten)++
        (exitF CRTBarrel.params d (start f+15*n)).flatten):=by
    rw [forwardW,forwardL,et]
    simp only [List.flatten_cons,List.flatten_append,List.append_assoc]
  have beg:∀k,RefW f k1 d x raw (run ((CRTBarrel.params.portal (start f) ::
      firstF CRTBarrel.params d f).flatten) k (pullState (OB5.sig (start f-1)) raw)):=by
    intro k
    rw [first_eqF d f]
    have first_index : f.val = 0 := by
      have e : 45 + 15*f.val = 45 + 15*WindowParams.first.val := hfb
      have first_val : WindowParams.first.val=0:=rfl
      omega
    exact beginG f k1 (by omega) (by omega) hk1 F FO d x good raw k stage
  rw [sp,run_append,run_append]
  exact lastG f n hn he jx hjx X d x good raw _ _
    (chainG f hfb I J hI2 hIf hJ L1 L2 d x good raw f js consec hb k1 jx hk1 (by omega) _ _ (beg _))

/-- Blocks of the 90..390 window (`WindowParams.rest = 2..21`, SA's `WindowCovered.rest_eq`). -/
theorem mem_rest21 {k : Fin 26} (h : k ∈ WindowParams.rest) : 2 ≤ k.val ∧ k.val ≤ 24 := by
  simp only [WindowParams.rest,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at h
  omega

/-- window390 (from build-chain's (at 360) main360): the exit at 405 (`resultW420` + the exit's blank holes), as `exitShip` at 270. -/
theorem exit420 : ExitSpec 420 ⟨25,by decide⟩ := by
  intro d x good raw s g sg pg ps m pre
  rw [(StockWindowW7.exitProg420 d).1]
  have lastF:=exitLast420 d x good raw s g sg pg ps pre m
  have direct:=resultW420 d x good raw s g sg m pre.domain pre.input (exitCut420 d x raw s g sg pg ps pre) lastF
  have nb:Ordinary420Terminal.newBank=newBankE 420:=by decide
  have one:span 420 1=EndTick4207.canonical:=by simp [span,EndTick4207.canonical]
  refine ⟨?_,?_⟩
  · rw [←nb,one,show 420-15=405 from rfl]; exact direct
  · obtain ⟨row,_,_,frame⟩:=lastF
    have cleared:=NativePack4207.cleared_holes d row _ frame
    intro r hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact cleared _ (by decide)
theorem wires405 (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    ∀q∉StockWindowGeo.archives 45 25,(run (CRTWindow.forwardCut d) m (pullState (OB5.sig 44) raw)).basis q=
      (StockArchiveReferenceW.common 45 25 d raw).basis q := by
  have h := wiresFold WindowParams.first ⟨1,by decide⟩ rfl rfl 1 24 (by decide) (by decide) (by decide) leaves22.endpoint
    leaves22.scratch (first_ship leaves22.first) (firstOrdinary_ship firstOrdinary)
    WindowParams7.rest7 WindowParams7.consec7 (fun k hk=>WindowParams7.mem_rest22 hk) 25 (by decide) (by decide)
    (by rw [WindowParams7.lastBlock_405]; rfl) ⟨25,by decide⟩ rfl exit420 d x good raw m stage
  -- restate the conclusion in the statement's syntax, so the kernel never unifies through the window program
  have e1 : start WindowParams.first = 45 := rfl
  have e2 : (45:Nat) - 1 = 44 := rfl
  rw [e1, e2, ← CRTWindow.run_cut] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowW7

/-- `OrdinaryChain.wires` of the ship (window 120..255, exit 270). -/
theorem wiresShip (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    ∀q∉StockWindowGeo.archives 45 25,(run (CRTWindow.forwardCut d) m (pullState (OB5.sig 44) raw)).basis q=
      (StockArchiveReferenceW.common 45 25 d raw).basis q :=
  wires405 d x good raw m stage

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ==== end build-main2 OrdW ====

-- ==== build-main2: the ship's stock comparison API (window 90..390, exit 405, 21 banks) ====
-- dadon's 3-bank names (StockArchiveReference.common, StockStrongChain.result, StockArchiveBanks.*,
-- StockRowVector.rows/binding, StockBaseline.comparison) re-opened as instances of the generic W sections.
section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowChainP
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 StockCanonicalRow StockWindowW7 StockStrongChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount key select WideReference.canonical
/-- window390: the exit archive's code ports at 405 (first 16 = `cellsRestoreP 405`). -/
def ExitPorts420 : Ports := ArchiveBoundary4207.codePorts
/-- window390: the exit at 420 (its step to the last frame and the keys it keeps). -/
theorem exitLeaves420 : ExitLeaves ⟨24,by decide⟩ ExitPorts420 := StockWindowW7.exitLeaves420
/-- window390 (from build-chain's (at 360) main360): dadon's `finalBank` at 420 (the exit archive keeps block 21's key; `finalS` at 270). -/
theorem finalKey420 : ∀ (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (m:List Bool), ReadyW d x p 420 s →
    SavedKey (value x p 405 (Shadow7.sbP 405) (StockRowVectorW.crossW ⟨24,by decide⟩)) ExitPorts420 d
      (run (exitF CRTBarrel.params d 420).flatten m s) := by
  intro d x good s m h
  obtain ⟨k,ek,raw,g,sg,pg,ps,pre⟩:=h
  have k19:k=⟨25,by decide⟩:=Fin.ext (by have := ek; simp only [StairPacket.start] at this; show k.val=25; omega)
  subst k19
  rw [(StockWindowW7.exitProg420 d).1]
  have cut:=OrdinaryChainG.exitCut420 d x raw s g sg pg ps pre
  obtain ⟨-,-,-,-,-,-,-,r20,r21,r22⟩:=StockWindowW7.exitBridge420
  let z:=unsigned 420 x p
  have short:Shadow7.SmallIfFar 39 15 z:=(Shadow7.Envelope.inputs x p 420 (lt_trans good.small good.cap) good.cap (by decide)).1
  have old:=LeaveJ7.Admission.actualNumbers ⟨24,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 39 420 x p=(2*2^54≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have facts:=pre.facts
  have mode:s.basis 1619=decide (Shadow.far 46 15 (unsigned 405 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1620=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 405 x p).v<(unsigned 405 x p).u))
        ((Shadow7.physicalCells ArchiveBoundary4207.sourceIdx s).take 5)):=by rw [←r21]; simpa only [Shadow7.physicalCells_eq] using facts.suffix
  have cross:s.basis 1621=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      HighBankSum.crossBit (LeaveJ7.TrueMiddle.d ⟨24,by decide⟩ (unsigned 405 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack4207.selected_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 420 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 405 x p) pg ps _
    old.odd old.farSmall (by simpa only [Shadow7.physicalCells_eq] using facts.records) mode side cross
  have canon:signedAt 405 x p pg ps=WideReference.canonical 405 x p:=pre.pastCanonical
  unfold signedAt at canon
  have cert:=last.2.1
  dsimp only at cert
  rw [canon] at cert
  have sbq:Shadow7.sbP 405=46:=by decide
  rw [sbq]
  exact ⟨cert.1,cert.2.1,kept_frame _ _ _ _ cert.2.2⟩

theorem mem21 {k : Fin 26} (h : k ∈ WindowParams.rest) : 2 ≤ k.val ∧ k.val ≤ (⟨21,by decide⟩:Fin 26).val := by
  simp only [WindowParams.rest,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at h
  show 2 ≤ k.val ∧ k.val ≤ 21
  omega
theorem exitT420 : exitTick WindowParams.first WindowParams7.rest7=start ⟨24,by decide⟩+15 := by
  rw [WindowParams7.rest7_eq]; rfl

/-- `StockWindowChain.result` of the 90..390 window (Final = FinalW 1 21 at 405), from build-chain's `checkedG`. -/
theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    let start:=pullState (OB5.sig 44) raw
    let out:=run (CRTWindow.forwardCut d) m start
    out.phase=raw.phase ∧ FinalW ⟨0,by decide⟩ ⟨24,by decide⟩ ExitPorts420 d x p out ∧
      ∀n,run (CRTWindow.reverseCut d) n out=start := by
  have law:=checkedG ⟨24,by decide⟩ (by decide) (by decide) ExitPorts420 WindowParams7.rest7 WindowParams7.consec7
    (fun k hk=>WindowParams7.mem_rest22 hk) exitT420 leaves22 exitLeaves420 d x good
  have law := law (pullState (OB5.sig 44) raw) m ⟨raw,stage,rfl⟩
  rw [←CRTWindow.run_cut,←CRTWindow.run_cut_rev] at law
  exact law

/-- Block `i`'s saved key (dadon's `SavedKey (value x p s b cross{s}) codePorts{s+15}`), for every block. -/
def KeyS (d:Bool) (x p:Nat) (i:Fin 26) (s:State) : Prop :=
  SavedKey (value x p (start i) (Shadow7.sbP (start i)) (StockRowVectorW.crossW i)) (ArchiveJ7.codePorts i) d s
def KeyLast (d:Bool) (x p:Nat) (s:State) : Prop :=
  SavedKey (value x p 405 (Shadow7.sbP 405) (StockRowVectorW.crossW ⟨24,by decide⟩)) ExitPorts420 d s
def LastS (d:Bool) (x p:Nat) (s:State) : Prop := LastAt ExitPorts420 ⟨24,by decide⟩ d x p s ∧ KeyLast d x p s

/-- dadon's `selected{s}` receipt for any interior block `k ≤ 22` (saves block `i = k-1`'s key). -/
theorem receiptS (d:Bool) (x p:Nat) (good:Bounds x p) (i k:Fin 26) (hk:k.val=i.val+1)
    (h2:1≤k.val) (h18:k.val≤24) :
    ∀ s m, ReadyW d x p (start k) s → KeyS d x p i (run (nextF CRTBarrel.params d i k).flatten m s) := by
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  have pk:=prev_of i k hk
  rw [next_eq d i k hk,←pk]
  simp only [run_append,run_take]
  have nums:=LeaveJ7.Admission.actualNumbers k (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (NativeJ7.prev k) (by simp only [NativeJ7.prev]; omega)
    (by simp only [NativeJ7.prev]; omega) x p good
  have hist:=pulled_history k rfl pre.domain
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=leaves22.scratch k (by omega) (by omega) d x p good raw s g sg pg ps m pre
  have cert:=NativeJ7.selected_receipt k (by omega) (by omega) d raw s m (unsigned (start k) x p) g sg nums.odd nums.farSmall
    pre.cut curr hist scr (unsigned (start (NativeJ7.prev k)) x p) pg ps _ old.odd old.farSmall pre.facts
  have canon:=pre.pastCanonical
  unfold signedAt at canon
  dsimp only at cert
  rw [canon] at cert
  exact ⟨cert.1,cert.2.1,ArchiveWindowPreserve.keep cert.2.2 (fun q hq=>leaves22.keepLeave k (by omega) h18 q hq _ _)⟩

theorem keyS_eq (x p b:Nat) (hb:0+b<26) :
    StockRowVectorW.keys ⟨0,by decide⟩ x p b=value x p (start ⟨0+b,hb⟩) (Shadow7.sbP (start ⟨0+b,hb⟩))
      (StockRowVectorW.crossW ⟨0+b,hb⟩) := by
  have e:start (⟨0,by decide⟩:Fin 26)+15*b=start ⟨0+b,hb⟩:=by simp only [StairPacket.start]; omega
  simp only [StockRowVectorW.keys,dif_pos hb]
  rw [e]

/-- The window's strong chain with the 22 saved keys (window_strong instance; dadon's `StockStrongChain.result`). -/
theorem strong (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    let start0:=pullState (OB5.sig 44) raw
    let out:=run (CRTWindow.forwardCut d) m start0
    out.phase=raw.phase ∧ StockRowVectorW.final ⟨0,by decide⟩ ⟨24,by decide⟩ ExitPorts420 d x p out ∧
      ∀n,run (CRTWindow.reverseCut d) n out=start0 := by
  have bl:blockOf (exitTick WindowParams.first WindowParams7.rest7)=25:=by rw [exitT420]; rfl
  have lastC:Checked (exitF CRTBarrel.params d (exitTick WindowParams.first WindowParams7.rest7)).flatten
      (exitR CRTBarrel.params d (exitTick WindowParams.first WindowParams7.rest7)).flatten
      (ReadyW d x p (exitTick WindowParams.first WindowParams7.rest7)) (LastS d x p):=by
    rw [exitT420]
    intro s n h
    have e:=exitLeaves420.step d x good s n h
    exact ⟨e.1,⟨e.2.1,finalKey420 d x good s n h⟩,e.2.2⟩
  have strong:=window_strong CRTBarrel.params d (ReadyW d x p) (KeyS d x p) (BeforeW d x p) (LastS d x p)
    WindowParams.first WindowParams7.rest7 WindowParams7.consec7 (firstStepG 24 leaves22 d x p good)
    (fun i k hm hk=>interiorG 24 (by decide) leaves22 d x p good i k hk (WindowParams7.mem_rest22 hm).1 (WindowParams7.mem_rest22 hm).2)
    (fun i k hm hk=>receiptS d x p good i k hk (by have h:1 ≤ k.val:=(WindowParams7.mem_rest22 hm).1; omega)
      (by have h:k.val ≤ 24:=(WindowParams7.mem_rest22 hm).2; omega))
    (fun i k hm hk s n _ i' h1 h2 key=>by
      obtain ⟨rr,c,kept⟩:=key
      have f3:WindowParams.first.val=0:=rfl
      exact ⟨rr,c,ArchiveWindowPreserve.keep kept (fun q hq=>leaves22.keepOlder i k i' hk (by omega) (by omega)
        (by have h:k.val ≤ 24:=(WindowParams7.mem_rest22 hm).2; exact h) d q hq s n)⟩)
    lastC
    (by
      intro s n _ i h1 h2 key
      rw [bl] at h2
      revert key
      rw [exitT420]
      intro key
      obtain ⟨r,c,kept⟩:=key
      exact ⟨r,c,ArchiveWindowPreserve.keep kept (fun q hq=>exitLeaves420.keep i h1 (by show i.val < 24; omega) d q hq s n)⟩)
  rw [CRTWindow.run_cut,CRTWindow.run_cut_rev]
  intro start0 out
  have hout:out=run (WindowFold.forwardW CRTBarrel.params d WindowParams.first WindowParams7.rest7) m start0:=
    rfl
  rw [hout]
  obtain ⟨ph,⟨⟨_,lastKey⟩,saved⟩,undo⟩:=strong start0 m ⟨raw,stage,rfl⟩
  refine ⟨ph,?_,undo⟩
  intro b hb
  change 0+b ≤ 24 at hb
  have lt:0+b<26:=by omega
  rw [keyS_eq x p b lt]
  unfold ArchiveStockRows.bankPorts
  by_cases h:(⟨0,by decide⟩:Fin 26).val+b<(⟨24,by decide⟩:Fin 26).val
  · rw [dif_pos h]
    change 0+b < 24 at h
    obtain ⟨bound,encoded,kept⟩ := saved ⟨0+b,lt⟩ (by show 0 ≤ 0+b; omega) (by rw [bl]; show 0+b+2 ≤ 25; omega)
    exact ⟨bound,encoded,ArchiveJ7.kept_stock _ _ _ _ kept⟩
  · rw [dif_neg h]
    change ¬(0+b < 24) at h
    have e:(⟨0+b,lt⟩:Fin 26)=⟨24,by decide⟩:=Fin.ext (by show 0+b=24; omega)
    rw [e]
    have s20:start (⟨24,by decide⟩:Fin 26)=405:=rfl
    rw [s20]
    exact lastKey
end ECDSAAdd.Entrant.StairPacket.StockWindowChainP
end


section
namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanks
open ECDSAAdd.Entrant.StairPacket.Partial
theorem exitCells : ∀j:Fin 16,StockWindowChainP.ExitPorts420 ⟨j.val,by omega⟩=
    (Partial.cellsRestoreP (start ⟨24, by decide⟩+15)).getD j 0 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.StockArchiveBanks
end


-- ==== begin Shadow7Wide20Trans150 ====
section

/-!
# Transition Block `s = 150 -> 165` (`Shadow7Wide20Trans150`)

Proves the complete semantics, frame preservation, exact roundtrip, and certified endpoint
handoff for the `s = 150 -> 165` transition leave (`leave150To20` / `leaveInv150To20`),
bridging 15-tick `NativeJ7` (`MixedWindow.j7`, tick `150`) directly into 20-tick `EnterJ20`
(`k0 = ⟨0, by decide⟩`, tick `165`) and `Archive150.rawPorts`.
-/

namespace ECDSAAdd.Entrant.StairPacket.Shadow20.Trans150

open ECDSAAdd.Arithmetic
open ECDSAAdd.Arithmetic.MappedCompressed
open ECDSAAdd.Entrant.IntegerPacket
open ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.GateMirror
open ECDSAAdd.Entrant.StairPacket.PortalAnd
open ECDSAAdd.Entrant.StairPacket.RailPair
open ECDSAAdd.Entrant.StairPacket.Shadow
open ECDSAAdd.Entrant.StairPacket.WideReference
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.LeaveCut20
open SkywalkNat IntegerHigh

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Section 1: `swap1` / `swap2` Head Bridge (`s = 150`) -/

def swap1 (a b : Wire) (f : BasisState) : BasisState :=
  fun q => f (if q = a then b else if q = b then a else q)

def swap2 (f : BasisState) : BasisState :=
  swap1 364 984 (swap1 365 985 f)

def swapSt (a b : Wire) (s : State) : State :=
  ⟨s.phase, swap1 a b s.basis⟩

def swap2St (s : State) : State :=
  ⟨s.phase, swap2 s.basis⟩

theorem swap1_symm (a b : Wire) (f : BasisState) : swap1 a b (swap1 a b f) = f := by
  funext q; unfold swap1
  by_cases h1 : q = a
  · rw [h1]; by_cases h2 : b = a <;> simp [h2]
  · by_cases h2 : q = b
    · rw [h2]; simp [h1, Ne.symm (show b ≠ a from h2 ▸ h1)]
    · simp [h1, h2]

theorem swap1_other {a b q : Wire} (h1 : q ≠ a) (h2 : q ≠ b) (f : BasisState) :
    swap1 a b f q = f q := by
  simp [swap1, h1, h2]

theorem swap1_fst {a b : Wire} (f : BasisState) : swap1 a b f a = f b := by
  simp [swap1]

theorem swap1_snd {a b : Wire} (hne : a ≠ b) (f : BasisState) : swap1 a b f b = f a := by
  simp [swap1, Ne.symm hne]

theorem swap2_other {q : Wire} (h1 : q ≠ 364) (h2 : q ≠ 984) (h3 : q ≠ 365) (h4 : q ≠ 985) (f : BasisState) :
    swap2 f q = f q := by
  simp [swap2, swap1, h1, h2, h3, h4]

private theorem writeBit_swap1 {a b x : Wire} (h1 : x ≠ a) (h2 : x ≠ b) (f : BasisState) (v : Bool) :
    writeBit (swap1 a b f) x v = swap1 a b (writeBit f x v) := by
  funext q; unfold writeBit swap1 Function.update
  by_cases hqa : q = a
  · rw [hqa]; simp [h1.symm, h2.symm]
  · by_cases hqb : q = b
    · rw [hqb]; by_cases hab : b = a <;> simp [hqa, hqb, hab, h1.symm, h2.symm]
    · simp [hqa, hqb]

private theorem swap1_comm_gate (a b : Wire) (g : Gate) (ha : a ∉ g.wires) (hb : b ∉ g.wires)
    (s : State) (m : List Bool) :
    run [front g] m (swapSt a b s) = swapSt a b (run [front g] m s) := by
  cases g with
  | x t =>
    simp only [Gate.wires, List.mem_singleton] at ha hb
    simp only [front, run, swapSt, writeBit_swap1 (Ne.symm ha) (Ne.symm hb),
      swap1_other (Ne.symm ha) (Ne.symm hb)]
  | cx c t =>
    simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
    simp only [front, run, swapSt, writeBit_swap1 (Ne.symm ha.2) (Ne.symm hb.2),
      swap1_other (Ne.symm ha.1) (Ne.symm hb.1), swap1_other (Ne.symm ha.2) (Ne.symm hb.2)]
  | ccx c1 c2 t =>
    simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
    simp only [front, run, swapSt, writeBit_swap1 (Ne.symm ha.2.2) (Ne.symm hb.2.2),
      swap1_other (Ne.symm ha.1) (Ne.symm hb.1), swap1_other (Ne.symm ha.2.1) (Ne.symm hb.2.1),
      swap1_other (Ne.symm ha.2.2) (Ne.symm hb.2.2)]
  | make c1 c2 t =>
    simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
    simp only [front, run, swapSt, writeBit_swap1 (Ne.symm ha.2.2) (Ne.symm hb.2.2),
      swap1_other (Ne.symm ha.1) (Ne.symm hb.1), swap1_other (Ne.symm ha.2.1) (Ne.symm hb.2.1),
      swap1_other (Ne.symm ha.2.2) (Ne.symm hb.2.2)]
  | pop c1 c2 t =>
    simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
    simp only [front, erase, run, measureAndCorrect, swapSt]
    rw [swap1_other (Ne.symm ha.2.2) (Ne.symm hb.2.2), writeBit_swap1 (Ne.symm ha.2.2) (Ne.symm hb.2.2)]
    cases hhd : m.headD false
    · simp [ECDSAAdd.correct]
    · simp only [↓reduceIte, ECDSAAdd.correct]
      rw [swap1_other (Ne.symm ha.1) (Ne.symm hb.1), swap1_other (Ne.symm ha.2.1) (Ne.symm hb.2.1)]

private theorem prepared_append : ∀ (a b : List Gate) (s : State),
    Prepared s a → Prepared (run (GateMirror.forward a) [] s) b → Prepared s (a ++ b)
  | [], _, _, _, hb => hb
  | g :: gs, b, s, ⟨h1, h2⟩, hb => by
    refine ⟨h1, prepared_append gs b (transition g s) h2 ?_⟩
    change Prepared (run ([front g] ++ GateMirror.forward gs) [] s) b at hb
    simpa only [run_append, run_take, List.drop_nil] using hb

private theorem swap1_comm_valid (a b : Wire) : ∀ (gs : List Gate) (s : State),
    (∀ g ∈ gs, a ∉ g.wires ∧ b ∉ g.wires) →
    (CRTBarrel.LeaveSplice.Valid s gs → CRTBarrel.LeaveSplice.Valid (swapSt a b s) gs) ∧
    (∀ m, run (GateMirror.forward gs) m (swapSt a b s) = swapSt a b (run (GateMirror.forward gs) m s))
  | [], s, _ => ⟨fun v => ⟨v.physical, trivial, trivial⟩, fun _ => rfl⟩
  | g :: gs, s, hall => by
    obtain ⟨ha, hb⟩ := hall g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, a ∉ g'.wires ∧ b ∉ g'.wires := fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')
    have htr : transition g (swapSt a b s) = swapSt a b (transition g s) :=
      swap1_comm_gate a b g ha hb s []
    have ih := swap1_comm_valid a b gs (transition g s) hrest
    constructor
    · intro v
      have hval : ValueOK (swapSt a b s) g := by
        have hv := v.prepared.1
        cases g with
        | pop c1 c2 t =>
          simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
          simp only [ValueOK, swapSt, swap1_other (Ne.symm ha.1) (Ne.symm hb.1),
            swap1_other (Ne.symm ha.2.1) (Ne.symm hb.2.1),
            swap1_other (Ne.symm ha.2.2) (Ne.symm hb.2.2)] at hv ⊢
          exact hv
        | _ => trivial
      have hfr : Fresh (swapSt a b s) g := by
        have hf := v.ready.1
        cases g with
        | make c1 c2 t =>
          simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false, not_or] at ha hb
          simp only [Fresh, swapSt, swap1_other (Ne.symm ha.2.2) (Ne.symm hb.2.2)] at hf ⊢
          exact hf
        | _ => trivial
      have vtail := ih.1 ⟨fun x hx => v.physical x (List.mem_cons_of_mem _ hx), v.prepared.2, v.ready.2⟩
      exact ⟨v.physical, ⟨hval, htr ▸ vtail.prepared⟩, ⟨hfr, htr ▸ vtail.ready⟩⟩
    · intro m
      change run ([front g] ++ GateMirror.forward gs) m (swapSt a b s) =
        swapSt a b (run ([front g] ++ GateMirror.forward gs) m s)
      rw [run_append, run_take, swap1_comm_gate a b g ha hb s,
        (swap1_comm_valid a b gs (run [front g] m s) hrest).2,
        run_append, run_take]

private theorem pairGM_swap (a s t : Wire) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t) (u : State)
    (v : CRTBarrel.LeaveSplice.Valid u (pairGM false a s t)) :
    CRTBarrel.LeaveSplice.Valid u (pairGM true a s t) ∧
    (∀ m, run (GateMirror.forward (pairGM true a s t)) m u =
      swapSt s t (run (GateMirror.forward (pairGM false a s t)) [] u)) := by
  have hval : u.basis t = (u.basis a && (u.basis s ^^ u.basis t)) := by
    have hp := v.prepared.2.2.1
    simp only [pairGM, Bool.false_eq_true, ↓reduceIte, transition, front, run, ValueOK,
      writeBit, Function.update_of_ne has, Function.update_of_ne hat, Function.update_of_ne hst,
      Function.update_of_ne hst.symm, Function.update_self] at hp
    simpa [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Bool.xor_comm] using hp
  have hphys : ∀ g ∈ pairGM true a s t, proper g = true := by
    intro g hg; simp only [pairGM, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp [proper, hst.symm]
    · simp [proper, has, hat, hst]
  have hprep : Prepared u (pairGM true a s t) := by
    simp only [pairGM, ↓reduceIte, Prepared, ValueOK, transition, front, run, writeBit,
      Function.update_of_ne has, Function.update_of_ne hat, Function.update_of_ne hst,
      Function.update_of_ne hst.symm, Function.update_self, true_and, and_true]
    exact hval
  have hready : Ready u (pairGM true a s t) := by
    simp only [pairGM, ↓reduceIte, Ready, Fresh, true_and, and_true]
  have hvt : CRTBarrel.LeaveSplice.Valid u (pairGM true a s t) := ⟨hphys, hprep, hready⟩
  refine ⟨hvt, fun m => ?_⟩
  rw [hvt.default_run m]
  apply State.extensionality
  · simp [pairGM, GateMirror.forward, front, erase, run, measureAndCorrect, ECDSAAdd.correct, swapSt]
  · funext q
    simp only [pairGM, ↓reduceIte, Bool.false_eq_true, GateMirror.forward, List.map_cons, List.map_nil,
      front, erase, run, measureAndCorrect, ECDSAAdd.correct, swapSt, swap1, writeBit]
    by_cases hqs : q = s
    · rw [hqs]
      cases hba : u.basis a <;> cases hbs : u.basis s <;> cases hbt : u.basis t <;>
        simp [hba, hbs, hbt, Function.update_of_ne hst, Function.update_of_ne hst.symm,
          Function.update_of_ne has, Function.update_of_ne hat, Function.update_self] at hval ⊢
    · by_cases hqt : q = t
      · rw [hqt]
        cases hba : u.basis a <;> cases hbs : u.basis s <;> cases hbt : u.basis t <;>
          simp [hba, hbs, hbt, hst.symm, Function.update_of_ne hst, Function.update_of_ne hst.symm,
            Function.update_of_ne has, Function.update_of_ne hat, Function.update_self] at hval ⊢
      · simp [hqs, hqt, Function.update_of_ne hqs, Function.update_of_ne hqt]

private theorem wordGM_flip_one (a : Wire) (r : HighBankJoin.Column) (rs : List HighBankJoin.Column)
    (hlow : r.low = false)
    (has : a ≠ r.shadow) (hat : a ≠ r.tube) (hst : r.shadow ≠ r.tube)
    (htog : ∀ g ∈ toggleG a r.hot, r.shadow ∉ g.wires ∧ r.tube ∉ g.wires)
    (hrest : ∀ g ∈ wordGM a rs, r.shadow ∉ g.wires ∧ r.tube ∉ g.wires)
    (u : State) (v : CRTBarrel.LeaveSplice.Valid u (wordGM a (r :: rs))) :
    let r' : HighBankJoin.Column := ⟨true, r.hot, r.shadow, r.tube⟩
    CRTBarrel.LeaveSplice.Valid u (wordGM a (r' :: rs)) ∧
    (∀ m, run (GateMirror.forward (wordGM a (r' :: rs))) m u =
      swapSt r.shadow r.tube (run (GateMirror.forward (wordGM a (r :: rs))) [] u)) := by
  intro r'
  have hw0 : wordGM a (r :: rs) = toggleG a r.hot ++ (pairGM false a r.shadow r.tube ++ (wordGM a rs ++ toggleG a r.hot)) := by
    change toggleG a r.hot ++ (pairGM r.low a r.shadow r.tube ++ (wordGM a rs ++ toggleG a r.hot)) = _
    rw [hlow]
  have hv0 : CRTBarrel.LeaveSplice.Valid u (toggleG a r.hot ++ (pairGM false a r.shadow r.tube ++ (wordGM a rs ++ toggleG a r.hot))) :=
    hw0 ▸ v
  obtain ⟨v1, v234⟩ := hv0.parts
  obtain ⟨v2, v34⟩ := v234.parts
  obtain ⟨v3, v4⟩ := v34.parts
  let u1 := run (GateMirror.forward (toggleG a r.hot)) [] u
  have hp := pairGM_swap a r.shadow r.tube has hat hst u1 v2
  have hc34 := swap1_comm_valid r.shadow r.tube (wordGM a rs ++ toggleG a r.hot)
    (run (GateMirror.forward (pairGM false a r.shadow r.tube)) [] u1)
    (fun g hg => (List.mem_append.mp hg).elim (hrest g) (htog g))
  have hv34' : CRTBarrel.LeaveSplice.Valid (run (GateMirror.forward (pairGM true a r.shadow r.tube)) [] u1)
      (wordGM a rs ++ toggleG a r.hot) := by
    rw [hp.2 []]; exact hc34.1 v34
  have hv234' : CRTBarrel.LeaveSplice.Valid u1 (pairGM true a r.shadow r.tube ++ (wordGM a rs ++ toggleG a r.hot)) :=
    ⟨proper_append hp.1.physical hv34'.physical,
     prepared_append _ _ _ hp.1.prepared hv34'.prepared,
     ready_append _ _ _ hp.1.ready hv34'.ready⟩
  have hv' : CRTBarrel.LeaveSplice.Valid u (wordGM a (r' :: rs)) := by
    change CRTBarrel.LeaveSplice.Valid u (toggleG a r.hot ++ (pairGM true a r.shadow r.tube ++ (wordGM a rs ++ toggleG a r.hot)))
    exact ⟨proper_append v1.physical hv234'.physical,
      prepared_append _ _ _ v1.prepared hv234'.prepared,
      ready_append _ _ _ v1.ready hv234'.ready⟩
  refine ⟨hv', fun m => ?_⟩
  rw [hv'.default_run m, hw0]
  change run (GateMirror.forward (toggleG a r.hot ++ (pairGM true a r.shadow r.tube ++ (wordGM a rs ++ toggleG a r.hot)))) [] u =
    swapSt r.shadow r.tube (run (GateMirror.forward (toggleG a r.hot ++ (pairGM false a r.shadow r.tube ++ (wordGM a rs ++ toggleG a r.hot)))) [] u)
  rw [forward_app (toggleG a r.hot), forward_app (toggleG a r.hot),
    forward_app (pairGM true a r.shadow r.tube), forward_app (pairGM false a r.shadow r.tube),
    run_append, run_take, List.drop_nil, run_append, run_take, List.drop_nil,
    run_append, run_take, List.drop_nil, run_append, run_take, List.drop_nil]
  change run (GateMirror.forward (wordGM a rs ++ toggleG a r.hot)) [] (run (GateMirror.forward (pairGM true a r.shadow r.tube)) [] u1) =
    swapSt r.shadow r.tube (run (GateMirror.forward (wordGM a rs ++ toggleG a r.hot)) [] (run (GateMirror.forward (pairGM false a r.shadow r.tube)) [] u1))
  rw [hp.2 [], hc34.2 []]

private theorem wordGM_step_valid (a : Wire) (r : HighBankJoin.Column) (rs1 rs2 : List HighBankJoin.Column)
    (w1 w2 : Wire)
    (htog : ∀ g ∈ toggleG a r.hot, w1 ∉ g.wires ∧ w2 ∉ g.wires)
    (hpair : ∀ g ∈ pairGM r.low a r.shadow r.tube, w1 ∉ g.wires ∧ w2 ∉ g.wires)
    (hsub : ∀ st, CRTBarrel.LeaveSplice.Valid st (wordGM a rs1) →
      CRTBarrel.LeaveSplice.Valid st (wordGM a rs2) ∧
      ∀ m, run (GateMirror.forward (wordGM a rs2)) m st =
        swapSt w1 w2 (run (GateMirror.forward (wordGM a rs1)) [] st))
    (u : State) (v : CRTBarrel.LeaveSplice.Valid u (wordGM a (r :: rs1))) :
    CRTBarrel.LeaveSplice.Valid u (wordGM a (r :: rs2)) ∧
    (∀ m, run (GateMirror.forward (wordGM a (r :: rs2))) m u =
      swapSt w1 w2 (run (GateMirror.forward (wordGM a (r :: rs1))) [] u)) := by
  change CRTBarrel.LeaveSplice.Valid u (toggleG a r.hot ++ (pairGM r.low a r.shadow r.tube ++ (wordGM a rs1 ++ toggleG a r.hot))) at v
  obtain ⟨v1, v234⟩ := v.parts
  obtain ⟨v2, v34⟩ := v234.parts
  obtain ⟨v3, v4⟩ := v34.parts
  let u1 := run (GateMirror.forward (toggleG a r.hot)) [] u
  let u2 := run (GateMirror.forward (pairGM r.low a r.shadow r.tube)) [] u1
  obtain ⟨v3', hrun3⟩ := hsub u2 v3
  have hc4 := swap1_comm_valid w1 w2 (toggleG a r.hot) (run (GateMirror.forward (wordGM a rs1)) [] u2) htog
  have hv4' : CRTBarrel.LeaveSplice.Valid (run (GateMirror.forward (wordGM a rs2)) [] u2) (toggleG a r.hot) := by
    rw [hrun3 []]; exact hc4.1 v4
  have hv34' : CRTBarrel.LeaveSplice.Valid u2 (wordGM a rs2 ++ toggleG a r.hot) :=
    ⟨proper_append v3'.physical hv4'.physical, prepared_append _ _ _ v3'.prepared hv4'.prepared,
     ready_append _ _ _ v3'.ready hv4'.ready⟩
  have hv234' : CRTBarrel.LeaveSplice.Valid u1 (pairGM r.low a r.shadow r.tube ++ (wordGM a rs2 ++ toggleG a r.hot)) :=
    ⟨proper_append v2.physical hv34'.physical, prepared_append _ _ _ v2.prepared hv34'.prepared,
     ready_append _ _ _ v2.ready hv34'.ready⟩
  have hv' : CRTBarrel.LeaveSplice.Valid u (wordGM a (r :: rs2)) :=
    ⟨proper_append v1.physical hv234'.physical, prepared_append _ _ _ v1.prepared hv234'.prepared,
     ready_append _ _ _ v1.ready hv234'.ready⟩
  refine ⟨hv', fun m => ?_⟩
  rw [hv'.default_run m]
  change run (GateMirror.forward (toggleG a r.hot ++ (pairGM r.low a r.shadow r.tube ++ (wordGM a rs2 ++ toggleG a r.hot)))) [] u =
    swapSt w1 w2 (run (GateMirror.forward (toggleG a r.hot ++ (pairGM r.low a r.shadow r.tube ++ (wordGM a rs1 ++ toggleG a r.hot)))) [] u)
  simp only [forward_app, run_append, run_take, List.drop_nil]
  rw [hrun3 [], hc4.2 []]

private def colsMid150 : List HighBankJoin.Column :=
  (List.range 17).map fun i =>
    ⟨decide (i < 11), if i < 16 then some (tagsP.getD i 0) else none,
      Shadow7.a0P 150 - 1 + i, Shadow7.bankW 150 i⟩

private theorem wordGM_step_prefix (a w1 w2 : Wire) (pref rs1 rs2 : List HighBankJoin.Column)
    (hpref : ∀ r ∈ pref,
      (∀ g ∈ toggleG a r.hot, w1 ∉ g.wires ∧ w2 ∉ g.wires) ∧
      (∀ g ∈ pairGM r.low a r.shadow r.tube, w1 ∉ g.wires ∧ w2 ∉ g.wires))
    (hsub : ∀ st, CRTBarrel.LeaveSplice.Valid st (wordGM a rs1) →
      CRTBarrel.LeaveSplice.Valid st (wordGM a rs2) ∧
      ∀ m, run (GateMirror.forward (wordGM a rs2)) m st =
        swapSt w1 w2 (run (GateMirror.forward (wordGM a rs1)) [] st))
    (u : State) (v : CRTBarrel.LeaveSplice.Valid u (wordGM a (pref ++ rs1))) :
    CRTBarrel.LeaveSplice.Valid u (wordGM a (pref ++ rs2)) ∧
    (∀ m, run (GateMirror.forward (wordGM a (pref ++ rs2))) m u =
      swapSt w1 w2 (run (GateMirror.forward (wordGM a (pref ++ rs1))) [] u)) := by
  induction pref generalizing u with
  | nil => exact hsub u v
  | cons r ps ih =>
    have hr := hpref r List.mem_cons_self
    exact wordGM_step_valid a r (ps ++ rs1) (ps ++ rs2) w1 w2 hr.1 hr.2
      (fun st vst => ih (fun r' hr' => hpref r' (List.mem_cons_of_mem _ hr')) st vst) u v

private theorem cols150_step1_eq :
    let p10 := (Shadow7.columnsP 150).take 10
    let c10 : HighBankJoin.Column := ⟨false, some (tagsP.getD 10 0), 364, 984⟩
    let c10' : HighBankJoin.Column := ⟨true, some (tagsP.getD 10 0), 364, 984⟩
    let t10 := (Shadow7.columnsP 150).drop 11
    Shadow7.columnsP 150 = p10 ++ c10 :: t10 ∧ colsMid150 = p10 ++ c10' :: t10 :=
  ⟨rfl, rfl⟩

private theorem cols150_step1_away :
    let p10 := (Shadow7.columnsP 150).take 10
    let c10 : HighBankJoin.Column := ⟨false, some (tagsP.getD 10 0), 364, 984⟩
    let t10 := (Shadow7.columnsP 150).drop 11
    p10.all (fun r => (toggleG 1614 r.hot ++ pairGM r.low 1614 r.shadow r.tube).all
      (fun g => g.wires.all fun q => decide (q ≠ 364 ∧ q ≠ 984))) = true ∧
    (toggleG 1614 c10.hot ++ wordGM 1614 t10).all
      (fun g => g.wires.all fun q => decide (q ≠ 364 ∧ q ≠ 984)) = true := by
  decide +kernel

private theorem cols150_step2_eq :
    let p11 := colsMid150.take 11
    let c11 : HighBankJoin.Column := ⟨false, some (tagsP.getD 11 0), 365, 985⟩
    let c11' : HighBankJoin.Column := ⟨true, some (tagsP.getD 11 0), 365, 985⟩
    let t11 := colsMid150.drop 12
    colsMid150 = p11 ++ c11 :: t11 ∧ columnsP150 = p11 ++ c11' :: t11 :=
  ⟨rfl, rfl⟩

private theorem cols150_step2_away :
    let p11 := colsMid150.take 11
    let c11 : HighBankJoin.Column := ⟨false, some (tagsP.getD 11 0), 365, 985⟩
    let t11 := colsMid150.drop 12
    p11.all (fun r => (toggleG 1614 r.hot ++ pairGM r.low 1614 r.shadow r.tube).all
      (fun g => g.wires.all fun q => decide (q ≠ 365 ∧ q ≠ 985))) = true ∧
    (toggleG 1614 c11.hot ++ wordGM 1614 t11).all
      (fun g => g.wires.all fun q => decide (q ≠ 365 ∧ q ≠ 985)) = true := by
  decide +kernel

private theorem wordGM_swap2 (u : State)
    (v : CRTBarrel.LeaveSplice.Valid u (wordGM 1614 (Shadow7.columnsP 150))) :
    CRTBarrel.LeaveSplice.Valid u (wordGM 1614 columnsP150) ∧
    (∀ m, run (GateMirror.forward (wordGM 1614 columnsP150)) m u =
      swap2St (run (GateMirror.forward (wordGM 1614 (Shadow7.columnsP 150))) [] u)) := by
  obtain ⟨e1a, e1b⟩ := cols150_step1_eq
  obtain ⟨hp1, hr1⟩ := cols150_step1_away
  obtain ⟨e2a, e2b⟩ := cols150_step2_eq
  obtain ⟨hp2, hr2⟩ := cols150_step2_away
  have mkNot : ∀ (w1 w2 : Wire) (gs : List Gate),
      gs.all (fun g => g.wires.all fun q => decide (q ≠ w1 ∧ q ≠ w2)) = true →
      ∀ g ∈ gs, w1 ∉ g.wires ∧ w2 ∉ g.wires := fun w1 w2 gs h g hg =>
    ⟨fun hm => (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h g hg) w1 hm)).1 rfl,
     fun hm => (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h g hg) w2 hm)).2 rfl⟩
  have h1 : CRTBarrel.LeaveSplice.Valid u (wordGM 1614 colsMid150) ∧
      ∀ m, run (GateMirror.forward (wordGM 1614 colsMid150)) m u =
        swapSt 364 984 (run (GateMirror.forward (wordGM 1614 (Shadow7.columnsP 150))) [] u) := by
    rw [e1a] at v ⊢; rw [e1b]
    refine wordGM_step_prefix 1614 364 984 _ _ _ (fun r hr => ?_) (fun st vst => ?_) u v
    · have h := mkNot 364 984 _ (List.all_eq_true.mp hp1 r hr)
      exact ⟨fun g hg => h g (List.mem_append_left _ hg), fun g hg => h g (List.mem_append_right _ hg)⟩
    · have h := mkNot 364 984 _ hr1
      exact wordGM_flip_one 1614 ⟨false, some (tagsP.getD 10 0), 364, 984⟩ _ rfl
        (by decide) (by decide) (by decide)
        (fun g hg => h g (List.mem_append_left _ hg))
        (fun g hg => h g (List.mem_append_right _ hg)) st vst
  have h2 : CRTBarrel.LeaveSplice.Valid u (wordGM 1614 columnsP150) ∧
      ∀ m, run (GateMirror.forward (wordGM 1614 columnsP150)) m u =
        swapSt 365 985 (run (GateMirror.forward (wordGM 1614 colsMid150)) [] u) := by
    rw [e2a] at h1 ⊢; rw [e2b]
    refine wordGM_step_prefix 1614 365 985 _ _ _ (fun r hr => ?_) (fun st vst => ?_) u h1.1
    · have h := mkNot 365 985 _ (List.all_eq_true.mp hp2 r hr)
      exact ⟨fun g hg => h g (List.mem_append_left _ hg), fun g hg => h g (List.mem_append_right _ hg)⟩
    · have h := mkNot 365 985 _ hr2
      exact wordGM_flip_one 1614 ⟨false, some (tagsP.getD 11 0), 365, 985⟩ _ rfl
        (by decide) (by decide) (by decide)
        (fun g hg => h g (List.mem_append_left _ hg))
        (fun g hg => h g (List.mem_append_right _ hg)) st vst
  refine ⟨h2.1, fun m => ?_⟩
  rw [h2.2 m, h1.2 []]
  apply State.extensionality
  · rfl
  · funext q; unfold swap2St swapSt swap2 swap1
    by_cases h1 : q = 364 <;> by_cases h2 : q = 984 <;> by_cases h3 : q = 365 <;> by_cases h4 : q = 985 <;>
      simp [h1, h2, h3, h4]

def afterHead150 : List Gate :=
  Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++ leaveJoinMove150 ++ Shadow7.fix10P 150 (Shadow7.sbP 150) ++
  leaveFix11 150 (Shadow7.sbP 150) ++ leaveFix12 150 (Shadow7.sbP 150) ++ Shadow7.lowSign 150

def afterHeadStock150 : List Gate :=
  Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++ Shadow7.leaveJoinMove 150 ++
  Shadow7.fix10P 150 (Shadow7.sbP 150) ++ leaveFix11 150 (Shadow7.sbP 150) ++ leaveFix12 150 (Shadow7.sbP 150) ++
  Shadow7.lowSign 150

private def fixTail150 : List Gate :=
  Shadow7.fix10P 150 (Shadow7.sbP 150) ++ leaveFix11 150 (Shadow7.sbP 150) ++
  leaveFix12 150 (Shadow7.sbP 150) ++ Shadow7.lowSign 150

private theorem fixTail150_away :
    fixTail150.all (fun g => g.wires.all fun q =>
      decide (q ≠ 364 ∧ q ≠ 984 ∧ q ≠ 365 ∧ q ≠ 985)) = true := by
  decide +kernel

private theorem hsp_move150 : Shadow7.leaveMoveOps 150 =
    (CRTBarrel.beforeReference 150 ++ Shadow7.leaveBarrel 150) ++ (afterHeadStock150 ++
      (Shadow7.lowRest 150 ++ Shadow7.leaveStoreMapped 150 ++ Shadow7.leaveLowClose 150 ++ Shadow7.leaveClose 150)) := by
  simp only [Shadow7.leaveMoveOps, CRTBarrel.beforeReference, afterHeadStock150, Shadow7.leaveLowStore,
    Shadow7.lowSign, Shadow7.lowRest, List.append_assoc]

private theorem haS_150 : afterHeadStock150 =
    (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++
      keptG (tagsP.getD · 0) (fun i => Shadow7.a0P 150 - 1 + i) 1613 0 8) ++
    (wordGM 1614 (Shadow7.columnsP 150) ++ fixTail150) := by
  simp only [afterHeadStock150, Shadow7.leaveJoinMove, fixTail150, List.append_assoc]

private theorem ha150_eq : afterHead150 =
    (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++ KeptParity.placed 150) ++
    (wordGM 1614 columnsP150 ++ fixTail150) := by
  simp only [afterHead150, leaveJoinMove150, fixTail150, List.append_assoc]

private theorem hC_shape_150 : (CRTBarrel.beforeReference 150 ++ Shadow7.leaveBarrel 150) ++ afterHeadStock150 =
    Shadow7.moveA 150 ++ (rowGates (Shadow7.e0P 150 + 6) (Shadow7.moveRows 150) ++
      (Shadow7.moveB 150 ++ (Shadow7.moveKept 150 ++ (wordGM 1614 (Shadow7.columnsP 150) ++ fixTail150)))) := by
  simp only [CRTBarrel.beforeReference, afterHeadStock150, Shadow7.moveA, Shadow7.moveB, Shadow7.moveKept,
    Shadow7.leaveJoinMove, Shadow7.leaveFix5Move, fixTail150, List.append_assoc]

private theorem hO_shape_150 : Shadow7.leaveHeadOps 150 =
    Shadow7.moveA 150 ++ (Shadow7.moveMux 150 ++ (Shadow7.moveB 150 ++
      (Shadow7.moveDig 150 ++ (wordGM 1614 (Shadow7.columnsP 150) ++ fixTail150)))) := by
  have e : Shadow7.fix5P 150 (Shadow7.sbP 150) = (Shadow7.fix5P 150 (Shadow7.sbP 150)).take 27 ++
      (((Shadow7.fix5P 150 (Shadow7.sbP 150)).drop 27).take 16 ++ (Shadow7.fix5P 150 (Shadow7.sbP 150)).drop 43) := rfl
  unfold Shadow7.leaveHeadOps Shadow7.moveA Shadow7.moveMux Shadow7.moveB Shadow7.moveDig Shadow7.leaveJoin fixTail150
  conv_lhs => rw [e]
  simp only [List.append_assoc]

private theorem hK_shape_150 : Shadow7.moveA 150 ++
    (GateMirror.rowGates (Shadow7.e0P 150 + 6) (Shadow7.moveRows 150) ++ Shadow7.moveB 150) =
      (CRTBarrel.beforeReference 150 ++ Shadow7.leaveBarrel 150) ++
        (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150) := by
  simp only [CRTBarrel.beforeReference, Shadow7.leaveFix5Move, Shadow7.moveA, Shadow7.moveB, List.append_assoc]

attribute [local irreducible] run in
private theorem before5_150 (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0) :
    DeadJoin.RawValid s (DeadJoin.before5 150) ∧
    run (GateMirror.forward (DeadJoin.before5 150)) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s := by
  have hi : MixedWindow.j7.val ≤ 24 := by decide
  have original : CRTBarrel.LeaveSplice.Valid s (DeadJoin.referenceOps (start MixedWindow.j7)) := by
    change CRTBarrel.LeaveSplice.Valid s (Shadow7.leaveMoveOps (start MixedWindow.j7))
    exact CRTBarrel.LeaveSplice.moved_valid (by decide) hi h
  have raw : DeadJoin.RawValid s (DeadJoin.referenceOps (start MixedWindow.j7)) :=
    ⟨original.physical, original.prepared, original.ready⟩
  have rel : FlagLeave.Rel (Shadow7.e0P (start MixedWindow.j7) + 3) (Shadow7.e0P (start MixedWindow.j7) + 4)
      (Shadow7.e0P (start MixedWindow.j7) + 6) false s := by
    simp only [FlagLeave.Rel, Bool.false_and, Bool.xor_false]
    rw [h.far, h.side]
    cases decide (Shadow.far (Shadow7.sbP (start MixedWindow.j7)) 15 z) <;>
      cases decide (2 ^ Shadow7.sbP (start MixedWindow.j7) ≤ z.u) <;> rfl
  have zero6 : s.basis (Shadow7.e0P (start MixedWindow.j7) + 6) = false := h.zero _ (by simp [LeaveJ7.watched])
  obtain ⟨v0, _, beforeEq⟩ := DeadJoin.raw_all_valid MixedWindow.j7 hi s raw
    (DeadJoin.pair_zero MixedWindow.j7 hi s (DeadJoin.entry_top_zero hi h)) (DeadJoin.admitted_scan_eq hi h) rel
  have shape0 : DeadJoin.allOps (start MixedWindow.j7) =
      DeadJoin.beforePre5Cut (start MixedWindow.j7) ++ (DeadJoin.row0Old (start MixedWindow.j7) ++
        (DeadJoin.beforePost5 (start MixedWindow.j7) ++ (Shadow7.leaveBarrel (start MixedWindow.j7) ++
          DeadJoin.afterAll (start MixedWindow.j7)))) := by
    rw [DeadJoin.all_split MixedWindow.j7 hi, DeadJoin.beforeAll_split5 MixedWindow.j7 hi]
    simp only [List.append_assoc]
  rw [shape0] at v0
  have hy6 : (run (GateMirror.forward (DeadJoin.beforePre5Cut (start MixedWindow.j7))) [] s).basis
      (Shadow7.e0P (start MixedWindow.j7) + 6) = false :=
    (DeadJoin.keeps_of_targets57 _ _ (fun g hg => of_decide_eq_true
      (List.all_eq_true.mp (DeadJoin.pre5Cut_targets MixedWindow.j7 hi) g hg)) [] s).trans zero6
  obtain ⟨hxy, htx, hty⟩ := DeadJoin.row0_distinct57 MixedWindow.j7 hi
  have eqRow0 : run (GateMirror.forward (DeadJoin.row0New (start MixedWindow.j7))) []
        (run (GateMirror.forward (DeadJoin.beforePre5Cut (start MixedWindow.j7))) [] s) =
      run (GateMirror.forward (DeadJoin.row0Old (start MixedWindow.j7))) []
        (run (GateMirror.forward (DeadJoin.beforePre5Cut (start MixedWindow.j7))) [] s) :=
    DeadJoin.swap_make57 _ _ _ _ hxy htx hty hy6
  have vRow0 : DeadJoin.RawValid (run (GateMirror.forward (DeadJoin.beforePre5Cut (start MixedWindow.j7))) [] s)
      (DeadJoin.row0New (start MixedWindow.j7)) :=
    ⟨fun x hx => List.all_eq_true.mp (DeadJoin.row0New_proper MixedWindow.j7 hi) x hx, ⟨trivial, trivial, trivial⟩,
      ⟨hy6, trivial, trivial⟩⟩
  obtain ⟨v5, _⟩ := DeadJoin.raw_swap_mid v0 vRow0 eqRow0
  have before5Eq : run (GateMirror.forward (DeadJoin.before5 (start MixedWindow.j7))) [] s =
      run (GateMirror.forward (DeadJoin.beforeAll (start MixedWindow.j7))) [] s := by
    rw [DeadJoin.before5, DeadJoin.beforeAll_split5 MixedWindow.j7 hi]
    simp only [forward_app, run_append, run_take, List.drop_nil, eqRow0]
  have v5' : DeadJoin.RawValid s (DeadJoin.before5 (start MixedWindow.j7) ++
      (Shadow7.leaveBarrel (start MixedWindow.j7) ++ DeadJoin.afterAll (start MixedWindow.j7))) := by
    simpa only [DeadJoin.before5, List.append_assoc] using v5
  have det5 : ∀ m', run (GateMirror.forward (DeadJoin.before5 (start MixedWindow.j7))) m' s =
      run (GateMirror.forward (DeadJoin.before5 (start MixedWindow.j7))) [] s := fun m' => v5'.parts.1.default_run m'
  exact ⟨v5'.parts.1, before5Eq.trans beforeEq⟩

attribute [local irreducible] run in
private theorem before150_pair (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0) :
    (∀ m, run (GateMirror.forward (CRTBarrel.before 150)) m s =
      run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s) ∧
    (∀ n, run (inverse (CRTBarrel.before 150)) n
      (run (GateMirror.forward (CRTBarrel.before 150)) [] s) = s) := by
  let j := MixedWindow.j7
  have hi : j.val ≤ 24 := by decide
  let b := Shadow7.sbP 150
  let scanHead := ScanRowGordo.firstRows 150 b
  let oldCell := ScanRowGordo.cell 150 b
  let shortCell := ScanRowGordo.shortCell 150 b
  let scanTail := Clean1556.rawTailClean 150
  let oldCore := Shadow7.leaveAdjustCore 150
  let newCore := CRTBarrel.leaveAdjustCoreTrim 150
  let oldStart := scanHead ++ (oldCell ++ scanTail)
  let reduced := scanHead ++ (shortCell ++ scanTail)
  let u := run (GateMirror.forward oldStart) [] s
  let t := run (GateMirror.forward (CRTBarrel.LeaveAdjustTrim.rawPrefix 150)) [] s
  have hs7 : start j = 150 := rfl
  have split : Clean1556.before5Clean 150 = oldStart ++ oldCore :=
    Clean1556.before5Clean_split 150
  obtain ⟨old, oldEq⟩ := before5_150 s z g0 s0 h
  obtain ⟨v, same⟩ := Clean1556.clean_prefix j hi s (hs7.symm ▸ old)
    (h.scratch 1556 (by decide)) (h.scratch 1571 (by decide))
  rw [hs7] at v same
  have baseEq := same.trans oldEq
  rw [split] at v baseEq
  obtain ⟨originalPrefix, originalCore⟩ := v.parts
  have original := CRTBarrel.LeaveSplice.moved_valid (j := j) (by decide) hi h
  change CRTBarrel.LeaveSplice.Valid s (DeadJoin.referenceOps (start j)) at original
  have raw : DeadJoin.RawValid s (DeadJoin.referenceOps (start j)) :=
    ⟨original.physical, original.prepared, original.ready⟩
  rw [show start j = 150 from rfl, CRTBarrel.LeaveAdjustTrim.rawReference] at raw
  have vr := raw.parts.1
  have refSplit := CRTBarrel.LeaveAdjustTrim.splitRaw 150
  rw [refSplit] at vr
  have coreEq : run (GateMirror.forward oldCore) [] u = run (GateMirror.forward oldCore) [] t := by
    rw [refSplit] at baseEq
    simpa only [CRTBarrel.LeaveAdjustTrim.run_append_nil, oldCore, u, t] using baseEq
  have preEq : u = t :=
    (originalCore.undo_run [] []).symm.trans
      ((congrArg (run (inverse oldCore) []) coreEq).trans (vr.parts.2.undo_run [] []))
  have facts := (CRTBarrel.LeaveCut.input_ext (Nat.zero_le _) hi h).2
  have premises := CRTBarrel.LeaveCut.shortPremises hi h h.tightRoom facts
  have conditions (chosen : CRTBarrel.trimAdjust (start j) = true) :
      (∀ q ∈ LeaveJ7.carries j, u.basis q = false) ∧
      regValue (LeaveJ7.ys j) u.basis + 1 < 2 ^ (Shadow7.wpP (start j) - 1) ∧
      (u.basis (Shadow7.e0P (start j) + 3) = true → 1 ≤ regValue (LeaveJ7.ys j) u.basis) := by
    rw [preEq]
    exact premises chosen
  obtain ⟨adjF, adjR⟩ := CRTBarrel.LeaveAdjustTrim.adjust_pair j hi u originalCore.physical
    originalCore.default_run (fun n => originalCore.undo_run [] n) conditions
  have coreF (m : List Bool) : run (GateMirror.forward newCore) m u =
      run (GateMirror.forward oldCore) [] u := adjF m
  have coreR (n : List Bool) : run (inverse newCore) n
      (run (GateMirror.forward oldCore) [] u) = u := adjR n
  have hsmall := (LeaveShadowRails.inputRow14 (Shadow7.sbP (start j)) z h.farSmall).1
  obtain ⟨scanF, scanR⟩ := ScanRowGordo.cell_pair j hi s _ _ _ _ h.ready h.fresh hsmall
  have cellF (m : List Bool) : run (GateMirror.forward shortCell) m (run (GateMirror.forward scanHead) [] s) =
      run (GateMirror.forward oldCell) [] (run (GateMirror.forward scanHead) [] s) := scanF m
  have cellR (n : List Bool) : run (inverse shortCell) n
      (run (GateMirror.forward oldCell) [] (run (GateMirror.forward scanHead) [] s)) =
    run (GateMirror.forward scanHead) [] s := scanR n
  obtain ⟨vFirst, vRest⟩ := originalPrefix.parts
  have vTail := vRest.parts.2
  have pF (m : List Bool) : run (GateMirror.forward reduced) m s = u := by
    simp only [reduced, u, oldStart, forward_app, run_append, run_take, List.take_nil,
      List.drop_nil, vFirst.default_run, cellF, vTail.default_run]
  have pR (n : List Bool) : run (inverse reduced) n u = s := by
    simp only [reduced, u, oldStart, DeadJoin.inverse_append, forward_app, run_append, run_take,
      List.take_nil, List.drop_nil]
    rw [vTail.undo_run [] _, cellR _, vFirst.undo_run [] _]
  have oldResult : run (GateMirror.forward oldCore) [] u =
      run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s := by
    rw [refSplit, CRTBarrel.LeaveAdjustTrim.run_append_nil]
    exact coreEq
  have shape : CRTBarrel.before 150 = reduced ++ newCore := rfl
  constructor
  · intro m
    rw [shape, forward_app, run_append, run_take, pF, coreF, oldResult]
  · intro n
    rw [shape, forward_app, DeadJoin.inverse_append]
    simp only [run_append, run_take, List.take_nil, List.drop_nil]
    rw [pF, coreF, coreR, pR]

attribute [local irreducible] run in
theorem before150_state (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0) (m : List Bool) :
    run (GateMirror.forward (CRTBarrel.before 150)) m s =
      run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s := (before150_pair s z g0 s0 h).1 m

attribute [local irreducible] run in
theorem before150_undo (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0) (n : List Bool) :
    run (inverse (CRTBarrel.before 150)) n (run (GateMirror.forward (CRTBarrel.before 150)) [] s) = s := (before150_pair s z g0 s0 h).2 n

attribute [local irreducible] run CRTBarrel.barrel in
theorem leaveMove150_head_eq (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0) :
    CRTBarrel.LeaveSplice.Valid (run (GateMirror.forward (CRTBarrel.before 150 ++ Shadow7.leaveBarrel 150)) [] s) afterHead150 ∧
    (∀ m, run (GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false ++ GateMirror.forward afterHead150) m s =
      swap2St (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s)) := by
  have hb := before150_state s z g0 s0 h
  have hpreEq : run (GateMirror.forward (CRTBarrel.before 150 ++ Shadow7.leaveBarrel 150)) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference 150 ++ Shadow7.leaveBarrel 150)) [] s := by
    simp only [forward_app, run_append, run_take, List.drop_nil, hb []]
  rw [hpreEq]
  have v := CRTBarrel.LeaveSplice.moved_valid (j := MixedWindow.j7) (by decide) (by decide) h
  rw [show start MixedWindow.j7 = 150 from rfl, hsp_move150] at v
  obtain ⟨vPre, vRest⟩ := v.parts
  obtain ⟨vHeadS, _⟩ := vRest.parts
  rw [haS_150] at vHeadS
  obtain ⟨vFK, vWT⟩ := vHeadS.parts
  obtain ⟨vW, vT⟩ := vWT.parts
  let uPreB := run (GateMirror.forward (CRTBarrel.beforeReference 150 ++ Shadow7.leaveBarrel 150)) [] s
  let uFK := run (GateMirror.forward (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++
    keptG (tagsP.getD · 0) (fun i => Shadow7.a0P 150 - 1 + i) 1613 0 8)) [] uPreB
  obtain ⟨vW', hrunW⟩ := wordGM_swap2 uFK vW
  have hFT1 : ∀ g ∈ fixTail150, (364 : Wire) ∉ g.wires ∧ (984 : Wire) ∉ g.wires := fun g hg =>
    ⟨fun hm => (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp fixTail150_away g hg) 364 hm)).1 rfl,
     fun hm => (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp fixTail150_away g hg) 984 hm)).2.1 rfl⟩
  have hFT2 : ∀ g ∈ fixTail150, (365 : Wire) ∉ g.wires ∧ (985 : Wire) ∉ g.wires := fun g hg =>
    ⟨fun hm => (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp fixTail150_away g hg) 365 hm)).2.2.1 rfl,
     fun hm => (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp fixTail150_away g hg) 985 hm)).2.2.2 rfl⟩
  have hc1 := swap1_comm_valid 365 985 fixTail150 (run (GateMirror.forward (wordGM 1614 (Shadow7.columnsP 150))) [] uFK) hFT2
  have hc2 := swap1_comm_valid 364 984 fixTail150 (swapSt 365 985 (run (GateMirror.forward (wordGM 1614 (Shadow7.columnsP 150))) [] uFK)) hFT1
  have hvT' : CRTBarrel.LeaveSplice.Valid (run (GateMirror.forward (wordGM 1614 columnsP150)) [] uFK) fixTail150 := by
    rw [hrunW []]; exact hc2.1 (hc1.1 vT)
  have hvWT' : CRTBarrel.LeaveSplice.Valid uFK (wordGM 1614 columnsP150 ++ fixTail150) :=
    ⟨proper_append vW'.physical hvT'.physical, prepared_append _ _ _ vW'.prepared hvT'.prepared,
     ready_append _ _ _ vW'.ready hvT'.ready⟩
  have hkp150_rel := h.movedRelation (by decide) (by decide)
  rw [show start MixedWindow.j7 = 150 from rfl, hK_shape_150] at hkp150_rel
  have hkp150_pair := KeptParity.placed_pair MixedWindow.j7 (by decide) _ hkp150_rel
  rw [show start MixedWindow.j7 = 150 from rfl] at hkp150_pair
  have hmc8 : measurementCount (GateMirror.forward (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150)) = 0 := rfl
  have hkpState : run (GateMirror.forward ((CRTBarrel.beforeReference 150 ++ Shadow7.leaveBarrel 150) ++
      (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150))) [] s =
      run (GateMirror.forward (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150)) [] uPreB := by
    simp only [uPreB, forward_app, run_append, run_take, List.drop_nil, List.take_nil]
  rw [hkpState] at hkp150_pair
  have hfk_eq : ∀ m', run (GateMirror.forward (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++
      KeptParity.placed 150)) m' uPreB = uFK := by
    intro m'
    rw [forward_app, run_append, hmc8, List.take_zero, List.drop_zero, hkp150_pair.1]
    simp only [uFK, Shadow7.moveKept, forward_app, run_append, hmc8, List.take_zero, List.drop_zero, List.take_nil,
      List.drop_nil]
  have hvFK_kp : CRTBarrel.LeaveSplice.Valid uPreB (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++
      KeptParity.placed 150) := by
    have hkp_p : Proper (KeptParity.placed 150) :=
      fun g hg => List.all_eq_true.mp (by decide +kernel : (KeptParity.placed 150).all proper = true) g hg
    have hkp_pl : (KeptParity.placed 150).all plainGate = true := by decide +kernel
    have hv8 := vFK.parts.1
    refine ⟨proper_append hv8.physical hkp_p, prepared_append _ _ _ hv8.prepared (by repeat' constructor),
      ready_append _ _ _ hv8.ready (ready_plain _ hkp_pl _)⟩
  have hvHead150 : CRTBarrel.LeaveSplice.Valid uPreB afterHead150 := by
    rw [ha150_eq]
    refine ⟨proper_append hvFK_kp.physical hvWT'.physical,
      prepared_append _ _ _ hvFK_kp.prepared (by rw [hfk_eq []]; exact hvWT'.prepared),
      ready_append _ _ _ hvFK_kp.ready (by rw [hfk_eq []]; exact hvWT'.ready)⟩
  have hstock_eq : run (GateMirror.forward ((CRTBarrel.beforeReference 150 ++ Shadow7.leaveBarrel 150) ++ afterHeadStock150)) [] s =
      run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s := by
    have hhot := h.hot (by decide) (by decide) []
    have hdead := h.dead (by decide) (by decide) []
    rw [show start MixedWindow.j7 = 150 from rfl] at hhot hdead
    rw [hC_shape_150, hO_shape_150]
    have h16 : run (GateMirror.forward (Shadow7.moveA 150 ++ (rowGates (Shadow7.e0P 150 + 6) (Shadow7.moveRows 150) ++
        (Shadow7.moveB 150 ++ (Shadow7.moveKept16 150 ++ (wordGM 1614 (Shadow7.columnsP 150) ++ fixTail150)))))) [] s =
        run (GateMirror.forward (Shadow7.moveA 150 ++ (Shadow7.moveMux 150 ++ (Shadow7.moveB 150 ++
          (Shadow7.moveDig 150 ++ (wordGM 1614 (Shadow7.columnsP 150) ++ fixTail150)))))) [] s := by
      simp only [forward_app]
      rw [rowGates_forward, Shadow7.mux_forward, Shadow7.dig_forward]
      exact MoveChain.splice (Shadow7.e0P 150 + 6) (Shadow7.moveRows 150)
        (GateMirror.forward (Shadow7.moveA 150)) (GateMirror.forward (Shadow7.moveB 150))
        (GateMirror.forward (wordGM 1614 (Shadow7.columnsP 150) ++ fixTail150))
        (GateMirror.forward (Shadow7.moveKept16 150)) s [] _
        (Shadow7.apart_move (by decide) (by decide)) (Shadow7.lone_move 150)
        (Shadow7.stillB (by decide) (by decide)) (Shadow7.woven_move (by decide) (by decide)) hhot.1 hhot.2
    rw [← h16, Shadow7.moveKept16_split]
    simp only [forward_app, rowGates_forward, List.append_assoc, run_append, run_take, List.drop_nil]
    have hpre : run (GateMirror.forward (Shadow7.moveB 150)) []
        (run (MoveChain.rows (Shadow7.e0P 150 + 6) (Shadow7.moveRows 150)) []
          (run (GateMirror.forward (Shadow7.moveA 150)) [] s)) =
        MoveChain.clrAll (Shadow7.e0P 150 + 6) (Shadow7.moveRows 150)
          (run (GateMirror.forward (Shadow7.moveA 150 ++ (Shadow7.moveMux 150 ++ Shadow7.moveB 150))) [] s) := by
      have hp := Shadow7.prefix_rows (by decide) (by decide) s [] _ hhot.1 hhot.2
      simp only [forward_app, run_append, run_take, List.drop_nil] at hp
      have hr : run (GateMirror.forward (Shadow7.moveA 150 ++ (Shadow7.moveMux 150 ++ Shadow7.moveB 150))) [] s =
          run (GateMirror.forward (Shadow7.moveB 150)) []
            (run (GateMirror.forward (Shadow7.moveMux 150)) [] (run (GateMirror.forward (Shadow7.moveA 150)) [] s)) := by
        simp only [forward_app, run_append, run_take, List.drop_nil]
      rw [hr]; exact hp
    rw [hpre]
    have hti := Shadow7.tail_idle (s := 150) (by decide) (by decide)
      (run (GateMirror.forward (Shadow7.moveA 150 ++ (Shadow7.moveMux 150 ++ Shadow7.moveB 150))) [] s)
      [] [] hdead
    rw [hti]
  obtain ⟨sameB, _⟩ := CRTBarrel.LeaveCut.barrel_pair MixedWindow.j7 (by decide) (by decide)
    _ (CRTBarrel.LeaveCut.input (by decide) (by decide) h)
  rw [show start MixedWindow.j7 = 150 from rfl] at sameB
  refine ⟨hvHead150, fun m => ?_⟩
  simp only [run_append, run_take]
  rw [hb, sameB]
  have hpreRun : run (GateMirror.forward (Shadow7.leaveBarrel 150)) []
      (run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s) = uPreB := by
    simp only [uPreB, forward_app, run_append, run_take, List.drop_nil]
  rw [hpreRun, hvHead150.default_run, ha150_eq]
  rw [forward_app (Shadow7.fix8P 150 (Shadow7.sbP 150) ++ Shadow7.glueG3 150 ++ KeptParity.placed 150),
    run_append, run_take, List.drop_nil, hfk_eq [],
    forward_app (wordGM 1614 columnsP150), run_append, run_take, List.drop_nil]
  change run (GateMirror.forward fixTail150) [] (run (GateMirror.forward (wordGM 1614 columnsP150)) [] uFK) = _
  rw [hrunW []]
  change run (GateMirror.forward fixTail150) []
      (swapSt 364 984 (swapSt 365 985 (run (GateMirror.forward (wordGM 1614 (Shadow7.columnsP 150))) [] uFK))) = _
  rw [hc2.2 [], hc1.2 [], ← hstock_eq, haS_150]
  simp only [uFK, uPreB, forward_app, run_append, run_take, List.drop_nil]
  rfl

/-! ### Section 2: Tail Forward Semantics (`s = 150 -> 165`) -/

def smallA150 : List Wire := (List.range (lows150 - 1)).map (Shadow7.a0P 150 + ·)
def smallM150 : List Wire := (List.range (lows150 - 1)).map (Shadow7.b0P 150 + ·)
def smallC150 : List Wire := (List.range (lows150 - 1 - 1)).map (1559 + ·)

def borrowG4_150 : Program :=
  [.CX (Shadow7.a0P 150 - 1) 1557, .X 1557, .CCX (Shadow7.b0P 150 - 1) 1557 1558]

def releaseMaskP150 : Program :=
  GateMirror.forward [.pop (Shadow7.b0P 150 - 1) 1557 1558, .cx (Shadow7.a0P 150 - 1) 1557, .x 1557]

def lowRest150 : List Gate :=
  let L := lows150 - 1
  let bs := (List.range L).map (Shadow7.b0P 150 + ·)
  [.cx (Shadow7.a0P 150 - 1) 1557, .x 1557, .make (Shadow7.b0P 150 - 1) 1557 1558] ++
  ((List.range L).map fun i => .make 1556 (Shadow7.a0P 150 + i) (Shadow7.b0P 150 + i)) ++ xsG bs ++
  addG bs ((List.range (L - 1)).map (1559 + ·)) 1558 ++ xsG bs ++
  [.pop (Shadow7.b0P 150 - 1) 1557 1558, .cx (Shadow7.a0P 150 - 1) 1557, .x 1557]

def pendingPairs150 : List (Wire × Wire) :=
  let L := lows150
  let H := Shadow7.liveW 150 - L
  (List.range (H + 1)).map fun k =>
    (if k = 0 then Shadow7.a0P 150 + L - 2 else Shadow7.bankW 150 (L + k - 1), Shadow7.storeW 150 (k + 1))

def clearFlagPairs150 : List (Wire × Wire) :=
  (List.range lows150).map fun k => (Shadow7.b0P 150 - 1 + k, 1559 + k)

def low150 : List (Wire × Wire) :=
  (List.range lows150).map fun i => (Shadow7.a0P 150 - 1 + i, Shadow7.b0P 150 - 1 + i)

def head150Prog : Program :=
  GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false ++ GateMirror.forward afterHead150

def full150Prog : Program :=
  head150Prog ++ (borrowG4_150 ++ Companion.restore smallA150 smallM150 smallC150 1556 1558)

def beforeStore150Prog : Program :=
  full150Prog ++ (releaseMaskP150 ++ GateMirror.forward leaveStoreMapped150)

def storeMapped150Prog : Program :=
  beforeStore150Prog ++ GateMirror.forward leaveLowClose150

private theorem lowStore150_parts :
    GateMirror.forward leaveLowStore150 =
      GateMirror.forward (Shadow7.lowSign 150) ++
      (borrowG4_150 ++ (Companion.restore smallA150 smallM150 smallC150 1556 1558 ++ releaseMaskP150)) := by
  have hc : GateMirror.forward ((List.range (lows150 - 1)).map
      fun i => Gate.make 1556 (Shadow7.a0P 150 + i) (Shadow7.b0P 150 + i)) =
      copyRegister (some 1556) smallA150 smallM150 := by
    rw [smallA150, smallM150, LeaveJ7.copy_map]; simp only [GateMirror.forward, List.map_map]; rfl
  simp only [leaveLowStore150, Shadow7.lowSign, forward_app, forward_addG, LeaveJ7.forward_xsG', hc,
    Companion.restore, HighBankUnit.sub, mappedSub, smallM150, smallC150, releaseMaskP150, borrowG4_150,
    List.append_assoc]
  rfl

private theorem pending150_fst :
    pendingPairs150.map Prod.fst =
      (Shadow7.a0P 150 + lows150 - 2) ::
        (List.range (Shadow7.liveW 150 - lows150)).map (fun i => Shadow7.bankW 150 (lows150 + i)) := by
  simp only [pendingPairs150, List.map_map, Function.comp]
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp, if_pos, Nat.succ_ne_zero, if_false]
  congr 1

private def shortFlagPairs150 : List (Wire × Wire) :=
  clearFlagPairs150.take smallM150.length

private theorem clearFlag150_fst :
    shortFlagPairs150.map Prod.fst = (List.range (lows150 - 1)).map (Shadow7.b0P 150 - 1 + ·) := by
  rfl

private theorem storeMapped150_parts :
    GateMirror.forward leaveStoreMapped150 =
      latch true none 1557 1558 pendingPairs150 ++
        ([.CCX 1556 1557 1558] ++ latch true none 1556 1558 shortFlagPairs150) := by
  have ch1 : GateMirror.forward (chainG (Shadow7.storeW 150)
      (fun i => if i = 0 then Shadow7.a0P 150 + lows150 - 2 else Shadow7.bankW 150 (lows150 + i - 1))
      [.cx (Shadow7.storeW 150 (Shadow7.liveW 150 - lows150 + 1)) 1557, .x 1557]
      0 (Shadow7.liveW 150 - lows150 + 1)) =
      PortalAnd.chain true none 1557 1558 pendingPairs150 := by
    rw [LeaveJ7.forward_chainG0, LeaveJ7.storeW_zero7]; rfl
  have ch2 : GateMirror.forward (chainG (fun i => (1558 + i : Wire)) (fun i => Shadow7.b0P 150 - 1 + i)
      [.cx (1558 + (lows150 - 1)) 1556, .x 1556] 0 (lows150 - 1)) =
      PortalAnd.chain true none 1556 1558 shortFlagPairs150 := by
    have h := LeaveJ7.forward_chainG0 (fun i => (1558 + i : Wire)) (fun i => Shadow7.b0P 150 - 1 + i) 1556 (lows150 - 1)
    have e : (List.range (lows150 - 1)).map (fun k => (Shadow7.b0P 150 - 1 + k, (1558 + (k + 1) : Wire))) =
        shortFlagPairs150 := by decide +kernel
    rw [← e]; exact h
  have fc (g : Gate) (gs : List Gate) : GateMirror.forward (g :: gs) = front g :: GateMirror.forward gs := rfl
  have fn : GateMirror.forward [] = [] := rfl
  simp only [leaveStoreMapped150, forward_app, LeaveJ7.forward_xsG', ch1, ch2, PortalAnd.latch, PortalAnd.digits,
    pending150_fst, clearFlag150_fst, fc, fn, front, GateMirror.erase, notRegister, List.map_cons, List.map_nil,
    List.map_append, List.reverse_cons, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
    if_true, ↓reduceIte]

private theorem lowClose150_parts :
    GateMirror.forward leaveLowClose150 =
      notRegister (LeaveJ7.history MixedWindow.j7) ++ RailPair.store 180 (Shadow7.e0P 150 + 5) low150 [] := by
  have e1 : GateMirror.forward ((List.range lows150).map
      fun i => Gate.cx (Shadow7.e0P 150 + 5) (Shadow7.b0P 150 - 1 + i)) =
      signComplement (Shadow7.e0P 150 + 5) (low150.map Prod.snd) := by
    simp only [GateMirror.forward, signComplement, low150, List.map_map]; rfl
  have e2 : GateMirror.forward ((List.range lows150).flatMap
      fun i => cswapG (150 + 30) (Shadow7.b0P 150 - 1 + i) (Shadow7.a0P 150 - 1 + i)) =
      exchange 180 low150 := by
    simp only [GateMirror.forward, exchange, low150, List.map_flatMap, List.flatMap_map]; rfl
  simp only [leaveLowClose150, forward_app, LeaveJ7.forward_xsG', e1, e2, RailPair.store, RailPair.transfer,
    List.flatMap_nil, List.nil_append, List.append_assoc, LeaveJ7.history]
  rfl

private theorem close150_parts :
    GateMirror.forward leaveClose150To20 =
      GateMirror.forward (Shadow7.closeFlag 150) ++
        LeaveRelocation.program movesP150To20 := by
  unfold leaveClose150To20
  rw [forward_app]
  have hsw : ∀ ps : List (Wire × Wire), GateMirror.forward (swapsG ps) = LeaveRelocation.program ps := by
    intro ps; induction ps with
    | nil => rfl
    | cons p ps ih =>
      show GateMirror.forward ([.cx p.1 p.2, .cx p.2 p.1, .cx p.1 p.2] ++ swapsG ps) = _
      rw [forward_app, ih]; rfl
  rw [hsw]

private theorem leave150To20_split :
    leave150To20 = storeMapped150Prog ++ GateMirror.forward leaveClose150To20 := by
  unfold leave150To20 storeMapped150Prog beforeStore150Prog full150Prog head150Prog
    leaveAfter150To20 afterHead150
  simp only [forward_app, List.append_assoc]
  rw [lowStore150_parts]
  simp only [List.append_assoc]

private theorem small150_geom : Companion.Geometry smallA150 smallM150 smallC150 1556 1558 := by
  constructor <;> decide +kernel

private theorem low150_geom : StoreGeometry 180 (Shadow7.e0P 150 + 5) low150 [] := by
  constructor <;> decide +kernel

private theorem pending150_layout :
    (1557 :: (1558 : Wire) :: PortalAnd.sites pendingPairs150).Nodup := by
  have hg : Shadow7.sbP 150 = 173 ∧ Shadow7.a0P 150 = 355 ∧ Shadow7.b0P 150 = 960 ∧
      Shadow7.wpP 150 = 70 ∧ Shadow7.e0P 150 = 1747 ∧ Shadow7.liveW 150 = 84 ∧
      bTopP 150 = 1043 ∧ lows150 = 12 := by decide
  have hperm : (1557 :: (1558 : Wire) :: PortalAnd.sites pendingPairs150).Perm
      (1557 :: (1558 : Wire) :: (pendingPairs150.map Prod.fst ++ pendingPairs150.map Prod.snd)) :=
    List.Perm.cons _ (List.Perm.cons _ (LeaveJ7.sites_perm _))
  rw [hperm.nodup_iff]
  have hfst_nd : (pendingPairs150.map Prod.fst).Nodup := by
    rw [pending150_fst, List.nodup_cons]
    refine ⟨?_, List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range⟩
    · intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have hbc := Shadow7.bank_cases (s := 150) (i := lows150 + i) (by decide) (by decide) (by omega)
      rcases hbc with ⟨_, eb⟩ | ⟨_, _, eb, _, _⟩ | ⟨_, eb, _⟩ <;> (unfold Wire at *; omega)
    · rw [List.mem_range] at ha hb
      have := Shadow7.bank_inj (s := 150) (by decide) (by decide) (by omega) (by omega) e
      omega
  have hsnd_nd : (pendingPairs150.map Prod.snd).Nodup := by
    simp only [pendingPairs150, List.map_map, Function.comp]
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    simp only [Function.comp_apply] at e
    have h1 := Shadow7.storeW_cases (s := 150) (by decide) (by decide) (a + 1)
    have h2 := Shadow7.storeW_cases (s := 150) (by decide) (by decide) (b + 1)
    unfold Wire at *; omega
  have hfst_r : ∀ q ∈ pendingPairs150.map Prod.fst, (q : Nat) ≤ 1043 ∨ (1598 ≤ (q : Nat) ∧ (q : Nat) ≤ 1612) := by
    intro q hq; rw [pending150_fst, List.mem_cons] at hq
    rcases hq with rfl | hm
    · left; decide
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      have hbc := Shadow7.bank_cases (s := 150) (i := lows150 + i) (by decide) (by decide) (by omega)
      rcases hbc with ⟨_, _⟩ | ⟨_, _, _, _, _⟩ | ⟨_, _, _⟩
      · omega
      · left; unfold Wire at *; omega
      · right; unfold Wire at *; omega
  have hsnd_r : ∀ q ∈ pendingPairs150.map Prod.snd, (1559 ≤ (q : Nat) ∧ (q : Nat) ≤ 1597) ∨ 1613 ≤ (q : Nat) := by
    intro q hq; simp only [pendingPairs150, List.map_map, Function.comp, List.mem_map, List.mem_range] at hq
    obtain ⟨k, _, rfl⟩ := hq
    have hs := Shadow7.storeW_cases (s := 150) (by decide) (by decide) (k + 1)
    unfold Wire at *; omega
  have hdisj : ∀ a ∈ pendingPairs150.map Prod.fst, ∀ b ∈ pendingPairs150.map Prod.snd, a ≠ b := by
    intro a ha b hb eq; subst eq
    rcases hfst_r a ha with x | x <;> rcases hsnd_r a hb with y | y <;> unfold Wire at * <;> omega
  rw [List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, List.nodup_append.mpr ⟨hfst_nd, hsnd_nd, hdisj⟩⟩
  · intro hm; simp only [List.mem_cons, List.mem_append] at hm
    rcases hm with h | h | h
    · exact (by decide : (1557 : Wire) ≠ 1558) h
    · rcases hfst_r 1557 h with a | a <;> unfold Wire at * <;> omega
    · rcases hsnd_r 1557 h with a | a <;> unfold Wire at * <;> omega
  · intro hm; simp only [List.mem_append] at hm
    rcases hm with h | h
    · rcases hfst_r 1558 h with a | a <;> unfold Wire at * <;> omega
    · rcases hsnd_r 1558 h with a | a <;> unfold Wire at * <;> omega

def bankW150Lit (i : Nat) : Wire :=
  if i < 70 then 974 + i else 1598 + (i - 70)

private theorem bankW150_lit (i : Nat) (h10 : 10 ≤ i) (hlt : i < 85) :
    Shadow7.bankW 150 i = bankW150Lit i := by
  have hg : Shadow7.sbP 150 = 173 ∧ Shadow7.b0P 150 = 960 ∧ Shadow7.wpP 150 = 70 ∧
      Shadow7.lowsP 150 = 10 ∧ Shadow7.liveW 150 = 84 ∧ bTopP 150 = 1043 := by decide
  have hbc := Shadow7.bank_cases (s := 150) (i := i) (by decide) (by decide) (by omega)
  unfold bankW150Lit
  rcases hbc with ⟨h1, _⟩ | ⟨h1, h2, eb, _, _⟩ | ⟨h1, eb, _⟩
  · omega
  · rw [if_pos (by omega)]; unfold Wire at *; omega
  · rw [if_neg (by omega)]; unfold Wire at *; omega

def bankPair150 (i : Nat) : Wire × Wire :=
  (if i < 58 then (986 + i : Wire) else (1598 + (i - 58) : Wire), (971 + i : Wire))

def flagPairs150 : List (Wire × Wire) :=
  [(1557, 1745), (1558, 1746), (1752, 1747), (1750, 1748), (1754, 1749), (1753, 1750)]

def movesP150Lit : List (Wire × Wire) :=
  (List.range 73).map bankPair150 ++ flagPairs150

theorem movesP150_eq : movesP150To20 = movesP150Lit := by
  have hg : wpP20 165 - 2 = 73 ∧ bTopP 165 = 1043 ∧ wpP20 165 = 75 ∧ lows150 = 12 ∧
      e0P20 165 = 1742 ∧ Shadow7.e0P 150 = 1747 := by decide
  unfold movesP150To20 movesP150Lit flagPairs150
  rw [hg.1]
  apply congrArg₂ List.append
  · refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    rw [hg.2.2.2.1, bankW150_lit (12 + i) (by omega) (by omega)]
    unfold bankW150Lit bankPair150
    refine Prod.ext ?_ (by rw [hg.2.1, hg.2.2.1]; unfold Wire; omega)
    by_cases h57 : i < 58
    · rw [if_pos (by omega), if_pos h57]; unfold Wire; omega
    · rw [if_neg (by omega), if_neg h57]; unfold Wire; omega
  · rw [hg.2.2.2.2.1, hg.2.2.2.2.2]

private theorem geom150_check :
    Companion.Geometry smallA150 smallM150 smallC150 1556 1558 ∧
    (1557 :: (1558 : Wire) :: PortalAnd.sites pendingPairs150).Nodup ∧
    (1556 :: (1558 : Wire) :: PortalAnd.sites clearFlagPairs150).Nodup ∧
    StoreGeometry 180 (Shadow7.e0P 150 + 5) low150 [] ∧
    (∀ p ∈ movesP150To20, p.1 ≠ p.2) ∧
    (∀ p ∈ pendingPairs150, (1559 ≤ (p.2 : Nat) ∧ (p.2 : Nat) ≤ 1597) ∨
      (1613 ≤ (p.2 : Nat) ∧ (p.2 : Nat) + 2 < Shadow7.e0P 150)) ∧
    (∀ p ∈ clearFlagPairs150, 1559 ≤ (p.2 : Nat) ∧ (p.2 : Nat) ≤ 1597) := by
  refine ⟨small150_geom, pending150_layout, by decide +kernel, low150_geom, ?_, ?_, by decide +kernel⟩
  · rw [movesP150_eq]; intro p hp; rw [movesP150Lit, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hk
      unfold bankPair150; split_ifs <;> (unfold Wire; omega)
    · simp only [flagPairs150, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro p hp
    simp only [pendingPairs150, List.mem_map, List.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    have hs := Shadow7.storeW_cases (s := 150) (by decide) (by decide) (k + 1)
    have hlt : k + 1 ≤ 73 := by
      have : Shadow7.liveW 150 = 84 ∧ lows150 = 12 := by decide
      omega
    have he : Shadow7.e0P 150 = 1747 := by decide
    rcases hs with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩
    · left; dsimp only; unfold Wire at *; omega
    · right; dsimp only; unfold Wire at *; omega
    · omega

theorem src150_bank_out (q : Wire)
    (hq : (q : Nat) < 971 ∨ (1043 < (q : Nat) ∧ (q : Nat) < 1598) ∨ 1612 < (q : Nat)) :
    LeaveRelocation.source ((List.range 73).map bankPair150) q = q := by
  apply LeaveRelocation.outside; intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hk
  unfold bankPair150; split_ifs <;> rcases hq with h | ⟨h1, h2⟩ | h <;> exact ⟨by unfold Wire at *; omega, by unfold Wire at *; omega⟩

theorem src150_flags_out (q : Wire) (hq : (q : Nat) < 1557) :
    LeaveRelocation.source flagPairs150 q = q := by
  apply LeaveRelocation.outside; intro p hp
  simp only [flagPairs150, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by unfold Wire at *; omega, by unfold Wire at *; omega⟩

private theorem src150_bank_at (i : Nat) (hi : i < 73) :
    LeaveRelocation.source ((List.range 73).map bankPair150) (971 + i) = bankW150Lit (12 + i) := by
  have hsplit : List.range 73 = List.range i ++ (i :: (List.range (73 - (i + 1))).map (i + 1 + ·)) := by
    have h1 : 73 = i + (1 + (73 - (i + 1))) := by omega
    conv_lhs => rw [h1, List.range_add, List.range_add]
    simp [List.range_one, Nat.add_assoc]
  rw [hsplit, List.map_append, List.map_cons, LeaveRelocation.append]
  have hafter : LeaveRelocation.source ((List.map (i + 1 + ·) (List.range (73 - (i + 1)))).map bankPair150) (971 + i) = 971 + i := by
    apply LeaveRelocation.outside; intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk; rw [List.mem_range] at hr
    unfold bankPair150; split_ifs <;> exact ⟨by unfold Wire; omega, by unfold Wire; omega⟩
  have hcons : LeaveRelocation.source (bankPair150 i :: (List.map (i + 1 + ·) (List.range (73 - (i + 1)))).map bankPair150) (971 + i) =
      bankW150Lit (12 + i) := by
    change LeaveRelocation.flip (bankPair150 i).1 (bankPair150 i).2
      (LeaveRelocation.source ((List.map (i + 1 + ·) (List.range (73 - (i + 1)))).map bankPair150) (971 + i)) = _
    rw [hafter]
    unfold LeaveRelocation.flip bankPair150 bankW150Lit
    dsimp only
    split_ifs <;> (unfold Wire at *; omega)
  rw [hcons]
  apply LeaveRelocation.outside; intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hk
  unfold bankPair150 bankW150Lit
  by_cases hi57 : i < 58 <;> by_cases hk57 : k < 58
  · rw [if_pos (by omega), if_pos hk57]; exact ⟨by unfold Wire; omega, by unfold Wire; omega⟩
  · omega
  · rw [if_neg (by omega), if_pos hk57]; exact ⟨by unfold Wire; omega, by unfold Wire; omega⟩
  · rw [if_neg (by omega), if_neg hk57]; exact ⟨by unfold Wire; omega, by unfold Wire; omega⟩

theorem reloc150_lit :
    LeaveRelocation.source movesP150Lit 1745 = 1557 ∧
    LeaveRelocation.source movesP150Lit 1746 = 1558 ∧
    LeaveRelocation.source movesP150Lit 1747 = 1752 ∧
    LeaveRelocation.source movesP150Lit 1748 = 1750 ∧
    LeaveRelocation.source movesP150Lit 1749 = 1754 ∧
    LeaveRelocation.source movesP150Lit 1750 = 1753 ∧
    (∀ i : Fin 15, LeaveRelocation.source movesP150Lit (166 + i.val) = 166 + i.val) ∧
    (∀ i : Fin 12, LeaveRelocation.source movesP150Lit (354 + i.val) = 354 + i.val ∧
      LeaveRelocation.source movesP150Lit (959 + i.val) = 959 + i.val) ∧
    (∀ i : Fin 73,
      LeaveRelocation.source movesP150Lit (971 + i.val) = bankW150Lit (12 + i.val) ∧
      LeaveRelocation.source movesP150Lit (367 + i.val) = 367 + i.val) := by
  have hfl : LeaveRelocation.source flagPairs150 1745 = 1557 ∧
      LeaveRelocation.source flagPairs150 1746 = 1558 ∧
      LeaveRelocation.source flagPairs150 1747 = 1752 ∧
      LeaveRelocation.source flagPairs150 1748 = 1750 ∧
      LeaveRelocation.source flagPairs150 1749 = 1754 ∧
      LeaveRelocation.source flagPairs150 1750 = 1753 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [movesP150Lit, LeaveRelocation.append, hfl.1, src150_bank_out _ (by decide)]
  · rw [movesP150Lit, LeaveRelocation.append, hfl.2.1, src150_bank_out _ (by decide)]
  · rw [movesP150Lit, LeaveRelocation.append, hfl.2.2.1, src150_bank_out _ (by decide)]
  · rw [movesP150Lit, LeaveRelocation.append, hfl.2.2.2.1, src150_bank_out _ (by decide)]
  · rw [movesP150Lit, LeaveRelocation.append, hfl.2.2.2.2.1, src150_bank_out _ (by decide)]
  · rw [movesP150Lit, LeaveRelocation.append, hfl.2.2.2.2.2, src150_bank_out _ (by decide)]
  · intro i; rw [movesP150Lit, LeaveRelocation.append, src150_flags_out _ (by have := i.isLt; unfold Wire; omega),
      src150_bank_out _ (Or.inl (by have := i.isLt; unfold Wire; omega))]
  · intro i; constructor
    · rw [movesP150Lit, LeaveRelocation.append, src150_flags_out _ (by have := i.isLt; unfold Wire; omega),
        src150_bank_out _ (Or.inl (by have := i.isLt; unfold Wire; omega))]
    · rw [movesP150Lit, LeaveRelocation.append, src150_flags_out _ (by have := i.isLt; unfold Wire; omega),
        src150_bank_out _ (Or.inl (by have := i.isLt; unfold Wire; omega))]
  · intro i; constructor
    · rw [movesP150Lit, LeaveRelocation.append, src150_flags_out _ (by have := i.isLt; unfold Wire; omega)]
      exact src150_bank_at i.val i.isLt
    · rw [movesP150Lit, LeaveRelocation.append, src150_flags_out _ (by have := i.isLt; unfold Wire; omega),
        src150_bank_out _ (Or.inl (by have := i.isLt; unfold Wire; omega))]

private theorem reloc150_check :
    LeaveRelocation.source movesP150To20 (e0P20 165 + 3) = 1557 ∧
    LeaveRelocation.source movesP150To20 (e0P20 165 + 4) = 1558 ∧
    LeaveRelocation.source movesP150To20 (e0P20 165 + 5) = Shadow7.e0P 150 + 5 ∧
    LeaveRelocation.source movesP150To20 (e0P20 165 + 6) = Shadow7.e0P 150 + 3 ∧
    LeaveRelocation.source movesP150To20 (e0P20 165 + 7) = Shadow7.e0P 150 + 7 ∧
    LeaveRelocation.source movesP150To20 (e0P20 165 + 8) = Shadow7.e0P 150 + 6 ∧
    (∀ i : Fin 15, LeaveRelocation.source movesP150To20 (166 + i.val) = 166 + i.val) ∧
    (∀ i : Fin 12, LeaveRelocation.source movesP150To20 (Shadow7.a0P 150 - 1 + i.val) = Shadow7.a0P 150 - 1 + i.val ∧
      LeaveRelocation.source movesP150To20 (Shadow7.b0P 150 - 1 + i.val) = Shadow7.b0P 150 - 1 + i.val) ∧
    (∀ i : Fin (wpP20 165 - 2),
      LeaveRelocation.source movesP150To20 (Shadow7.b0P 150 + lows150 - 1 + i.val) = Shadow7.bankW 150 (lows150 + i.val) ∧
      LeaveRelocation.source movesP150To20 (Shadow7.a0P 150 + lows150 + i.val) = Shadow7.a0P 150 + lows150 + i.val) := by
  rw [movesP150_eq]
  have hr := reloc150_lit
  refine ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, fun i => ?_⟩
  have h1 := hr.2.2.2.2.2.2.2.2 ⟨i.val, i.isLt⟩
  have hwp : wpP20 165 - 2 = 73 := by decide
  refine ⟨?_, h1.2⟩
  rw [show lows150 = 12 from rfl, bankW150_lit (12 + i.val) (by omega) (by have := i.isLt; omega)]
  exact h1.1

private theorem nextFlag150_orientation (a : SkywalkNat.State) (sign : Nat) (bit : sign ≤ 1)
    (small : Shadow7.SmallIfFar 163 20 a) (hfar : Shadow.far 163 20 a) :
    (2 ^ 173 ≤ a.u - sign) ↔ (2 ^ 163 ≤ a.u) := by
  have hsm := small hfar
  have lower := (Nat.le_div_iff_mul_le (by unfold Shadow.limb; positivity : 0 < Shadow.limb 163 20)).mp hfar
  unfold Shadow.limb at lower
  have p2 : (2 : Nat) ^ (163 + 20) = 2 ^ 20 * 2 ^ 163 := by rw [← Nat.pow_add, Nat.add_comm]
  have p1 : (2 : Nat) ^ 173 = 1024 * 2 ^ 163 := by
    rw [show (173 : Nat) = 163 + 10 by decide, Nat.pow_add, Nat.mul_comm]
  rw [p2] at lower; rw [p1]
  generalize (2 : Nat) ^ 163 = P at *
  constructor <;> intro h <;> omega

private theorem nextFlag150_boundShort (a : SkywalkNat.State) (sign : Nat)
    (near : ¬ far 163 20 a) :
    a.u - sign < (2 * 2 ^ 173) * 2 ^ (smallM150.length - 1) := by
  have limit := (Nat.div_lt_iff_lt_mul (by unfold limb; positivity : 0 < limb 163 20)).mp
    (Nat.lt_of_not_ge near)
  have size : (2 * 2 ^ 173) * 2 ^ (smallM150.length - 1) = 2 * limb 163 20 := by
    rw [show smallM150.length - 1 = 10 from rfl, Nat.mul_assoc, ← Nat.pow_add]
    rfl
  rw [size]
  omega

private theorem bankW150_ne_swap :
    ∀ k : Fin (Shadow7.wpP 150 + 15), 12 ≤ k.val →
      (Shadow7.bankW 150 k.val : Wire) ≠ 364 ∧ (Shadow7.bankW 150 k.val : Wire) ≠ 984 ∧
      (Shadow7.bankW 150 k.val : Wire) ≠ 365 ∧ (Shadow7.bankW 150 k.val : Wire) ≠ 985 := by
  intro k h12
  rw [bankW150_lit k.val (by omega) k.isLt]
  unfold bankW150Lit; split_ifs <;> refine ⟨by unfold Wire; omega, by unfold Wire; omega, by unfold Wire; omega, by unfold Wire; omega⟩

private theorem bankW150_ne_store :
    ∀ r : Fin 72, (Shadow7.bankW 150 (12 + r.val) : Wire) ≠ 1557 ∧
      (Shadow7.bankW 150 (12 + r.val) : Wire) ≠ 1558 ∧
      Shadow7.bankW 150 (12 + r.val) ∉ smallM150 := by
  intro r
  rw [bankW150_lit (12 + r.val) (by omega) (by omega)]
  unfold bankW150Lit
  have hnotM (q : Wire) (hq : 986 ≤ (q : Nat)) : q ∉ smallM150 := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    have hb : Shadow7.b0P 150 = 960 ∧ lows150 = 12 := by decide
    unfold Wire at *; omega
  split_ifs <;> refine ⟨by unfold Wire; omega, by unfold Wire; omega, hnotM _ (by unfold Wire; omega)⟩

private theorem events150_away :
    ∀ w ∈ [Shadow7.e0P 150 + 3, Shadow7.e0P 150 + 4, Shadow7.e0P 150 + 6, Shadow7.e0P 150 + 7] ++
      (LeaveJ7.Close.events MixedWindow.j7).flatMap (fun p => [p.1, p.2]),
      w ≠ 364 ∧ w ≠ 984 ∧ w ≠ 365 ∧ w ≠ 985 ∧ w ∉ RailPair.sites low150 ∧
      w ∉ LeaveJ7.history MixedWindow.j7 ∧ w ∉ smallM150 ∧ w ≠ 1557 ∧ w ≠ 1558 ∧
      w ∉ RailPair.sites (LeaveJ7.Close.low MixedWindow.j7) ∧ w ∉ LeaveJ7.smallM MixedWindow.j7 := by
  decide +kernel

private theorem bankW150_away :
    ∀ k : Fin (wpP20 165 - 2),
      (Shadow7.bankW 150 (lows150 + k.val) : Wire) ≠ Shadow7.e0P 150 + 4 ∧
      Shadow7.bankW 150 (lows150 + k.val) ∉ RailPair.sites low150 ∧
      Shadow7.bankW 150 (lows150 + k.val) ∉ LeaveJ7.history MixedWindow.j7 ∧
      (Shadow7.bankW 150 (lows150 + k.val) : Wire) ≠ 1556 ∧
      (Shadow7.bankW 150 (lows150 + k.val) : Wire) ≠ 1557 ∧
      (Shadow7.bankW 150 (lows150 + k.val) : Wire) ≠ 1558 ∧
      Shadow7.bankW 150 (lows150 + k.val) ∉ smallM150 := by
  intro k
  have hg : wpP20 165 - 2 = 73 ∧ lows150 = 12 ∧ Shadow7.e0P 150 = 1747 ∧
      Shadow7.a0P 150 = 355 ∧ Shadow7.b0P 150 = 960 := by decide
  rw [hg.2.1, bankW150_lit (12 + k.val) (by omega) (by omega)]
  have hr : 986 ≤ (bankW150Lit (12 + k.val) : Nat) ∧ (bankW150Lit (12 + k.val) : Nat) ≤ 1043 ∨
      (1598 ≤ (bankW150Lit (12 + k.val) : Nat) ∧ (bankW150Lit (12 + k.val) : Nat) ≤ 1612) := by
    unfold bankW150Lit; split_ifs <;> [left; right] <;> (unfold Wire; omega)
  have hnotL : bankW150Lit (12 + k.val) ∉ RailPair.sites low150 := by
    intro hm; obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp; rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hr with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases hq with hq | hq <;> (unfold Wire at *; omega)
  have hnotH : bankW150Lit (12 + k.val) ∉ LeaveJ7.history MixedWindow.j7 := by
    intro hm; unfold LeaveJ7.history at hm; rw [show start MixedWindow.j7 = 150 from rfl] at hm
    obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    rcases hr with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire at *; omega)
  have hnotM : bankW150Lit (12 + k.val) ∉ smallM150 := by
    intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
    rcases hr with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire at *; omega)
  refine ⟨by rcases hr with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire at *; omega), hnotL, hnotH,
    by rcases hr with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire at *; omega),
    by rcases hr with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire at *; omega),
    by rcases hr with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire at *; omega), hnotM⟩

theorem not_mem_smallM150 (q : Wire) (hq : (q : Nat) < 960 ∨ 972 ≤ (q : Nat)) :
    q ∉ smallM150 := by
  intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
  have hg : Shadow7.b0P 150 = 960 ∧ lows150 = 12 := by decide
  unfold Wire at *; omega

theorem swap2St_other (q : Nat) (h1 : q ≠ 364) (h2 : q ≠ 984)
    (h3 : q ≠ 365) (h4 : q ≠ 985) (u : State) :
    (swap2St u).basis q = u.basis q :=
  swap2_other h1 h2 h3 h4 u.basis

private theorem releaseMaskP150_eq :
    releaseMaskP150 = [.measureX 1558 [] [.CZ (Shadow7.b0P 150 - 1) 1557],
      .CX (Shadow7.a0P 150 - 1) 1557, .X 1557] := rfl

private theorem borrowG4_150_phase (t : State) : (run borrowG4_150 [] t).phase = t.phase := by
  simp [borrowG4_150, run]

private theorem borrowG4_150_keep (t : State) (q : Wire) (n7 : q ≠ 1557) (n8 : q ≠ 1558) :
    (run borrowG4_150 [] t).basis q = t.basis q := by
  simp [borrowG4_150, run, writeBit, Function.update_apply, n7, n8]

private theorem borrowG4_150_57 (t : State) (h57 : t.basis 1557 = false) :
    (run borrowG4_150 [] t).basis 1557 = !t.basis (Shadow7.a0P 150 - 1) := by
  have na : (Shadow7.a0P 150 - 1 : Wire) ≠ 1557 := by decide
  simp [borrowG4_150, run, writeBit, Function.update_apply, na, na.symm, h57]

private theorem borrowG4_150_58 (t : State) (h57 : t.basis 1557 = false) (h58 : t.basis 1558 = false) :
    (run borrowG4_150 [] t).basis 1558 = (t.basis (Shadow7.b0P 150 - 1) && !t.basis (Shadow7.a0P 150 - 1)) := by
  have na : (Shadow7.a0P 150 - 1 : Wire) ≠ 1557 ∧ (Shadow7.a0P 150 - 1 : Wire) ≠ 1558 := by decide
  have nb : (Shadow7.b0P 150 - 1 : Wire) ≠ 1557 ∧ (Shadow7.b0P 150 - 1 : Wire) ≠ 1558 := by decide
  simp [borrowG4_150, run, writeBit, Function.update_apply, na.1, na.2, nb.1, nb.2, na.1.symm, na.2.symm,
    nb.1.symm, nb.2.symm, h57, h58]

private theorem F150_eq (z : SkywalkNat.State) :
    LeaveJ7.TrueMiddle.F MixedWindow.j7 z = ((step^[15] z).u + (step^[15] z).v) / 2 ^ 173 := by
  unfold LeaveJ7.TrueMiddle.F HighBankSum.total
  rw [show Shadow7.sbP (start MixedWindow.j7) = 173 by decide]

private theorem scan150_sites_lt :
    ∀ q ∈ RailPair.sites (LeaveJ7.scanPairs MixedWindow.j7), q < 976 := by
  decide +kernel

section Forward150

attribute [local irreducible] run SkywalkNat.step Shadow.far CRTBarrel.barrel GateMirror.forward
  head150Prog full150Prog beforeStore150Prog storeMapped150Prog leave150To20
  Shadow7.leaveHeadOps Shadow7.fix0P leaveFix1
  leaveStoreMapped150 leaveLowClose150 leaveClose150To20 afterHead150 lowRest150
  Companion.restore releaseMaskP150 PortalAnd.latch RailPair.store

private theorem stock_full_eq_head150 (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0) (q : Wire)
    (hq : q ∉ LeaveJ7.smallM MixedWindow.j7) (h7 : q ≠ 1557) (h8 : q ≠ 1558) :
    (run (LeaveJ7.fullProgram MixedWindow.j7) [] s).basis q =
      (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s).basis q := by
  let u := LeaveJ7.Admission.flags z g0 s0
  have hi : MixedWindow.j7.val ≤ 24 := by decide
  have par := LeaveJ7.RecordedParity.result MixedWindow.j7 (by decide) hi s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start MixedWindow.j7)) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P (start MixedWindow.j7) + 3))
        (s.basis (Shadow7.e0P (start MixedWindow.j7) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := LeaveJ7.RecordedEvents.result MixedWindow.j7 (by decide) hi s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have gflag := LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) hi s z g0 s0 ⟨h.farSmall, h.endSmall⟩
    h.odd h.record h.far h.side
  have front := LeaveJ7.entry_core MixedWindow.j7 (by decide) hi s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp
    (Shadow.far (Shadow7.sbP (start MixedWindow.j7)) 15 z ∧
      LeaveShadowRails.farKey (Shadow7.sbP (start MixedWindow.j7)) z = 0)
    (LeaveJ7.glueBound MixedWindow.j7 z u.2 ⟨h.farSmall, h.endSmall⟩) gflag
  have used := LeaveJ7.full_routed MixedWindow.j7 (by decide) hi s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 gflag
  have bm1 := LeaveJ7.full_bm1 MixedWindow.j7 (by decide) hi s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 gflag
  dsimp only at front used
  rw [List.drop_nil] at used bm1
  have restored := LeaveJ7.routedRestore_result MixedWindow.j7 (by decide) hi z u.2
    (run (GateMirror.forward (LeaveJ7.entryOps (start MixedWindow.j7))) [] s) [] [] ⟨h.farSmall, h.endSmall⟩
    front.2.1 ⟨front.2.2.2.1, front.2.2.2.2.1⟩ used.2.1 bm1 used.2.2.2.1
  dsimp only at restored
  have hhead : run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s =
      run (GateMirror.forward (LeaveJ7.bodyOps MixedWindow.j7)) []
        (run (GateMirror.forward (LeaveJ7.entryOps 150)) [] s) := by
    rw [show Shadow7.leaveHeadOps 150 = LeaveJ7.entryOps 150 ++ LeaveJ7.bodyOps MixedWindow.j7 from
        (LeaveJ7.head_eq MixedWindow.j7).symm, forward_app, run_append, run_take, List.drop_nil]
  have r := restored.2.1 q h7 h8 hq
  rw [hhead]
  simp only [LeaveJ7.fullProgram, forward_app, List.append_assoc, run_append, run_take, List.drop_nil,
    List.take_nil] at r ⊢
  rw [show start MixedWindow.j7 = 150 from rfl] at r
  exact r

private theorem beforeStore150_result (s : State) (m : List Bool) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) :
    let a := step^[15] z
    let u := LeaveJ7.Admission.flags z g0 s0
    let sign := PortalValues.negative u.2 a.u
    let mag := a.u - sign.toNat
    let next := decide (Shadow.far 163 20 a)
    let bs := run beforeStore150Prog m s
    bs.phase = s.phase ∧
    bs.basis 1556 = false ∧
    bs.basis 1557 = next ∧
    bs.basis 1558 = (next && decide (2 ^ 163 ≤ a.u)) ∧
    bs.basis (Shadow7.e0P 150 + 5) = sign ∧
    (∀ q ∈ LeaveJ7.history MixedWindow.j7, bs.basis q = !s.basis q) ∧
    (∀ i : Fin 12,
      bs.basis (Shadow7.a0P 150 - 1 + i.val) = (a.u + a.v).testBit (173 + i.val) ∧
      bs.basis (Shadow7.b0P 150 - 1 + i.val) = mag.testBit (173 + i.val)) ∧
    (∀ i : Fin (wpP20 165 - 2),
      (run head150Prog m s).basis (Shadow7.bankW 150 (lows150 + i.val)) =
        (LeaveJ7.TrueMiddle.F MixedWindow.j7 z).testBit (lows150 + i.val)) ∧
    (∀ q : Nat, q ≠ 1556 → q ≠ 1557 → q ≠ 1558 → q ∉ smallM150 →
      bs.basis q = (run head150Prog m s).basis q) ∧
    (∀ q : Nat, q ≠ 364 → q ≠ 984 → q ≠ 365 → q ≠ 985 →
      (run head150Prog m s).basis q = (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s).basis q) := by
  let a := step^[15] z
  let u := LeaveJ7.Admission.flags z g0 s0
  let sign := PortalValues.negative u.2 a.u
  let mag := a.u - sign.toNat
  have hi : MixedWindow.j7.val ≤ 24 := by decide
  have par := LeaveJ7.RecordedParity.result MixedWindow.j7 (by decide) hi s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP (start MixedWindow.j7)) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P (start MixedWindow.j7) + 3))
        (s.basis (Shadow7.e0P (start MixedWindow.j7) + 4)) z.u := by
    rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _
  have ev := LeaveJ7.RecordedEvents.result MixedWindow.j7 (by decide) hi s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have gflag := LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) hi s z g0 s0 ⟨h.farSmall, h.endSmall⟩
    h.odd h.record h.far h.side
  have hfront := LeaveJ7.entry_core MixedWindow.j7 (by decide) hi s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp
    (Shadow.far (Shadow7.sbP (start MixedWindow.j7)) 15 z ∧
      LeaveShadowRails.farKey (Shadow7.sbP (start MixedWindow.j7)) z = 0)
    (LeaveJ7.glueBound MixedWindow.j7 z u.2 ⟨h.farSmall, h.endSmall⟩) gflag
  have hrouted := LeaveJ7.full_routed MixedWindow.j7 (by decide) hi s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 gflag
  have hbm1 := LeaveJ7.full_bm1 MixedWindow.j7 (by decide) hi s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 gflag
  have hpar0 := LeaveJ7.entry_parity MixedWindow.j7 (by decide) hi s []
  have hck := LeaveJ7.CoreCheckpoint.result MixedWindow.j7 (by decide) hi s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2 gflag
  have hck_prog : LeaveJ7.CoreCheckpoint.program MixedWindow.j7 = GateMirror.forward (Shadow7.leaveHeadOps 150) := rfl
  dsimp only at hck
  rw [hck_prog] at hck
  dsimp only at hfront hrouted
  rw [List.drop_nil] at hrouted hbm1
  rw [show start MixedWindow.j7 = 150 from rfl] at hfront hrouted hbm1 hpar0
  have hsb : Shadow7.sbP 150 = 173 := by decide
  have ha0 : Shadow7.a0P 150 = 355 := by decide
  have hb0 : Shadow7.b0P 150 = 960 := by decide
  have hwp : Shadow7.wpP 150 = 70 := by decide
  have he0 : Shadow7.e0P 150 = 1747 := by decide
  have hlows : Shadow7.lowsP 150 = 10 := by decide
  have hwp20 : wpP20 165 = 75 := by decide
  have hlow12 : lows150 = 12 := by decide
  rw [hsb] at hfront hrouted hbm1
  -- the stock head state and the transition head state
  let E := run (GateMirror.forward (LeaveJ7.entryOps 150)) [] s
  let U := run (GateMirror.forward (LeaveJ7.bodyOps MixedWindow.j7)) [] E
  have hst_eq : run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s = U := by
    rw [show Shadow7.leaveHeadOps 150 = LeaveJ7.entryOps 150 ++ LeaveJ7.bodyOps MixedWindow.j7 from
        (LeaveJ7.head_eq MixedWindow.j7).symm, forward_app, run_append, run_take, List.drop_nil]
  let hst := run head150Prog m s
  have hhst_eq : hst = swap2St U := by
    show run head150Prog m s = _; unfold head150Prog; rw [← hst_eq]; exact (leaveMove150_head_eq s z g0 s0 h).2 m
  have hst_ph : hst.phase = s.phase := by rw [hhst_eq]; exact hrouted.1.trans hfront.1
  have hst_basis (q : Nat) (h1 : q ≠ 364) (h2 : q ≠ 984) (h3 : q ≠ 365) (h4 : q ≠ 985) :
      hst.basis q = U.basis q := by
    rw [hhst_eq]; exact swap2St_other q h1 h2 h3 h4 _
  have keepE (q : Nat) (hm : ¬ LeaveJ7.midT MixedWindow.j7 q) : U.basis q = E.basis q :=
    LeaveReadoutFrame.preserved _ _ _ _ (fun hit => hm (LeaveJ7.body_dest MixedWindow.j7 (by decide) hi q hit))
  have hF_low : ∀ (i : Nat), i < 12 →
      hst.basis (Shadow7.a0P 150 - 1 + i) = (LeaveJ7.TrueMiddle.F MixedWindow.j7 z).testBit i := by
    intro i hi'
    by_cases h10 : i < 10
    · rw [hst_basis (Shadow7.a0P 150 - 1 + i) (by rw [ha0]; omega) (by rw [ha0]; omega)
          (by rw [ha0]; omega) (by rw [ha0]; omega)]
      have hr := hrouted.2.1 i (by rw [hwp]; omega)
      unfold LeaveJ7.live at hr
      rw [show start MixedWindow.j7 = 150 from rfl, if_pos (by rw [hlows]; omega)] at hr
      exact hr
    · have hi'' : i = 10 ∨ i = 11 := by omega
      rcases hi'' with rfl | rfl
      · have hr := hrouted.2.1 10 (by rw [hwp]; decide)
        unfold LeaveJ7.live at hr
        rw [show start MixedWindow.j7 = 150 from rfl, if_neg (by rw [hlows]; decide)] at hr
        have hb10 : Shadow7.bankW 150 10 = 984 := by decide
        have ha10 : (Shadow7.a0P 150 - 1 + 10 : Wire) = 364 := by decide
        rw [hb10] at hr
        rw [hhst_eq, ha10, show (swap2St U).basis 364 = U.basis 984 by simp [swap2St, swap2, swap1]]
        exact hr
      · have hr := hrouted.2.1 11 (by rw [hwp]; decide)
        unfold LeaveJ7.live at hr
        rw [show start MixedWindow.j7 = 150 from rfl, if_neg (by rw [hlows]; decide)] at hr
        have hb11 : Shadow7.bankW 150 11 = 985 := by decide
        have ha11 : (Shadow7.a0P 150 - 1 + 11 : Wire) = 365 := by decide
        rw [hb11] at hr
        rw [hhst_eq, ha11, show (swap2St U).basis 365 = U.basis 985 by simp [swap2St, swap2, swap1]]
        exact hr
  have hF_hi : ∀ i, 12 ≤ i → i < Shadow7.wpP 150 + 15 →
      hst.basis (Shadow7.bankW 150 i) = (LeaveJ7.TrueMiddle.F MixedWindow.j7 z).testBit i := by
    intro i h12 hlt
    have hne := bankW150_ne_swap ⟨i, hlt⟩ h12
    rw [hst_basis _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2]
    have hr := hrouted.2.1 i hlt
    unfold LeaveJ7.live at hr
    rw [show start MixedWindow.j7 = 150 from rfl, if_neg (by rw [hlows]; omega)] at hr
    exact hr
  have h56E : E.basis 1556 = decide (2 ^ 173 ≤ mag) := by
    have ch := LeaveRestoreTruth.truth_shadow7 173 z h.farSmall u.2
    dsimp only at ch
    show E.basis 1556 = decide (2 ^ 173 ≤ (step^[15] z).u - (PortalValues.negative u.2 (step^[15] z).u).toNat)
    rw [hfront.2.2.2.1, ch.1, ← ch.2.1]; simp
  have h56 : hst.basis 1556 = decide (2 ^ 173 ≤ mag) := by
    rw [hst_basis 1556 (by decide) (by decide) (by decide) (by decide),
      keepE 1556 (by unfold LeaveJ7.midT LeaveJ7.workT; decide)]
    exact h56E
  have h57 : hst.basis 1557 = false := by
    rw [hst_basis 1557 (by decide) (by decide) (by decide) (by decide),
      keepE 1557 (by unfold LeaveJ7.midT LeaveJ7.workT; decide)]
    exact hfront.2.2.2.2.1.1
  have h58 : hst.basis 1558 = false := by
    rw [hst_basis 1558 (by decide) (by decide) (by decide) (by decide),
      keepE 1558 (by unfold LeaveJ7.midT LeaveJ7.workT; decide)]
    exact hfront.2.2.2.2.1.2
  have hbB : hst.basis (Shadow7.b0P 150 - 1) = (mag / 2 ^ 173).testBit 0 := by
    rw [hst_basis _ (by rw [hb0]; decide) (by rw [hb0]; decide) (by rw [hb0]; decide) (by rw [hb0]; decide)]
    exact hbm1
  have hbA : hst.basis (Shadow7.a0P 150 - 1) = ((a.u + a.v) / 2 ^ 173).testBit 0 := by
    have e0 := hF_low 0 (by decide); rw [Nat.add_zero] at e0; rw [e0, F150_eq]
  have hret : ∀ i : Fin 39, hst.basis (1559 + i.val) = false := by
    intro i
    rw [hst_basis _ (by omega) (by omega) (by omega) (by omega)]
    exact hrouted.2.2.2.1 i
  have hM0 : regValue smallM150 hst.basis = 0 := by
    rw [regValue_zero]; intro q hq
    obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hq; rw [List.mem_range, hlow12] at hi'
    rw [hst_basis _ (by rw [hb0]; omega) (by rw [hb0]; omega) (by rw [hb0]; omega) (by rw [hb0]; omega),
      keepE _ (by unfold LeaveJ7.midT LeaveJ7.workT; rw [show start MixedWindow.j7 = 150 from rfl, ha0, hb0, he0]; omega)]
    exact (regValue_zero _ _).mp hfront.2.1 _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)
  have hhst_def : run head150Prog m s = hst := rfl
  clear_value hst
  -- borrow G4 and the eleven-bit restore
  let m1 := m.drop (measurementCount head150Prog)
  have hmcG : measurementCount borrowG4_150 = 0 := rfl
  let g := run borrowG4_150 [] hst
  have hg_run : run borrowG4_150 m1 hst = g := by
    rw [← run_take, hmcG, List.take_zero]
  have na : (Shadow7.a0P 150 - 1 : Wire) ≠ 1557 ∧ (Shadow7.a0P 150 - 1 : Wire) ≠ 1558 := by decide
  have nb : (Shadow7.b0P 150 - 1 : Wire) ≠ 1557 ∧ (Shadow7.b0P 150 - 1 : Wire) ≠ 1558 := by decide
  have gph : g.phase = hst.phase := borrowG4_150_phase hst
  have gq (q : Nat) (n7 : q ≠ 1557) (n8 : q ≠ 1558) : g.basis q = hst.basis q := borrowG4_150_keep hst q n7 n8
  have g57 : g.basis 1557 = !hst.basis (Shadow7.a0P 150 - 1) := borrowG4_150_57 hst h57
  have g58 : g.basis 1558 = (hst.basis (Shadow7.b0P 150 - 1) && !hst.basis (Shadow7.a0P 150 - 1)) :=
    borrowG4_150_58 hst h57 h58
  have gClean : ∀ q ∈ smallC150, g.basis q = false := by
    intro q hq; obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hq; rw [List.mem_range, hlow12] at hi'
    rw [gq (1559 + i) (by omega) (by omega)]; exact hret ⟨i, by omega⟩
  have gM0 : regValue smallM150 g.basis = 0 := by
    rw [← hM0]; apply (regValue_eq_iff _ _ _).mpr; intro q hq
    obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hq; rw [List.mem_range, hlow12] at hi'
    exact gq _ (by rw [hb0]; omega) (by rw [hb0]; omega)
  let m2 := m1.drop (measurementCount borrowG4_150)
  have hrest := Companion.write smallA150 smallM150 smallC150 1556 1558 geom150_check.1 g m2 gClean gM0
  have hfull_eq : run full150Prog m s = run (Companion.restore smallA150 smallM150 smallC150 1556 1558) m2 g := by
    rw [show full150Prog = head150Prog ++ (borrowG4_150 ++ Companion.restore smallA150 smallM150 smallC150 1556 1558)
      by unfold full150Prog; rfl, run_append, run_take, run_append, run_take, hhst_def]
    show run (Companion.restore smallA150 smallM150 smallC150 1556 1558) m2 (run borrowG4_150 m1 hst) = _
    rw [hg_run]
  have hmag_smallM : regValue smallM150 (run full150Prog m s).basis = (mag / 2 ^ 174) % 2 ^ 11 := by
    have gLatch : g.basis 1556 = decide (2 ^ 173 ≤ mag) := by rw [gq 1556 (by decide) (by decide)]; exact h56
    have gBorrow : (g.basis 1558).toNat = LeaveCompanion.upperBorrow (2 ^ 173) a.u a.v sign.toNat := by
      rw [g58, hbB, hbA, LeaveShadowRails.borrow_bits _ _ _ _ (Nat.two_pow_pos _), Nat.testBit_zero, Nat.testBit_zero]
      show (decide ((((step^[15] z).u - (PortalValues.negative u.2 (step^[15] z).u).toNat) / 2 ^ 173) % 2 = 1) &&
          !decide ((((step^[15] z).u + (step^[15] z).v) / 2 ^ 173) % 2 = 1)).toNat =
        if (((step^[15] z).u - (PortalValues.negative u.2 (step^[15] z).u).toNat) / 2 ^ 173) % 2 = 1 ∧
          (((step^[15] z).u + (step^[15] z).v) / 2 ^ 173) % 2 = 0 then 1 else 0
      generalize (((step^[15] z).u - (PortalValues.negative u.2 (step^[15] z).u).toNat) / 2 ^ 173) = X
      generalize (((step^[15] z).u + (step^[15] z).v) / 2 ^ 173) = S
      rcases Nat.mod_two_eq_zero_or_one X with p1 | p1 <;> rcases Nat.mod_two_eq_zero_or_one S with p2 | p2 <;>
        simp [p1, p2]
    have gReg : regValue smallA150 g.basis = ((a.u + a.v) / 2 ^ 174) % 2 ^ 11 := by
      have hv := EnterProof.value_of_bits smallA150 g.basis (LeaveJ7.TrueMiddle.F MixedWindow.j7 z / 2) (by
        intro i hi'
        have hlen : smallA150.length = 11 := rfl
        rw [hlen] at hi'
        have hg' : smallA150.getD i 0 = Shadow7.a0P 150 - 1 + (i + 1) := by
          simp only [smallA150, lows150, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range (show i < 12 - 1 by omega), Option.map_some, Option.getD_some]
          show (Shadow7.a0P 150 + i : Nat) = Shadow7.a0P 150 - 1 + (i + 1)
          rw [ha0]; omega
        rw [hg', gq (Shadow7.a0P 150 - 1 + (i + 1)) (by rw [ha0]; omega) (by rw [ha0]; omega),
          hF_low (i + 1) (by omega), Nat.testBit_div_two])
      have hlen : smallA150.length = 11 := rfl
      rw [hlen] at hv
      rw [hv, F150_eq, Nat.div_div_eq_div_mul, ← pow_succ]
    rw [hfull_eq, hrest.2.2, show smallM150.length = 11 from rfl, gReg, gBorrow]
    simp only [copyValue, gLatch, decide_eq_true_eq]
    have hrt := LeaveRestoreTruth.restored_shadow7 173 11 z h.endSmall u.2
    dsimp only at hrt
    exact hrt
  have hfull_keep (q : Nat) (n7 : q ≠ 1557) (n8 : q ≠ 1558) (hM : q ∉ smallM150) :
      (run full150Prog m s).basis q = hst.basis q := by
    rw [hfull_eq, hrest.2.1 q hM, gq q n7 n8]
  have hnotA : (Shadow7.a0P 150 - 1 : Wire) ∉ smallM150 := by decide
  have hnotB : (Shadow7.b0P 150 - 1 : Wire) ∉ smallM150 := by decide
  have hfull_1557 : (run full150Prog m s).basis 1557 = !(run full150Prog m s).basis (Shadow7.a0P 150 - 1) := by
    rw [hfull_eq, hrest.2.1 _ (by decide), hrest.2.1 _ hnotA, g57, gq _ na.1 na.2]
  have hfull_1558 : (run full150Prog m s).basis 1558 =
      ((run full150Prog m s).basis (Shadow7.b0P 150 - 1) && (run full150Prog m s).basis 1557) := by
    rw [hfull_1557, hfull_eq, hrest.2.1 _ (by decide), hrest.2.1 _ hnotB, hrest.2.1 _ hnotA, g58,
      gq _ nb.1 nb.2, gq _ na.1 na.2]
  have hfull_ph : (run full150Prog m s).phase = s.phase := by
    rw [hfull_eq, hrest.1, gph, hst_ph]
  -- release the mask
  let nRel := m.drop (measurementCount full150Prog)
  let uRel := run releaseMaskP150 nRel (run full150Prog m s)
  have huRel : uRel = ⟨(run full150Prog m s).phase,
      writeBit (writeBit (run full150Prog m s).basis 1557 false) 1558 false⟩ := by
    dsimp only [uRel]; rw [releaseMaskP150_eq]
    exact LeaveJ7.release_ok MixedWindow.j7 (by decide) hi (run full150Prog m s) nRel hfull_1557 hfull_1558
  have hrel_keep (q : Nat) (h7 : q ≠ 1557) (h8 : q ≠ 1558) : uRel.basis q = (run full150Prog m s).basis q := by
    rw [huRel]; simp [writeBit, h7, h8]
  let nSM := nRel.drop (measurementCount releaseMaskP150)
  have hclean_pen : ∀ p ∈ pendingPairs150, uRel.basis p.2 = false := by
    clear hmag_smallM hrest
    rintro ⟨pa, q⟩ hp
    have hr := geom150_check.2.2.2.2.2.1 (pa, q) hp
    dsimp only at hr ⊢
    unfold Wire at *
    have hq_r : (1559 ≤ q ∧ q ≤ 1597) ∨ (1613 ≤ q ∧ q + 2 < 1747) := by
      rcases hr with ⟨lo, hi'⟩ | ⟨lo, hi'⟩
      · exact Or.inl ⟨lo, hi'⟩
      · rw [he0] at hi'; exact Or.inr ⟨lo, hi'⟩
    have hq7 : q ≠ 1557 ∧ q ≠ 1558 ∧ 972 ≤ q := by rcases hq_r with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hnotM : q ∉ smallM150 := not_mem_smallM150 q (Or.inr hq7.2.2)
    rw [hrel_keep q hq7.1 hq7.2.1, hfull_keep q hq7.1 hq7.2.1 hnotM]
    rcases hq_r with ⟨lo, hi'⟩ | ⟨lo, hi'⟩
    · rw [show q = 1559 + (q - 1559) by omega]
      exact hret ⟨q - 1559, by omega⟩
    · have e1 : q ∉ (1556 : Wire) :: (1557 : Wire) :: (1558 : Wire) :: LeaveJ7.fullM MixedWindow.j7 := by
        simp only [List.mem_cons, not_or]
        refine ⟨by omega, by omega, by omega, ?_⟩
        intro hm; obtain ⟨i, hi2, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi2
        rw [show start MixedWindow.j7 = 150 from rfl, hb0] at e; omega
      have e2 : q < 150 + 16 ∨ 150 + 30 < q := Or.inr (by omega)
      have e3 : q ≠ Shadow7.e0P 150 + 5 := by rw [he0]; omega
      have hq976 : ¬ (q < 976) := by omega
      have e4 : q ∉ RailPair.sites (LeaveJ7.scanPairs MixedWindow.j7) := fun hm => hq976 (scan150_sites_lt q hm)
      have n1 : q ≠ 364 ∧ q ≠ 984 ∧ q ≠ 365 ∧ q ≠ 985 ∧ 1556 ≤ q := by omega
      have hraw : q ∈ LeaveJ7.CoreCheckpoint.rawSites MixedWindow.j7 := by
        simp only [LeaveJ7.CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1]
        left; left; exact ⟨lo, by rw [show start MixedWindow.j7 = 150 from rfl, he0]; omega⟩
      rw [hst_basis q n1.1 n1.2.1 n1.2.2.1 n1.2.2.2.1, ← hst_eq, hck.2.2.1 q hraw]
      exact LeaveJ7.native_carryJ_lt MixedWindow.j7 (by decide) hi _ s h.ready q n1.2.2.2.2
        (by rw [show start MixedWindow.j7 = 150 from rfl, he0]; exact hi')
  have hclean_clr : ∀ p ∈ clearFlagPairs150, uRel.basis p.2 = false := by
    clear hmag_smallM hrest
    intro p hp
    have hr := geom150_check.2.2.2.2.2.2 p hp
    let q : Nat := p.2
    have hq_r : 1559 ≤ q ∧ q ≤ 1597 := hr
    have hnotM : p.2 ∉ smallM150 := not_mem_smallM150 p.2 (Or.inr (by change 972 ≤ q; omega))
    change uRel.basis q = false
    rw [hrel_keep q (by omega) (by omega), hfull_keep q (by omega) (by omega) hnotM]
    rw [show q = 1559 + (q - 1559) by omega]
    exact hret ⟨q - 1559, by omega⟩
  have hpen_any : (PortalAnd.digits 1558 pendingPairs150).any uRel.basis = decide (Shadow.far 163 20 a) := by
    clear hrest
    change (uRel.basis 1558 || (pendingPairs150.map Prod.fst).any uRel.basis) = _
    rw [show uRel.basis 1558 = false by rw [huRel]; simp [writeBit], Bool.false_or]
    have hscan_eq : regValue (pendingPairs150.map Prod.fst) uRel.basis = (a.u + a.v) / 2 ^ 184 := by
      have hfit : LeaveJ7.TrueMiddle.F MixedWindow.j7 z < 2 ^ 84 := h.fit
      apply Nat.eq_of_testBit_eq; intro i
      have hlen : (pendingPairs150.map Prod.fst).length = 73 := by
        rw [pending150_fst]; simp only [List.length_cons, List.length_map, List.length_range]; decide
      by_cases hi' : i < 73
      · rw [← HighBankAdjust.bit_read (pendingPairs150.map Prod.fst) i uRel.basis (by rw [hlen]; exact hi')]
        rw [Nat.testBit_div_two_pow]
        cases i with
        | zero =>
          have hg0 : (pendingPairs150.map Prod.fst).getD 0 0 = Shadow7.a0P 150 - 1 + 11 := by
            rw [pending150_fst]; show Shadow7.a0P 150 + lows150 - 2 = Shadow7.a0P 150 - 1 + 11; rw [ha0, hlow12]
          rw [hg0, hrel_keep _ (by rw [ha0]; decide) (by rw [ha0]; decide),
            hfull_keep _ (by rw [ha0]; decide) (by rw [ha0]; decide) (by rw [ha0]; decide), hF_low 11 (by decide), F150_eq,
            Nat.testBit_div_two_pow]
        | succ k =>
          have hlw : Shadow7.liveW 150 = 84 := by decide
          have hgk : (pendingPairs150.map Prod.fst).getD (k + 1) 0 = Shadow7.bankW 150 (12 + k) := by
            rw [pending150_fst, List.getD_cons_succ, List.getD_eq_getElem?_getD,
              List.getElem?_map, List.getElem?_range (by rw [hlw, hlow12]; omega)]; rw [hlow12]; rfl
          have hnot78 := bankW150_ne_store ⟨k, by omega⟩
          rw [hgk, hrel_keep _ hnot78.1 hnot78.2.1, hfull_keep _ hnot78.1 hnot78.2.1 hnot78.2.2,
            hF_hi (12 + k) (by omega) (by rw [hwp]; omega), F150_eq, Nat.testBit_div_two_pow,
            show 12 + k + 173 = k + 1 + 184 by omega]
      · rw [Nat.testBit_lt_two_pow ((regValue_lt _ _).trans_le (Nat.pow_le_pow_right (by decide) (by rw [hlen]; omega)))]
        have hlt : (a.u + a.v) / 2 ^ 184 < 2 ^ 73 := by
          rw [F150_eq] at hfit
          have e : (a.u + a.v) / 2 ^ 184 = (a.u + a.v) / 2 ^ 173 / 2 ^ 11 := by
            rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
          rw [e]
          exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hfit)
        rw [Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
    rw [LeaveCompanion.any_positive, hscan_eq]
    have hiff : 0 < (a.u + a.v) / 2 ^ 184 ↔ Shadow.far 163 20 a := by
      unfold Shadow.far Shadow.high Shadow.limb
      rw [Nat.pos_iff_ne_zero, ne_eq, Nat.div_eq_zero_iff, not_or]
      have hdiv : 2 ≤ (a.u + a.v) / 2 ^ (163 + 20) ↔ 2 * 2 ^ (163 + 20) ≤ a.u + a.v :=
        Nat.le_div_iff_mul_le (by positivity)
      rw [hdiv, show (2 : Nat) * 2 ^ (163 + 20) = 2 ^ 184 by rw [← Nat.pow_succ']]
      constructor <;> intro hh
      · exact Nat.le_of_not_lt hh.2
      · exact ⟨by positivity, Nat.not_lt.mpr hh⟩
    exact decide_eq_decide.mpr hiff
  have hsm_run : run (GateMirror.forward leaveStoreMapped150) nSM uRel =
      ⟨uRel.phase, writeBit (writeBit (writeBit uRel.basis 1557 (decide (Shadow.far 163 20 a)))
        1558 (decide (Shadow.far 163 20 a) && decide (2 ^ 163 ≤ a.u))) 1556 false⟩ := by
    let f20 := decide (Shadow.far 163 20 a)
    let u20 := f20 && decide (2 ^ 163 ≤ a.u)
    have h56R : uRel.basis 1556 = decide (2 ^ 173 ≤ mag) := by
      rw [hrel_keep 1556 (by decide) (by decide), hfull_keep 1556 (by decide) (by decide) (by decide), h56]
    have hside : (uRel.basis 1556 && f20) = u20 := by
      rw [h56R]
      by_cases hf : Shadow.far 163 20 a
      · simp only [f20, u20, hf, decide_true, Bool.and_true, Bool.true_and]
        exact decide_eq_decide.mpr (nextFlag150_orientation a sign.toNat (by cases sign <;> decide) nextSmall20 hf)
      · simp [f20, u20, hf]
    have h1 := PortalAnd.run_latch true none 1557 1558 pendingPairs150 geom150_check.2.1 (by simp) uRel nSM hclean_pen
    simp only [PortalAnd.active, Option.elim_none, Bool.true_and] at h1
    rw [hpen_any, show uRel.basis 1557 = false by rw [huRel]; simp [writeBit], Bool.false_xor] at h1
    let st1 : State := ⟨uRel.phase, writeBit uRel.basis 1557 f20⟩
    have h2 : run ([.CCX 1556 1557 1558] : Program) (nSM.drop (measurementCount (latch true none 1557 1558 pendingPairs150))) st1 =
        ⟨uRel.phase, writeBit st1.basis 1558 u20⟩ := by
      rw [LeaveJ7.nextU_run st1 _ (by simp [st1, writeBit, huRel])]
      simp [st1, writeBit, hside]
    let st2 : State := ⟨uRel.phase, writeBit st1.basis 1558 u20⟩
    have h3 : run (latch true none 1556 1558 shortFlagPairs150)
        ((nSM.drop (measurementCount (latch true none 1557 1558 pendingPairs150))).drop (measurementCount [.CCX 1556 1557 1558])) st2 =
        ⟨uRel.phase, writeBit st2.basis 1556 false⟩ := by
      have hst2_keep : ∀ q : Wire, q ≠ 1557 → q ≠ 1558 → st2.basis q = uRel.basis q := fun q h7 h8 => by
        simp [st2, st1, writeBit, h7, h8]
      have hlow_b0 : st2.basis (Shadow7.b0P 150 - 1) = decide (2 ^ 173 ≤ mag % (2 * 2 ^ 173)) := by
        rw [hst2_keep _ (by decide) (by decide), hrel_keep _ (by decide) (by decide),
          hfull_keep _ nb.1 nb.2 hnotB, hbB, LeaveCompanion.thresholdBit _ _ (Nat.two_pow_pos _)]
      have hup_sm : regValue smallM150 st2.basis = (mag / (2 * 2 ^ 173)) % 2 ^ smallM150.length := by
        rw [(regValue_eq_iff _ _ _).mpr (fun q hq => by
          have hne : q ≠ 1557 ∧ q ≠ 1558 := by
            obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi'
            exact ⟨by rw [hb0]; unfold Wire; omega, by rw [hb0]; unfold Wire; omega⟩
          rw [hst2_keep q hne.1 hne.2, hrel_keep q hne.1 hne.2]), hmag_smallM]
        rw [show (2 : Nat) * 2 ^ 173 = 2 ^ 174 by rw [← Nat.pow_succ']]; rfl
      have h56_st2 : st2.basis 1556 = decide (2 ^ 173 ≤ mag) := by
        rw [hst2_keep 1556 (by decide) (by decide), h56R]
      have h58_st2 : st2.basis 1558 = (st2.basis 1556 && st2.basis 1557) := by
        rw [show st2.basis 1558 = u20 by simp [st2, writeBit],
          show st2.basis 1557 = f20 by simp [st2, st1, writeBit],
          hst2_keep 1556 (by decide) (by decide), hside]
      have hnear_st2 : st2.basis 1557 = false → mag < (2 * 2 ^ 173) * 2 ^ (smallM150.length - 1) := fun hf =>
        nextFlag150_boundShort a sign.toNat (of_decide_eq_false (by simpa [st2, st1, writeBit, f20] using hf))
      have fresh : ∀ p ∈ clearFlagPairs150, st2.basis p.2 = false :=
        (fun p hp => by
          have hr' := geom150_check.2.2.2.2.2.2 p hp
          simp only [st2, st1, writeBit, Function.update_of_ne (show p.2 ≠ 1558 by unfold Wire at *; omega),
            Function.update_of_ne (show p.2 ≠ 1557 by unfold Wire at *; omega)]
          exact hclean_clr p hp)
      exact shorten_narrow_flag_latch 1556 1558 1557 (Shadow7.b0P 150 - 1) smallM150 clearFlagPairs150
        st2 _ (2 ^ 173) mag (Nat.two_pow_pos _) (by decide) geom150_check.2.2.1 (by decide)
        fresh hnear_st2 h56_st2 h58_st2 hlow_b0 hup_sm
    rw [storeMapped150_parts, run_append, run_take, h1, run_append, run_take, h2, h3]
  have hbs_eq : run beforeStore150Prog m s = run (GateMirror.forward leaveStoreMapped150) nSM uRel := by
    simp only [beforeStore150Prog, run_append, run_take, nRel, uRel, nSM]
  have hbs_ph : (run beforeStore150Prog m s).phase = s.phase := by
    rw [hbs_eq, hsm_run]; show uRel.phase = _; rw [huRel]; exact hfull_ph
  have hbs_frame (q : Nat) (h6 : q ≠ 1556) (h7 : q ≠ 1557) (h8 : q ≠ 1558) (hM : q ∉ smallM150) :
      (run beforeStore150Prog m s).basis q = hst.basis q := by
    rw [hbs_eq, hsm_run]; simp only [writeBit, Function.update_of_ne h6, Function.update_of_ne h8, Function.update_of_ne h7]
    rw [hrel_keep q h7 h8, hfull_keep q h7 h8 hM]
  have hswap_frame (q : Nat) (h1 : q ≠ 364) (h2 : q ≠ 984) (h3 : q ≠ 365) (h4 : q ≠ 985) :
      hst.basis q = (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s).basis q := by
    rw [hst_eq]; exact hst_basis q h1 h2 h3 h4
  rw [hhst_def]
  refine ⟨hbs_ph, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbs_frame, hswap_frame⟩
  · rw [hbs_eq, hsm_run]; simp only [writeBit, Function.update_self]
  · rw [hbs_eq, hsm_run]; simp only [writeBit, Function.update_of_ne (by decide : (1557 : Wire) ≠ 1556),
      Function.update_of_ne (by decide : (1557 : Wire) ≠ 1558), Function.update_self]; rfl
  · rw [hbs_eq, hsm_run]; simp only [writeBit, Function.update_of_ne (by decide : (1558 : Wire) ≠ 1556), Function.update_self]; rfl
  · rw [hbs_frame _ (by decide) (by decide) (by decide) (by decide),
      hst_basis _ (by decide) (by decide) (by decide) (by decide),
      keepE _ (by unfold LeaveJ7.midT LeaveJ7.workT; decide)]
    exact hfront.2.2.1.trans (LeaveRestoreTruth.truth_shadow7 173 z h.farSmall u.2).1.symm
  · intro q hq
    unfold LeaveJ7.history at hq; rw [show start MixedWindow.j7 = 150 from rfl] at hq
    obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi'
    rw [hbs_frame (150 + 16 + i) (by omega) (by omega) (by omega)
        (not_mem_smallM150 _ (Or.inl (by change (150 : Nat) + 16 + i < 960; omega))),
      hst_basis (150 + 16 + i) (by omega) (by omega) (by omega) (by omega),
      keepE (150 + 16 + i) (by unfold LeaveJ7.midT LeaveJ7.workT; rw [show start MixedWindow.j7 = 150 from rfl, ha0, hb0, he0]; omega)]
    unfold LeaveSelector.parityBits LeaveJ7.oddRead at hpar0
    exact (List.map_inj_left.mp hpar0) i (List.mem_range.mpr hi')
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      constructor
      · rw [hbs_frame _ (by decide) (by decide) (by decide) hnotA, hbA, Nat.testBit_div_two_pow, Nat.zero_add]
      · rw [hbs_frame _ (by decide) (by decide) (by decide) hnotB, hbB, Nat.testBit_div_two_pow, Nat.zero_add]
    | succ k =>
      have hka : Shadow7.a0P 150 - 1 + (k + 1) = Shadow7.a0P 150 + k := by rw [ha0]; omega
      have hkb : Shadow7.b0P 150 - 1 + (k + 1) = Shadow7.b0P 150 + k := by rw [hb0]; omega
      constructor
      · rw [hka, hbs_frame (Shadow7.a0P 150 + k) (by rw [ha0]; omega) (by rw [ha0]; omega) (by rw [ha0]; omega)
            (not_mem_smallM150 _ (Or.inl (by change Shadow7.a0P 150 + k < 960; rw [ha0]; omega))),
          ← hka, hF_low (k + 1) (by omega), F150_eq, Nat.testBit_div_two_pow, show k + 1 + 173 = 173 + (k + 1) by omega]
      · rw [hkb, hbs_eq, hsm_run]
        simp only [writeBit,
          Function.update_of_ne (show (Shadow7.b0P 150 + k : Wire) ≠ 1556 by rw [hb0]; omega),
          Function.update_of_ne (show (Shadow7.b0P 150 + k : Wire) ≠ 1558 by rw [hb0]; omega),
          Function.update_of_ne (show (Shadow7.b0P 150 + k : Wire) ≠ 1557 by rw [hb0]; omega)]
        rw [hrel_keep (Shadow7.b0P 150 + k) (by rw [hb0]; omega) (by rw [hb0]; omega)]
        have hlenM : smallM150.length = 11 := rfl
        have hbit := HighBankAdjust.bit_read smallM150 k (run full150Prog m s).basis (by rw [hlenM]; omega)
        have hg : smallM150.getD k 0 = Shadow7.b0P 150 + k := by
          simp only [smallM150, lows150, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range (show k < 12 - 1 by omega), Option.map_some, Option.getD_some]
        rw [hg, hmag_smallM, Nat.testBit_mod_two_pow, decide_eq_true (show k < 11 by omega), Bool.true_and,
          Nat.testBit_div_two_pow, show k + 174 = 173 + (k + 1) by omega] at hbit
        exact hbit
  · intro i
    have hi' : i.val < 73 := Nat.lt_of_lt_of_eq i.isLt (by rw [hwp20])
    exact hF_hi (lows150 + i.val) (by rw [hlow12]; omega) (by rw [hwp, hlow12]; omega)

private theorem lowClose150_result (s : State) (m : List Bool) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) :
    let a := step^[15] z
    let u := LeaveJ7.Admission.flags z g0 s0
    let sign := PortalValues.negative u.2 a.u
    let mag := a.u - sign.toNat
    let mid := run storeMapped150Prog m s
    mid.phase = s.phase ∧
    (∀ q ∈ LeaveJ7.history MixedWindow.j7, mid.basis q = s.basis q) ∧
    (∀ i : Fin 12,
      let pos := (a.u + a.v).testBit (173 + i.val)
      let neg := mag.testBit (173 + i.val) ^^ sign
      mid.basis (Shadow7.a0P 150 - 1 + i.val) = (if u.1 then neg else pos) ∧
      mid.basis (Shadow7.b0P 150 - 1 + i.val) = (if u.1 then pos else neg)) ∧
    (∀ q, q ∉ RailPair.sites low150 → q ∉ LeaveJ7.history MixedWindow.j7 →
      mid.basis q = (run beforeStore150Prog m s).basis q) := by
  let a := step^[15] z
  let u := LeaveJ7.Admission.flags z g0 s0
  let sign := PortalValues.negative u.2 a.u
  let mag := a.u - sign.toNat
  obtain ⟨hbs_ph, _, _, _, hlc_sign, hlc_hist, hlc_words, _, _, _⟩ :=
    beforeStore150_result s m z g0 s0 h nextSmall20
  have hlc_prev : s.basis 180 = u.1 := by
    have hr := h.ready.2.2.1
    change s.basis (start MixedWindow.j7 + 30) = u.1
    rw [(LeaveJ7.scan_ports MixedWindow.j7 (by decide) (by decide)).2.2.2.2.1]
    cases h1 : u.1 <;> simpa only [u, h1] using hr
  let nLC := m.drop (measurementCount beforeStore150Prog)
  have hndH : (LeaveJ7.history MixedWindow.j7).Nodup := by decide
  have hw := RailPair.store_run 180 (Shadow7.e0P 150 + 5) low150 [] geom150_check.2.2.2.1
    ⟨(run beforeStore150Prog m s).phase, fun q => if q ∈ LeaveJ7.history MixedWindow.j7 then !(run beforeStore150Prog m s).basis q else (run beforeStore150Prog m s).basis q⟩
    (nLC.drop (measurementCount (notRegister (LeaveJ7.history MixedWindow.j7)))) (by simp)
  have hsep : ∀ q ∈ LeaveJ7.history MixedWindow.j7, q ∉ RailPair.sites low150 := by decide
  have h180_mem : (180 : Wire) ∈ LeaveJ7.history MixedWindow.j7 := by decide
  have hnot_hist_e5 : (Shadow7.e0P 150 + 5 : Wire) ∉ LeaveJ7.history MixedWindow.j7 := by decide
  have hsm_split : run storeMapped150Prog m s =
      run (RailPair.store 180 (Shadow7.e0P 150 + 5) low150 [])
        (nLC.drop (measurementCount (notRegister (LeaveJ7.history MixedWindow.j7))))
        ⟨(run beforeStore150Prog m s).phase, fun q => if q ∈ LeaveJ7.history MixedWindow.j7 then !(run beforeStore150Prog m s).basis q else (run beforeStore150Prog m s).basis q⟩ := by
    simp only [storeMapped150Prog, run_append, run_take, lowClose150_parts, nLC]
    rw [notRegister_correct _ hndH]
  dsimp only; rw [hsm_split]
  refine ⟨hw.1.trans hbs_ph, ?_, ?_, ?_⟩
  · intro q hq; rw [hw.2.1 q (hsep q hq) (by simp [RailPair.sites])]; dsimp only; rw [if_pos hq, hlc_hist q hq, Bool.not_not]
  · intro i
    have hmem : (Shadow7.a0P 150 - 1 + i.val, Shadow7.b0P 150 - 1 + i.val) ∈ low150 :=
      List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    have hl := hw.2.2.2 _ hmem
    have hnh1 : (Shadow7.a0P 150 - 1 + i.val : Wire) ∉ LeaveJ7.history MixedWindow.j7 := by
      have : ∀ k : Fin 12, (Shadow7.a0P 150 - 1 + k.val : Wire) ∉ LeaveJ7.history MixedWindow.j7 := by decide
      exact this i
    have hnh2 : (Shadow7.b0P 150 - 1 + i.val : Wire) ∉ LeaveJ7.history MixedWindow.j7 := by
      have : ∀ k : Fin 12, (Shadow7.b0P 150 - 1 + k.val : Wire) ∉ LeaveJ7.history MixedWindow.j7 := by decide
      exact this i
    simp only [if_pos h180_mem, hlc_hist 180 h180_mem, Bool.not_not, hlc_prev,
      if_neg hnot_hist_e5, hlc_sign, if_neg hnh1, if_neg hnh2, (hlc_words i).1, (hlc_words i).2] at hl
    exact hl
  · intro q hnl hnh; rw [hw.2.1 q hnl (by simp [RailPair.sites])]; dsimp only; rw [if_neg hnh]

private theorem mid150_eq_stock (s : State) (m : List Bool) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) (q : Wire)
    (hq : q = Shadow7.e0P 150 + 3 ∨ q = Shadow7.e0P 150 + 4 ∨ q = Shadow7.e0P 150 + 6 ∨
      q = Shadow7.e0P 150 + 7 ∨ (∃ p ∈ LeaveJ7.Close.events MixedWindow.j7, q = p.1 ∨ q = p.2)) :
    (run storeMapped150Prog m s).basis q = (run (LeaveJ7.StoreMapped.program MixedWindow.j7) [] s).basis q := by
  let u := LeaveJ7.Admission.flags z g0 s0
  obtain ⟨_, hbs_1556, _, _, _, _, _, _, hbs_frame, hst_basis⟩ :=
    beforeStore150_result s m z g0 s0 h nextSmall20
  have hlc_frame := (lowClose150_result s m z g0 s0 h nextSmall20).2.2.2
  have par := LeaveJ7.RecordedParity.result MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP 150) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P 150 + 3)) (s.basis (Shadow7.e0P 150 + 4)) z.u := by
    have hf := h.far; have hs := h.side
    rw [show start MixedWindow.j7 = 150 from rfl] at hf hs
    rw [hf, hs]; exact LeaveTraceHistory.flags _ _
  have ev := LeaveJ7.RecordedEvents.result MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have hbsStock := LeaveJ7.BeforeStore.result MixedWindow.j7 (by decide) (by decide) s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2
    ⟨h.nextFarSmall, h.endSmall⟩ h.fit
    (LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
      h.far h.side)
  have hsm_st := (LeaveJ7.StoreMapped.result MixedWindow.j7 (by decide) (by decide) s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2
    ⟨h.nextFarSmall, h.endSmall⟩ h.fit
    (LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
      h.far h.side)).2.2.2
  have haway : q ≠ 364 ∧ q ≠ 984 ∧ q ≠ 365 ∧ q ≠ 985 ∧ q ∉ RailPair.sites low150 ∧
      q ∉ LeaveJ7.history MixedWindow.j7 ∧ q ∉ smallM150 ∧ q ≠ 1557 ∧ q ≠ 1558 ∧
      q ∉ RailPair.sites (LeaveJ7.Close.low MixedWindow.j7) ∧ q ∉ LeaveJ7.smallM MixedWindow.j7 := by
    have hlist : q ∈ [Shadow7.e0P 150 + 3, Shadow7.e0P 150 + 4, Shadow7.e0P 150 + 6, Shadow7.e0P 150 + 7] ++
        (LeaveJ7.Close.events MixedWindow.j7).flatMap (fun p => [p.1, p.2]) := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap]
      rcases hq with rfl | rfl | rfl | rfl | ⟨p, hp, rfl | rfl⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
      · exact Or.inr ⟨p, hp, Or.inl rfl⟩
      · exact Or.inr ⟨p, hp, Or.inr rfl⟩
    exact events150_away q hlist
  rw [hlc_frame q haway.2.2.2.2.1 haway.2.2.2.2.2.1,
    hsm_st q haway.2.2.2.2.2.2.2.2.2.1 haway.2.2.2.2.2.1]
  by_cases h56 : q = 1556
  · subst h56; rw [hbs_1556, hbsStock.2.1]
  · rw [hbs_frame q h56 haway.2.2.2.2.2.2.2.1 haway.2.2.2.2.2.2.2.2.1 haway.2.2.2.2.2.2.1,
      hst_basis q haway.1 haway.2.1 haway.2.2.1 haway.2.2.2.1,
      hbsStock.2.2.2.2.2.2 q h56 haway.2.2.2.2.2.2.2.1 haway.2.2.2.2.2.2.2.2.1]
    exact (stock_full_eq_head150 s z g0 s0 h q haway.2.2.2.2.2.2.2.2.2.2 haway.2.2.2.2.2.2.2.1
      haway.2.2.2.2.2.2.2.2.1).symm

theorem whole150_result (s : State) (m : List Bool) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) :
    let a := step^[15] z
    let u := LeaveJ7.Admission.flags z g0 s0
    let sign := PortalValues.negative u.2 a.u
    let mag := a.u - sign.toNat
    let f15 := decide (Shadow.far (Shadow7.sbP 150) 15 z)
    let next := decide (Shadow.far 163 20 a)
    let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
    let out := run leave150To20 m s
    let mid := run storeMapped150Prog m s
    out.phase = s.phase ∧
    out.basis (e0P20 165 + 3) = next ∧
    out.basis (e0P20 165 + 4) = (next && decide (2 ^ 163 ≤ a.u)) ∧
    out.basis (e0P20 165 + 5) = sign ∧
    out.basis (e0P20 165 + 6) = f15 ∧
    out.basis (e0P20 165 + 7) = (f15 && StairArchiveTrace.afterFlags (decide (2 ^ (Shadow7.sbP 150) ≤ z.u)) (xs.take 5)) ∧
    out.basis (e0P20 165 + 8) = (f15 && HighBankSum.crossBit (LeaveJ7.TrueMiddle.d MixedWindow.j7 z)) ∧
    (∀ q ∈ LeaveJ7.Close.history MixedWindow.j7, out.basis q = s.basis q) ∧
    (∀ i : Fin 12,
      let pos := (a.u + a.v).testBit (173 + i.val)
      let neg := mag.testBit (173 + i.val) ^^ sign
      out.basis (Shadow7.a0P 150 - 1 + i.val) = (if u.1 then neg else pos) ∧
      out.basis (Shadow7.b0P 150 - 1 + i.val) = (if u.1 then pos else neg)) ∧
    (∀ i : Fin (wpP20 165 - 2),
      out.basis (Shadow7.b0P 150 + lows150 - 1 + i.val) = (a.u + a.v).testBit (173 + lows150 + i.val)) ∧
    (∀ q, out.basis q = writeBit mid.basis (Shadow7.e0P 150 + 4) false (LeaveRelocation.source movesP150To20 q)) ∧
    (run beforeStore150Prog m s).basis 1556 = false ∧
    (∀ q : Nat, q ≠ 1556 → q ≠ 1557 → q ≠ 1558 → q ∉ smallM150 →
      (run beforeStore150Prog m s).basis q = (run head150Prog m s).basis q) ∧
    (∀ q, q ∉ RailPair.sites low150 → q ∉ LeaveJ7.history MixedWindow.j7 →
      mid.basis q = (run beforeStore150Prog m s).basis q) := by
  let a := step^[15] z
  let u := LeaveJ7.Admission.flags z g0 s0
  let sign := PortalValues.negative u.2 a.u
  let mag := a.u - sign.toNat
  let xs := SkywalkTrace.trace 15 (SkywalkRails.encode g0 s0 z.u z.v)
  have hsb : Shadow7.sbP 150 = 173 := by decide
  obtain ⟨_, hbs_1556, hbs_1557, hbs_1558, hlc_sign, _, _, hF_hi, hbs_frame, _⟩ :=
    beforeStore150_result s m z g0 s0 h nextSmall20
  have hlc_run := lowClose150_result s m z g0 s0 h nextSmall20
  have hmid_eq_stock := mid150_eq_stock s m z g0 s0 h nextSmall20
  have par := LeaveJ7.RecordedParity.result MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP 150) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P 150 + 3)) (s.basis (Shadow7.e0P 150 + 4)) z.u := by
    have hf := h.far; have hs := h.side
    rw [show start MixedWindow.j7 = 150 from rfl] at hf hs
    rw [hf, hs]; exact LeaveTraceHistory.flags _ _
  have ev := LeaveJ7.RecordedEvents.result MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have hpostStock := LeaveJ7.PostReady.result MixedWindow.j7 (by decide) (by decide) s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2
    ⟨h.nextFarSmall, h.endSmall⟩ h.fit
    (LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record
      h.far h.side)
  have hp3 : (run (LeaveJ7.StoreMapped.program MixedWindow.j7) [] s).basis (Shadow7.e0P 150 + 3) = s.basis (Shadow7.e0P 150 + 3) :=
    hpostStock.1
  have hp4 : (run (LeaveJ7.StoreMapped.program MixedWindow.j7) [] s).basis (Shadow7.e0P 150 + 4) = s.basis (Shadow7.e0P 150 + 4) :=
    hpostStock.2.1
  have hp7 : (run (LeaveJ7.StoreMapped.program MixedWindow.j7) [] s).basis (Shadow7.e0P 150 + 7) =
      LeaveSelector.nearby (LeaveSelector.actualMode (Shadow7.sbP 150) z) :=
    hpostStock.2.2.1
  have hp6 : (run (LeaveJ7.StoreMapped.program MixedWindow.j7) [] s).basis (Shadow7.e0P 150 + 6) =
      (decide (Shadow.far (Shadow7.sbP 150) 15 z) && HighBankSum.crossBit (LeaveJ7.TrueMiddle.d MixedWindow.j7 z)) :=
    hpostStock.2.2.2.1
  have hpEv := hpostStock.2.2.2.2
  let mid := run storeMapped150Prog m s
  let nCl := m.drop (measurementCount storeMapped150Prog)
  have hcl_run : run (GateMirror.forward leaveClose150To20) nCl mid =
      ⟨mid.phase, fun q => (writeBit mid.basis (Shadow7.e0P 150 + 4) false) (LeaveRelocation.source movesP150To20 q)⟩ := by
    have hcold : ∀ p ∈ LeaveJ7.Close.events MixedWindow.j7, mid.basis p.2 = false := fun p hp =>
      (hmid_eq_stock p.2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, Or.inr rfl⟩))))).trans (hpEv p hp).2
    have hreads : (LeaveJ7.Close.events MixedWindow.j7).map (fun p => mid.basis p.1) = (xs.take 5).map Prod.snd :=
      (List.map_congr_left fun p hp =>
        (hmid_eq_stock p.1 (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hp, Or.inl rfl⟩))))).trans (hpEv p hp).1).trans ev.1
    have hvp := LeavePendingHistory.pending (decide (Shadow.far (Shadow7.sbP 150) 15 z))
      (decide (2 ^ (Shadow7.sbP 150) ≤ z.u)) xs
      ⟨IntegerHigh.wait 15 z.u, by have hw := IntegerHigh.wait_le 15 z.u; omega⟩
      (SkywalkTrace.trace_length _ _)
      (fun hf => LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd (of_decide_eq_true hf))
      (fun hf hu => LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd (of_decide_eq_true hf) hu)
    have hev_all : (LeaveJ7.Close.events MixedWindow.j7).all (fun p => !mid.basis p.1) = !(xs.take 5).any Prod.snd := by
      have hm : (LeaveJ7.Close.events MixedWindow.j7).any (fun p => mid.basis p.1) = (xs.take 5).any Prod.snd := by
        simpa only [List.any_map, Function.comp_def, id_eq] using congrArg (List.any · id) hreads
      rw [← hm]; simp only [List.all_eq_not_any_not, Bool.not_not]
    have hclr : (mid.basis (Shadow7.e0P 150 + 4) ^^ (mid.basis (Shadow7.e0P 150 + 7) &&
        (LeaveJ7.Close.events MixedWindow.j7).all (fun p => !mid.basis p.1))) = false := by
      rw [hmid_eq_stock _ (Or.inr (Or.inl rfl)), hmid_eq_stock _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        hp4, hp7, show s.basis (Shadow7.e0P 150 + 4) = _ from h.side, hev_all]
      exact hvp.2
    have hrecs150_map :
        ([OB5.sig 164 1194, OB5.sig 164 1195, OB5.sig 164 1196, OB5.sig 164 1197, OB5.sig 164 1198] : List Wire).map mid.basis =
          (xs.take 5).map Prod.snd := hreads
    have hval150 : mid.basis (Shadow7.e0P 150 + 4) =
        (mid.basis (Shadow7.e0P 150 + 7) && !HighBankControl.parity mid.basis
          [OB5.sig 164 1194, OB5.sig 164 1195, OB5.sig 164 1196, OB5.sig 164 1197, OB5.sig 164 1198]) := by
      by_cases hf : Shadow.far (Shadow7.sbP 150) 15 z
      · have hcp := Shadow7.chain_parity 5 _ xs (LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd hf)
        have hpar : HighBankControl.parity mid.basis [OB5.sig 164 1194, OB5.sig 164 1195, OB5.sig 164 1196, OB5.sig 164 1197, OB5.sig 164 1198] =
            (xs.take 5).any Prod.snd := by rw [Shadow7.parity_bits, hrecs150_map, hcp]
        rw [hpar, hmid_eq_stock _ (Or.inr (Or.inl rfl)), hmid_eq_stock _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
          hp4, hp7, show s.basis (Shadow7.e0P 150 + 4) = _ from h.side]
        have hxor : ∀ a b : Bool, (a ^^ b) = false → a = b := by decide
        exact hxor _ _ hvp.2
      · rw [hmid_eq_stock _ (Or.inr (Or.inl rfl)), hmid_eq_stock _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
          hp4, hp7, show s.basis (Shadow7.e0P 150 + 4) = _ from h.side, show start MixedWindow.j7 = 150 from rfl, decide_eq_false hf]
        have hn0 : LeaveSelector.nearby (LeaveSelector.actualMode (Shadow7.sbP 150) z) = false := by
          unfold LeaveSelector.actualMode; rw [decide_eq_false hf]; rfl
        rw [hn0]; rfl
    have hc56 : mid.basis 1556 = false := hcold (OB5.sig 164 1194, 1556) (by decide)
    rw [close150_parts, run_append, run_take, Shadow7.closeFlag,
      Shadow7.parity_run _ _ _ _ mid _ (by decide) (by decide) (by decide) (by decide) (by decide) hc56 hval150,
      LeaveRelocation.actual _ geom150_check.2.2.2.2.1]
  have hout_eq : run leave150To20 m s = run (GateMirror.forward leaveClose150To20) nCl mid := by
    simp only [leave150To20_split, run_append, run_take, mid, nCl]
  have hrc := reloc150_check
  have hvp := LeavePendingHistory.pending (decide (Shadow.far (Shadow7.sbP 150) 15 z))
    (decide (2 ^ (Shadow7.sbP 150) ≤ z.u)) xs
    ⟨IntegerHigh.wait 15 z.u, by have hw := IntegerHigh.wait_le 15 z.u; omega⟩
    (SkywalkTrace.trace_length _ _)
    (fun hf => LeaveJ7.Far.certifiedChain _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd (of_decide_eq_true hf))
    (fun hf hu => LeaveJ7.Far.firstSwap _ _ _ _ ⟨h.farSmall, h.endSmall⟩ h.odd (of_decide_eq_true hf) hu)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbs_1556, hbs_frame, hlc_run.2.2.2⟩
  · rw [hout_eq, hcl_run]; exact hlc_run.1
  · rw [hout_eq, hcl_run]; dsimp only; rw [hrc.1]
    simp only [writeBit, Function.update_of_ne (by decide : (1557 : Wire) ≠ Shadow7.e0P 150 + 4)]
    rw [hlc_run.2.2.2 1557 (by decide) (by decide)]; exact hbs_1557
  · rw [hout_eq, hcl_run]; dsimp only; rw [hrc.2.1]
    simp only [writeBit, Function.update_of_ne (by decide : (1558 : Wire) ≠ Shadow7.e0P 150 + 4)]
    rw [hlc_run.2.2.2 1558 (by decide) (by decide)]; exact hbs_1558
  · rw [hout_eq, hcl_run]; dsimp only; rw [hrc.2.2.1]
    simp only [writeBit, Function.update_of_ne (by decide : Shadow7.e0P 150 + 5 ≠ Shadow7.e0P 150 + 4)]
    rw [hlc_run.2.2.2 _ (by decide) (by decide)]; exact hlc_sign
  · rw [hout_eq, hcl_run]; dsimp only; rw [hrc.2.2.2.1]
    simp only [writeBit, Function.update_of_ne (by decide : Shadow7.e0P 150 + 3 ≠ Shadow7.e0P 150 + 4)]
    rw [hmid_eq_stock _ (Or.inl rfl), hp3]; exact h.far
  · rw [hout_eq, hcl_run]; dsimp only; rw [hrc.2.2.2.2.1]
    simp only [writeBit, Function.update_of_ne (by decide : Shadow7.e0P 150 + 7 ≠ Shadow7.e0P 150 + 4)]
    rw [hmid_eq_stock _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hp7]
    exact hvp.1
  · rw [hout_eq, hcl_run]; dsimp only; rw [hrc.2.2.2.2.2.1]
    simp only [writeBit, Function.update_of_ne (by decide : Shadow7.e0P 150 + 6 ≠ Shadow7.e0P 150 + 4)]
    rw [hmid_eq_stock _ (Or.inr (Or.inr (Or.inl rfl))), hp6]
  · intro q hq; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq; rw [List.mem_range] at hi
    rw [hout_eq, hcl_run]; dsimp only
    rw [show start MixedWindow.j7 + 16 + i = 166 + i from rfl, hrc.2.2.2.2.2.2.1 ⟨i, hi⟩]
    simp only [writeBit, Function.update_of_ne (show (166 + i : Wire) ≠ Shadow7.e0P 150 + 4 by unfold Shadow7.e0P Shadow7.sbP Wire; omega)]
    exact hlc_run.2.1 _ hq
  · intro i
    rw [hout_eq, hcl_run]; dsimp only
    rw [(hrc.2.2.2.2.2.2.2.1 i).1, (hrc.2.2.2.2.2.2.2.1 i).2]
    have h1 : (Shadow7.a0P 150 - 1 + i.val : Wire) ≠ Shadow7.e0P 150 + 4 := by have := i.isLt; unfold Shadow7.a0P Shadow7.e0P Shadow7.sbP Wire; omega
    have h2 : (Shadow7.b0P 150 - 1 + i.val : Wire) ≠ Shadow7.e0P 150 + 4 := by have := i.isLt; unfold Shadow7.b0P Shadow7.e0P Shadow7.sbP Wire; omega
    simp only [writeBit, Function.update_of_ne h1, Function.update_of_ne h2]
    exact hlc_run.2.2.1 i
  · intro i
    rw [hout_eq, hcl_run]; dsimp only
    rw [(hrc.2.2.2.2.2.2.2.2 i).1]
    have haway := bankW150_away i
    simp only [writeBit, Function.update_of_ne haway.1]
    rw [hlc_run.2.2.2 _ haway.2.1 haway.2.2.1, hbs_frame _ haway.2.2.2.1 haway.2.2.2.2.1 haway.2.2.2.2.2.1 haway.2.2.2.2.2.2, hF_hi i]
    unfold LeaveJ7.TrueMiddle.F HighBankSum.total
    rw [show start MixedWindow.j7 = 150 from rfl, hsb, Nat.testBit_div_two_pow,
      show lows150 + i.val + 173 = 173 + lows150 + i.val by omega]
  · intro q; rw [hout_eq, hcl_run]

end Forward150

/-! ### Section 3: Frame Preservation (`leave150To20_keeps`) & Exact Roundtrip (`leave150To20_roundtrip`) -/

private theorem leaveAfter150_box2 :
    leaveAfter150To20.all (fun g => g.wires.all fun q =>
      decide ((166 ≤ (q : Nat) ∧ (q : Nat) ≤ 180) ∨
        (Shadow7.a0P 150 - 1 ≤ (q : Nat) ∧ (q : Nat) ≤ Shadow7.a0P 150 + 15) ∨
        (Shadow7.b0P 150 - 1 ≤ (q : Nat) ∧ (q : Nat) ≤ bTopP 150) ∨
        (1194 ≤ (q : Nat) ∧ (q : Nat) ≤ 1208) ∨
        (1556 ≤ (q : Nat) ∧ (q : Nat) ≤ 1812))) = true ∧
    leaveAfter150To20.all (fun g => g.wires.all fun q => decide ((q : Nat) + 150 ≤ 2069)) = true := by
  decide +kernel

private theorem box2_150_consts :
    Shadow7.a0P 150 = 355 ∧ Shadow7.b0P 150 = 960 ∧ bTopP 150 = 1043 ∧
    railP 150 = 258 ∧ railP 164 = 258 ∧ Shadow7.wpP 150 = 70 := by
  decide

private theorem before150_box2 (q : Wire) (h : q ∈ wires (GateMirror.forward (CRTBarrel.before 150))) :
    Shadow7.leaveBox2 150 q := by
  have hi : MixedWindow.j7.val ≤ 24 := by decide
  have pieces := Shadow7.allW_leaveMove (start MixedWindow.j7)
    (Shadow7.leaveOps_box2 MixedWindow.j7 (Nat.zero_le _) hi)
  rw [CRTWindow.split_ops, allW_append_iff, allW_append_iff] at pieces
  have preAll : AllW (Shadow7.leaveBox2 (start MixedWindow.j7)) (DeadJoin.beforeAll (start MixedWindow.j7)) :=
    FlagLeave.cut_allW (Shadow7.e0P (start MixedWindow.j7) + 3) (Shadow7.e0P (start MixedWindow.j7) + 4) 1559 2
      (DeadJoin.beforeScan (start MixedWindow.j7)) (DeadJoin.before_scan_allW _ pieces.1)
  exact (allW_programs (P := Shadow7.leaveBox2 (start MixedWindow.j7)) (ops := CRTBarrel.before (start MixedWindow.j7))
    (Clean1556.before5RowClean_allW MixedWindow.j7 hi (CRTBarrel.LeaveAdjustTrim.row_allW MixedWindow.j7 hi (DeadJoin.before5_allW MixedWindow.j7 hi preAll)))).1 q h

attribute [local irreducible] run CRTBarrel.barrel GateMirror.forward leave150To20 leaveAfter150To20 in
theorem leave150To20_keeps (q : Wire) (hq : ¬ Shadow7.leaveBox2 150 q) (m : List Bool) (s : State) :
    (run leave150To20 m s).basis q = s.basis q := by
  obtain ⟨ha0, hb0, hbt, hr0, hr14, hwp⟩ := box2_150_consts
  refine run_preserves_outside leave150To20 m s q (fun hm => hq ?_)
  unfold leave150To20 at hm; simp only [wires_append, Finset.mem_union] at hm
  rcases hm with (h | h) | h
  · exact before150_box2 q h
  · exact CRTWindow.barrel_box2 MixedWindow.j7 (by decide) (by decide) false q h
  · have hall : AllW (fun w => Shadow7.leaveBox2 150 w) leaveAfter150To20 := fun g hg w hw => by
      have h' := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp leaveAfter150_box2.1 g hg) w hw)
      unfold Shadow7.leaveBox2; rw [show 150 + 14 = 164 from rfl, hr14, hr0, ha0, hb0, hwp]
      rw [ha0, hb0, hbt] at h'
      unfold Wire at *; omega
    exact (allW_programs hall).1 q h

attribute [local irreducible] run CRTBarrel.barrel GateMirror.forward leave150To20 leaveAfter150To20 in
theorem leave150To20_keeps_mirror (q : Wire) (lo : 2070 ≤ (q : Nat) + 150) (m : List Bool) (s : State) :
    (run leave150To20 m s).basis q = s.basis q := by
  obtain ⟨ha0, hb0, hbt, hr0, hr14, hwp⟩ := box2_150_consts
  refine run_preserves_outside leave150To20 m s q (fun hm => ?_)
  have hle : (q : Nat) + 150 ≤ 2069 := by
    unfold leave150To20 at hm; simp only [wires_append, Finset.mem_union] at hm
    rcases hm with (h | h) | h
    · have hbox := before150_box2 q h
      unfold Shadow7.leaveBox2 at hbox
      rw [show 150 + 14 = 164 from rfl, hr14, hr0] at hbox
      unfold Wire at *; omega
    · have hbox := CRTWindow.barrel_box2 MixedWindow.j7 (by decide) (by decide) false q h
      unfold Shadow7.leaveBox2 at hbox; rw [show start MixedWindow.j7 = 150 from rfl] at hbox
      rw [show 150 + 14 = 164 from rfl, hr14, hr0] at hbox
      unfold Wire at *; omega
    · have hall : AllW (fun w => (w : Nat) + 150 ≤ 2069) leaveAfter150To20 := fun g hg w hw =>
        of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp leaveAfter150_box2.2 g hg) w hw)
      exact (allW_programs hall).1 q h
  unfold Wire at *; omega

private def maskSubset150 (a b : Nat) : Bool := (a ||| b) == b

private def checkMask150 (gs : List Gate) (post allow : Nat) : Bool :=
  match bitCheck gs post with
  | some pre => maskSubset150 pre allow
  | none => false

private theorem masked_of_subset150 {s : State} {a b : Nat} (hsub : maskSubset150 a b = true)
    (hb : Masked s b) : Masked s a := by
  intro q hq
  have heq : a ||| b = b := of_decide_eq_true hsub
  have htb : (a ||| b).testBit q = b.testBit q := congrArg (fun n : Nat => n.testBit q) heq
  rw [Nat.testBit_or, hq, Bool.true_or] at htb
  exact hb q htb.symm

private theorem ready_of_checkMask150 (gs : List Gate) (s : State) (post allow : Nat)
    (hc : checkMask150 gs post allow = true) (hallow : Masked s allow) :
    Ready s gs ∧ Masked (run (GateMirror.forward gs) [] s) post := by
  unfold checkMask150 at hc
  cases hx : bitCheck gs post with
  | none => simp [hx] at hc
  | some pre =>
    simp only [hx] at hc
    have hs := bit_sound gs s pre post hx (masked_of_subset150 hc hallow)
    exact ⟨hs.2.1, hs.2.2⟩

private def storePart1Mid150 : List Gate :=
  let L := lows150
  let top := Shadow7.a0P 150 + L - 2
  let H := Shadow7.liveW 150 - L
  let hi := (List.range H).map fun i => Shadow7.bankW 150 (L + i)
  let seq := fun i => if i = 0 then top else Shadow7.bankW 150 (L + i - 1)
  [.x top] ++ xsG hi ++
  chainG (Shadow7.storeW 150) seq [.cx (Shadow7.storeW 150 (H + 1)) 1557, .x 1557] 0 (H + 1) ++
  xsG hi.reverse ++ [.x top]

private def storePart1_150 : List Gate := [.x 1558] ++ storePart1Mid150 ++ [.x 1558]

private def storePart2_150 : List Gate :=
  let L := lows150
  let seq2 := (List.range (L - 1)).map (Shadow7.b0P 150 - 1 + ·)
  [.x 1558] ++ xsG seq2 ++
  chainG (1558 + ·) (Shadow7.b0P 150 - 1 + ·) [.cx (1558 + (L - 1)) 1556, .x 1556] 0 (L - 1) ++
  xsG seq2.reverse ++ [.x 1558]

private def storeAllow1_150 : Nat :=
  GateMirror.interval 1559 39 ||| GateMirror.interval 1613 (Shadow7.e0P 150 - 1615)

private theorem tail150_checks :
    checkMask150 lowRest150 (1 <<< 1558)
      (GateMirror.interval (Shadow7.b0P 150) lows150 ||| GateMirror.interval 1559 39 ||| (1 <<< 1558)) = true ∧
    checkMask150 storePart1_150 (GateMirror.interval 1559 39) storeAllow1_150 = true ∧
    storePart1Mid150.all (fun g => decide (GateMirror.target g ≠ 1558)) = true ∧
    checkMask150 storePart2_150 0 (GateMirror.interval 1559 39) = true ∧
    leaveAfter150To20.all proper = true := by
  decide +kernel

private theorem testBit_one_shl150 (a q : Nat) : (1 <<< a).testBit q = decide (a = q) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : a ≤ q
  · by_cases he : a = q
    · subst he; simp
    · have hdiv : 1 / 2 ^ (q - a) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega))
      rw [decide_eq_true h, Bool.true_and, decide_eq_false he, Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]; rfl
  · rw [decide_eq_false h, Bool.false_and]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq, Bool.false_eq_true, false_iff]; omega)

private theorem testBit_interval150 (lo w q : Nat) :
    (GateMirror.interval lo w).testBit q = decide (lo ≤ q ∧ q < lo + w) := by
  unfold GateMirror.interval; rw [Nat.testBit_shiftLeft]
  by_cases h1 : lo ≤ q
  · simp only [decide_eq_true h1, Bool.true_and, Nat.testBit_two_pow_sub_one, ge_iff_le]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]; omega)
  · simp only [decide_eq_false h1, Bool.false_and]
    exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq, Bool.false_eq_true, false_iff, not_and]; omega)

private theorem close150_ev_away :
    ∀ p ∈ ([(OB5.sig 164 (150 + 1044), (1556 : Wire)), (OB5.sig 164 (150 + 1045), 1559),
      (OB5.sig 164 (150 + 1046), 1560), (OB5.sig 164 (150 + 1047), 1561), (OB5.sig 164 (150 + 1048), 1562)]),
    ¬ (p.1 = 1556 ∨ (1559 ≤ (p.1 : Nat) ∧ (p.1 : Nat) ≤ 1562)) ∧
      (p.2 = 1556 ∨ (1559 ≤ (p.2 : Nat) ∧ (p.2 : Nat) ≤ 1562)) := by
  decide +kernel

private theorem lowClose150_safe :
    Safe (leaveLowClose150 ++ leaveClose150To20)
      (fun q => q = 1556 ∨ (1559 ≤ q ∧ q ≤ 1562)) (fun _ => False) := by
  have hlc : Safe leaveLowClose150 (fun q => q = 1556 ∨ (1559 ≤ q ∧ q ≤ 1562))
      (fun q => q = 1556 ∨ (1559 ≤ q ∧ q ≤ 1562)) := by
    refine safe_lit ?_ ?_
    · unfold leaveLowClose150
      exact noMake_append (noMake_append (noMake_xsG _) (noMake_map _ _ fun _ _ => rfl))
        (noMake_flatMap _ _ fun _ _ => noMake_cswapG _ _ _)
    · intro g hg
      have hall : leaveLowClose150.all (fun g => decide (¬ (GateMirror.target g = 1556 ∨ (1559 ≤ GateMirror.target g ∧ GateMirror.target g ≤ 1562)))) = true := by
        decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp hall g hg)
  have hcl : Safe leaveClose150To20 (fun q => q = 1556 ∨ (1559 ≤ q ∧ q ≤ 1562)) (fun _ => False) := by
    unfold leaveClose150To20 Shadow7.closeFlag
    exact safe_append (safe_drop (Shadow7.noMake_parityG _ _ _ _)) (safe_drop (noMake_swapsG _))
  exact safe_append hlc hcl

private theorem storePart1_150_fwd :
    GateMirror.forward storePart1_150 = [.X 1558] ++ GateMirror.forward storePart1Mid150 ++ [.X 1558] := by
  simp only [storePart1_150, forward_app]; rfl

private theorem run_x150 (a : Wire) (t : List Bool) (s : State) :
    run [.X a] t s = ⟨s.phase, writeBit s.basis a (!s.basis a)⟩ := rfl

private theorem fwd_make150 (a b c : Wire) : GateMirror.forward [.make a b c] = [.CCX a b c] := rfl

private theorem run_ccx150 (a b c : Wire) (t : List Bool) (s : State) :
    run [.CCX a b c] t s = ⟨s.phase, writeBit s.basis c (s.basis c ^^ (s.basis a && s.basis b))⟩ := rfl

attribute [local irreducible] run SkywalkNat.step Shadow.far CRTBarrel.barrel GateMirror.forward inverse
  leave150To20 leaveInv150To20 leaveAfter150To20 afterHead150 lowRest150 leaveStoreMapped150
  storePart1_150 storePart1Mid150 storePart2_150 leaveLowClose150 leaveClose150To20
  head150Prog full150Prog beforeStore150Prog storeMapped150Prog in
theorem leaveAfter150_valid (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) :
    CRTBarrel.LeaveSplice.Valid
      (run (GateMirror.forward (CRTBarrel.before 150 ++ Shadow7.leaveBarrel 150)) [] s) leaveAfter150To20 := by
  have vMov := CRTBarrel.LeaveSplice.moved_valid (j := MixedWindow.j7) (by decide) (by decide) h
  rw [show start MixedWindow.j7 = 150 from rfl, CRTWindow.split_ops] at vMov
  obtain ⟨va, vbc⟩ := vMov.parts
  have hb := before150_state s z g0 s0 h
  obtain ⟨sameB, backB⟩ := CRTBarrel.LeaveCut.barrel_pair MixedWindow.j7 (by decide) (by decide)
    _ (CRTBarrel.LeaveCut.input (by decide) (by decide) h)
  rw [show start MixedWindow.j7 = 150 from rfl] at sameB backB
  obtain ⟨vHead150, hhead_eq⟩ := leaveMove150_head_eq s z g0 s0 h
  have hhead_prog : ∀ m', run head150Prog m' s = swap2St (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s) := by
    intro m'; unfold head150Prog; exact hhead_eq m'
  let uA := run (GateMirror.forward (CRTBarrel.before 150)) [] s
  have huA : uA = run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s := hb []
  let uB := run (GateMirror.forward (Shadow7.leaveBarrel 150)) [] uA
  have huB_eq : uB = run (GateMirror.forward (CRTBarrel.before 150 ++ Shadow7.leaveBarrel 150)) [] s := by
    simp only [uB, uA, forward_app, run_append, run_take, List.drop_nil]
  have hspAfter : leaveAfter150To20 = afterHead150 ++ (lowRest150 ++ (leaveStoreMapped150 ++ (leaveLowClose150 ++ leaveClose150To20))) := by
    simp only [leaveAfter150To20, afterHead150, lowRest150, leaveLowStore150, Shadow7.lowSign, List.append_assoc]
  let uH := run (GateMirror.forward afterHead150) [] uB
  have huH_eq : uH = run head150Prog [] s := by
    simp only [uH, uB, uA, head150Prog, run_append, run_take, List.drop_nil]
    rw [hb [], sameB]
  have gflag := LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩
    h.odd h.record h.far h.side
  have hfront := LeaveJ7.entry_core MixedWindow.j7 (by decide) (by decide) s [] z
    (LeaveJ7.Admission.flags z g0 s0).1 (LeaveJ7.Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp
    (Shadow.far (Shadow7.sbP (start MixedWindow.j7)) 15 z ∧
      LeaveShadowRails.farKey (Shadow7.sbP (start MixedWindow.j7)) z = 0)
    (LeaveJ7.glueBound MixedWindow.j7 z (LeaveJ7.Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩) gflag
  dsimp only at hfront
  rw [show start MixedWindow.j7 = 150 from rfl] at hfront
  have h1558H : (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s).basis 1558 = false := by
    rw [show Shadow7.leaveHeadOps 150 = LeaveJ7.entryOps 150 ++ LeaveJ7.bodyOps MixedWindow.j7 from
        (LeaveJ7.head_eq MixedWindow.j7).symm, forward_app, run_append, run_take, List.drop_nil,
      LeaveReadoutFrame.preserved _ _ _ 1558 (fun hit => absurd (LeaveJ7.body_dest MixedWindow.j7 (by decide) (by decide) 1558 hit)
        (by unfold LeaveJ7.midT LeaveJ7.workT; decide))]
    exact hfront.2.2.2.2.1.2
  have hck := LeaveJ7.CoreCheckpoint.result MixedWindow.j7 (by decide) (by decide) s [] z
    (LeaveJ7.Admission.flags z g0 s0).1 (LeaveJ7.Admission.flags z g0 s0).2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero
    (LeaveJ7.RecordedParity.result MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record)
    (by rw [h.far, h.side]; exact LeaveTraceHistory.flags _ _)
    (LeaveJ7.RecordedEvents.result MixedWindow.j7 (by decide) (by decide) s z g0 s0 ⟨h.farSmall, h.endSmall⟩ h.odd h.record).2
    gflag
  have hck_prog : LeaveJ7.CoreCheckpoint.program MixedWindow.j7 = GateMirror.forward (Shadow7.leaveHeadOps 150) := rfl
  rw [hck_prog] at hck
  have hgeo : Shadow7.sbP 150 = 173 ∧ Shadow7.b0P 150 = 960 ∧ Shadow7.e0P 150 = 1747 ∧ lows150 = 12 := by decide
  obtain ⟨hsb, hb0, he0, hlow12⟩ := hgeo
  have hmaskLR : Masked uH (GateMirror.interval (Shadow7.b0P 150) lows150 ||| GateMirror.interval 1559 39 ||| (1 <<< 1558)) := by
    intro q hq
    rw [Nat.testBit_or, Nat.testBit_or, testBit_interval150, testBit_interval150, testBit_one_shl150,
      Bool.or_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq] at hq
    rw [huH_eq, hhead_prog]
    rcases hq with (⟨h1, h2⟩ | ⟨h1, h2⟩) | h3
    · rw [hb0] at h1 h2; rw [hlow12] at h2
      rw [swap2St_other q (by omega) (by omega) (by omega) (by omega)]
      exact hck.2.2.2 _ (List.mem_map.mpr ⟨q - 960, List.mem_range.mpr (by omega),
        by change Shadow7.b0P (start MixedWindow.j7) + (q - 960) = q
           rw [show start MixedWindow.j7 = 150 from rfl, hb0]; omega⟩)
    · rw [swap2St_other q (by omega) (by omega) (by omega) (by omega)]
      rw [show q = 1559 + (q - 1559) by omega]
      exact hck.1 ⟨q - 1559, by omega⟩
    · subst h3; rw [swap2St_other 1558 (by decide) (by decide) (by decide) (by decide)]; exact h1558H
  have hlr := ready_of_checkMask150 lowRest150 uH (1 <<< 1558) _ tail150_checks.1 hmaskLR
  let uLR := run (GateMirror.forward lowRest150) [] uH
  have hlr_prog : GateMirror.forward lowRest150 =
      borrowG4_150 ++ (Companion.restore smallA150 smallM150 smallC150 1556 1558 ++ releaseMaskP150) := by
    have h1 := lowStore150_parts
    have h2 : GateMirror.forward leaveLowStore150 =
        GateMirror.forward (Shadow7.lowSign 150) ++ GateMirror.forward lowRest150 := by
      unfold leaveLowStore150 Shadow7.lowSign lowRest150; simp only [forward_app, List.append_assoc]
    rw [h2] at h1; exact List.append_cancel_left h1
  have huLR_keep : ∀ q : Wire, q ≠ 1557 → q ≠ 1558 → q ∉ smallM150 → uLR.basis q = uH.basis q := by
    intro q h7 h8 hM
    change (run (GateMirror.forward lowRest150) [] uH).basis q = uH.basis q
    rw [hlr_prog, run_append, run_take, List.drop_nil, run_append, run_take, List.drop_nil]
    have hnr : q ∉ releaseMaskP150.map LeaveReadoutFrame.destination := by
      intro hm; simp only [releaseMaskP150, GateMirror.forward, front, erase, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, LeaveReadoutFrame.destination] at hm
      rcases hm with rfl | rfl | rfl <;> contradiction
    rw [LeaveReadoutFrame.preserved _ _ _ q hnr]
    have hrest := Companion.write smallA150 smallM150 smallC150 1556 1558 geom150_check.1 (run borrowG4_150 [] uH) []
      (fun w hw => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; rw [List.mem_range] at hi
        have hl : lows150 = 12 := rfl
        rw [hl] at hi
        rw [borrowG4_150_keep uH (1559 + i) (by unfold Wire; omega) (by unfold Wire; omega)]
        exact hmaskLR (1559 + i) (by
          rw [Nat.testBit_or, Nat.testBit_or, testBit_interval150, testBit_interval150]
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          left; right; omega))
      (by
        rw [regValue_zero]; intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; rw [List.mem_range] at hi
        have hl : lows150 = 12 := rfl
        rw [hl] at hi
        rw [borrowG4_150_keep uH (Shadow7.b0P 150 + i) (by rw [hb0]; unfold Wire; omega) (by rw [hb0]; unfold Wire; omega)]
        exact hmaskLR (Shadow7.b0P 150 + i) (by
          rw [Nat.testBit_or, Nat.testBit_or, testBit_interval150]
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          left; left; rw [hlow12]; omega))
    rw [hrest.2.1 q hM, borrowG4_150_keep uH q h7 h8]
  have hmaskSM1 : Masked uLR storeAllow1_150 := by
    intro q hq
    unfold storeAllow1_150 at hq
    rw [Nat.testBit_or, testBit_interval150, testBit_interval150, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hq
    have hnotM : (q : Wire) ∉ smallM150 := by
      intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
      rcases hq with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire at *; omega)
    rw [huLR_keep q (by rcases hq with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire; omega))
        (by rcases hq with ⟨_, _⟩ | ⟨_, _⟩ <;> (unfold Wire; omega)) hnotM,
      huH_eq, hhead_prog]
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [swap2St_other q (by omega) (by omega) (by omega) (by omega)]
      rw [show q = 1559 + (q - 1559) by omega]
      exact hck.1 ⟨q - 1559, by omega⟩
    · rw [swap2St_other q (by omega) (by omega) (by omega) (by omega)]
      have hraw : (q : Wire) ∈ LeaveJ7.CoreCheckpoint.rawSites MixedWindow.j7 := by
        simp only [LeaveJ7.CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1]
        left; left; exact ⟨h1, by rw [show start MixedWindow.j7 = 150 from rfl]; omega⟩
      rw [hck.2.2.1 q hraw]
      exact LeaveJ7.native_carryJ_lt MixedWindow.j7 (by decide) (by decide) _ s h.ready q
        (by change 1556 ≤ q; omega)
        (by change q + 2 < Shadow7.e0P (start MixedWindow.j7); rw [show start MixedWindow.j7 = 150 from rfl, he0]; rw [he0] at h2; omega)
  have hsm1 := ready_of_checkMask150 storePart1_150 uLR (GateMirror.interval 1559 39) storeAllow1_150 tail150_checks.2.1 hmaskSM1
  let uSM1 := run (GateMirror.forward storePart1_150) [] uLR
  have h1558_uLR : uLR.basis 1558 = false := hlr.2 1558 (by rw [testBit_one_shl150]; decide)
  have h1558_uSM1 : uSM1.basis 1558 = false := by
    have hnot58 : (1558 : Wire) ∉ (GateMirror.forward storePart1Mid150).map LeaveReadoutFrame.destination := by
      rw [forward_map_dest]; intro hm; obtain ⟨g, hg, e⟩ := List.mem_map.mp hm
      exact of_decide_eq_true (List.all_eq_true.mp tail150_checks.2.2.1 g hg) e
    show (run (GateMirror.forward storePart1_150) [] uLR).basis 1558 = false
    rw [storePart1_150_fwd, run_append, run_take, List.drop_nil, run_append, run_take, List.drop_nil, run_x150]
    simp only [writeBit, Function.update_self]
    rw [LeaveReadoutFrame.preserved _ _ _ 1558 hnot58, run_x150]
    simp only [writeBit, Function.update_self, h1558_uLR]; rfl
  have hmake : Ready uSM1 [.make 1556 1557 1558] := ⟨h1558_uSM1, trivial⟩
  let uMk := run (GateMirror.forward [.make 1556 1557 1558]) [] uSM1
  have hmaskSM2 : Masked uMk (GateMirror.interval 1559 39) := by
    intro q hq
    rw [testBit_interval150, decide_eq_true_eq] at hq
    have hne58 : (q : Wire) ≠ 1558 := by omega
    dsimp only [uMk]; rw [fwd_make150, run_ccx150]
    simp only [writeBit, Function.update_of_ne hne58]
    exact hsm1.2 q (by rw [testBit_interval150, decide_eq_true_eq]; exact hq)
  have hsm2 := ready_of_checkMask150 storePart2_150 uMk 0 (GateMirror.interval 1559 39) tail150_checks.2.2.2.1 hmaskSM2
  have hsm_split : leaveStoreMapped150 = storePart1_150 ++ ([.make 1556 1557 1558] ++ storePart2_150) := by
    simp only [leaveStoreMapped150, storePart1_150, storePart1Mid150, storePart2_150, List.append_assoc, List.cons_append, List.nil_append]
  have hsm_ready : Ready uLR leaveStoreMapped150 := by
    rw [hsm_split]; exact ready_append _ _ _ hsm1.1 (ready_append _ _ _ hmake hsm2.1)
  have hw := whole150_result s [] z g0 s0 h nextSmall20
  have huBS_eq : run (GateMirror.forward leaveStoreMapped150) [] uLR = run beforeStore150Prog [] s := by
    have hfull : uLR = run (full150Prog ++ releaseMaskP150) [] s := by
      simp only [uLR, huH_eq, full150Prog, hlr_prog, run_append, run_take, List.drop_nil]
    rw [hfull]; simp only [beforeStore150Prog, run_append, run_take, List.drop_nil]
  have hclean_lc : ∀ q, (q = 1556 ∨ (1559 ≤ q ∧ q ≤ 1562)) → (run (GateMirror.forward leaveStoreMapped150) [] uLR).basis q = false := by
    intro q hq; rw [huBS_eq]
    rcases hq with rfl | ⟨h1, h2⟩
    · exact hw.2.2.2.2.2.2.2.2.2.2.2.1
    · have hnotM : (q : Wire) ∉ smallM150 := by
        intro hm; obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi
        unfold Wire at *; omega
      rw [hw.2.2.2.2.2.2.2.2.2.2.2.2.1 q (by unfold Wire at *; omega) (by unfold Wire at *; omega)
          (by unfold Wire at *; omega) hnotM, hhead_prog,
        swap2St_other q (by unfold Wire at *; omega) (by unfold Wire at *; omega)
          (by unfold Wire at *; omega) (by unfold Wire at *; omega)]
      rw [show (q : Nat) = 1559 + ((q : Nat) - 1559) by unfold Wire at *; omega]
      exact hck.1 ⟨(q : Nat) - 1559, by unfold Wire at *; omega⟩
  have hlc_ready := (lowClose150_safe _ hclean_lc).1
  have hAfter_ready : Ready uB leaveAfter150To20 := by
    rw [hspAfter]
    exact ready_append _ _ _ (huB_eq ▸ vHead150.ready)
      (ready_append _ _ _ hlr.1 (ready_append _ _ _ hsm_ready hlc_ready))
  have hAfter_phys : ∀ g ∈ leaveAfter150To20, proper g = true := fun g hg =>
    List.all_eq_true.mp tail150_checks.2.2.2.2 g hg
  have hAfter_phase : ∀ t, (run (GateMirror.forward leaveAfter150To20) t uB).phase = uB.phase := by
    intro t
    have hpre_ph : uB.phase = s.phase := by
      rw [huB_eq]; exact GateMirror.no_phase _ s
    have hlen : (List.replicate (measurementCount (GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false)) false).length =
        measurementCount (GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false) := List.length_replicate
    let t0 := List.replicate (measurementCount (GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false)) false
    have hw_ph := (whole150_result s (t0 ++ t) z g0 s0 h nextSmall20).1
    unfold leave150To20 at hw_ph
    rw [run_append, run_take, show (t0 ++ t).drop (measurementCount (GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false)) = t by
      rw [← hlen, List.drop_left]] at hw_ph
    have hrun_uB : run (GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false) (t0 ++ t) s = uB := by
      rw [run_append, run_take, hb, sameB]
      show _ = run (GateMirror.forward (Shadow7.leaveBarrel 150)) [] uA
      rw [huA]
    rw [hrun_uB] at hw_ph
    exact hw_ph.trans hpre_ph.symm
  rw [← huB_eq]
  exact ⟨hAfter_phys, all_prepared _ uB hAfter_phys hAfter_phase, hAfter_ready⟩

attribute [local irreducible] run SkywalkNat.step Shadow.far CRTBarrel.barrel GateMirror.forward inverse
  leave150To20 leaveInv150To20 leaveAfter150To20 in
theorem leave150To20_roundtrip (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) (m n : List Bool) :
    run leaveInv150To20 n (run leave150To20 m s) = s := by
  obtain ⟨sameB, backB⟩ := CRTBarrel.LeaveCut.barrel_pair MixedWindow.j7 (by decide) (by decide)
    _ (CRTBarrel.LeaveCut.input (by decide) (by decide) h)
  rw [show start MixedWindow.j7 = 150 from rfl] at sameB backB
  have hb := before150_state s z g0 s0 h
  have hAfter_valid : CRTBarrel.LeaveSplice.Valid
      (run (GateMirror.forward (Shadow7.leaveBarrel 150)) [] (run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s))
      leaveAfter150To20 := by
    have v := leaveAfter150_valid s z g0 s0 h nextSmall20
    rw [forward_app, run_append, run_take, List.drop_nil, hb []] at v
    exact v
  unfold leave150To20 leaveInv150To20
  simp only [run_append, run_take]
  rw [hb, sameB, hAfter_valid.undo_run, backB, ← hb []]
  exact before150_undo s z g0 s0 h _


/-! ### Section 4 (Stage 6B3): `leave150To20Red_pair`, `leave150To20Red_keeps`, `leave150To20Red_keeps_mirror` -/

section LeaveRed150Proofs

open CRTBarrel.LeaveSplice CRTBarrel.FlagCut CRTBarrel.FlagCut4 CRTBarrel.FlagCut6

private theorem columnsP150_snoc :
    columnsP150 = colsC150 ++ [⟨false, none, Shadow7.a0P 150 - 1 + 16, Shadow7.bankW 150 16⟩] := rfl

private theorem leaveAfter150_split4 :
    let top := Shadow7.a0P 150 + lows150 - 2
    leaveAfter150To20 = tailD0_150 ++ (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
      (tailD1_150 ++ ([.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++ (tailE0_150 ++
        ([.make 1558 top 1559] ++ (chainMid150 ++ ([.pop 1558 top 1559] ++ tailE1_150))))))) := by
  have hw : wordGM 1614 columnsP150 = CRTBarrel.wordPre 1614 colsC150 ++
      (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++ CRTBarrel.wordPost 1614 colsC150) := by
    rw [columnsP150_snoc]
    exact CRTWindow.wordGM_snoc 1614 ⟨false, none, Shadow7.a0P 150 - 1 + 16, Shadow7.bankW 150 16⟩ rfl colsC150
  have hsw0 : Shadow7.storeW 150 0 = 1558 := by decide
  have hsw1 : Shadow7.storeW 150 1 = 1559 := by decide
  have hch : chainG (Shadow7.storeW 150)
      (fun i => if i = 0 then Shadow7.a0P 150 + lows150 - 2 else Shadow7.bankW 150 (lows150 + i - 1))
      [.cx (Shadow7.storeW 150 (Shadow7.liveW 150 - lows150 + 1)) 1557, .x 1557] 0 (Shadow7.liveW 150 - lows150 + 1) =
      [.make 1558 (Shadow7.a0P 150 + lows150 - 2) 1559] ++
        (chainMid150 ++ [.pop 1558 (Shadow7.a0P 150 + lows150 - 2) 1559]) := by
    simp only [chainG, chainMid150, hsw0, hsw1, Nat.zero_add, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append]
  unfold leaveAfter150To20 leaveJoinMove150 leaveLowStore150 leaveStoreMapped150
    tailD0_150 tailD1_150 tailE0_150 lowRest150_pub storeHead150 tailE1_150
  dsimp only
  rw [hw, hch]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- `CRTBarrel.beforeReference` around its flag make (`leaveFix3`'s first gate). -/
private theorem ref150_split_flag :
    CRTBarrel.beforeReference 150 = LeaveJ7.entryOps 150 ++
      ([.make (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559] ++
        (([.cx (Shadow7.sbP 150 + 1577) 1560, .cx 1559 1560] ++ leaveFix4 150 (Shadow7.sbP 150) ++
          Shadow7.leaveFix5Move 150 (Shadow7.sbP 150)) ++ Shadow7.leaveAdjust 150)) := by
  unfold CRTBarrel.beforeReference LeaveJ7.entryOps leaveFix3
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem red150_targets :
    ([Gate.make (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559, Gate.cx (Shadow7.sbP 150 + 1577) 1560,
      Gate.cx 1559 1560] ++ leaveFix4 150 (Shadow7.sbP 150) ++ Shadow7.leaveFix5Move 150 (Shadow7.sbP 150) ++
      Shadow7.leaveAdjust 150 ++ Shadow7.leaveBarrel 150 ++ tailD0_150).all
      (fun g => decide (GateMirror.target g ≠ Shadow7.a0P 150 - 1 + 16)) = true ∧
    (LeaveJ7.entryOps 150).all
      (fun g => decide (GateMirror.target g ≠ Shadow7.sbP 150 + 1577 ∧ GateMirror.target g ≠ Shadow7.sbP 150 + 1578)) = true ∧
    ([Gate.cx (Shadow7.sbP 150 + 1577) 1560, Gate.cx 1559 1560] ++ leaveFix4 150 (Shadow7.sbP 150) ++
      Shadow7.leaveFix5Move 150 (Shadow7.sbP 150) ++ Shadow7.leaveAdjust 150 ++ Shadow7.leaveBarrel 150 ++
      tailD0_150 ++ pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++ tailD1_150).all
      (fun g => decide (GateMirror.target g ≠ 1559 ∧ GateMirror.target g ≠ Shadow7.e0P 150 + 4)) = true ∧
    (storeHead150.drop 1).all (fun g => decide (GateMirror.target g ≠ 1558)) = true ∧
    chainMid150.all (fun g => decide (GateMirror.target g ≠ 1558)) = true ∧
    Shadow7.sbP 150 + 1578 = Shadow7.e0P 150 + 4 ∧ Shadow7.sbP 150 + 1577 = Shadow7.e0P 150 + 3 := by
  decide +kernel

private theorem lowRest150_1558 (t : State) :
    (run (GateMirror.forward lowRest150_pub) [] t).basis 1558 = false := by
  obtain ⟨X, hX⟩ : ∃ X, lowRest150_pub =
      X ++ [.pop (Shadow7.b0P 150 - 1) 1557 1558, .cx (Shadow7.a0P 150 - 1) 1557, .x 1557] := ⟨_, rfl⟩
  rw [hX, run_nil_append]
  generalize run (GateMirror.forward X) [] t = u
  obtain ⟨ph, f⟩ := u
  simp [GateMirror.forward, front, GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit,
    Function.update_apply]

private theorem red150_box2 :
    (CRTBarrel.before 150).all (fun g => g.wires.all fun q =>
      decide ((166 ≤ (q : Nat) ∧ (q : Nat) ≤ 180) ∨
        (Shadow7.a0P 150 - 1 ≤ (q : Nat) ∧ (q : Nat) ≤ Shadow7.a0P 150 + 15) ∨
        (Shadow7.b0P 150 - 1 ≤ (q : Nat) ∧ (q : Nat) ≤ bTopP 150) ∨
        (1194 ≤ (q : Nat) ∧ (q : Nat) ≤ 1208) ∨
        (1556 ≤ (q : Nat) ∧ (q : Nat) ≤ 1812))) = true ∧
    (CRTBarrel.before 150).all (fun g => g.wires.all fun q => decide ((q : Nat) + 150 ≤ 2069)) = true ∧
    afterRow150.all (fun g => g.wires.all fun q =>
      decide ((166 ≤ (q : Nat) ∧ (q : Nat) ≤ 180) ∨
        (Shadow7.a0P 150 - 1 ≤ (q : Nat) ∧ (q : Nat) ≤ Shadow7.a0P 150 + 15) ∨
        (Shadow7.b0P 150 - 1 ≤ (q : Nat) ∧ (q : Nat) ≤ bTopP 150) ∨
        (1194 ≤ (q : Nat) ∧ (q : Nat) ≤ 1208) ∨
        (1556 ≤ (q : Nat) ∧ (q : Nat) ≤ 1812))) = true ∧
    afterRow150.all (fun g => g.wires.all fun q => decide ((q : Nat) + 150 ≤ 2069)) = true := by
  decide +kernel

private theorem red150_1558_make (t : State) :
    (run (GateMirror.forward tailE0_150) [] t).basis 1558 = true := by
  have hrt := red150_targets
  have he : storeHead150 = [.x 1558] ++ storeHead150.drop 1 := rfl
  rw [tailE0_150, run_nil_append, he, run_nil_append,
      keeps_of_targets _ _ (fun g hg => of_decide_eq_true (List.all_eq_true.mp hrt.2.2.2.1 g hg))]
  have hz := lowRest150_1558 t
  generalize run (GateMirror.forward lowRest150_pub) [] t = w at hz ⊢
  obtain ⟨ph, f⟩ := w; simp only at hz
  simp [GateMirror.forward, front, run, writeBit, Function.update_apply, hz]

private theorem red150_aft_fprog :
    let top : Wire := Shadow7.a0P 150 + lows150 - 2
    GateMirror.forward afterRow150 =
      GateMirror.forward tailD0_150 ++ [] ++ GateMirror.forward tailD1_150 ++
      [.CX (Shadow7.e0P 150 + 4) 1559] ++ GateMirror.forward tailE0_150 ++ [.CX top 1559] ++
      GateMirror.forward chainMid150 ++ [.CX top 1559] ++ GateMirror.forward tailE1_150 := by
  simp only [afterRow150, forward_app, fwd_cons, front, List.append_assoc, List.cons_append, List.nil_append,
    List.append_nil]

private theorem red150_aft_rprog :
    let top : Wire := Shadow7.a0P 150 + lows150 - 2
    inverse afterRow150 =
      inverse tailE1_150 ++ [.CX top 1559] ++ inverse chainMid150 ++ [.CX top 1559] ++
      inverse tailE0_150 ++ [.CX (Shadow7.e0P 150 + 4) 1559] ++ inverse tailD1_150 ++ [] ++
      inverse tailD0_150 := by
  simp only [afterRow150, inv_app, inv_cons, GateMirror.back, List.append_assoc, List.cons_append, List.nil_append,
    List.append_nil]

private theorem red150_run_nil_any (t : List Bool) (u : State) : run [] t u = u := rfl

attribute [local irreducible] run SkywalkNat.step Shadow.far CRTBarrel.barrel CRTBarrel.before
  CRTBarrel.beforeReference LeaveJ7.entryOps leaveFix4 Shadow7.leaveFix5Move Shadow7.leaveAdjust
  Shadow7.leaveBarrel leaveAfter150To20 afterRow150 tailD0_150 tailD1_150 tailE0_150 chainMid150 tailE1_150 pairGM in
theorem leave150To20Red_pair (s : State) (z : SkywalkNat.State) (g0 s0 : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z g0 s0)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) :
    (∀ m, run leave150To20Red m s = run leave150To20 m s) ∧
    (∀ m n, run leaveInv150To20Red n (run leave150To20Red m s) = s) := by
  have vMov := CRTBarrel.LeaveSplice.moved_valid (j := MixedWindow.j7) (by decide) (by decide) h
  rw [show start MixedWindow.j7 = 150 from rfl, CRTBarrel.LeaveCut.move_shape] at vMov
  obtain ⟨vRef, _⟩ := vMov.parts
  obtain ⟨sameB, backB⟩ := CRTBarrel.LeaveCut.barrel_pair MixedWindow.j7 (by decide) (by decide)
    _ (CRTBarrel.LeaveCut.input (by decide) (by decide) h)
  rw [show start MixedWindow.j7 = 150 from rfl] at sameB backB
  have hrt := red150_targets
  -- the shared before part: the reduced `CRTBarrel.before 150` runs as the reference on admitted inputs
  let uA := run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s
  have hbef (m : List Bool) : run (GateMirror.forward (CRTBarrel.before 150)) m s = uA :=
    before150_state s z g0 s0 h m
  let uB := run (GateMirror.forward (Shadow7.leaveBarrel 150)) [] uA
  have huB_eq : uB = run (GateMirror.forward (CRTBarrel.before 150 ++ Shadow7.leaveBarrel 150)) [] s := by
    simp only [uB, forward_app, run_append, run_take, List.drop_nil, hbef]
  have vAft : Valid uB leaveAfter150To20 := huB_eq ▸ leaveAfter150_valid s z g0 s0 h nextSmall20
  let top : Wire := Shadow7.a0P 150 + lows150 - 2
  -- 1. the high column (16) of the join word is idle: its shadow is clear after the entry
  have huB_a16 : (run (GateMirror.forward tailD0_150) [] uB).basis (Shadow7.a0P 150 - 1 + 16) = false := by
    have e0 := DeadJoin.entry_top_zero (j := MixedWindow.j7) (by decide) h
    rw [show start MixedWindow.j7 = 150 from rfl] at e0
    have kR : ∀ g ∈ [Gate.make (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559,
        Gate.cx (Shadow7.sbP 150 + 1577) 1560, Gate.cx 1559 1560] ++ leaveFix4 150 (Shadow7.sbP 150) ++
        Shadow7.leaveFix5Move 150 (Shadow7.sbP 150) ++ Shadow7.leaveAdjust 150 ++ Shadow7.leaveBarrel 150 ++
        tailD0_150, GateMirror.target g ≠ Shadow7.a0P 150 - 1 + 16 :=
      fun g hg => of_decide_eq_true (List.all_eq_true.mp hrt.1 g hg)
    have hsplit : CRTBarrel.beforeReference 150 ++ (Shadow7.leaveBarrel 150 ++ tailD0_150) =
        LeaveJ7.entryOps 150 ++ (([Gate.make (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559,
          Gate.cx (Shadow7.sbP 150 + 1577) 1560, Gate.cx 1559 1560] ++ leaveFix4 150 (Shadow7.sbP 150) ++
          Shadow7.leaveFix5Move 150 (Shadow7.sbP 150) ++ Shadow7.leaveAdjust 150 ++ Shadow7.leaveBarrel 150 ++
          tailD0_150)) := by
      rw [ref150_split_flag]; simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hrun : run (GateMirror.forward tailD0_150) [] uB =
        run (GateMirror.forward (CRTBarrel.beforeReference 150 ++ (Shadow7.leaveBarrel 150 ++ tailD0_150))) [] s := by
      simp only [uB, uA, forward_app, run_append, run_take, List.drop_nil]
    rw [hrun, hsplit, run_nil_append, keeps_of_targets _ _ kR]
    exact e0
  -- 2. the flag 1559 equals the side flag `e0P + 4` before the after-part pop
  have hv1559 :
      let uMid := run (GateMirror.forward (tailD0_150 ++
        (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++ tailD1_150))) [] uB
      uMid.basis 1559 = uMid.basis (Shadow7.e0P 150 + 4) := by
    have vFl : Valid s (LeaveJ7.entryOps 150 ++
        ([.make (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559] ++
          (([.cx (Shadow7.sbP 150 + 1577) 1560, .cx 1559 1560] ++ leaveFix4 150 (Shadow7.sbP 150) ++
            Shadow7.leaveFix5Move 150 (Shadow7.sbP 150)) ++ Shadow7.leaveAdjust 150))) := ref150_split_flag ▸ vRef
    have imp0 : s.basis (Shadow7.sbP 150 + 1578) = true → s.basis (Shadow7.sbP 150 + 1577) = true := by
      have hf := h.far; have hs := h.side
      rw [show start MixedWindow.j7 = 150 from rfl] at hf hs
      rw [hrt.2.2.2.2.2.1, hrt.2.2.2.2.2.2, hs, hf]
      intro h'; exact ((Bool.and_eq_true _ _).mp h').1
    have imp1 : (run (GateMirror.forward (LeaveJ7.entryOps 150)) [] s).basis (Shadow7.sbP 150 + 1578) = true →
        (run (GateMirror.forward (LeaveJ7.entryOps 150)) [] s).basis (Shadow7.sbP 150 + 1577) = true := by
      rw [keeps_of_targets _ _ (fun g hg => (of_decide_eq_true (List.all_eq_true.mp hrt.2.1 g hg)).2),
          keeps_of_targets _ _ (fun g hg => (of_decide_eq_true (List.all_eq_true.mp hrt.2.1 g hg)).1)]
      exact imp0
    have hmk := make_flag (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559 _
      vFl.parts.2.parts.1.ready.1 (by decide) imp1
    have hkeep (q : Wire) (hq : q = 1559 ∨ q = Shadow7.e0P 150 + 4) :
        (run (GateMirror.forward (tailD0_150 ++
          (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++ tailD1_150))) [] uB).basis q =
        (run (GateMirror.forward [.make (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559]) []
          (run (GateMirror.forward (LeaveJ7.entryOps 150)) [] s)).basis q := by
      have kA : ∀ g ∈ [Gate.cx (Shadow7.sbP 150 + 1577) 1560, Gate.cx 1559 1560] ++ leaveFix4 150 (Shadow7.sbP 150) ++
          Shadow7.leaveFix5Move 150 (Shadow7.sbP 150) ++ Shadow7.leaveAdjust 150 ++ Shadow7.leaveBarrel 150 ++
          tailD0_150 ++ pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++ tailD1_150,
          GateMirror.target g ≠ q := fun g hg => by
        have ht := of_decide_eq_true (List.all_eq_true.mp hrt.2.2.1 g hg)
        rcases hq with rfl | rfl; exact ht.1; exact ht.2
      have hrun : run (GateMirror.forward (tailD0_150 ++
          (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++ tailD1_150))) [] uB =
          run (GateMirror.forward ([Gate.cx (Shadow7.sbP 150 + 1577) 1560, Gate.cx 1559 1560] ++
            leaveFix4 150 (Shadow7.sbP 150) ++ Shadow7.leaveFix5Move 150 (Shadow7.sbP 150) ++ Shadow7.leaveAdjust 150 ++
            Shadow7.leaveBarrel 150 ++ tailD0_150 ++
            pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++ tailD1_150)) []
            (run (GateMirror.forward [.make (Shadow7.sbP 150 + 1577) (Shadow7.sbP 150 + 1578) 1559]) []
              (run (GateMirror.forward (LeaveJ7.entryOps 150)) [] s)) := by
        simp only [uB, uA, ref150_split_flag, forward_app, run_append, run_take, List.drop_nil, List.append_assoc]
      rw [hrun, keeps_of_targets _ q kA]
    dsimp only
    rw [hkeep 1559 (Or.inl rfl), hkeep (Shadow7.e0P 150 + 4) (Or.inr rfl), ← hrt.2.2.2.2.2.1]
    exact hmk
  -- 3. the chain head 1558 is set at the store's make and pop
  have vAft4 : Valid uB (tailD0_150 ++ (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
      (tailD1_150 ++ ([.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++ (tailE0_150 ++
        ([.make 1558 top 1559] ++ (chainMid150 ++ ([.pop 1558 top 1559] ++ tailE1_150)))))))) :=
    leaveAfter150_split4 ▸ vAft
  have h1558_M : (run (GateMirror.forward (tailD0_150 ++
      (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
      (tailD1_150 ++ ([.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++ tailE0_150))))) [] uB).basis 1558 = true := by
    simp only [run_nil_append]; exact red150_1558_make _
  have h1558_P : (run (GateMirror.forward (tailD0_150 ++
      (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
      (tailD1_150 ++ ([.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++ (tailE0_150 ++
        ([.make 1558 top 1559] ++ chainMid150))))))) [] uB).basis 1558 = true := by
    simp only [run_nil_append]
    rw [keeps_of_targets _ _ (fun g hg => of_decide_eq_true (List.all_eq_true.mp hrt.2.2.2.2.1 g hg)),
        keeps_of_targets [.make 1558 top 1559] 1558 (fun g hg => by simp at hg; subst hg; simp [GateMirror.target])]
    exact red150_1558_make _
  have hvPop59 :
      let uP := run (GateMirror.forward (tailD0_150 ++
        (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
        (tailD1_150 ++ ([.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++ (tailE0_150 ++
          ([.make 1558 top 1559] ++ chainMid150))))))) [] uB
      uP.basis 1559 = uP.basis top := by
    have vP : Valid uB ((tailD0_150 ++ (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16) ++
        (tailD1_150 ++ ([.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559] ++ (tailE0_150 ++
          ([.make 1558 top 1559] ++ chainMid150)))))) ++ ([.pop 1558 top 1559] ++ tailE1_150)) := by
      simpa only [List.append_assoc] using vAft4
    have val := vP.parts.2.parts.1.prepared.1
    simp only [GateMirror.ValueOK] at val
    dsimp only; rw [val, h1558_P, Bool.true_and]
  -- 4. the four after-part cuts
  have haft_rep := replace4
    tailD0_150 (pairGM false 1614 (Shadow7.a0P 150 - 1 + 16) (Shadow7.bankW 150 16))
    tailD1_150 [.pop (Shadow7.e0P 150 + 3) (Shadow7.e0P 150 + 4) 1559]
    tailE0_150 [.make 1558 top 1559]
    chainMid150 [.pop 1558 top 1559]
    tailE1_150
    [] []
    [.CX (Shadow7.e0P 150 + 4) 1559] [.CX (Shadow7.e0P 150 + 4) 1559]
    [.CX top 1559] [.CX top 1559]
    [.CX top 1559] [.CX top 1559]
    uB vAft4
    (fun t => (red150_run_nil_any t _).trans (pair_high_id 1614 _ _ _ (by decide) huB_a16).symm)
    (fun t => (red150_run_nil_any t _).trans (pair_high_id 1614 _ _ _ (by decide) huB_a16))
    (fun t => erase_cx _ _ _ _ hv1559 t)
    (fun t => erase_cx_back _ _ _ _ (by decide) hv1559 t)
    (fun t => ccx_cx 1558 top 1559 _ (fun _ => h1558_M) t)
    (fun t => ccx_cx_back 1558 top 1559 _ (by decide) (fun _ => h1558_M) t)
    (fun t => erase_cx 1558 top 1559 _ hvPop59 t)
    (fun t => erase_cx_back 1558 top 1559 _ (by decide) hvPop59 t)
  have haft_fwd (m : List Bool) : run (GateMirror.forward afterRow150) m uB =
      run (GateMirror.forward leaveAfter150To20) [] uB := by
    rw [red150_aft_fprog, haft_rep.1 m, ← leaveAfter150_split4]; exact vAft.default_run m
  have haft_rev (n : List Bool) :
      run (inverse afterRow150) n (run (GateMirror.forward leaveAfter150To20) [] uB) = uB := by
    rw [← haft_fwd [], red150_aft_rprog, red150_aft_fprog]; exact haft_rep.2 [] n
  -- 5. compose the shared before, the barrel and the two after parts
  have hred_eq (m : List Bool) : run leave150To20Red m s = run (GateMirror.forward leaveAfter150To20) [] uB := by
    unfold leave150To20Red; simp only [run_append, run_take]
    rw [hbef, sameB, haft_fwd]
  have hold_eq (m : List Bool) : run leave150To20 m s = run (GateMirror.forward leaveAfter150To20) [] uB := by
    unfold leave150To20; simp only [run_append, run_take]
    rw [hbef, sameB, vAft.default_run]
  refine ⟨fun m => (hred_eq m).trans (hold_eq m).symm, fun m n => ?_⟩
  rw [hred_eq m]
  unfold leaveInv150To20Red; simp only [run_append, run_take]
  rw [haft_rev, backB]
  rw [show run (GateMirror.forward (CRTBarrel.beforeReference 150)) [] s =
      run (GateMirror.forward (CRTBarrel.before 150)) [] s from (hbef []).symm]
  exact before150_undo s z g0 s0 h _

attribute [local irreducible] run CRTBarrel.barrel in
theorem leave150To20Red_keeps (q : Wire) (hq : ¬ Shadow7.leaveBox2 150 q) (m : List Bool) (s : State) :
    (run leave150To20Red m s).basis q = s.basis q := by
  obtain ⟨ha0, hb0, hbt, hr0, hr14, hwp⟩ := box2_150_consts
  have hb := red150_box2
  refine run_preserves_outside leave150To20Red m s q (fun hm => hq ?_)
  unfold leave150To20Red at hm; simp only [wires_append, Finset.mem_union] at hm
  rcases hm with (h | h) | h
  · have hall : AllW (fun w => Shadow7.leaveBox2 150 w) (CRTBarrel.before 150) := fun g hg w hw => by
      have h' := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hb.1 g hg) w hw)
      unfold Shadow7.leaveBox2; rw [show 150 + 14 = 164 from rfl, hr14, hr0, ha0, hb0, hwp]
      rw [ha0, hb0, hbt] at h'; unfold Wire at *; omega
    exact (allW_programs hall).1 q h
  · exact CRTWindow.barrel_box2 MixedWindow.j7 (by decide) (by decide) false q h
  · have hall : AllW (fun w => Shadow7.leaveBox2 150 w) afterRow150 := fun g hg w hw => by
      have h' := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hb.2.2.1 g hg) w hw)
      unfold Shadow7.leaveBox2; rw [show 150 + 14 = 164 from rfl, hr14, hr0, ha0, hb0, hwp]
      rw [ha0, hb0, hbt] at h'; unfold Wire at *; omega
    exact (allW_programs hall).1 q h

attribute [local irreducible] run CRTBarrel.barrel in
theorem leave150To20Red_keeps_mirror (q : Wire) (lo : 2070 ≤ (q : Nat) + 150) (m : List Bool) (s : State) :
    (run leave150To20Red m s).basis q = s.basis q := by
  obtain ⟨ha0, hb0, hbt, hr0, hr14, hwp⟩ := box2_150_consts
  have hb := red150_box2
  refine run_preserves_outside leave150To20Red m s q (fun hm => ?_)
  have hle : (q : Nat) + 150 ≤ 2069 := by
    unfold leave150To20Red at hm; simp only [wires_append, Finset.mem_union] at hm
    rcases hm with (h | h) | h
    · have hall : AllW (fun w => (w : Nat) + 150 ≤ 2069) (CRTBarrel.before 150) := fun g hg w hw =>
        of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hb.2.1 g hg) w hw)
      exact (allW_programs hall).1 q h
    · have hbox := CRTWindow.barrel_box2 MixedWindow.j7 (by decide) (by decide) false q h
      unfold Shadow7.leaveBox2 at hbox
      rw [show start MixedWindow.j7 = 150 from rfl, show 150 + 14 = 164 from rfl, hr14, hr0] at hbox
      unfold Wire at *; omega
    · have hall : AllW (fun w => (w : Nat) + 150 ≤ 2069) afterRow150 := fun g hg w hw =>
        of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hb.2.2.2 g hg) w hw)
      exact (allW_programs hall).1 q h
  unfold Wire at *; omega

end LeaveRed150Proofs

end ECDSAAdd.Entrant.StairPacket.Shadow20.Trans150
end
-- ==== end Shadow7Wide20Trans150 ====

-- ==== begin Shadow7Wide20End150 ====
section

/-!
# Transition Block `s = 150 -> 165` Endpoint & Mixed Window Slot Bounds (`Shadow7Wide20End150`)
-/

namespace ECDSAAdd.Entrant.StairPacket.Shadow20.Trans150

open ECDSAAdd.Arithmetic
open ECDSAAdd.Arithmetic.MappedCompressed
open ECDSAAdd.Challenge
open ECDSAAdd.Entrant.IntegerPacket
open ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.GateMirror
open ECDSAAdd.Entrant.StairPacket.PortalAnd
open ECDSAAdd.Entrant.StairPacket.RailPair
open ECDSAAdd.Entrant.StairPacket.Shadow
open ECDSAAdd.Entrant.StairPacket.WideReference
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.LeaveCut20
open SkywalkNat IntegerHigh

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Section 4: `endpoint150To20` -/

private theorem swaps150_entry_no_target :
    (LeaveJ7.entryOps 150).all (fun g => decide (¬ (1194 ≤ (GateMirror.target g : Nat) ∧ (GateMirror.target g : Nat) ≤ 1208))) = true := by
  decide +kernel

private theorem swaps150_away :
    ∀ i : Fin 15,
      (1194 + i.val : Wire) ≠ Shadow7.e0P 150 + 4 ∧
      (1194 + i.val : Wire) ∉ RailPair.sites low150 ∧
      (1194 + i.val : Wire) ∉ LeaveJ7.history MixedWindow.j7 ∧
      (1194 + i.val : Wire) ∉ smallM150 := by
  decide +kernel

attribute [local irreducible] run SkywalkNat.step Shadow.far GateMirror.forward leave150To20 beforeStore150Prog storeMapped150Prog head150Prog in
private theorem swaps150_kept (s : State) (m : List Bool) (z : SkywalkNat.State) (G S : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z G S)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) (i : Fin 15) :
    (run leave150To20 m s).basis (1194 + i.val) = s.basis (1194 + i.val) := by
  have hi := i.isLt
  have w := whole150_result s m z G S h nextSmall20
  have hhead := (leaveMove150_head_eq s z G S h).2 m
  have hhst_eq : run head150Prog m s = swap2St (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s) := by
    unfold head150Prog; exact hhead
  have hsrc : LeaveRelocation.source movesP150Lit (1194 + i.val) = 1194 + i.val := by
    unfold movesP150Lit
    rw [LeaveRelocation.append, src150_flags_out _ (by unfold Wire; omega),
      src150_bank_out _ (Or.inr (Or.inl ⟨by unfold Wire; omega, by unfold Wire; omega⟩))]
  have haw := swaps150_away i
  rw [w.2.2.2.2.2.2.2.2.2.2.1 _, movesP150_eq, hsrc]
  simp only [writeBit, Function.update_of_ne haw.1]
  rw [w.2.2.2.2.2.2.2.2.2.2.2.2.2 _ haw.2.1 haw.2.2.1,
    w.2.2.2.2.2.2.2.2.2.2.2.2.1 (1194 + i.val) (by omega) (by omega) (by omega) haw.2.2.2,
    hhst_eq, swap2St_other (1194 + i.val) (by omega) (by omega) (by omega) (by omega)]
  have hst_eq : run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s =
      run (GateMirror.forward (LeaveJ7.bodyOps MixedWindow.j7)) []
        (run (GateMirror.forward (LeaveJ7.entryOps 150)) [] s) := by
    rw [show Shadow7.leaveHeadOps 150 = LeaveJ7.entryOps 150 ++ LeaveJ7.bodyOps MixedWindow.j7 from
        (LeaveJ7.head_eq MixedWindow.j7).symm, forward_app, run_append, run_take, List.drop_nil]
  rw [hst_eq]
  have hnm : ¬ LeaveJ7.midT MixedWindow.j7 (1194 + i.val) := by
    unfold LeaveJ7.midT LeaveJ7.workT
    rw [show start MixedWindow.j7 = 150 from rfl, show Shadow7.a0P 150 = 355 by decide,
      show Shadow7.b0P 150 = 960 by decide, show Shadow7.e0P 150 = 1747 by decide]
    omega
  rw [LeaveReadoutFrame.preserved _ _ _ _ (fun hit => hnm (LeaveJ7.body_dest MixedWindow.j7 (by decide) (by decide) _ hit))]
  refine LeaveReadoutFrame.preserved _ _ _ _ (fun hit => ?_)
  rw [forward_map_dest] at hit; obtain ⟨g, hg, e⟩ := List.mem_map.mp hit
  have ht := of_decide_eq_true (List.all_eq_true.mp swaps150_entry_no_target g hg)
  rw [e] at ht; unfold Wire at ht; omega

private theorem readCells_congr (sh : IntegerPacket.Shape) (b1 b2 : BasisState) :
    ∀ a n, (∀ k, a ≤ k → k < a + n → IntegerPacket.cell sh k b1 = IntegerPacket.cell sh k b2) →
      IntegerPacket.readCells sh a n b1 = IntegerPacket.readCells sh a n b2
  | _, 0, _ => rfl
  | a, n + 1, h => by
    simp only [IntegerPacket.readCells, h a (Nat.le_refl _) (by omega),
      readCells_congr sh b1 b2 (a + 1) n (fun k h1 h2 => h k (by omega) (by omega))]

private theorem physicalCells150_eq (s t : State)
    (ha : ∀ i : Fin 15, t.basis (166 + i.val) = s.basis (166 + i.val))
    (hs : ∀ i : Fin 15, t.basis (1194 + i.val) = s.basis (1194 + i.val)) :
    Shadow7.physicalCells MixedWindow.j7 t = Shadow7.physicalCells MixedWindow.j7 s := by
  apply readCells_congr
  intro k _ hk
  have hgeo : windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) k).a0 = 166 + k ∧
      windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) k).history = 1194 + k := by
    constructor
    · show OB5.sig 164 (150 + k + 16) = 166 + k
      unfold OB5.sig; rw [if_neg (by unfold Wire; omega)]; unfold Wire; omega
    · show OB5.sig 164 (150 + k + 16 + 1028) = 1194 + k
      unfold OB5.sig; rw [if_neg (by unfold Wire; omega)]; unfold Wire; omega
  unfold IntegerPacket.cell mappedBasis
  rw [hgeo.1, hgeo.2, ha ⟨k, by omega⟩, hs ⟨k, by omega⟩]

private theorem archive150_flag_ports :
    Archive150.rawPorts 20 = e0P20 165 + 6 ∧
    Archive150.rawPorts 21 = e0P20 165 + 7 ∧
    Archive150.rawPorts 22 = e0P20 165 + 8 := by
  decide +kernel

theorem archiveCut150To20 (s : State) (m : List Bool) (z : SkywalkNat.State) (G S : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z G S)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z)) :
    PastFacts MixedWindow.j7 Archive150.rawPorts (Shadow7.sbP 150) z G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d MixedWindow.j7 z)) (run leave150To20 m s) := by
  have w := whole150_result s m z G S h nextSmall20
  have hkept : Shadow7.physicalCells MixedWindow.j7 (run leave150To20 m s) =
      Shadow7.physicalCells MixedWindow.j7 s :=
    physicalCells150_eq s (run leave150To20 m s)
      (fun i => w.2.2.2.2.2.2.2.1 (166 + i.val) (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩))
      (fun i => swaps150_kept s m z G S h nextSmall20 i)
  have hrec : Shadow7.physicalCells MixedWindow.j7 (run leave150To20 m s) =
      SkywalkTrace.trace 15 (SkywalkRails.encode G S z.u z.v) := hkept.trans h.record
  have hfp := archive150_flag_ports
  refine ⟨hrec, ?_, ?_, ?_⟩
  · rw [hfp.1]; exact w.2.2.2.2.1
  · rw [hfp.2.1, ← Shadow7.physicalCells_eq, hrec, w.2.2.2.2.2.1]
    by_cases active : Shadow.far (Shadow7.sbP 150) 15 z
    · rw [LeaveJ7.Far.orient (Shadow7.sbP 150) z ⟨h.farSmall, h.endSmall⟩ active]
    · simp [active]
  · rw [hfp.2.2]; exact w.2.2.2.2.2.2.1

def zeros150 : List Nat :=
  List.range' 1556 (e0P20 165 + 3 - 1556) ++
  List.range' (e0P20 165 + 9) (1813 - (e0P20 165 + 9))

private theorem src150_flags_out_gen (q : Nat)
    (h57 : q ≠ 1557) (h58 : q ≠ 1558) (hfl : q < 1745 ∨ 1754 < q) :
    LeaveRelocation.source flagPairs150 q = q := by
  apply LeaveRelocation.outside; intro p hp
  simp only [flagPairs150, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by unfold Wire at *; omega, by unfold Wire at *; omega⟩

private theorem zeros150_active_class :
    ∀ q ∈ ([1556, 1557, 1558, 1751, 1752, 1753, 1754] ++ List.range' 1598 15 : List Nat),
      let r := LeaveRelocation.source movesP150Lit q
      r = Shadow7.e0P 150 + 4 ∨
      (r ≠ Shadow7.e0P 150 + 4 ∧ r ∉ RailPair.sites low150 ∧ r ∉ LeaveJ7.history MixedWindow.j7 ∧
        (r = 1556 ∨
         (r ≠ 1556 ∧ r ≠ 1557 ∧ r ≠ 1558 ∧ r ∉ smallM150 ∧
          ((r = 984 ∨ r = 985) ∨
           (r ≠ 364 ∧ r ≠ 984 ∧ r ≠ 365 ∧ r ≠ 985 ∧
            ((1559 ≤ r ∧ r < 1598) ∨ (1613 ≤ r ∧ r < Shadow7.e0P 150 + 3) ∨
             (Shadow7.e0P 150 + 8 ≤ r ∧ r < 1813) ∨
             (Shadow7.b0P 150 + 11 ≤ r ∧ r < Shadow7.b0P 150 + 24))))))) := by
  decide +kernel

private theorem zeros150_src_class :
    ∀ q ∈ zeros150,
      let r := LeaveRelocation.source movesP150Lit q
      r = Shadow7.e0P 150 + 4 ∨
      (r ≠ Shadow7.e0P 150 + 4 ∧ r ∉ RailPair.sites low150 ∧ r ∉ LeaveJ7.history MixedWindow.j7 ∧
        (r = 1556 ∨
         (r ≠ 1556 ∧ r ≠ 1557 ∧ r ≠ 1558 ∧ r ∉ smallM150 ∧
          ((r = 984 ∨ r = 985) ∨
           (r ≠ 364 ∧ r ≠ 984 ∧ r ≠ 365 ∧ r ≠ 985 ∧
            ((1559 ≤ r ∧ r < 1598) ∨ (1613 ≤ r ∧ r < Shadow7.e0P 150 + 3) ∨
             (Shadow7.e0P 150 + 8 ≤ r ∧ r < 1813) ∨
             (Shadow7.b0P 150 + 11 ≤ r ∧ r < Shadow7.b0P 150 + 24))))))) := by
  intro q hq
  by_cases hact : q ∈ ([1556, 1557, 1558, 1751, 1752, 1753, 1754] ++ List.range' 1598 15 : List Nat)
  · exact zeros150_active_class q hact
  · simp only [zeros150, show e0P20 165 = 1742 by decide, List.mem_append, List.mem_range'_1] at hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1, not_or, not_and] at hact
    have hsrc : LeaveRelocation.source movesP150Lit q = q := by
      unfold movesP150Lit
      rw [LeaveRelocation.append,
        src150_flags_out_gen q (by omega) (by omega) (by omega),
        src150_bank_out q (by change q < 971 ∨ (1043 < q ∧ q < 1598) ∨ 1612 < q; omega)]
    rw [hsrc]
    have hnotL : (q : Wire) ∉ RailPair.sites low150 := by
      intro hm; obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.mp hm; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      rw [List.mem_range] at hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hqp
      have hg : Shadow7.a0P 150 = 355 ∧ Shadow7.b0P 150 = 960 ∧ lows150 = 12 := by decide
      rcases hqp with e | e <;> (unfold Wire at *; omega)
    have hnotH : (q : Wire) ∉ LeaveJ7.history MixedWindow.j7 := by
      intro hm; unfold LeaveJ7.history at hm; rw [show start MixedWindow.j7 = 150 from rfl] at hm
      obtain ⟨i, hi, e⟩ := List.mem_map.mp hm; rw [List.mem_range] at hi; unfold Wire at *; omega
    have hnotM : (q : Wire) ∉ smallM150 := not_mem_smallM150 q (Or.inr (by change 972 ≤ q; omega))
    have he0 : Shadow7.e0P 150 = 1747 := by decide
    have hb0 : Shadow7.b0P 150 = 960 := by decide
    refine Or.inr ⟨by change q ≠ Shadow7.e0P 150 + 4; rw [he0]; omega, hnotL, hnotH,
      Or.inr ⟨by change q ≠ 1556; omega, by change q ≠ 1557; omega, by change q ≠ 1558; omega, hnotM,
        Or.inr ⟨by change q ≠ 364; omega, by change q ≠ 984; omega, by change q ≠ 365; omega, by change q ≠ 985; omega, ?_⟩⟩⟩
    rw [he0, hb0]; unfold Wire; omega

private theorem row150_free_vals :
    (LeaveJ7.row MixedWindow.j7 ⟨10, by decide⟩).free = 364 ∧
    (LeaveJ7.row MixedWindow.j7 ⟨11, by decide⟩).free = 365 ∧
    (∀ k : Fin 5, (LeaveJ7.row MixedWindow.j7 ⟨12 + k.val, by omega⟩).free = Shadow7.a0P 150 + 11 + k.val) := by
  have ha0 : Shadow7.a0P 150 = 355 := by decide
  have hlows : Shadow7.lowsP 150 = 10 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [LeaveJ7.row_free, if_neg (by decide), show start MixedWindow.j7 = 150 from rfl, ha0]
  · rw [LeaveJ7.row_free, if_neg (by decide), show start MixedWindow.j7 = 150 from rfl, ha0]
  · intro k; rw [LeaveJ7.row_free, if_neg (by rw [show start MixedWindow.j7 = 150 from rfl, hlows]; omega),
      show start MixedWindow.j7 = 150 from rfl, ha0]; simp only [Wire] at *; omega

private theorem upperA150_src :
    ∀ i : Fin 5,
      LeaveRelocation.source movesP150Lit (Shadow7.a0P 150 + 11 + i.val) = Shadow7.a0P 150 + 11 + i.val ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ Shadow7.e0P 150 + 4 ∧
      Shadow7.a0P 150 + 11 + i.val ∉ RailPair.sites low150 ∧
      Shadow7.a0P 150 + 11 + i.val ∉ LeaveJ7.history MixedWindow.j7 ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ 1556 ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ 1557 ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ 1558 ∧
      Shadow7.a0P 150 + 11 + i.val ∉ smallM150 ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ 364 ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ 984 ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ 365 ∧
      (Shadow7.a0P 150 + 11 + i.val : Wire) ≠ 985 := by
  intro i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (revert i; decide +kernel)

section Endpoint150

attribute [local irreducible] run SkywalkNat.step Shadow.far GateMirror.forward CRTBarrel.barrel
  Shadow7.leaveHeadOps leave150To20 leaveAfter150To20 beforeStore150Prog storeMapped150Prog head150Prog
  movesP150Lit movesP150To20 NativeJ7.nextWindow Shadow7.enterP Shadow7.body

private theorem boundaryClean150To20 (s : State) (m : List Bool) (z : SkywalkNat.State) (G S : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z G S)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z))
    (quiet : ∀ q ∈ LeaveJ7.CoreCheckpoint.rawSites MixedWindow.j7, s.basis q = false) :
    ∀ q ∈ zeros150, (run leave150To20 m s).basis q = false := by
  let u := LeaveJ7.Admission.flags z G S
  have w := whole150_result s m z G S h nextSmall20
  have par := LeaveJ7.RecordedParity.result MixedWindow.j7 (by decide) (by decide) s z G S ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP 150) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P 150 + 3)) (s.basis (Shadow7.e0P 150 + 4)) z.u := by
    have hf := h.far; have hs := h.side
    rw [show start MixedWindow.j7 = 150 from rfl] at hf hs
    rw [hf, hs]; exact LeaveTraceHistory.flags _ _
  have ev := LeaveJ7.RecordedEvents.result MixedWindow.j7 (by decide) (by decide) s z G S ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have hck := LeaveJ7.CoreCheckpoint.result MixedWindow.j7 (by decide) (by decide) s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2
    (LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) (by decide) s z G S ⟨h.farSmall, h.endSmall⟩
      h.odd h.record h.far h.side)
  have hhead := (leaveMove150_head_eq s z G S h).2 m
  have hhst_eq : run head150Prog m s = swap2St (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s) := by
    unfold head150Prog; exact hhead
  have hck_prog : LeaveJ7.CoreCheckpoint.program MixedWindow.j7 = GateMirror.forward (Shadow7.leaveHeadOps 150) := rfl
  rw [hck_prog] at hck
  intro q hq
  rw [w.2.2.2.2.2.2.2.2.2.2.1 q, movesP150_eq]
  rcases zeros150_src_class q hq with heq | ⟨hne4, hnl, hnh, hsrc⟩
  · rw [heq]; simp [writeBit]
  · simp only [writeBit, Function.update_of_ne hne4]
    rw [w.2.2.2.2.2.2.2.2.2.2.2.2.2 _ hnl hnh]
    rcases hsrc with h56 | ⟨hn56, hn57, hn58, hnM, h98 | ⟨h1, h2, h3, h4, hr⟩⟩
    · rw [h56]; exact w.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [w.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hn56 hn57 hn58 hnM, hhst_eq]
      rcases h98 with hA10 | hA11
      · rw [hA10, show (swap2St _).basis 984 = (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s).basis 364 by
          simp [swap2St, swap2, swap1]]
        rw [← row150_free_vals.1]; exact hck.2.1 ⟨10, by decide⟩
      · rw [hA11, show (swap2St _).basis 985 = (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s).basis 365 by
          simp [swap2St, swap2, swap1]]
        rw [← row150_free_vals.2.1]; exact hck.2.1 ⟨11, by decide⟩
    · rw [w.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hn56 hn57 hn58 hnM, hhst_eq, swap2St_other _ h1 h2 h3 h4]
      have hmem : LeaveRelocation.source movesP150Lit q ∈ LeaveJ7.CoreCheckpoint.targets MixedWindow.j7 :=
        LeaveJ7.BoundaryClean.mem_targets MixedWindow.j7 (by decide) (by decide) _ (by
          rw [show start MixedWindow.j7 = 150 from rfl, show Shadow7.lowsP 150 = 10 by decide]
          rcases hr with h | h | h | h
          · left; exact h
          · right; left; exact h
          · right; right; left; exact ⟨h.1, by simp only [Wire] at h ⊢; omega⟩
          · right; right; right; have hb960 : Shadow7.b0P 150 = 960 := by decide
            simp only [Wire] at h ⊢; omega)
      simp only [LeaveJ7.CoreCheckpoint.targets, List.mem_append, List.mem_range'_1, List.mem_map, List.mem_finRange, true_and] at hmem
      rcases hmem with ((⟨lo, hi⟩ | ⟨r, hrf⟩) | hraw) | hmag
      · rw [← Nat.add_sub_of_le lo]
        exact hck.1 ⟨_, Nat.sub_lt_left_of_lt_add lo hi⟩
      · rw [← hrf]; exact hck.2.1 r
      · exact (hck.2.2.1 _ hraw).trans (quiet _ hraw)
      · exact hck.2.2.2 _ hmag

private theorem boundaryRails150To20 (s : State) (m : List Bool) (z : SkywalkNat.State) (G S : Bool)
    (h : LeaveJ7.Admission.Inputs MixedWindow.j7 s z G S)
    (nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] z))
    (highZero : ∀ q : Nat, Shadow7.a0P 150 + 16 ≤ q → q ≤ 180 + railP 165 → s.basis q = false)
    (raw : State)
    (input : let a := step^[15] z
      let u := LeaveJ7.Admission.flags z G S
      SkywalkIntegerInput (LeaveJ7.WideWords.L MixedWindow.j7)
        (SkywalkRails.encode u.1 u.2 a.u a.v).a (SkywalkRails.encode u.1 u.2 a.u a.v).b u.1 raw.basis) :
    let o := pullState (OB5.sig 164) raw
    let out := run leave150To20 m s
    (∀ i : Fin (sbP20 165 + 22),
      out.basis (165 + 16 + i.val) = o.basis (165 + 16 + i.val) ∧
      out.basis (786 + i.val) = o.basis (786 + i.val)) ∧
    (∀ i : Fin (wpP20 165 - 2),
      out.basis (Shadow7.a0P 150 - 1 + lows150 + i.val) = false ∧
      out.basis (Shadow7.b0P 150 - 1 + lows150 + i.val) =
        (if o.basis 180 then o.basis (Shadow7.b0P 150 - 1 + lows150 + i.val)
         else o.basis (Shadow7.a0P 150 - 1 + lows150 + i.val))) := by
  let a := step^[15] z
  let u := LeaveJ7.Admission.flags z G S
  let o := pullState (OB5.sig 164) raw
  have w := whole150_result s m z G S h nextSmall20
  have hsb : Shadow7.sbP 150 = 173 := by decide
  have ha0 : Shadow7.a0P 150 = 355 := by decide
  have hb0 : Shadow7.b0P 150 = 960 := by decide
  have hr165 : railP 165 = 258 := by decide
  have hlow12 : lows150 = 12 := by decide
  have hsb20 : sbP20 165 = 163 := by decide
  have hwp20 : wpP20 165 = 75 := by decide
  have orient : o.basis 180 = u.1 := by
    have geo : (LeaveJ7.WideWords.L MixedWindow.j7).previous = OB5.sig 164 180 := by decide
    change raw.basis (OB5.sig 164 180) = u.1
    rw [← geo]; exact input.2.2.1
  have law := LeaveShadowRails.retainedLow_shadow7 173 z h.farSmall u.2
  have par := LeaveJ7.RecordedParity.result MixedWindow.j7 (by decide) (by decide) s z G S ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have mode : LeaveSelector.actualMode (Shadow7.sbP 150) z =
      LeaveSelector.farMode (s.basis (Shadow7.e0P 150 + 3)) (s.basis (Shadow7.e0P 150 + 4)) z.u := by
    have hf := h.far; have hs := h.side
    rw [show start MixedWindow.j7 = 150 from rfl] at hf hs
    rw [hf, hs]; exact LeaveTraceHistory.flags _ _
  have ev := LeaveJ7.RecordedEvents.result MixedWindow.j7 (by decide) (by decide) s z G S ⟨h.farSmall, h.endSmall⟩ h.odd h.record
  have hck := LeaveJ7.CoreCheckpoint.result MixedWindow.j7 (by decide) (by decide) s [] z u.1 u.2 ⟨h.farSmall, h.endSmall⟩
    h.ready h.fresh h.scratch h.temp h.odd h.room h.clean h.padding h.bank h.zero par mode ev.2
    (LeaveJ7.RecordedEvents.glueFlag MixedWindow.j7 (by decide) (by decide) s z G S ⟨h.farSmall, h.endSmall⟩
      h.odd h.record h.far h.side)
  have hhead := (leaveMove150_head_eq s z G S h).2 m
  have hhst_eq : run head150Prog m s = swap2St (run (GateMirror.forward (Shadow7.leaveHeadOps 150)) [] s) := by
    unfold head150Prog; exact hhead
  have hck_prog : LeaveJ7.CoreCheckpoint.program MixedWindow.j7 = GateMirror.forward (Shadow7.leaveHeadOps 150) := rfl
  rw [hck_prog] at hck
  constructor
  · intro i
    have hi : i.val < 185 := by have := i.isLt; omega
    have ref := LeaveJ7.WideWords.wide MixedWindow.j7 (by decide) (by decide) a u.1 u.2 raw input ⟨i.val, by rw [show start MixedWindow.j7 = 150 from rfl, hr165]; omega⟩
    dsimp only at ref
    rw [show start MixedWindow.j7 = 150 from rfl] at ref
    by_cases low : i.val < 173
    · have hw := LeaveJ7.WideWords.short MixedWindow.j7 (by decide) (by decide)
        (step^[15] (Shadow.reduced (Shadow7.sbP 150) 15 z)) u.1 u.2 s h.ready ⟨i.val, by rw [show start MixedWindow.j7 = 150 from rfl, hsb]; exact low⟩
      dsimp only at hw; rw [show start MixedWindow.j7 = 150 from rfl] at hw
      have hna : ¬ Shadow7.leaveBox2 150 (165 + 16 + i.val) := by
        unfold Shadow7.leaveBox2
        rw [show 150 + 14 = 164 from rfl, show railP 164 = 258 by decide, show railP 150 = 258 by decide, ha0, hb0, show Shadow7.wpP 150 = 70 by decide]
        omega
      have hnb : ¬ Shadow7.leaveBox2 150 (786 + i.val) := by
        unfold Shadow7.leaveBox2
        rw [show 150 + 14 = 164 from rfl, show railP 164 = 258 by decide, show railP 150 = 258 by decide, ha0, hb0, show Shadow7.wpP 150 = 70 by decide]
        omega
      have ua := leave150To20_keeps _ hna m s
      have ub := leave150To20_keeps _ hnb m s
      have spos := LeaveJ7.BoundaryRails.sharedDigitLow _ _ 173 i.val law.2.1 low
      have smag := LeaveJ7.BoundaryRails.sharedDigitLow _ _ 173 i.val law.2.2 low
      rw [law.1, spos, smag] at ref
      rw [hsb] at hw
      exact ⟨ua.trans (hw.1.trans ref.1.symm), ub.trans (hw.2.trans ref.2.symm)⟩
    · have hk : i.val - 173 < 12 := by omega
      have vals := w.2.2.2.2.2.2.2.2.1 ⟨i.val - 173, hk⟩
      dsimp only at vals
      rw [show 173 + (i.val - 173) = i.val by omega,
        show Shadow7.a0P 150 - 1 + (i.val - 173) = 165 + 16 + i.val by rw [ha0]; omega,
        show Shadow7.b0P 150 - 1 + (i.val - 173) = 786 + i.val by rw [hb0]; omega] at vals
      exact ⟨vals.1.trans ref.1.symm, vals.2.trans ref.2.symm⟩
  · intro i
    have hi : i.val < 73 := by have := i.isLt; omega
    have ref := LeaveJ7.WideWords.wide MixedWindow.j7 (by decide) (by decide) a u.1 u.2 raw input ⟨185 + i.val, by rw [show start MixedWindow.j7 = 150 from rfl, hr165]; omega⟩
    dsimp only at ref; rw [show start MixedWindow.j7 = 150 from rfl] at ref
    rw [show 150 + 31 + (185 + i.val) = Shadow7.a0P 150 - 1 + lows150 + i.val by rw [ha0, hlow12]; omega,
      show 786 + (185 + i.val) = Shadow7.b0P 150 - 1 + lows150 + i.val by rw [hb0, hlow12]; omega] at ref
    constructor
    · by_cases h5 : i.val < 5
      · have ua := upperA150_src ⟨i.val, h5⟩
        have hloc : Shadow7.a0P 150 - 1 + lows150 + i.val = Shadow7.a0P 150 + 11 + i.val := by
          have := ha0; have := hlow12; omega
        rw [hloc, w.2.2.2.2.2.2.2.2.2.2.1 _, movesP150_eq, ua.1]
        simp only [writeBit, Function.update_of_ne ua.2.1]
        rw [w.2.2.2.2.2.2.2.2.2.2.2.2.2 _ ua.2.2.1 ua.2.2.2.1,
          w.2.2.2.2.2.2.2.2.2.2.2.2.1 _ ua.2.2.2.2.1 ua.2.2.2.2.2.1 ua.2.2.2.2.2.2.1 ua.2.2.2.2.2.2.2.1,
          hhst_eq, swap2St_other _ ua.2.2.2.2.2.2.2.2.1 ua.2.2.2.2.2.2.2.2.2.1 ua.2.2.2.2.2.2.2.2.2.2.1 ua.2.2.2.2.2.2.2.2.2.2.2]
        rw [← row150_free_vals.2.2 ⟨i.val, h5⟩]
        exact hck.2.1 ⟨12 + i.val, by omega⟩
      · have hna : ¬ Shadow7.leaveBox2 150 (Shadow7.a0P 150 - 1 + lows150 + i.val) := by
          unfold Shadow7.leaveBox2
          rw [show 150 + 14 = 164 from rfl, show railP 164 = 258 by decide, show railP 150 = 258 by decide, ha0, hb0, show Shadow7.wpP 150 = 70 by decide, hlow12]
          omega
        rw [leave150To20_keeps _ hna m s]
        exact highZero _ (by rw [ha0, hlow12]; omega) (by rw [ha0, hlow12, hr165]; omega)
    · have hb := w.2.2.2.2.2.2.2.2.2.1 i
      rw [show Shadow7.b0P 150 + lows150 - 1 + i.val = Shadow7.b0P 150 - 1 + lows150 + i.val by
          have := hb0; omega,
        show 173 + lows150 + i.val = 185 + i.val by simp [hlow12]] at hb
      rw [orient, hb]
      cases h1 : u.1 <;> simp only [h1, Bool.false_eq_true, ite_false, ite_true] at ref ⊢
      · exact ref.1.symm
      · exact ref.2.symm

private theorem assembleCut150To20 (s o : State) (neg far long : Bool)
    (phase : s.phase = o.phase)
    (sign : s.basis (EnterJ20.flagN ⟨0, by decide⟩) = neg)
    (mode : s.basis (EnterJ20.flagF ⟨0, by decide⟩) = far)
    (side : s.basis (EnterJ20.flagU ⟨0, by decide⟩) = long)
    (low : ∀ i : Fin (sbP20 165 + 22),
      s.basis (165 + 16 + i.val) = o.basis (165 + 16 + i.val) ∧
      s.basis (786 + i.val) = o.basis (786 + i.val))
    (high : ∀ i : Fin (wpP20 165 - 2),
      s.basis (165 + EnterJ20.h20 ⟨0, by decide⟩ + 33 + i.val) = false ∧
      s.basis (EnterJ20.h20 ⟨0, by decide⟩ + 803 + i.val) =
        (if o.basis (EnterJ20.gate ⟨0, by decide⟩) then o.basis (EnterJ20.h20 ⟨0, by decide⟩ + 803 + i.val)
         else o.basis (165 + EnterJ20.h20 ⟨0, by decide⟩ + 33 + i.val)))
    (ext : ∀ q : Wire, ¬ WideReference.Box 150 q → ¬ LeaveJ7.AssembleCut.leftovers MixedWindow.j7 q →
      ¬ (2070 ≤ (q : Nat) + 150 ∧ (q : Nat) ≤ 1812) → s.basis q = o.basis q)
    (mirror : ∀ q : Nat, 2070 ≤ q + 150 → q ≤ 1812 → s.basis q = o.basis q)
    (left : ∀ q, LeaveJ7.AssembleCut.leftovers MixedWindow.j7 q → s.basis q = o.basis q)
    (clear : ∀ q ∈ zeros150, s.basis q = false)
    (carry : ∀ q : Nat, 1556 ≤ q → q + 150 ≤ 2054 → q ≤ 1812 → o.basis q = false) :
    PackedCut (EnterJ20.lowerPairs ⟨0, by decide⟩) (EnterJ20.upperPairs ⟨0, by decide⟩)
      (EnterJ20.gate ⟨0, by decide⟩) (EnterJ20.flagN ⟨0, by decide⟩) (EnterJ20.flagF ⟨0, by decide⟩)
      (EnterJ20.flagU ⟨0, by decide⟩) neg far long o (eraseSites (EnterJ20.pending ⟨0, by decide⟩) s) := by
  let k0 : Fin 9 := ⟨0, by decide⟩
  have hk0 : EnterJ20.flagN k0 = 1747 ∧ EnterJ20.flagF k0 = 1745 ∧ EnterJ20.flagU k0 = 1746 ∧
      EnterJ20.pending k0 = [1748, 1749, 1750] ∧ EnterJ20.h20 k0 = 168 ∧
      EnterJ20.lowerPairs k0 = [(364, 969), (365, 970)] ∧
      EnterJ20.upperPairs k0 = (List.range 73).map (fun i => (366 + i, 971 + i)) := by
    decide +kernel
  have away (q : Wire) (hq : (q : Nat) < 1556) : (eraseSites (EnterJ20.pending k0) s).basis q = s.basis q := by
    have no : q ∉ EnterJ20.pending k0 := by rw [hk0.2.2.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false]; unfold Wire at *; omega
    simp [eraseSites, no]
  have flagOff (q : Wire) (hq : q = 1747 ∨ q = 1745 ∨ q = 1746) : (eraseSites (EnterJ20.pending k0) s).basis q = s.basis q := by
    have no : q ∉ EnterJ20.pending k0 := by rw [hk0.2.2.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false]; rcases hq with rfl | rfl | rfl <;> decide
    simp [eraseSites, no]
  refine ⟨phase, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [flagOff _ (Or.inl hk0.1)]; exact sign
  · rw [flagOff _ (Or.inr (Or.inl hk0.2.1))]; exact mode
  · rw [flagOff _ (Or.inr (Or.inr hk0.2.2.1))]; exact side
  · intro pair mem
    rw [hk0.2.2.2.2.2.1] at mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> dsimp only <;>
    · rw [away _ (by decide), away _ (by decide)]
      first
      | exact low ⟨183, by decide⟩
      | exact low ⟨184, by decide⟩
  · intro pair mem
    rw [hk0.2.2.2.2.2.2] at mem; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem; rw [List.mem_range] at hi; dsimp only
    rw [away _ (by unfold Wire; omega), away _ (by unfold Wire; omega)]
    have h' := high ⟨i, by rw [show wpP20 165 = 75 by decide]; omega⟩
    dsimp only at h'
    rw [hk0.2.2.2.2.1] at h'
    exact h'
  · intro q notN notF notU notLo notHi
    have hsb20 : sbP20 165 = 163 := by decide
    change (eraseSites (EnterJ20.pending k0) s).basis q = o.basis q
    by_cases pend : q ∈ EnterJ20.pending k0
    · have r : 1556 ≤ (q : Nat) ∧ (q : Nat) + 150 ≤ 2054 ∧ (q : Nat) ≤ 1812 := by
        rw [hk0.2.2.2.1] at pend; simp only [List.mem_cons, List.not_mem_nil, or_false] at pend
        rcases pend with rfl | rfl | rfl <;> decide
      simp [eraseSites, pend, carry q r.1 r.2.1 r.2.2]
    simp only [eraseSites, if_neg pend]
    by_cases lf : LeaveJ7.AssembleCut.leftovers MixedWindow.j7 q
    · exact left q lf
    have lf' := lf; unfold LeaveJ7.AssembleCut.leftovers LeaveJ7.ReleasedOrigin.releasedSite at lf'
    rw [show start MixedWindow.j7 = 150 from rfl] at lf'; simp only [not_or, not_and] at lf'
    by_cases inBox : WideReference.Box 150 q
    · have inBox' := inBox; unfold WideReference.Box at inBox'
      rw [LeaveJ7.AssembleCut.route_rail 150 (by decide), LeaveJ7.AssembleCut.route_rail 164 (by decide),
        show railP 150 = 258 by decide, show railP 164 = 258 by decide] at inBox'
      by_cases hc : 1556 ≤ (q : Nat)
      · have top : (q : Nat) + 150 ≤ 2054 ∧ (q : Nat) ≤ 1812 := by
          unfold Wire at *; rcases inBox' with h | h | h | h <;> omega
        rw [carry q hc top.1 top.2]
        apply clear q
        simp only [zeros150, List.mem_append, List.mem_range'_1, show e0P20 165 = 1742 by decide]
        rw [hk0.1] at notN; rw [hk0.2.1] at notF; rw [hk0.2.2.1] at notU; rw [hk0.2.2.2.1] at pend
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at pend
        unfold Wire at hc top notN notF notU pend
        rcases Nat.lt_or_ge q 1745 with hlt | hlt
        · left; omega
        · right; omega
      · have hrails : (181 ≤ (q : Nat) ∧ (q : Nat) < 439) ∨ (786 ≤ (q : Nat) ∧ (q : Nat) < 1044) := by
          unfold Wire at *; rcases inBox' with h | h | h | h <;> omega
        rcases hrails with ⟨a1, a2⟩ | ⟨b1, b2⟩
        · by_cases lo : (q : Nat) < 366
          · have l := (low ⟨q - 181, by rw [hsb20]; unfold Wire at *; omega⟩).1; dsimp only at l
            rwa [show 165 + 16 + ((q : Nat) - 181) = q by unfold Wire at *; omega] at l
          · exfalso; apply notHi
            rw [hk0.2.2.2.2.2.2]
            simp only [RailPair.sites, List.mem_flatMap, List.mem_map, List.mem_range]
            exact ⟨_, ⟨q - 366, by unfold Wire at *; omega, rfl⟩, by simp only [List.mem_cons]; left; unfold Wire at *; omega⟩
        · by_cases lo : (q : Nat) < 971
          · have l := (low ⟨q - 786, by rw [hsb20]; unfold Wire at *; omega⟩).2; dsimp only at l
            rwa [show 786 + ((q : Nat) - 786) = q by unfold Wire at *; omega] at l
          · exfalso; apply notHi
            rw [hk0.2.2.2.2.2.2]
            simp only [RailPair.sites, List.mem_flatMap, List.mem_map, List.mem_range]
            exact ⟨_, ⟨q - 971, by unfold Wire at *; omega, rfl⟩, by simp only [List.mem_cons, List.mem_singleton]; right; unfold Wire at *; omega⟩
    · by_cases mi : 2070 ≤ (q : Nat) + 150 ∧ (q : Nat) ≤ 1812
      · exact mirror q mi.1 mi.2
      · exact ext q inBox lf mi

private theorem frameHistory150To20 (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool) (G S : Bool)
    (domain : Domain 150 x p raw)
    (input : InputAt 150 (SkywalkRails.encode G S (unsigned 150 x p).u (unsigned 150 x p).v) raw)
    (record : Shadow7.physicalCells MixedWindow.j7 s = SkywalkTrace.trace 15 (SkywalkRails.encode G S (unsigned 150 x p).u (unsigned 150 x p).v))
    (kept : Shadow7.physicalCells MixedWindow.j7 (run leave150To20 m s) = Shadow7.physicalCells MixedWindow.j7 s) :
    ∀ q, LeaveJ7.AssembleCut.leftovers MixedWindow.j7 q →
      (run leave150To20 m s).basis q = (WideReference.origin 150 raw s).basis q := by
  let out := run leave150To20 m s
  let o := WideReference.origin 150 raw s
  have hgeo : ∀ i : Fin 15, windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) i.val).a0 = 166 + i.val ∧
      windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) i.val).history = LeaveJ7.swaps MixedWindow.j7 i.val := by
    intro i; have hi := i.isLt
    constructor
    · show OB5.sig 164 (150 + i.val + 16) = 166 + i.val
      unfold OB5.sig; rw [if_neg (by unfold Wire; omega)]; unfold Wire; omega
    · show OB5.sig 164 (150 + i.val + 16 + 1028) = OB5.sig 164 (150 + 1044 + i.val)
      congr 1; unfold Wire; omega
  have agree (i : Fin 15) : out.basis (166 + i.val) = o.basis (166 + i.val) ∧
      out.basis (LeaveJ7.swaps MixedWindow.j7 i.val) = o.basis (LeaveJ7.swaps MixedWindow.j7 i.val) := by
    have old := WideReference.recorded_equal 150 MixedWindow.j7 x p (by decide) (WideReference.places MixedWindow.j7) good raw s domain G S input record i
    have now := congrArg (fun a => StairArchiveRaw.read a i.val) kept
    change StairArchiveRaw.read (readCells (Shadow7.shape MixedWindow.j7) 0 15 (mappedBasis MixedWindow.j7 out.basis)) i.val =
      StairArchiveRaw.read (readCells (Shadow7.shape MixedWindow.j7) 0 15 (mappedBasis MixedWindow.j7 s.basis)) i.val at now
    rw [StairPacket.read_cells _ _ _ _ _ i.isLt, StairPacket.read_cells _ _ _ _ _ i.isLt, Nat.zero_add] at now
    have eq := now.trans old
    change (out.basis (windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) i.val).a0),
        out.basis (windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) i.val).history)) =
      (o.basis (windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) i.val).a0),
        o.basis (windowNet MixedWindow.j7 (IntegerPacket.ports (Shadow7.shape MixedWindow.j7) i.val).history)) at eq
    rw [(hgeo i).1, (hgeo i).2] at eq
    exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩
  have inSites : (165 : Wire) ∈ WideReference.sites 150 := by
    apply (WideReference.mem_sites (i := 150) (by decide) 165).mpr
    rw [show OB5.sig 164 165 = 165 by decide]
    unfold WideReference.oldSites
    refine List.mem_flatMap.mpr ⟨149, List.mem_range'_1.mpr (by decide), ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, MappedCompressed.base]; decide
  have previous : out.basis 165 = o.basis 165 := by
    rw [show o.basis 165 = s.basis 165 from WideReference.inside 150 raw s 165 inSites]
    exact leave150To20_keeps 165 (by unfold Shadow7.leaveBox2; decide) m s
  have noRel : ∀ q : Wire, ¬ LeaveJ7.ReleasedOrigin.releasedSite MixedWindow.j7 q := by
    intro q hr; unfold LeaveJ7.ReleasedOrigin.releasedSite at hr
    rw [show start MixedWindow.j7 = 150 from rfl, show railP 150 = 258 by decide, show railP 165 = 258 by decide] at hr
    omega
  intro q residual
  unfold LeaveJ7.AssembleCut.leftovers at residual
  rw [show start MixedWindow.j7 = 150 from rfl] at residual
  rcases residual with ⟨lo, hi⟩ | ⟨lo, hi⟩ | rel | ⟨lo, hi, top⟩
  · by_cases e : (q : Nat) = 165
    · rw [show q = 165 from e]; exact previous
    · have a := (agree ⟨(q : Nat) - 166, by unfold Wire at *; omega⟩).1; dsimp only at a
      rwa [show 166 + ((q : Nat) - 166) = q by unfold Wire at *; omega] at a
  · have a := (agree ⟨(q : Nat) - 1194, by unfold Wire at *; omega⟩).2; dsimp only at a
    rwa [show LeaveJ7.swaps MixedWindow.j7 ((q : Nat) - 1194) = q by
      unfold LeaveJ7.swaps OB5.sig; rw [show start MixedWindow.j7 = 150 from rfl, if_neg (by unfold Wire at *; omega)]
      unfold Wire at *; omega] at a
  · exact absurd rel (noRel q)
  · unfold Wire at *; omega

theorem endpoint150To20 (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m n : List Bool)
    (domain : Domain 150 x p raw) (G S : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs MixedWindow.j7) (EnterJ7.upperPairs MixedWindow.j7)
      (EnterJ7.gate MixedWindow.j7) (EnterJ7.flagN MixedWindow.j7) (EnterJ7.flagF MixedWindow.j7)
      (EnterJ7.flagU MixedWindow.j7) (PortalValues.negative S (unsigned 150 x p).u)
      (decide (Shadow.far (Shadow7.sbP 150) 15 (unsigned 150 x p)))
      (decide (Shadow.far (Shadow7.sbP 150) 15 (unsigned 150 x p) ∧ 2 ^ Shadow7.sbP 150 ≤ (unsigned 150 x p).u))
      (pullState (EnterJ7.pull MixedWindow.j7) raw) (eraseSites (EnterJ7.pending MixedWindow.j7) s))
    (input : SkywalkIntegerInput (EnterJ7.lay MixedWindow.j7)
      (SkywalkRails.encode G S (unsigned 150 x p).u (unsigned 150 x p).v).a
      (SkywalkRails.encode G S (unsigned 150 x p).u (unsigned 150 x p).v).b G raw.basis)
    (scratch : ∀ k : Fin 157, 23 ≤ k.val →
      let pre := run (Shadow7.enterP MixedWindow.j7) m s
      let tape := m.drop (measurementCount (Shadow7.enterP MixedWindow.j7))
      (run (NativeJ7.program MixedWindow.j7 d) (tape.drop (measurementCount (Shadow7.routed MixedWindow.j7 0 1)))
        (run (Shadow7.routed MixedWindow.j7 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (NativeJ7.prev MixedWindow.j7) k) = false)
    (pg ps cross : Bool)
    (prior : PastFacts (NativeJ7.prev MixedWindow.j7) (ArchiveJ7.rawPorts (NativeJ7.prev MixedWindow.j7))
      (Shadow7.sbP (start (NativeJ7.prev MixedWindow.j7))) (unsigned (start (NativeJ7.prev MixedWindow.j7)) x p) pg ps cross s) :
    let v := run (NativeJ7.nextWindow MixedWindow.j7 d) m s
    let out := run leave150To20 n v
    PackedCut (EnterJ20.lowerPairs ⟨0, by decide⟩) (EnterJ20.upperPairs ⟨0, by decide⟩)
      (EnterJ20.gate ⟨0, by decide⟩) (EnterJ20.flagN ⟨0, by decide⟩) (EnterJ20.flagF ⟨0, by decide⟩)
      (EnterJ20.flagU ⟨0, by decide⟩)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned 150 x p) G S).2 (unsigned 165 x p).u)
      (decide (Shadow.far (sbP20 165) 20 (unsigned 165 x p)))
      (decide (Shadow.far (sbP20 165) 20 (unsigned 165 x p) ∧ 2 ^ sbP20 165 ≤ (unsigned 165 x p).u))
      (pullState (EnterJ20.pull ⟨0, by decide⟩) (WideReference.endRaw 150 raw v))
      (eraseSites (EnterJ20.pending ⟨0, by decide⟩) out) ∧
    PastFacts MixedWindow.j7 Archive150.rawPorts (Shadow7.sbP 150) (unsigned 150 x p) G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d MixedWindow.j7 (unsigned 150 x p))) out ∧
    (∀ r, run leaveInv150To20 r out = v) := by
  have numbers := LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good
  have old := LeaveJ7.Admission.actualNumbers (NativeJ7.prev MixedWindow.j7) (by decide) (by decide) x p good
  have next20 := actualNumbers20 ⟨0, by decide⟩ x p good
  have hist := WideReference.pulled_history MixedWindow.j7 rfl domain
  have native := NativeJ7.from_domain MixedWindow.j7 (by decide) (by decide) d x p good raw s m domain G S cut input scratch pg ps cross prior
  obtain ⟨_, _, _, _, tags⟩ := NativeJ7.real_receipt MixedWindow.j7 (by decide) (by decide) d raw s m (unsigned 150 x p) G S
    numbers.odd numbers.farSmall cut input hist scratch (unsigned (start (NativeJ7.prev MixedWindow.j7)) x p) pg ps cross old.odd old.farSmall prior
  let pre := run (Shadow7.enterP MixedWindow.j7) m s
  let tape := m.drop (measurementCount (Shadow7.enterP MixedWindow.j7))
  let T := Shadow.reduced (Shadow7.sbP 150) 15 (unsigned 150 x p)
  let Z := SkywalkRails.encode G S T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd_shadow7 (Shadow7.sbP 150) (unsigned 150 x p) numbers.farSmall numbers.odd
  have parity : (Z.a + Z.b) % 2 = 1 := SkywalkRails.encode_odd_sum G S _ _ (by omega)
  have ready := EnterJ7.ready_pending_at MixedWindow.j7 raw s (unsigned 150 x p) G S m numbers.farSmall cut input hist
  obtain ⟨_, row, limit, frame⟩ := NativeJ7.admits MixedWindow.j7 (by decide) (by decide) d s m tape
    (tape.drop (measurementCount (Shadow7.routed MixedWindow.j7 0 1))) Z parity ready.2.1 scratch
    (unsigned (start (NativeJ7.prev MixedWindow.j7)) x p) pg ps cross old.odd old.farSmall prior
  have final := NativeJ7.archive_result MixedWindow.j7 (by decide) (by decide) d row limit _ _ frame
  have tail := NativeJ7.tail_clean MixedWindow.j7 (by decide) (by decide) d x p raw s domain m tape _ _ _ cut row final
  let v := run (NativeJ7.nextWindow MixedWindow.j7 d) m s
  have runEq : v = run (Shadow7.body MixedWindow.j7 (NativeJ7.withArchive MixedWindow.j7 d)) tape pre := by
    simp only [v, NativeJ7.nextWindow, NativeJ7.window, run_append, run_take, pre, tape]
  have gg : ∀ (g sg : Bool) (u v : Int), (SkywalkRails.encode g sg u v).g = g := fun g _ _ _ => by cases g <;> rfl
  have origIn : InputAt 150 (SkywalkRails.encode G S (unsigned 150 x p).u (unsigned 150 x p).v) raw := by
    unfold InputAt; rw [gg]; exact input
  have hAdm := native.1
  have hPh := native.2.1
  have endpointState : step^[15] (unsigned 150 x p) = unsigned 165 x p := by
    show step^[15] (step^[150] (init x p)) = step^[165] (init x p)
    rw [show (165 : Nat) = 150 + 15 by decide, Nat.add_comm, Function.iterate_add_apply]
  have nextSmall20 : Shadow7.SmallIfFar 163 20 (step^[15] (unsigned 150 x p)) := by
    rw [endpointState]; exact next20.small.1
  have harch := archiveCut150To20 v n (unsigned 150 x p) G S hAdm nextSmall20
  have hrt := fun r => leave150To20_roundtrip v (unsigned 150 x p) G S hAdm nextSmall20 n r
  refine ⟨?_, harch, hrt⟩
  have bit : v.basis (Shadow7.e0P 150 + 8) = false := by
    have t2 := tags ⟨2, by decide⟩
    have e : Shadow7.e0P 150 + 8 = Shadow7.sbP 150 + 1580 + (⟨2, by decide⟩ : Fin 3).val := by decide
    rw [e]; exact t2
  have quiet : ∀ q ∈ LeaveJ7.CoreCheckpoint.rawSites MixedWindow.j7, v.basis q = false := by
    intro q hq
    simp only [LeaveJ7.CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1, List.mem_singleton] at hq
    rcases hq with (⟨lo, hi⟩ | ⟨lo, hi⟩) | p17
    rotate_right
    · rw [p17]; exact hAdm.parked
    · exact LeaveJ7.native_carryJ MixedWindow.j7 (by decide) (by decide) _ v hAdm.ready hAdm.top hAdm.top2 q
        (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · by_cases e8 : (q : Nat) = Shadow7.e0P 150 + 8
      · rw [show q = Shadow7.e0P 150 + 8 from e8]; exact bit
      · rw [runEq]; exact tail q (by
          simp only [NativeJ7.tailTemps, List.mem_range'_1, show start MixedWindow.j7 = 150 from rfl,
            show Shadow7.e0P 150 = 1747 by decide] at lo hi e8 ⊢
          unfold Wire at *; omega)
  have hclear := boundaryClean150To20 v n (unsigned 150 x p) G S hAdm nextSmall20 quiet
  have hup : ∀ q : Nat, Shadow7.a0P 150 + 16 ≤ q → q ≤ 180 + railP 165 → v.basis q = false := by
    intro q lo hi; rw [runEq]
    exact NativeJ7.upper_clear MixedWindow.j7 (by decide) (by decide) d raw s x p domain m tape _ _ _ cut q
      (by unfold Shadow7.a0P at lo; rw [show start MixedWindow.j7 = 150 from rfl]; omega)
      (by rw [show start MixedWindow.j7 = 150 from rfl, show (150 : Nat) + 14 = 164 from rfl,
          show railP 164 = 258 by decide]; rw [show railP 165 = 258 by decide] at hi; omega)
  have carried := StockWindowTicket.stepInput_gen_shadow7 150 (Shadow7.sbP 150) x p (by decide) (by decide) good raw v
    G S domain origIn hAdm.farSmall
  have nextInput : let a := step^[15] (unsigned 150 x p)
      let u := LeaveJ7.Admission.flags (unsigned 150 x p) G S
      SkywalkIntegerInput (LeaveJ7.WideWords.L MixedWindow.j7)
        (SkywalkRails.encode u.1 u.2 a.u a.v).a (SkywalkRails.encode u.1 u.2 a.u a.v).b u.1
        (WideReference.endRaw 150 raw v).basis := by
    have c2 := carried.2; unfold InputAt StockWindowTicket.signedAt at c2; rw [gg] at c2
    rw [endpointState]; exact c2
  have hrails := boundaryRails150To20 v n (unsigned 150 x p) G S hAdm nextSmall20 hup (WideReference.endRaw 150 raw v) nextInput
  have eo : pullState (OB5.sig 164) (WideReference.endRaw 150 raw v) = WideReference.origin 150 raw v :=
    WideReference.endpoint 150 (by decide) raw v
  dsimp only at hrails; rw [eo] at hrails
  have hkept : Shadow7.physicalCells MixedWindow.j7 (run leave150To20 n v) = Shadow7.physicalCells MixedWindow.j7 v :=
    harch.records.trans hAdm.record.symm
  have hleft := frameHistory150To20 x p good raw v n G S domain origIn hAdm.record hkept
  have w := whole150_result v n (unsigned 150 x p) G S hAdm nextSmall20
  have pk : pullState (EnterJ20.pull ⟨0, by decide⟩) (WideReference.endRaw 150 raw v) = WideReference.origin 150 raw v := eo
  have hboth : ∀ P Q : Prop, [Decidable P] → [Decidable Q] → (decide P && decide Q) = decide (P ∧ Q) := fun P Q _ _ => by
    by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
  have hfl0 : EnterJ20.flagN ⟨0, by decide⟩ = e0P20 165 + 5 ∧
      EnterJ20.flagF ⟨0, by decide⟩ = e0P20 165 + 3 ∧
      EnterJ20.flagU ⟨0, by decide⟩ = e0P20 165 + 4 := by decide
  rw [pk]
  refine assembleCut150To20 (run leave150To20 n v) (WideReference.origin 150 raw v) _ _ _
    (w.1.trans (hPh.trans (cut.phase.trans (WideReference.origin_phase 150 x p (by decide) good raw v domain).symm)))
    ?_ ?_ ?_ hrails.1 ?_ ?_ ?_ hleft hclear ?_
  · rw [hfl0.1, ← endpointState]; exact w.2.2.2.1
  · rw [hfl0.2.1, ← endpointState]; exact w.2.1
  · rw [hfl0.2.2, ← endpointState]; exact w.2.2.1.trans (hboth _ _)
  · intro i
    have r := hrails.2 i
    have e1 : 165 + EnterJ20.h20 ⟨0, by decide⟩ + 33 + i.val = Shadow7.a0P 150 - 1 + lows150 + i.val := by
      have : 165 + EnterJ20.h20 ⟨0, by decide⟩ + 33 = Shadow7.a0P 150 - 1 + lows150 := by decide
      omega
    have e2 : EnterJ20.h20 ⟨0, by decide⟩ + 803 + i.val = Shadow7.b0P 150 - 1 + lows150 + i.val := by
      have : EnterJ20.h20 ⟨0, by decide⟩ + 803 = Shadow7.b0P 150 - 1 + lows150 := by decide
      omega
    have e3 : EnterJ20.gate ⟨0, by decide⟩ = 180 := by decide
    rw [e1, e2, e3]; exact r
  · intro q nb nl nm
    rw [leave150To20_keeps q (fun hb => nb (LeaveJ7.AssembleCut.box_of_box2 MixedWindow.j7 (by decide) (by decide) q hb)) n v, runEq]
    unfold LeaveJ7.AssembleCut.leftovers LeaveJ7.ReleasedOrigin.releasedSite at nl
    rw [show start MixedWindow.j7 = 150 from rfl] at nl; simp only [not_or, not_and] at nl
    exact NativeJ7.agree_origin MixedWindow.j7 (by decide) (by decide) (by decide) d raw s m tape _ _ _ cut q nb
      (by rw [show start MixedWindow.j7 = 150 from rfl]; unfold Wire at *; omega)
      (by rw [show start MixedWindow.j7 = 150 from rfl]; unfold Wire at *; omega)
      (by rw [show start MixedWindow.j7 = 150 from rfl]; unfold Wire at *; omega)
  · intro q lo hi
    rw [leave150To20_keeps_mirror q lo n v, runEq]
    exact NativeJ7.mirror_origin MixedWindow.j7 (by decide) (by decide) (by decide) d raw s m tape _ _ _ cut q lo hi
  · intro q lo hs hi
    exact WideReference.carry_origin (i := 150) (upper := 1812) (by decide) (by decide) good raw v domain
      (fun q' l u' => sig_fixed (by intro h; unfold Wire at *; omega) (by intro h; unfold Wire at *; omega))
      q lo hi

end Endpoint150

end ECDSAAdd.Entrant.StairPacket.Shadow20.Trans150
end
-- ==== end Shadow7Wide20End150 ====


-- ==== begin Shadow7Wide20ReentryEnd ====
section

/-!
# Re-entry Block `j20` (`s = 345`) Endpoint, Selected Receipt & Ordinary Step (`Shadow7Wide20ReentryEnd`)

Bridges the 20-tick block `k8` (`s = 325..344`) back into the standard 15-tick suffix
(`j21..j24`, exit `420`) by:
1. Packing ticks `325..329` into `rawPack325 d raw := run (Rolling1588.encodeAt base d 325) [] raw`,
   proving `Domain 345`, `InputAt 345`, and `WideReference.origin 345 (rawPack325 d raw) out = WideReference20.origin 345 20 15 raw out`.
2. Proving `admitted345`, `mirror_origin345`, `band_clean345`, `upper_clear345`, and `endpoint345`
   (reusing `LeaveJ7.CertifiedCut.result j20 j21`, `LeaveJ7.ArchiveCut.result j20`, and `CRTBarrel.leave j20` verbatim!).
3. Defining `value20` (canonical 20-tick archive key) and proving `value20_chronology`,
   `selected_receipt345`, `cleared_holes345`, and `ordinary345`.
-/

namespace ECDSAAdd.Entrant.StairPacket.Shadow20.Reentry345

open ECDSAAdd.Arithmetic
open ECDSAAdd.Arithmetic.MappedCompressed
open ECDSAAdd.Entrant.IntegerPacket
open ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open ECDSAAdd.Entrant.StairArchiveRaw
open ECDSAAdd.Entrant.StairArchiveTrace
open ECDSAAdd.Entrant.StairPacket.EnterProof
open ECDSAAdd.Entrant.StairPacket.WideReference
open ECDSAAdd.Entrant.StairPacket.StockCanonicalRow
open ECDSAAdd.Entrant.StairPacket.StockStrongChain
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.WideReference20
open ECDSAAdd.Entrant.StairPacket.Shadow20.LeaveCut20
open SkywalkRails

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ### Section 1: Reference Packing `rawPack325` & `origin` Equivalence -/

def rawPack325 (d : Bool) (raw : State) : State :=
  run (Rolling1588.encodeAt base d 325) [] raw

def plain325 : Fin 10 → Wire := History5.historyMap base 325
def plain330 : Fin 10 → Wire := History5.historyMap base 330

private theorem plain325_inj : Function.Injective plain325 :=
  History5.historyMap_injective base base_pool_nodup 325 (by decide)

private theorem plain330_inj : Function.Injective plain330 :=
  History5.historyMap_injective base base_pool_nodup 330 (by decide)

private theorem hist345_geom :
    Function.Injective histA345 ∧ Function.Injective histB345 ∧
    (∀ i : Fin 10,
      OB5.sig 344 (histA345 i) = plain325 i ∧
      OB5.sig 359 (histA345 i) = plain325 i ∧
      OB5.sig 344 (histB345 i) = plain330 i ∧
      OB5.sig 359 (histB345 i) = plain330 i ∧
      oldRange 346 (windowNet j20 (histA345 i)) ∧
      oldRange 346 (windowNet j20 (histB345 i)) ∧
      histA345 i ∉ EnterJ7.pending j20 ∧ histB345 i ∉ EnterJ7.pending j20 ∧
      histA345 i ≠ EnterJ7.flagN j20 ∧ histA345 i ≠ EnterJ7.flagF j20 ∧ histA345 i ≠ EnterJ7.flagU j20 ∧
      histB345 i ≠ EnterJ7.flagN j20 ∧ histB345 i ≠ EnterJ7.flagF j20 ∧ histB345 i ≠ EnterJ7.flagU j20 ∧
      histA345 i ∉ RailPair.sites (EnterJ7.upperPairs j20) ∧
      histB345 i ∉ RailPair.sites (EnterJ7.upperPairs j20) ∧
      histA345 i ∉ ArchiveJ20.rawPortsList k8 ∧
      histB345 i ∉ ArchiveJ20.rawPortsList k8) ∧
    (∀ i j : Fin 10, histA345 i ≠ histB345 j) := by
  decide +kernel

private theorem encode325_off_lay :
    ∀ r : Fin 5,
      base (325 + r.val) ∉ (W.compactSkywalkTickLayout base 345).a ∧
      base (325 + r.val) ∉ (W.compactSkywalkTickLayout base 345).b ∧
      base (325 + r.val) ≠ (W.compactSkywalkTickLayout base 345).previous ∧
      base (325 + r.val) ≠ (W.compactSkywalkTickLayout base 345).ext ∧
      base (325 + r.val) ≠ (W.compactSkywalkTickLayout base 345).history ∧
      base (325 + r.val) ∉ (W.compactSkywalkTickLayout base 345).carry ∧
      base (1028 + (325 + r.val)) ∉ (W.compactSkywalkTickLayout base 345).a ∧
      base (1028 + (325 + r.val)) ∉ (W.compactSkywalkTickLayout base 345).b ∧
      base (1028 + (325 + r.val)) ≠ (W.compactSkywalkTickLayout base 345).previous ∧
      base (1028 + (325 + r.val)) ≠ (W.compactSkywalkTickLayout base 345).ext ∧
      base (1028 + (325 + r.val)) ≠ (W.compactSkywalkTickLayout base 345).history ∧
      base (1028 + (325 + r.val)) ∉ (W.compactSkywalkTickLayout base 345).carry := by
  decide +kernel

private theorem encode325_off_hist :
    ∀ (r : Fin 5) (k : Fin 15),
      base (325 + r.val) ≠ EnterJ7.pull j20 (windowNet j20 (IntegerPacket.ports (Shadow7.shape j20) k).history) ∧
      base (1028 + (325 + r.val)) ≠ EnterJ7.pull j20 (windowNet j20 (IntegerPacket.ports (Shadow7.shape j20) k).history) := by
  decide +kernel

private theorem moves_wires_local (ps : List (Wire × Wire)) :
    ∀ q ∈ wires (moves ps), ∃ p ∈ ps, q = p.1 ∨ q = p.2 := by
  induction ps with
  | nil => intro q h; simp [moves, wires] at h
  | cons p ps ih =>
    intro q h; obtain ⟨a, b⟩ := p
    simp only [moves, List.flatMap_cons, wires_append, Finset.mem_union] at h
    rcases h with h | h
    · refine ⟨(a, b), List.mem_cons_self, ?_⟩
      simp [swapBits, wires, Instr.wires] at h ⊢; tauto
    · obtain ⟨p', hp', e⟩ := ih q (by simpa [moves] using h)
      exact ⟨p', List.mem_cons_of_mem _ hp', e⟩

private theorem load_cover_k8_pub (d : Bool) :
    wires (archiveLoadP20 k8 d) ⊆ (ArchiveJ20.rawPortsList k8).toFinset := by
  rw [ArchiveJ20.load_program, wires_append, Finset.union_subset_iff]
  constructor
  · rw [StairArchiveIntegerHook.placed, renameProgram_support]
    intro q hq; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
    have small : w < 155 := by cases d; exact Partial.load1_ports w hw; exact Partial.load0_ports w hw
    rw [ArchiveJ20.load_map k8 ⟨w, small⟩, List.mem_toFinset, ArchiveJ20.rawPorts,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [ArchiveJ20.rawLength]; omega), Option.getD_some]
    exact List.getElem_mem _
  · intro q hq; obtain ⟨p, hp, e⟩ := moves_wires_local _ q hq
    have hm : ∀ r ∈ ArchiveJ20.loadMoves k8, r.1 ∈ ArchiveJ20.rawHead k8 ∧ r.2 ∈ ArchiveJ20.rawHead k8 := by
      decide +kernel
    obtain ⟨h1, h2⟩ := hm p hp
    rw [List.mem_toFinset, ArchiveJ20.raw_split]
    rcases e with rfl | rfl
    · exact List.mem_append_left _ h1
    · exact List.mem_append_left _ h2

private theorem rawPack325_outside (d : Bool) (raw : State) (q : Wire)
    (hq : ∀ r : Nat, 325 ≤ r → r ≤ 329 → q ≠ base r ∧ q ≠ base (1028 + r)) :
    (rawPack325 d raw).basis q = raw.basis q := by
  apply run_preserves_outside
  intro used
  obtain ⟨r, r1, r2, e | e⟩ := OrdinaryChainW.encode_cells d 325 q used
  · exact (hq r r1 r2).1 e
  · exact (hq r r1 r2).2 e

theorem rawPack325_phase (d : Bool) (raw : State) : (rawPack325 d raw).phase = raw.phase :=
  Rolling1588.codeEncodeAt_zero_phase d plain325 plain325_inj raw

theorem rawPack325_domain (d : Bool) (x p : Nat) (raw : State) (dom : Domain 345 x p raw) :
    Domain 345 x p (rawPack325 d raw) := by
  obtain ⟨ref, coh, st⟩ := dom
  refine ⟨ref, ⟨(rawPack325_phase d raw).trans coh.1, fun q hq => ?_⟩, st⟩
  refine (rawPack325_outside d raw q fun r r1 r2 => ?_).trans (coh.2 q hq)
  exact ⟨fun e => hq ⟨r, by omega, Or.inl e⟩, fun e => hq ⟨r, by omega, Or.inr e⟩⟩

theorem rawPack325_input (d : Bool) (raw : State) (Z : SkywalkRails.State)
    (inp : InputAt 345 Z raw) : InputAt 345 Z (rawPack325 d raw) := by
  let L := W.compactSkywalkTickLayout base 345
  have agree : ∀ q, (q ∈ L.a ∨ q ∈ L.b ∨ q = L.previous ∨ q = L.ext ∨ q = L.history ∨ q ∈ L.carry) →
      (rawPack325 d raw).basis q = raw.basis q := by
    intro q hq
    apply rawPack325_outside d raw q
    intro r r1 r2
    have h := encode325_off_lay ⟨r - 325, by omega⟩
    rw [show 325 + (r - 325) = r by omega] at h
    rcases hq with hq | hq | rfl | rfl | rfl | hq
    · exact ⟨fun e => h.1 (e ▸ hq), fun e => h.2.2.2.2.2.2.1 (e ▸ hq)⟩
    · exact ⟨fun e => h.2.1 (e ▸ hq), fun e => h.2.2.2.2.2.2.2.1 (e ▸ hq)⟩
    · exact ⟨h.2.2.1.symm, h.2.2.2.2.2.2.2.2.1.symm⟩
    · exact ⟨h.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.2.1.symm⟩
    · exact ⟨h.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.2.2.1.symm⟩
    · exact ⟨fun e => h.2.2.2.2.2.1 (e ▸ hq), fun e => h.2.2.2.2.2.2.2.2.2.2.2 (e ▸ hq)⟩
  have hreg : ∀ (xs : List Wire), (∀ q ∈ xs, (rawPack325 d raw).basis q = raw.basis q) →
      signedRegValue xs (rawPack325 d raw).basis = signedRegValue xs raw.basis := by
    intro xs hxs
    unfold signedRegValue
    rw [regValue_congr xs (rawPack325 d raw).basis raw.basis hxs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg L.a (fun q hq => agree q (Or.inl hq))]; exact inp.1
  · rw [hreg L.b (fun q hq => agree q (Or.inr (Or.inl hq)))]; exact inp.2.1
  · rw [agree L.previous (Or.inr (Or.inr (Or.inl rfl)))]; exact inp.2.2.1
  · rw [agree L.ext (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact inp.2.2.2.1
  · rw [agree L.history (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact inp.2.2.2.2.1
  · rw [regValue_congr L.carry (rawPack325 d raw).basis raw.basis
      (fun q hq => agree q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq))))))]; exact inp.2.2.2.2.2

theorem rawPack325_span_comm (d : Bool) (raw : State) :
    run (span 345 15) [] (rawPack325 d raw) = rawPack325 d (run (span 345 15) [] raw) := by
  have disj : Disjoint (wires (span 345 15)) (wires (Rolling1588.encodeAt base d 325)) := by
    rw [Finset.disjoint_left]
    intro q hsp hen
    obtain ⟨r, r1, r2, e | e⟩ := OrdinaryChainW.encode_cells d 325 q hen
    · exact pastOffSpan 345 15 q (by decide) ⟨r, by omega, Or.inl e⟩ hsp
    · exact pastOffSpan 345 15 q (by decide) ⟨r, by omega, Or.inr e⟩ hsp
  have hcm := run_disjoint_commute (span 345 15) (Rolling1588.encodeAt base d 325) disj [] [] raw
  simpa only [rawPack325] using hcm

attribute [local irreducible] run SkywalkNat.step Shadow.far nextWindow345 window345 withArchive345
  packProg345 archiveLoadP20 Shadow7.enterP Shadow7.body Shadow7.routed in
theorem pack345_hist_vals (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool)
    (dom : Domain 345 x p raw) (neg far long : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) neg far long
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s))
    (Z : SkywalkRails.State) (parity : (Z.a + Z.b) % 2 = 1)
    (active : Shadow7.onRails j20 0 Z (run (Shadow7.enterP j20) m s).basis) :
    let out := run (nextWindow345 d) m s
    (∀ i : Fin 10, out.basis (histA345 i) = (rawPack325 d raw).basis (plain325 i)) ∧
    (∀ i : Fin 10, out.basis (histB345 i) =
      (run (Rolling1588.encodeAt base d 330) [] (run (span 345 15) [] (rawPack325 d raw))).basis (plain330 i)) := by
  let pre := run (Shadow7.enterP j20) m s
  let tape := m.drop (measurementCount (Shadow7.enterP j20))
  let st1 := run (Shadow7.routed j20 0 1) tape pre
  let t1 := tape.drop (measurementCount (Shadow7.routed j20 0 1))
  have runEq : run (nextWindow345 d) m s = run (Shadow7.body j20 (withArchive345 d)) tape pre := by
    simp only [nextWindow345, window345, run_append, run_take, pre, tape]
  have hc := pack_codes345_aux d
  have hA_in : ∀ i : Fin 10, st1.basis (histA345 i) = raw.basis (plain325 i) := by
    intro i
    have g := hist345_geom.2.2.1 i
    have h1 := Shadow7.first_preserves j20 Z parity pre tape active (histA345 i)
      (firstFree345 (heads345_ok.2.1 i).1)
    have h2 := run_preserves_outside (Shadow7.enterP j20) m s (histA345 i)
      (EnterJ7.notWire j20 (heads345_ok.2.1 i).2.1)
    have h3 := cut.unchanged (histA345 i) g.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.1
      g.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [h1, h2]
    have e : s.basis (histA345 i) = (eraseSites (EnterJ7.pending j20) s).basis (histA345 i) := by
      simp [eraseSites, g.2.2.2.2.2.2.1]
    rw [e, h3]; change raw.basis (OB5.sig 344 (histA345 i)) = _; rw [g.1]
  have hB_in : ∀ i : Fin 10, st1.basis (histB345 i) = raw.basis (plain330 i) := by
    intro i
    have g := hist345_geom.2.2.1 i
    have h1 := Shadow7.first_preserves j20 Z parity pre tape active (histB345 i)
      (firstFree345 (heads345_ok.2.1 i).2.2.1)
    have h2 := run_preserves_outside (Shadow7.enterP j20) m s (histB345 i)
      (EnterJ7.notWire j20 (heads345_ok.2.1 i).2.2.2)
    have h3 := cut.unchanged (histB345 i) g.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.1
      g.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [h1, h2]
    have e : s.basis (histB345 i) = (eraseSites (EnterJ7.pending j20) s).basis (histB345 i) := by
      simp [eraseSites, g.2.2.2.2.2.2.2.1]
    rw [e, h3]; change raw.basis (OB5.sig 344 (histB345 i)) = _; rw [g.2.2.1]
  have hA_offB (i : Fin 10) : histA345 i ∉ wires (MixedWindow.packW d 345 335) := by
    intro used
    rw [hc.2.2.2.2.2.2.1, Rolling1588.codeEncodeAt, renameProgram_support, (Rolling1588.code_support d).1] at used
    obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp used
    have lt := Finset.mem_range.mp hw
    simp only [MeasuredCodec5.label, dif_pos lt] at eq
    exact hist345_geom.2.2.2 i ⟨w, lt⟩ eq.symm
  have hB_offA (i : Fin 10) : histB345 i ∉ wires (MixedWindow.packW d 345 330) := by
    intro used
    rw [hc.2.2.2.2.1, Rolling1588.codeEncodeAt, renameProgram_support, (Rolling1588.code_support d).1] at used
    obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp used
    have lt := Finset.mem_range.mp hw
    simp only [MeasuredCodec5.label, dif_pos lt] at eq
    exact hist345_geom.2.2.2 ⟨w, lt⟩ i eq
  have hP330_stable (i : Fin 10) : raw.basis (plain330 i) = (run (span 345 15) [] (rawPack325 d raw)).basis (plain330 i) := by
    have hr : ∃ r, 330 ≤ r ∧ r ≤ 334 ∧ (plain330 i = base r ∨ plain330 i = base (1028 + r)) := by
      refine ⟨330 + i.val / 2, by omega, by omega, ?_⟩
      unfold plain330 History5.historyMap History5.historyId
      split_ifs
      · left; rfl
      · right; congr 1; omega
    obtain ⟨r, r1, r2, hq | hq⟩ := hr
    · have hsp : plain330 i ∉ wires (span 345 15) := pastOffSpan 345 15 _ (by decide) ⟨r, by omega, Or.inl hq⟩
      rw [run_preserves_outside _ _ _ _ hsp, rawPack325_outside d raw _ (fun r' a b => by
        rw [hq]; exact ⟨by simp only [base, Wire]; omega, by simp only [base, Wire]; omega⟩)]
    · have hsp : plain330 i ∉ wires (span 345 15) := pastOffSpan 345 15 _ (by decide) ⟨r, by omega, Or.inr hq⟩
      rw [run_preserves_outside _ _ _ _ hsp, rawPack325_outside d raw _ (fun r' a b => by
        rw [hq]; exact ⟨by simp only [base, Wire]; omega, by simp only [base, Wire]; omega⟩)]
  constructor
  · intro i
    have g := hist345_geom.2.2.1 i
    rw [runEq, OrdinaryJ.kept j20 (withArchive345 d) tape pre (histA345 i) g.2.2.2.2.1]
    simp only [withArchive345, packProg345, run_append, run_take]
    rw [run_preserves_outside (archiveLoadP20 k8 d) _ _ _ (fun h => g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        (List.mem_toFinset.mp (load_cover_k8_pub d h))),
      run_preserves_outside (MixedWindow.packW d 345 335) _ _ _ (hA_offB i), hc.2.2.2.2.1]
    exact ArchiveOrdinaryFive.stock_relocated d histA345 plain325 hist345_geom.1 plain325_inj st1 raw _ [] hA_in i
  · intro i
    have g := hist345_geom.2.2.1 i
    rw [runEq, OrdinaryJ.kept j20 (withArchive345 d) tape pre (histB345 i) g.2.2.2.2.2.1]
    simp only [withArchive345, packProg345, run_append, run_take]
    rw [run_preserves_outside (archiveLoadP20 k8 d) _ _ _ (fun h => g.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        (List.mem_toFinset.mp (load_cover_k8_pub d h))), hc.2.2.2.2.2.2.1]
    have hB_mid : ∀ k : Fin 10, (run (MixedWindow.packW d 345 330) t1 st1).basis (histB345 k) =
        (run (span 345 15) [] (rawPack325 d raw)).basis (plain330 k) := fun k =>
      (run_preserves_outside (MixedWindow.packW d 345 330) t1 st1 (histB345 k) (hB_offA k)).trans
        ((hB_in k).trans (hP330_stable k))
    exact ArchiveOrdinaryFive.stock_relocated d histB345 plain330 hist345_geom.2.1 plain330_inj _ _ _ [] hB_mid i

private theorem cell325_eq_plain325 {q : Wire} (hr : ∃ r, 325 ≤ r ∧ r ≤ 329 ∧ (q = base r ∨ q = base (1028 + r))) :
    ∃ i : Fin 10, q = plain325 i := by
  obtain ⟨r, r1, r2, rfl | rfl⟩ := hr
  · refine ⟨⟨2 * (r - 325), by omega⟩, ?_⟩
    simp only [plain325, History5.historyMap, History5.historyId, Fin.val_mk]
    rw [if_pos (by omega)]; congr 1; omega
  · refine ⟨⟨2 * (r - 325) + 1, by omega⟩, ?_⟩
    simp only [plain325, History5.historyMap, History5.historyId, Fin.val_mk]
    rw [if_neg (by omega)]; congr 1; omega

theorem origin345_eq (d : Bool) (raw out : State)
    (hA : ∀ i : Fin 10, out.basis (histA345 i) = (rawPack325 d raw).basis (plain325 i)) :
    ∀ q : Wire, (WideReference.origin 345 (rawPack325 d raw) out).basis q =
      (WideReference20.origin 345 20 15 raw out).basis q := by
  intro q
  by_cases h15 : q ∈ WideReference.sites 345
  · have h20 : q ∈ WideReference20.sites 345 20 15 := by
      rw [WideReference.mem_sites (by decide)] at h15
      rw [WideReference20.mem_sites (by decide)]
      obtain ⟨r, r1, r2, e⟩ := WideReference.old_cell h15
      have hs : oldStart 345 = 330 ∧ oldCount 345 = 15 := by decide
      rw [hs.1] at r1 r2; rw [hs.2] at r2
      simp only [WideReference20.oldSites, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
      refine ⟨r, ⟨by omega, by omega⟩, ?_⟩
      rw [show (345 : Nat) + 15 - 1 = 345 + 14 from rfl]
      rcases e with e | e
      · left; exact e
      · right; simp only [base, Wire] at e ⊢; omega
    rw [WideReference.inside 345 _ out q h15, WideReference20.inside 345 20 15 raw out q h20]
  · rw [WideReference.outside 345 _ out q h15]
    by_cases h20 : q ∈ WideReference20.sites 345 20 15
    · rw [WideReference20.inside 345 20 15 raw out q h20]
      rw [WideReference20.mem_sites (by decide)] at h20
      have hnot : OB5.sig 359 q ∉ WideReference.oldSites 345 := fun h =>
        h15 ((WideReference.mem_sites (by decide) q).mpr h)
      obtain ⟨r, r1, r2, e⟩ := WideReference20.old_cell h20
      rw [show (345 : Nat) + 15 - 1 = 359 from rfl] at e
      have hr : 325 ≤ r ∧ r ≤ 329 := by
        by_contra hbad
        apply hnot
        have hs : oldStart 345 = 330 ∧ oldCount 345 = 15 := by decide
        simp only [WideReference.oldSites, hs.1, hs.2, List.mem_flatMap, List.mem_range'_1,
          List.mem_cons, List.not_mem_nil, or_false]
        refine ⟨r, ⟨by omega, by omega⟩, ?_⟩
        rcases e with e | e
        · left; exact e
        · right; simp only [base, Wire] at e ⊢; omega
      obtain ⟨i, hi⟩ := cell325_eq_plain325 ⟨r, hr.1, hr.2, by
        rcases e with e | e; exact Or.inl e; exact Or.inr (by simp only [base, Wire] at e ⊢; omega)⟩
      have hq : q = histA345 i := by
        have h1 := (hist345_geom.2.2.1 i).2.1
        have h2 : OB5.sig 359 q = OB5.sig 359 (histA345 i) := hi.trans h1.symm
        exact OB5.sig_injective 359 (by decide) h2
      have hsp : plain325 i ∉ wires (span 345 15) := by
        apply pastOffSpan 345 15 _ (by decide)
        rcases e with e | e
        · exact ⟨r, by omega, Or.inl (hi.symm.trans e)⟩
        · exact ⟨r, by omega, Or.inr (hi.symm.trans (by simp only [base, Wire] at e ⊢; omega))⟩
      rw [show (345 : Nat) + 14 = 359 from rfl, hi, run_preserves_outside _ _ _ _ hsp, hq, hA i]
    · rw [WideReference20.outside 345 20 15 raw out q h20, show (345 : Nat) + 14 = 359 from rfl,
        show (345 : Nat) + 15 - 1 = 359 from rfl, rawPack325_span_comm]
      apply rawPack325_outside d _ _
      intro r r1 r2
      have hnot : OB5.sig 359 q ∉ WideReference20.oldSites 345 20 := fun h =>
        h20 ((WideReference20.mem_sites (by decide) q).mpr h)
      refine ⟨fun e => hnot ?_, fun e => hnot ?_⟩
      · simp only [WideReference20.oldSites, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨r, ⟨by omega, by omega⟩, Or.inl e⟩
      · simp only [WideReference20.oldSites, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨r, ⟨by omega, by omega⟩, Or.inr e⟩

/-! ### Section 2: `mirror_origin345`, `band_clean345`, `upper_clear345`, `admitted345`, `endpoint345` -/

private theorem j20_vals :
    start j20 = 345 ∧ Shadow7.sbP 345 = 76 ∧ Shadow7.wpP 345 = 77 ∧ Shadow7.e0P 345 = 1650 ∧
    EnterJ7.flagN j20 = 1655 ∧ EnterJ7.flagF j20 = 1653 ∧ EnterJ7.flagU j20 = 1654 ∧
    EnterJ7.pending j20 = [1656, 1657, 1658] ∧ railP 345 = 168 ∧ railP 359 = 154 := by
  decide +kernel

private theorem admin345_away (q : Wire)
    (hq : (1301 ≤ (q : Nat) ∧ (q : Nat) ≤ 1058 + 345) ∨
          (2070 ≤ (q : Nat) + 345 ∧ (q : Nat) ≤ 1812 ∧
           ¬ (2070 ≤ (q : Nat) + 345 ∧ (q : Nat) + 345 < 2090))) :
    q ∉ support345 ++ ArchiveJ20.rawPortsList k8 := by
  intro mem
  rw [List.mem_append, ArchiveJ20.raw_split, List.mem_append] at mem
  have hall : (support345 ++ ArchiveJ20.rawHead k8).all (fun w =>
      decide ((w : Nat) < 1301 ∨ (1058 + 345 < (w : Nat) ∧ (w : Nat) + 345 < 2070) ∨
        (2070 ≤ (w : Nat) + 345 ∧ (w : Nat) + 345 < 2090))) = true := by
    decide +kernel
  rcases mem with h | h | h
  · have := of_decide_eq_true (List.all_eq_true.mp hall q (List.mem_append_left _ h))
    simp only [Wire] at *; omega
  · have := of_decide_eq_true (List.all_eq_true.mp hall q (List.mem_append_right _ h))
    simp only [Wire] at *; omega
  · obtain ⟨k, hk, eq⟩ := List.mem_map.mp h; rw [List.mem_range] at hk
    have hb : 1556 ≤ (q : Nat) ∧ (q : Nat) ≤ 1699 := by
      rw [← eq]; unfold archScratch20; dsimp only; split_ifs <;> (unfold Wire; omega)
    simp only [Wire] at *; omega

attribute [local irreducible] run SkywalkNat.step nextWindow345 window345 withArchive345 Shadow7.enterP Shadow7.body in
private theorem mirror_origin345 (d : Bool) (raw s : State) (m t : List Bool) (neg far long : Bool)
    (packed : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) neg far long
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s))
    (q : Wire) (lo : 2070 ≤ (q : Nat) + 345) (hi : (q : Nat) ≤ 1812) :
    let history := run (window345 d) t (run (Shadow7.enterP j20) m s)
    history.basis q = (WideReference20.origin 345 20 15 raw history).basis q := by
  intro history
  have ext : ¬ WideReference20.Box20 345 15 q := by
    unfold WideReference20.Box20
    rw [show 345 + 15 - 1 = 359 from rfl, WideReference.route_eq 345 (by decide), WideReference.route_eq 359 (by decide)]
    simp only [Wire] at *; split_ifs <;> omega
  have wn : windowNet j20 q = 3113 - q := by
    show OB5.sig 359 q = _
    exact NativeJ7.sig_moved 359 q (Or.inr ⟨by simp only [Wire] at *; omega, hi⟩)
  have free : ¬ Shadow7.MayTouch j20 (windowNet j20 q) := by
    rw [wn]; unfold Shadow7.MayTouch
    have jv := j20_vals; simp only [Shadow7.shape, Shadow7.smallBits, jv.1, jv.2.1, Wire] at *; omega
  have port : q ∉ EnterJ7.ports j20 := fun mem => by
    have r := EnterJ7.portsRegion j20 mem; have jv := j20_vals
    simp only [jv.1, jv.2.1, Wire] at *; omega
  apply WideReference20.box_origin20 (by decide) (by decide) (by decide) ext raw history
  intro notSite
  have notAdmin : q ∉ support345 ++ ArchiveJ20.rawPortsList k8 := by
    by_cases hb : 2070 ≤ (q : Nat) + 345 ∧ (q : Nat) + 345 < 2090
    · exfalso; apply notSite
      rw [WideReference20.mem_sites (by decide), show 345 + 15 - 1 = 359 from rfl,
        show OB5.sig 359 q = 3113 - q from wn]
      simp only [WideReference20.oldSites, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨2069 - (q : Nat), ⟨by simp only [Wire] at *; omega, by simp only [Wire] at *; omega⟩,
        Or.inr (by simp only [base, Wire] at *; omega)⟩
    · exact admin345_away q (Or.inr ⟨lo, hi, hb⟩)
  have stay := Shadow7.ext_head (Shadow7.enterP j20) j20 (withArchive345 d) (support345 ++ ArchiveJ20.rawPortsList k8)
    s m t q free (EnterJ7.notWire j20 port) notAdmin (admin_cover345 d)
  have jv := j20_vals
  have hn : q ≠ EnterJ7.flagN j20 := by rw [jv.2.2.2.2.1]; simp only [Wire] at *; omega
  have hf : q ≠ EnterJ7.flagF j20 := by rw [jv.2.2.2.2.2.1]; simp only [Wire] at *; omega
  have hu : q ≠ EnterJ7.flagU j20 := by rw [jv.2.2.2.2.2.2.1]; simp only [Wire] at *; omega
  have hi' : q ∉ RailPair.sites (EnterJ7.upperPairs j20) := fun mm => by
    have u := EnterJ7.upperSites j20 mm; simp only [jv.1, jv.2.1, jv.2.2.1, Wire] at *; omega
  have pend : q ∉ EnterJ7.pending j20 := by
    rw [jv.2.2.2.2.2.2.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false, Wire] at *; omega
  have old := packed.unchanged q hn hf hu hi'
  have pullEq : OB5.sig 344 q = 3113 - q := NativeJ7.sig_moved 344 q (Or.inr ⟨by simp only [Wire] at *; omega, hi⟩)
  have hwEq : window345 d = Shadow7.body j20 (withArchive345 d) := by unfold window345; rfl
  change (run (window345 d) t (run (Shadow7.enterP j20) m s)).basis q = _
  rw [hwEq, stay]
  have e : s.basis q = (eraseSites (EnterJ7.pending j20) s).basis q := by simp [eraseSites, pend]
  rw [e, old]; rfl

attribute [local irreducible] run SkywalkNat.step nextWindow345 window345 withArchive345 Shadow7.enterP Shadow7.body in
private theorem band_clean345 (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool)
    (domain : Domain 345 x p raw) (neg far long : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) neg far long
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s)) :
    ∀ q : Nat, 1301 ≤ q → q ≤ 1058 + 345 → (run (nextWindow345 d) m s).basis q = false := by
  intro q lo hi
  have jv := j20_vals
  have split : run (nextWindow345 d) m s = run (Shadow7.body j20 (withArchive345 d))
      (m.drop (measurementCount (Shadow7.enterP j20))) (run (Shadow7.enterP j20) m s) := by
    simp only [nextWindow345, window345, run_append, run_take]
  rw [split]
  have wn : windowNet j20 q = 3113 - q := NativeJ7.sig_moved 359 q (Or.inl ⟨lo, by omega⟩)
  have free : ¬ Shadow7.MayTouch j20 (windowNet j20 q) := by
    rw [wn]; unfold Shadow7.MayTouch; simp only [Shadow7.shape, Shadow7.smallBits, jv.1, jv.2.1, Wire] at *; omega
  have port : q ∉ EnterJ7.ports j20 := fun mem => by
    have r := EnterJ7.portsRegion j20 mem; simp only [jv.1, jv.2.1, Wire] at *; omega
  have notAdmin := admin345_away q (Or.inl ⟨lo, hi⟩)
  rw [Shadow7.ext_head (Shadow7.enterP j20) j20 (withArchive345 d) _ s m _ q free (EnterJ7.notWire j20 port) notAdmin
    (admin_cover345 d)]
  have hn : (q : Wire) ≠ EnterJ7.flagN j20 := by rw [jv.2.2.2.2.1]; omega
  have hf : (q : Wire) ≠ EnterJ7.flagF j20 := by rw [jv.2.2.2.2.2.1]; omega
  have hu : (q : Wire) ≠ EnterJ7.flagU j20 := by rw [jv.2.2.2.2.2.2.1]; omega
  have hi' : (q : Wire) ∉ RailPair.sites (EnterJ7.upperPairs j20) := fun mm => by
    have u := EnterJ7.upperSites j20 mm; simp only [jv.1, jv.2.1, jv.2.2.1, Wire] at *; omega
  have pend : (q : Wire) ∉ EnterJ7.pending j20 := by
    rw [jv.2.2.2.2.2.2.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false, Wire]; omega
  have old := cut.unchanged q hn hf hu hi'
  have e1 : s.basis q = (eraseSites (EnterJ7.pending j20) s).basis q := by simp [eraseSites, pend]
  rw [e1, old]; show raw.basis (OB5.sig 344 q) = false
  by_cases mv : q ≤ 1043 + 345
  · rw [NativeJ7.sig_moved 344 q (Or.inl ⟨lo, by omega⟩)]
    have c := WideReference.full_carry 345 0 x p (by decide) good raw domain [] (3113 - q) (by omega) (by omega)
    simpa only [WideReference.span, run] using c
  · rw [NativeJ7.sig_kept 344 q (by omega) (by omega)]
    rw [show (q : Wire) = base (1028 + (q - 1044)) by simp only [base, Wire]; omega]
    exact WideReference.future_history (show 345 ≤ q - 1044 by omega) (by omega) domain

attribute [local irreducible] run SkywalkNat.step nextWindow345 window345 withArchive345 Shadow7.enterP Shadow7.body in
private theorem upper_clear345 (d : Bool) (raw s : State) (x p : Nat) (domain : Domain 345 x p raw)
    (m t : List Bool) (neg far long : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) neg far long
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s)) :
    ∀ q : Nat, 345 + Shadow7.sbP 345 + 48 ≤ q → q ≤ min (345 + 30 + railP 359) 529 →
      (run (window345 d) t (run (Shadow7.enterP j20) m s)).basis q = false := by
  intro q lo hi
  have jv := j20_vals
  have hq : 469 ≤ q ∧ q ≤ 529 := by omega
  have wn : windowNet j20 q = q := NativeJ7.sig_kept 359 q (by omega) (by omega)
  have free : ¬ Shadow7.MayTouch j20 (windowNet j20 q) := by
    rw [wn]; unfold Shadow7.MayTouch; simp only [Shadow7.shape, Shadow7.smallBits, jv.1, jv.2.1, Wire] at *; omega
  have port : (q : Wire) ∉ EnterJ7.ports j20 := fun mem => by
    have r := EnterJ7.portsRegion j20 mem; simp only [jv.1, jv.2.1, Wire] at *; omega
  have notAdmin : (q : Wire) ∉ support345 ++ ArchiveJ20.rawPortsList k8 := by
    intro mem; rw [List.mem_append, ArchiveJ20.raw_split, List.mem_append] at mem
    rcases mem with h | h | h
    · have := (codesOld345.2.2.2.2 q (List.mem_append_right _ h)).2.2.2; simp only [Wire] at *; omega
    · have := (codesOld345.2.2.2.2 q (List.mem_append_left _ h)).2.2.2; simp only [Wire] at *; omega
    · obtain ⟨k, hk, eq⟩ := List.mem_map.mp h; rw [List.mem_range] at hk
      have hb : 1556 ≤ q ∧ q ≤ 1699 := by
        rw [← eq]; unfold archScratch20; dsimp only; split_ifs <;> (unfold Wire; omega)
      omega
  have stay := Shadow7.ext_head (Shadow7.enterP j20) j20 (withArchive345 d) _ s m t q free
    (EnterJ7.notWire j20 port) notAdmin (admin_cover345 d)
  have pend : (q : Wire) ∉ EnterJ7.pending j20 := by
    rw [jv.2.2.2.2.2.2.2.1]; simp only [List.mem_cons, List.not_mem_nil, or_false, Wire]; omega
  have hwEq : window345 d = Shadow7.body j20 (withArchive345 d) := by unfold window345; rfl
  rw [hwEq, stay]
  have e : s.basis q = (eraseSites (EnterJ7.pending j20) s).basis q := by simp [eraseSites, pend]
  rw [e]
  by_cases hq529 : q < 529
  · have hup : (q : Wire) ∈ (EnterJ7.upperPairs j20).map Prod.fst := by
      have hu : EnterJ7.upperPairs j20 = (List.range 75).map (fun i => (454 + i, 879 + i)) := by decide +kernel
      rw [hu, List.mem_map]
      refine ⟨(q, q + 425), ?_, rfl⟩
      rw [List.mem_map]; exact ⟨q - 454, List.mem_range.mpr (by omega), by ext <;> (simp only [Wire]; omega)⟩
    obtain ⟨pair, hpm, rfl⟩ := List.mem_map.mp hup
    exact (cut.upper pair hpm).1
  · have hqeq : q = 529 := by omega
    subst hqeq
    have hn : (529 : Wire) ≠ EnterJ7.flagN j20 := by rw [jv.2.2.2.2.1]; decide
    have hf : (529 : Wire) ≠ EnterJ7.flagF j20 := by rw [jv.2.2.2.2.2.1]; decide
    have hu : (529 : Wire) ≠ EnterJ7.flagU j20 := by rw [jv.2.2.2.2.2.2.1]; decide
    have notHi : (529 : Wire) ∉ RailPair.sites (EnterJ7.upperPairs j20) := fun mm => by
      have u := EnterJ7.upperSites j20 mm; simp only [jv.1, jv.2.1, jv.2.2.1, Wire] at *; omega
    have same : EnterJ7.pull j20 529 = 529 := by decide
    have free : (529 : Wire) ∈ (W.compactSkywalkSignPoolA base 345).released ∨ 345 + 274 ≤ 529 ∧ 529 < 786 := by decide +kernel
    have src := WideReference.incoming_free_A 345 x p (by decide) raw domain 529 (by omega) (by omega) free
    exact (cut.unchanged 529 hn hf hu notHi).trans (by simpa only [pullState, same] using src)

attribute [local irreducible] run SkywalkNat.step Shadow.far nextWindow345 nextUnwind345 window345 withArchive345
  Shadow7.enterP Shadow7.body in
theorem admitted345 (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool)
    (domain : Domain 345 x p raw) (G S : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) (PortalValues.negative S (unsigned 345 x p).u)
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p)))
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p) ∧ 2 ^ Shadow7.sbP 345 ≤ (unsigned 345 x p).u))
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s))
    (input : SkywalkIntegerInput (EnterJ7.lay j20)
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).a
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).b G raw.basis)
    (pg ps cross : Bool)
    (prior : PastFacts20 k8 (ArchiveJ20.rawPorts k8) (unsigned 325 x p) pg ps cross s) :
    let out := run (nextWindow345 d) m s
    LeaveJ7.Admission.Inputs j20 out (unsigned 345 x p) G S ∧
    out.phase = s.phase ∧
    (∀ t, run (TickCut.Reentry20.nextUnwind345 d) t out = s) := by
  have nums := LeaveJ7.Admission.actualNumbers j20 (by decide) (by decide) x p good
  have old := actualNumbers20 k8 x p good
  have hist := WideReference.pulled_history j20 rfl domain
  let pre := run (Shadow7.enterP j20) m s
  let tape := m.drop (measurementCount (Shadow7.enterP j20))
  let T := Shadow.reduced (Shadow7.sbP 345) 15 (unsigned 345 x p)
  let Z := encode G S T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd_shadow7 (Shadow7.sbP 345) (unsigned 345 x p) nums.farSmall nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum G S _ _ (by omega)
  have ready := EnterJ7.ready_pending_at j20 raw s (unsigned 345 x p) G S m nums.farSmall cut input hist
  have scr := scratch_raw_clean345 d raw s m x p good domain _ _ _ Z parity ready.2.1 cut
  have nw := TickCut.Reentry20.next_window345 d raw s m (unsigned 345 x p) G S nums.odd nums.farSmall cut input hist scr
    (unsigned 325 x p) pg ps cross old.odd old.small.1 prior
  obtain ⟨_, _, _, _, tags⟩ := real_receipt345 d raw s m (unsigned 345 x p) G S nums.odd nums.farSmall
    cut input hist scr (unsigned 325 x p) pg ps cross old.odd old.small.1 prior
  have sv := saved_with_pending345 d raw s (unsigned 345 x p) G S m tape nums.farSmall cut input
  have pk := parked_clean345 d raw s (unsigned 345 x p) G S m tape nums.farSmall cut input
  obtain ⟨_, _, row, limit, frame⟩ := admits345 d s m tape (tape.drop (measurementCount (Shadow7.routed j20 0 1)))
    Z parity ready.2.1 scr (unsigned 325 x p) pg ps cross old.odd old.small.1 prior
  have cframe : Frame (ArchiveJ20.codePorts k8) (code d) row
      (run (withArchive345 d) (tape.drop (measurementCount (Shadow7.routed j20 0 1))) (run (Shadow7.routed j20 0 1) tape pre)) := by
    rw [show withArchive345 d = packProg345 d ++ archiveLoadP20 k8 d by unfold withArchive345; rfl]
    exact from_append (prop := Frame (ArchiveJ20.codePorts k8) (code d) row)
      (ArchiveJ20.load_run k8 d row limit _ _ frame).2.1
  have top := top_clean345 d x p raw s domain m tape _ _ _ cut row cframe
  have top2 := top_clean345' d x p raw s domain m tape _ _ _ cut row cframe
  have tail := tail_clean345 d x p raw s domain m tape _ _ _ cut row cframe
  have runEq : run (nextWindow345 d) m s = run (window345 d) tape pre := by
    simp only [nextWindow345, run_append, run_take, pre, tape]
  refine ⟨?_, nw.1, nw.2.2.2⟩
  apply LeaveJ7.Admission.assemble j20 (by decide) (by decide) _ (unsigned 345 x p) G S nums nw.2.1 nw.2.2.1
  · rw [runEq, ← NativeJ7.saved_ys j20 (by decide) (by decide)]
    have jv := j20_vals
    refine ⟨sv.1, ?_, ?_, ?_⟩
    · rw [show Shadow7.e0P (start j20) + 5 = EnterJ7.flagN j20 by rw [jv.1, jv.2.2.2.1, jv.2.2.2.2.1]]; exact sv.2.1
    · rw [show Shadow7.e0P (start j20) + 3 = EnterJ7.flagF j20 by rw [jv.1, jv.2.2.2.1, jv.2.2.2.2.2.1]]; exact sv.2.2.1
    · rw [show Shadow7.e0P (start j20) + 4 = EnterJ7.flagU j20 by rw [jv.1, jv.2.2.2.1, jv.2.2.2.2.2.2.1]]; exact sv.2.2.2
  · intro q hq
    rw [LeaveJ7.Admission.mem_spare] at hq
    have jv := j20_vals
    rcases hq with rfl | rfl | ⟨lo, hi⟩
    · have t := tags ⟨0, by decide⟩
      rw [show Shadow7.e0P (start j20) + 6 = 1656 + 0 by rw [jv.1, jv.2.2.2.1]]; exact t
    · have t := tags ⟨1, by decide⟩
      rw [show Shadow7.e0P (start j20) + 7 = 1656 + 1 by rw [jv.1, jv.2.2.2.1]]; exact t
    · rw [runEq]
      apply tail q
      simp only [tailTemps345, List.mem_range'_1, jv.1, jv.2.2.1, jv.2.2.2.1] at lo hi ⊢
      simp only [Wire] at *; omega
  · intro q lo hi
    have jv := j20_vals
    rw [jv.1] at lo hi; rw [jv.2.2.1] at hi; omega
  · rw [runEq]; exact top
  · rw [runEq]; exact top2
  · rw [runEq]; exact pk

/-! ### Section 3: Canonical 20-Tick Key `value20`, `selected_receipt345`, `endpoint345`, `cleared_holes345` -/

noncomputable def value20 (x p : Nat) (k : Fin 9) : Nat → Bool :=
  let s := start20 k
  let z := unsigned s x p
  let xs := SkywalkTrace.trace 20 (WideReference.canonical s x p)
  let f := decide (Shadow.far (sbP20 s) 20 z)
  let u := f && StairArchiveTrace.afterFlags (decide (z.v < z.u)) (xs.take 10)
  let c := f && HighBankSum.crossBit (TrueMiddle20.d k z)
  StairArchiveRaw.rawBit (StairArchiveRaw.read (xs.drop 10)) f u c

private theorem trace_drop_eq (n k : Nat) (z : SkywalkRails.State) :
    (SkywalkTrace.trace (k + n) z).drop k = SkywalkTrace.trace n (SkywalkTrace.next^[k] z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + n = (k + n) + 1 by omega, SkywalkTrace.trace, List.drop_succ_cons, Function.iterate_succ_apply]
    exact ih (SkywalkTrace.next z)

theorem value20_chronology (x p : Nat) (k : Fin 9) (r : Nat) (h : Encodes (value20 x p k) r) :
    ArchiveStockRows.Chronology (start20 k + 5) x p r := by
  intro q
  have bit := h ⟨q.val, by omega⟩
  simp only [value20, StairArchiveRaw.rawBit, q.isLt, ↓reduceIte] at bit
  have h1 : (SkywalkTrace.trace 20 (WideReference.canonical (start20 k) x p)).drop 10 =
      SkywalkTrace.trace 10 (SkywalkTrace.next^[10] (WideReference.canonical (start20 k) x p)) :=
    trace_drop_eq 10 10 _
  have h2 : (SkywalkTrace.trace 15 (WideReference.canonical (start20 k + 5) x p)).drop 5 =
      SkywalkTrace.trace 10 (SkywalkTrace.next^[5] (WideReference.canonical (start20 k + 5) x p)) :=
    trace_drop_eq 10 5 _
  have h3 : SkywalkTrace.next^[5] (WideReference.canonical (start20 k + 5) x p) =
      SkywalkTrace.next^[10] (WideReference.canonical (start20 k) x p) := by
    unfold WideReference.canonical
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, show 5 + (start20 k + 5) = 10 + start20 k by omega]
  rw [h1, ← h3, ← h2] at bit
  exact bit

theorem frame_key20 (k : Fin 9) (ps : Ports) (chron : ∀ i : Fin 20, ps ⟨i, by omega⟩ = nativeRawPort20 k i)
    (r : Nat) (z : SkywalkNat.State) (g sg cross : Bool) (before out : State)
    (prior : PastFacts20 k ps z g sg cross before)
    (kept : ∀ i : Fin 23, out.basis (ps ⟨i, by omega⟩) = before.basis (ps ⟨i, by omega⟩))
    (frame : Frame ps raw r out) :
    let xs := SkywalkTrace.trace 20 (encode g sg z.u z.v)
    let f := decide (Shadow.far (sbP20 (start20 k)) 20 z)
    let u := f && StairArchiveTrace.afterFlags (decide (z.v < z.u)) (xs.take 10)
    Encodes (StairArchiveRaw.rawBit (StairArchiveRaw.read (xs.drop 10)) f u (f && cross)) r := by
  intro xs f u q
  have same : (rawCol q).testBit r = before.basis (ps ⟨q, by omega⟩) :=
    ((congrArg (fun n : Nat => n.testBit r) (io true true ⟨q, by omega⟩).1).trans (frame ⟨q, by omega⟩).symm).trans (kept q)
  by_cases h : q.val < 20
  · have eq := row_truth20 k ps chron r z g sg before out prior.records kept frame ⟨q, h⟩
    simpa only [StairArchiveRaw.rawBit, if_pos h] using eq
  · rcases q with ⟨q, bound⟩
    change ¬ q < 20 at h
    have cases : q = 20 ∨ q = 21 ∨ q = 22 := by omega
    rcases cases with rfl | rfl | rfl
    · exact same.trans prior.far
    · have h := same.trans prior.suffix; rw [prior.records] at h; exact h
    · exact same.trans prior.crossed

private theorem fourHoles345_eq :
    fourHoles345 = (List.finRange 4).map (fun i : Fin 4 => ArchiveJ20.codePorts k8 ⟨150 + i.val, by omega⟩) := by
  decide +kernel

attribute [local irreducible] run SkywalkNat.step nextWindow345 window345 withArchive345 Shadow7.enterP Shadow7.body in
theorem selected_receipt345 (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool)
    (domain : Domain 345 x p raw) (G S : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) (PortalValues.negative S (unsigned 345 x p).u)
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p)))
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p) ∧ 2 ^ Shadow7.sbP 345 ≤ (unsigned 345 x p).u))
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s))
    (input : SkywalkIntegerInput (EnterJ7.lay j20)
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).a
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).b G raw.basis)
    (pg ps : Bool)
    (canon : StockWindowTicket.signedAt 325 x p pg ps = WideReference.canonical 325 x p)
    (prior : PastFacts20 k8 (ArchiveJ20.rawPorts k8) (unsigned 325 x p) pg ps
      (HighBankSum.crossBit (TrueMiddle20.d k8 (unsigned 325 x p))) s) :
    SavedKey (value20 x p k8) (ArchiveJ20.codePorts k8) d (run (nextWindow345 d) m s) := by
  have nums := LeaveJ7.Admission.actualNumbers j20 (by decide) (by decide) x p good
  have old := actualNumbers20 k8 x p good
  have hist := WideReference.pulled_history j20 rfl domain
  let pre := run (Shadow7.enterP j20) m s
  let tape := m.drop (measurementCount (Shadow7.enterP j20))
  let T := Shadow.reduced (Shadow7.sbP 345) 15 (unsigned 345 x p)
  let Z := encode G S T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd_shadow7 (Shadow7.sbP 345) (unsigned 345 x p) nums.farSmall nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum G S _ _ (by omega)
  have ready := EnterJ7.ready_pending_at j20 raw s (unsigned 345 x p) G S m nums.farSmall cut input hist
  have scr := scratch_raw_clean345 d raw s m x p good domain _ _ _ Z parity ready.2.1 cut
  obtain ⟨_, _, row, limit, frame⟩ := admits345 d s m tape (tape.drop (measurementCount (Shadow7.routed j20 0 1)))
    Z parity ready.2.1 scr (unsigned 325 x p) pg ps _ old.odd old.small.1 prior
  have held := bank_kept345 d s m tape (tape.drop (measurementCount (Shadow7.routed j20 0 1))) Z parity ready.2.1
  have all := frame_key20 k8 (ArchiveJ20.rawPorts k8) chron345 row (unsigned 325 x p) pg ps _ s _ prior held frame
  have hval : StairArchiveRaw.rawBit
      (StairArchiveRaw.read ((SkywalkTrace.trace 20 (encode pg ps (unsigned 325 x p).u (unsigned 325 x p).v)).drop 10))
      (decide (Shadow.far (sbP20 (start20 k8)) 20 (unsigned 325 x p)))
      (decide (Shadow.far (sbP20 (start20 k8)) 20 (unsigned 325 x p)) &&
        StairArchiveTrace.afterFlags (decide ((unsigned 325 x p).v < (unsigned 325 x p).u))
          ((SkywalkTrace.trace 20 (encode pg ps (unsigned 325 x p).u (unsigned 325 x p).v)).take 10))
      (decide (Shadow.far (sbP20 (start20 k8)) 20 (unsigned 325 x p)) &&
        HighBankSum.crossBit (TrueMiddle20.d k8 (unsigned 325 x p))) = value20 x p k8 := by
    unfold value20; dsimp only
    change _ = StairArchiveRaw.rawBit (StairArchiveRaw.read ((SkywalkTrace.trace 20 (WideReference.canonical 325 x p)).drop 10)) _ _ _
    unfold StockWindowTicket.signedAt at canon; rw [canon]; rfl
  dsimp only at all; rw [hval] at all
  have spec := select_spec ⟨row, limit, all⟩
  have rf := reframe limit all (ArchiveJ20.rawPorts k8) _ frame
  have cframe : Frame (ArchiveJ20.codePorts k8) (code d) (select (value20 x p k8))
      (run (withArchive345 d) (tape.drop (measurementCount (Shadow7.routed j20 0 1))) (run (Shadow7.routed j20 0 1) tape pre)) := by
    rw [show withArchive345 d = packProg345 d ++ archiveLoadP20 k8 d by unfold withArchive345; rfl]
    exact from_append (prop := Frame (ArchiveJ20.codePorts k8) (code d) (select (value20 x p k8)))
      (ArchiveJ20.load_run k8 d _ spec.1 _ _ rf).2.1
  have runEq : run (nextWindow345 d) m s = run (Shadow7.body j20 (withArchive345 d)) tape pre := by
    simp only [nextWindow345, window345, run_append, run_take, pre, tape]
  rw [runEq]
  exact ⟨spec.1, spec.2, Shadow7.body_keeps j20 (withArchive345 d) (ArchiveJ20.codePorts k8) d _ pre tape
    (fun i => Shadow7.old_clear (by decide) (codesOld345.1 i)) cframe⟩

attribute [local irreducible] run SkywalkNat.step nextWindow345 window345 withArchive345 Shadow7.enterP Shadow7.body in
theorem cleared_holes345 (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool)
    (domain : Domain 345 x p raw) (G S : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) (PortalValues.negative S (unsigned 345 x p).u)
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p)))
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p) ∧ 2 ^ Shadow7.sbP 345 ≤ (unsigned 345 x p).u))
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s))
    (input : SkywalkIntegerInput (EnterJ7.lay j20)
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).a
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).b G raw.basis)
    (pg ps cross : Bool)
    (prior : PastFacts20 k8 (ArchiveJ20.rawPorts k8) (unsigned 325 x p) pg ps cross s) :
    ∀ q ∈ fourHoles345, (run (nextWindow345 d) m s).basis q = false := by
  have nums := LeaveJ7.Admission.actualNumbers j20 (by decide) (by decide) x p good
  have old := actualNumbers20 k8 x p good
  have hist := WideReference.pulled_history j20 rfl domain
  let pre := run (Shadow7.enterP j20) m s
  let tape := m.drop (measurementCount (Shadow7.enterP j20))
  let T := Shadow.reduced (Shadow7.sbP 345) 15 (unsigned 345 x p)
  let Z := encode G S T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd_shadow7 (Shadow7.sbP 345) (unsigned 345 x p) nums.farSmall nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum G S _ _ (by omega)
  have ready := EnterJ7.ready_pending_at j20 raw s (unsigned 345 x p) G S m nums.farSmall cut input hist
  have scr := scratch_raw_clean345 d raw s m x p good domain _ _ _ Z parity ready.2.1 cut
  obtain ⟨_, _, row, limit, frame⟩ := admits345 d s m tape (tape.drop (measurementCount (Shadow7.routed j20 0 1)))
    Z parity ready.2.1 scr (unsigned 325 x p) pg ps cross old.odd old.small.1 prior
  have cframe : Frame (ArchiveJ20.codePorts k8) (code d) row
      (run (withArchive345 d) (tape.drop (measurementCount (Shadow7.routed j20 0 1))) (run (Shadow7.routed j20 0 1) tape pre)) := by
    rw [show withArchive345 d = packProg345 d ++ archiveLoadP20 k8 d by unfold withArchive345; rfl]
    exact from_append (prop := Frame (ArchiveJ20.codePorts k8) (code d) row)
      (ArchiveJ20.load_run k8 d row limit _ _ frame).2.1
  have runEq : run (nextWindow345 d) m s = run (Shadow7.body j20 (withArchive345 d)) tape pre := by
    simp only [nextWindow345, window345, run_append, run_take, pre, tape]
  intro q hq
  have hmem : ∃ i : Fin 4, ArchiveJ20.codePorts k8 ⟨150 + i.val, by omega⟩ = q := by
    rw [fourHoles345_eq, List.mem_map] at hq
    obtain ⟨i, _, eq⟩ := hq; exact ⟨i, eq⟩
  obtain ⟨i, hi⟩ := hmem
  rw [runEq]
  exact Shadow7.after_encoded j20 (withArchive345 d) (ArchiveJ20.codePorts k8) d row pre tape cframe
    ⟨150 + i.val, by omega⟩ (by dsimp; omega) q hi (codesOld345.2.2.1 q hq)

attribute [local irreducible] run SkywalkNat.step Shadow.far nextWindow345 nextUnwind345 window345 withArchive345
  Shadow7.enterP Shadow7.body CRTBarrel.leave CRTBarrel.unleave Shadow7.leaveP in
theorem endpoint345 (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m n : List Bool)
    (domain : Domain 345 x p raw) (G S : Bool)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) (PortalValues.negative S (unsigned 345 x p).u)
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p)))
      (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p) ∧ 2 ^ Shadow7.sbP 345 ≤ (unsigned 345 x p).u))
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s))
    (input : SkywalkIntegerInput (EnterJ7.lay j20)
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).a
      (encode G S (unsigned 345 x p).u (unsigned 345 x p).v).b G raw.basis)
    (pg ps cross : Bool)
    (prior : PastFacts20 k8 (ArchiveJ20.rawPorts k8) (unsigned 325 x p) pg ps cross s) :
    let v := run (nextWindow345 d) m s
    let out := run (CRTBarrel.leave j20) n v
    out.phase = s.phase ∧
    PackedCut (EnterJ7.lowerPairs ⟨21, by decide⟩) (EnterJ7.upperPairs ⟨21, by decide⟩)
      (EnterJ7.gate ⟨21, by decide⟩) (EnterJ7.flagN ⟨21, by decide⟩) (EnterJ7.flagF ⟨21, by decide⟩)
      (EnterJ7.flagU ⟨21, by decide⟩)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned 345 x p) G S).2 (unsigned 360 x p).u)
      (decide (Shadow.far (Shadow7.sbP 360) 15 (unsigned 360 x p)))
      (decide (Shadow.far (Shadow7.sbP 360) 15 (unsigned 360 x p) ∧ 2 ^ Shadow7.sbP 360 ≤ (unsigned 360 x p).u))
      (pullState (EnterJ7.pull ⟨21, by decide⟩) (WideReference.endRaw 345 (rawPack325 d raw) v))
      (eraseSites (EnterJ7.pending ⟨21, by decide⟩) out) ∧
    PastFacts j20 (ArchiveJ7.rawPorts j20) (Shadow7.sbP 345) (unsigned 345 x p) G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j20 (unsigned 345 x p))) out ∧
    (∀ r, run (CRTBarrel.unleave j20) r out = v) ∧
    (∀ r, run (TickCut.Reentry20.nextUnwind345 d) r v = s) := by
  have nums := LeaveJ7.Admission.actualNumbers j20 (by decide) (by decide) x p good
  have old := actualNumbers20 k8 x p good
  have hist := WideReference.pulled_history j20 rfl domain
  let pre := run (Shadow7.enterP j20) m s
  let tape := m.drop (measurementCount (Shadow7.enterP j20))
  let T := Shadow.reduced (Shadow7.sbP 345) 15 (unsigned 345 x p)
  let Z := encode G S T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd_shadow7 (Shadow7.sbP 345) (unsigned 345 x p) nums.farSmall nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum G S _ _ (by omega)
  have ready := EnterJ7.ready_pending_at j20 raw s (unsigned 345 x p) G S m nums.farSmall cut input hist
  have scr := scratch_raw_clean345 d raw s m x p good domain _ _ _ Z parity ready.2.1 cut
  have adm := admitted345 d x p good raw s m domain G S cut input pg ps cross prior
  obtain ⟨_, _, _, _, tags⟩ := real_receipt345 d raw s m (unsigned 345 x p) G S nums.odd nums.farSmall
    cut input hist scr (unsigned 325 x p) pg ps cross old.odd old.small.1 prior
  obtain ⟨_, _, row, limit, frame⟩ := admits345 d s m tape (tape.drop (measurementCount (Shadow7.routed j20 0 1)))
    Z parity ready.2.1 scr (unsigned 325 x p) pg ps cross old.odd old.small.1 prior
  have cframe : Frame (ArchiveJ20.codePorts k8) (code d) row
      (run (withArchive345 d) (tape.drop (measurementCount (Shadow7.routed j20 0 1))) (run (Shadow7.routed j20 0 1) tape pre)) := by
    rw [show withArchive345 d = packProg345 d ++ archiveLoadP20 k8 d by unfold withArchive345; rfl]
    exact from_append (prop := Frame (ArchiveJ20.codePorts k8) (code d) row)
      (ArchiveJ20.load_run k8 d row limit _ _ frame).2.1
  have tail := tail_clean345 d x p raw s domain m tape _ _ _ cut row cframe
  have hpack := pack345_hist_vals d x p good raw s m domain _ _ _ cut Z parity ready.2.1
  let v := run (nextWindow345 d) m s
  have runEq : v = run (window345 d) tape pre := by
    simp only [v, nextWindow345, run_append, run_take, pre, tape]
  have origEq := origin345_eq d raw v hpack.1
  have crt := LeaveJ7.Admission.Inputs.crt_pair (j := j20) (by decide) (by decide) adm.1
  have hsame : run (CRTBarrel.leave j20) n v = run (Shadow7.leaveP j20) n v := crt.1 n
  have domP := rawPack325_domain d x p raw domain
  have gg : ∀ (g sg : Bool) (u v : Int), (encode g sg u v).g = g := fun g _ _ _ => by cases g <;> rfl
  have origIn : InputAt 345 (encode G S (unsigned 345 x p).u (unsigned 345 x p).v) raw := by
    unfold InputAt; rw [gg]; exact input
  have inpP := rawPack325_input d raw _ origIn
  have ph : v.phase = (WideReference.origin 345 (rawPack325 d raw) v).phase := by
    have h1 : v.phase = s.phase := adm.2.1
    have h2 : s.phase = raw.phase := cut.phase
    have h3 : (WideReference.origin 345 (rawPack325 d raw) v).phase = (rawPack325 d raw).phase :=
      WideReference.origin_phase 345 x p (by decide) good (rawPack325 d raw) v domP
    rw [h1, h2, h3, rawPack325_phase]
  have ag : ∀ q : Wire, ¬ WideReference.Box 345 q → ¬ LeaveJ7.AssembleCut.leftovers j20 q →
      ¬ (2070 ≤ (q : Nat) + 345 ∧ (q : Nat) ≤ 1812) →
      v.basis q = (WideReference.origin 345 (rawPack325 d raw) v).basis q := by
    intro q nb nl nm
    rw [origEq q, runEq]
    unfold LeaveJ7.AssembleCut.leftovers LeaveJ7.ReleasedOrigin.releasedSite at nl
    rw [show start j20 = 345 from rfl] at nl; simp only [not_or, not_and] at nl
    have nb20 : ¬ WideReference20.Box20 345 15 q := by
      intro h; apply nb; unfold WideReference20.Box20 at h; unfold WideReference.Box
      simpa only [show 345 + 15 - 1 = 345 + 14 from rfl] using h
    exact agree_origin345 d raw s m tape _ _ _ cut q nb20
      (by simp only [Wire] at *; omega) (by simp only [Wire] at *; omega)
  have mir : ∀ q : Nat, 2070 ≤ q + 345 → q ≤ 1812 →
      v.basis q = (WideReference.origin 345 (rawPack325 d raw) v).basis q := fun q lo hi => by
    rw [origEq q, runEq]
    exact mirror_origin345 d raw s m tape _ _ _ cut q lo hi
  have up : ∀ q : Nat, Shadow7.a0P 345 + 16 ≤ q → q ≤ min (345 + 30 + railP 359) 529 → v.basis q = false :=
    fun q lo hi => by rw [runEq]; exact upper_clear345 d raw s x p domain m tape _ _ _ cut q (by unfold Shadow7.a0P at lo; omega) hi
  have band := band_clean345 d x p good raw s m domain _ _ _ cut
  have hj20 : start j20 = 345 := rfl
  have quiet : ∀ q ∈ LeaveJ7.CoreCheckpoint.rawSites j20, v.basis q = false := by
    intro q hq
    simp only [LeaveJ7.CoreCheckpoint.rawSites, List.mem_append, List.mem_range'_1, List.mem_singleton] at hq
    rcases hq with (⟨lo, hi⟩ | ⟨lo, hi⟩) | p17
    rotate_right
    · rw [p17]; exact adm.1.parked
    · exact LeaveJ7.native_carryJ j20 (by decide) (by decide) _ v adm.1.ready adm.1.top adm.1.top2 q
        (by unfold Wire at *; omega) (by unfold Wire at *; omega)
    · by_cases e8 : (q : Nat) = Shadow7.e0P 345 + 8
      · have t2 := tags ⟨2, by decide⟩
        rw [show q = 1656 + 2 by unfold Wire at e8 ⊢; have := j20_vals; omega]; exact t2
      · rw [runEq]; exact tail q (by
          simp only [tailTemps345, List.mem_range'_1, hj20, show Shadow7.e0P 345 = 1650 by decide] at lo hi e8 ⊢
          unfold Wire at *; omega)
  have hcut := LeaveJ7.CertifiedCut.result j20 ⟨21, by decide⟩ (by decide) (by decide) (by decide) (by decide)
    rfl x p good (rawPack325 d raw) v n G S adm.1 domP inpP ph ag mir up band (fun _ h _ _ => by rw [hj20] at h; omega) quiet
  have harch := LeaveJ7.ArchiveCut.result j20 (by decide) (by decide) v n (unsigned 345 x p) G S adm.1
  have hph : (run (Shadow7.leaveP j20) n v).phase = s.phase := by
    have h1 := StockWindowTicket.cutPhase hcut
    have h2 := WideReference.endRaw_phase 345 x p (by decide) good (rawPack325 d raw) v domP
    rw [hj20] at h1
    rw [h1, h2, rawPack325_phase]
    exact cut.phase.symm
  dsimp only
  refine ⟨by rw [hsame]; exact hph, by rw [hsame]; exact hcut, by rw [hsame]; exact harch,
    fun r => crt.2 n r, adm.2.2⟩

end ECDSAAdd.Entrant.StairPacket.Shadow20.Reentry345
end
-- ==== end Shadow7Wide20ReentryEnd ====


-- ==== begin Shadow7Wide20Chain ====
section

/-!
# End-to-End Mixed 15/20-Tick Strong Chain (`Shadow7Wide20Chain`)

Proves `MixedChain.strong`: running `MixedWindow.forwardMixed d` from
`pullState (OB5.sig 44) raw` (at a valid `Rolling1588.Integer.Stage ... 45`) preserves phase,
stores all 22 key-selected archive banks (`MixedGeo.Bank = Fin 22`), and roundtrips exactly
under `MixedWindow.reverseMixed d` for arbitrary measurement tapes.
-/

end

end

end

end

