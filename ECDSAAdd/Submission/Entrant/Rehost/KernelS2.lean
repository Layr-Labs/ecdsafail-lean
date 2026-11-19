import ECDSAAdd.Submission.Entrant.Rehost.Defs
/-!
# S2 rehost: the kernels p5 / p7 avoid pool 723 and pool 724 (port of the record-era `Sites41` kernel part)

S1 changes: k41 A- tail groups have deficits 11 / 20 / 28 / 34 / 39 (were 14 / 23 / 31 / 37 / 42).

`notIn<j>_<wire>`: the physical piece `p<j>` of the record program never touches the tracked wire.

Method.  The kernels (`p5`, `p7`) are proved as `PieceOK [4838, 4839]` with the record's own composition
(`entryInner_ok` / `exitInner_ok`, copied with the leaf facts replaced): the staircase leaves hold for every
sub-list of the 44 physical holes (which contain pool 723 = 4838 and pool 724 = 4839), the other leaves keep the
record's arena half (`*39`) and get a sharper hole half.  Every kernel placement sends a label to 4838 / 4839
only from the labels 739 / 740 (`base 723`, `base 724`): `kp_label`, `pp_free`, `tp_free`.  The record covers
`PPI` / `TPI` contain 739 / 740, so each leaf is re-checked against `deB` (no 739 / 740) on the same cover.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed BalancedField
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy

namespace Sites41

/-! ## Generic helpers -/

/-- The two re-hosted sites, pool 723 and pool 724. -/
abbrev hDE : List Wire := [4838, 4839]

theorem hDE_sub : ∀ q ∈ hDE, q ∈ StairPhysicalInventory.physicalHoles := by
  rw [StairPhysicalLayout.physicalHoles_eq_nat]
  intro q hq
  simp only [hDE, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> decide

/-- A label that is neither 739 nor 740 (`base 723`, `base 724`). -/
def NDE (x : Nat) : Prop := x ≠ 739 ∧ x ≠ 740

/-- Every label of `P` is `NDE`. -/
def DE (P : Program) : Prop := ∀ x ∈ wires P, NDE x

theorem DE.append {P Q : Program} (hP : DE P) (hQ : DE Q) : DE (P ++ Q) := by
  intro x hx
  rw [wires_append, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact hP x hx
  · exact hQ x hx

/-- `NDE`, kernel-fast. -/
def deB (x : Nat) : Bool := !(Nat.beq x 739 || Nat.beq x 740)

theorem deB_spec {x : Nat} (h : deB x = true) : NDE x := by
  unfold deB at h
  constructor <;> intro e <;> subst e <;> exact absurd h (by decide)

theorem notIn_of_ok {holes : List Wire} {f : Wire → Wire} {P : Program} {w : Wire}
    (h : PieceOK holes f P) (hw : w ∈ holes) : w ∉ wires (renameProgram f P) := by
  rw [renameProgram_support]
  intro hm
  obtain ⟨x, hx, e⟩ := Finset.mem_image.mp hm
  exact h.2 x hx (e ▸ hw)

/-! ## Closed-form inversion of the kernel placements -/

open StairPlaceFast in
theorem sw_inv {a b y w : Nat} (h : sw a b y = w) : y = sw a b w := by
  subst h
  unfold sw
  split_ifs <;> omega

set_option maxHeartbeats 8000000 in
open StairPlaceFast in
theorem pwN_pool {i c : Nat} (h : pwN i = c) (h1 : 4115 ≤ c) (h2 : c < 4885) : i = c - 4115 := by
  unfold pwN at h
  split_ifs at h
  all_goals first
    | omega
    | (unfold metaN at h; split_ifs at h <;> omega)

open StairPlaceFast in
/-- The outer exchanges of `kernelPlaceN`, inverted. -/
theorem kpN_inv {q c : Nat} (h : kernelPlaceN q = c) :
    pwN (sw 785 1813 q - 16) =
      sw 1 5515 (sw 4799 4832 (sw 4113 9814 (sw 4112 4799 (sw 9815 5655 (sw 9815 0
        (sw 4799 4832 c)))))) := by
  unfold kernelPlaceN at h
  have h1 := sw_inv h
  have h2 := sw_inv h1
  have h3 := sw_inv h2
  have h4 := sw_inv h3
  have h5 := sw_inv h4
  have h6 := sw_inv h5
  exact sw_inv h6

open StairPlaceFast in
/-- A kernel label placed on a pool site `pre` (after the outer exchanges) is `sw 785 1813 (pre - 4099)`. -/
theorem kp_label {q c pre : Nat} (h : StairOuterPlacement.kernelPlace q = c)
    (hpre : sw 1 5515 (sw 4799 4832 (sw 4113 9814 (sw 4112 4799 (sw 9815 5655 (sw 9815 0
        (sw 4799 4832 c)))))) = pre) (h1 : 4116 ≤ pre) (h2 : pre < 4885) :
    q = sw 785 1813 (pre - 4099) := by
  rw [kernelPlace_eqN] at h
  have e := kpN_inv h
  rw [hpre] at e
  have e2 := pwN_pool e (by omega) h2
  have e3 : sw 785 1813 q = pre - 4099 := by omega
  exact sw_inv e3

theorem kp_de {q : Wire} (h : StairOuterPlacement.kernelPlace q ∈ hDE) : q = 739 ∨ q = 740 := by
  simp only [hDE, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · left
    have e := kp_label h (pre := 4838) (by decide) (by omega) (by omega)
    rw [e]; decide
  · right
    have e := kp_label h (pre := 4839) (by decide) (by omega) (by omega)
    rw [e]; decide

theorem kp_free {x : Wire} (h : NDE x) : KP x ∉ hDE := fun m =>
  (kp_de m).elim h.1 h.2

theorem pp_free {x : Wire} (h : NDE x) : PP x ∉ hDE := by
  intro m
  rcases kp_de m with e | e
  · rw [StairPlaceFast.phaseHost_eqN] at e
    have := sw_inv (sw_inv (sw_inv e))
    exact h.1 (by rw [this]; decide)
  · rw [StairPlaceFast.phaseHost_eqN] at e
    have := sw_inv (sw_inv (sw_inv e))
    exact h.2 (by rw [this]; decide)

theorem tp_free {x : Wire} (h : NDE x) : TP x ∉ hDE := by
  intro m
  rcases kp_de m with e | e
  · rw [StairPlaceFast.fieldPlace_eqN] at e
    have := sw_inv (sw_inv (sw_inv (sw_inv e)))
    exact h.1 (by rw [this]; decide)
  · rw [StairPlaceFast.fieldPlace_eqN] at e
    have := sw_inv (sw_inv (sw_inv (sw_inv e)))
    exact h.2 (by rw [this]; decide)

/-- A leaf under `PP`: the record's arena half and a label-level `DE` cover. -/
theorem okPP {P : Program} (r : PieceOK StairCertificate.holes39 PP P) (h : DE P) :
    PieceOK hDE PP P :=
  ⟨r.1, fun x hx => pp_free (h x hx)⟩

theorem okTP {P : Program} (r : PieceOK StairCertificate.holes39 TP P) (h : DE P) :
    PieceOK hDE TP P :=
  ⟨r.1, fun x hx => tp_free (h x hx)⟩

theorem de_of_all {P : Program} (h : allSites deB P = true) : DE P :=
  fun x hx => deB_spec (allSites_sound h x hx)

theorem de_of_int {q : Wire} (h : StackOB5Base.Good q) : NDE q := by
  obtain ⟨l, rfl, hl⟩ := (StackOB5Base.integerSites_mem q).mp h
  unfold NDE
  simp only [MappedCompressed.base]
  omega

/-- 739 and 740 are retired roles. -/
theorem de_of_notRole {x : Wire} (h : x ∉ StairSchedule.exclusiveRoles) : NDE x := by
  have h1 : (739 : Wire) ∈ StairSchedule.exclusiveRoles := by decide +kernel
  have h2 : (740 : Wire) ∈ StairSchedule.exclusiveRoles := by decide +kernel
  exact ⟨fun e => h (e ▸ h1), fun e => h (e ▸ h2)⟩

theorem de_of_notHole {x : Wire} (h : x ∉ StairBoundaryLoan.exclusiveHoles) : NDE x := by
  have h1 : (739 : Wire) ∈ StairBoundaryLoan.exclusiveHoles := by decide +kernel
  have h2 : (740 : Wire) ∈ StairBoundaryLoan.exclusiveHoles := by decide +kernel
  exact ⟨fun e => h (e ▸ h1), fun e => h (e ▸ h2)⟩

/-! ## Phase leaves (`PP`) -/

theorem forward_de (isA : Bool) (n : Nat) (hn : n ≤ 511) :
    DE (Rolling1588TickGap.forward isA 1 n) := by
  intro x hx
  have h1 := Rolling1588TickGap.forward_support isA 1 n (by omega) hx
  rw [Rolling1588.forward_support_eq, NewStackOB5.forward_support_eq] at h1
  exact de_of_int ((StackOB5.support_gen 1 n (by omega) (by omega)).1 x h1)

theorem reverse_de (isA : Bool) (n : Nat) (hn : n ≤ 511) : DE (Rolling1588.reverse isA 1 n) := by
  intro x hx
  rw [Rolling1588.reverse_support_eq, NewStackOB5.reverse_support_eq] at hx
  exact de_of_int ((StackOB5.support_gen 1 n (by omega) (by omega)).2 x hx)

theorem entryTicksDE : PieceOK hDE PP (Rolling1588TickGap.forward true 1 424) :=
  okPP entryTicks39 (forward_de true 424 (by omega))

theorem exitTicksDE : PieceOK hDE PP (Rolling1588.reverse true 1 424) :=
  okPP exitTicks39 (reverse_de true 424 (by omega))

section
attribute [local irreducible] wires run FrontierEntry1591NativeH.inverse FrontierEntry1591Native.inverse

set_option exponentiation.threshold 600 in
theorem nativeInverse_de : DE (FrontierEntry1591NativeH.inverse base) := by
  have pre : (NativeFirstDirect.prefixSites base).all deB = true := by
    decide +kernel
  intro x hx
  have h := (FrontierEntry1591Native.support base base_pool_nodup).2
    (FrontierEntry1591NativeH.wires_sub base base_pool_nodup hx)
  have h2 : x ≠ base 1797 ∧ x ∈ insert (base 511) (NativeFirstDirect.prefixSites base).toFinset :=
    Finset.mem_erase.mp h
  rcases Finset.mem_insert.mp h2.2 with h3 | h3
  · rw [h3]
    show NDE (511 + 16)
    unfold NDE
    omega
  · exact deB_spec (List.all_eq_true.mp pre x (List.mem_toFinset.mp h3))

end

theorem tail15_de :
    DE (renameProgram (OB5.sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)) := by
  have hu : allSites (fun y => deB (OB5.sig 510 y)) (Rolling1588.unpackAtTick false 510) = true := by
    decide +kernel
  have hc : StairTerminalV3.cand15Sites.all (fun y => deB (OB5.sig 510 y)) = true := by
    decide +kernel
  intro x hx
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  rw [wires_append, Finset.mem_union] at hy
  rcases hy with hy | hy
  · exact deB_spec (allSites_sound hu y hy)
  · exact deB_spec (List.all_eq_true.mp hc y
      (List.mem_toFinset.mp (StairTerminalV3.candidate15_support hy)))

theorem entryLastDE : PieceOK hDE PP (InverseFive23.lastPhase15 false) := by
  refine okPP entryLast39 ?_
  unfold InverseFive23.lastPhase15 InverseFive23.stackReverse15 InverseFive23.reverseTail15
  refine DE.append (DE.append ?_ (DE.append ?_ (DE.append ?_ ?_))) ?_
  · exact de_of_all (by decide +kernel)
  · exact de_of_all (by decide +kernel)
  · exact tail15_de
  · exact reverse_de false 505 (by omega)
  · exact nativeInverse_de

theorem merged6_de : DE Six505.merged6 := by
  have hc : StairTerminalV3.cand6Sites.all (fun y => deB (OB5.sig 510 y)) = true := by
    decide +kernel
  intro x hx
  unfold Six505.merged6 at hx
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact deB_spec (List.all_eq_true.mp hc y
    (List.mem_toFinset.mp (StairTerminalV3.cand6_support hy)))

theorem exitTailDE : PieceOK hDE PP (Rolling1588TickGap.tailPhase false) := by
  refine okPP exitTail39 ?_
  unfold Rolling1588TickGap.tailPhase Rolling1588TickGap.stackForward Six505.stackForward6
  refine DE.append (DE.append ?_ (DE.append ?_ ?_)) ?_
  · exact forward_de false 504 (by omega)
  · exact merged6_de
  · exact de_of_all (by decide +kernel)
  · exact de_of_all (by decide +kernel)

theorem rows87_de : ∀ q ∈ StairPhysicalPrimitives.rowSitesL 87,
    NDE (StairPhysicalLayout.phaseRelabel q) := by
  have hB : (StairPhysicalPrimitives.rowSitesL 87).all
      (fun q => deB (StairPlaceFast.phaseHostB (StairPlaceFast.fieldPlaceB q))) = true := by
    decide +kernel
  intro q hq
  rw [kbRelabel_eqB]
  exact deB_spec (List.all_eq_true.mp hB q hq)

theorem phaseRows_de {P : Program}
    (h : ∀ q ∈ wires P, q ∈ StairPhysicalPrimitives.rowSitesL 87) :
    DE (renameProgram StairPhysicalLayout.phaseRelabel P) := by
  intro x hx
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact rows87_de y (h y hy)

theorem firstOrient_de :
    DE (renameProgram StairV3Primitives.xRelabel (StairV3Primitives.orient 425)) := by
  have hO : kbOrientSites.all
      (fun q => deB (StairPlaceFast.phaseHostB (StairPlaceFast.fieldPlaceB q))) = true := by
    decide +kernel
  have hBs : (List.range 88).all (fun k => deB (StairPhysicalLayout.bSite k)) = true := by
    decide +kernel
  intro x hx
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have hsup : wires (StairV3Primitives.orient 425) ⊆ (StairPhysicalLayout.letterSite 424 ::
      ((StairCodec.reg (StairPhysicalLayout.physicalLayout 87).S 87 ++ [base 512]) ++
        (StairCodec.reg (StairPhysicalLayout.physicalLayout 87).D 87 ++
          [StairPhysicalLayout.bSite 87]))).toFinset :=
    swapRegisters_wires _ _ _ (by simp [StairCodec.reg])
  have hyL : y ∈ kbOrientSites := List.mem_toFinset.mp (hsup hy)
  show NDE (StairV3Primitives.xSwap (StairPhysicalLayout.phaseRelabel y))
  rcases StairV3Primitives.xSwap_cases (StairPhysicalLayout.phaseRelabel y) with
    ⟨k, hk, -, e⟩ | ⟨k, hk, -, e⟩ | e
  · rw [e]
    exact deB_spec (List.all_eq_true.mp hBs k hk)
  · rw [e]
    have hk' := List.mem_range.mp hk
    unfold NDE
    simp only [MappedCompressed.base]
    omega
  · rw [e, kbRelabel_eqB]
    exact deB_spec (List.all_eq_true.mp hO y hyL)

theorem entryFirstPackDE : PieceOK hDE PP pr.firstPack := by
  refine okPP entryFirstPack39 ?_
  show DE StairV3Primitives.firstPack
  unfold StairV3Primitives.firstPack
  exact DE.append (DE.append (DE.append firstOrient_de (de_of_all (by decide +kernel)))
    (de_of_all (by decide +kernel))) (phaseRows_de (StairPhysicalPrimitives.pack_rows 87 (by decide)))

theorem exitFirstUnpackDE : PieceOK hDE PP pr.firstUnpack := by
  refine okPP exitFirstUnpack39 ?_
  show DE StairV3Primitives.firstUnpack
  unfold StairV3Primitives.firstUnpack
  exact DE.append (DE.append (DE.append
    (phaseRows_de (StairPhysicalPrimitives.unpack_rows 87 (by decide))) (de_of_all (by decide +kernel)))
      (de_of_all (by decide +kernel))) firstOrient_de

/-! ## Field-tail leaves (`TP`) -/

theorem hosts_de : schedule.all (fun g => (hp.group true g.1 g.2.1 g.2.2).all deB) = true := by
  decide +kernel

theorem hostedGroupDE (divide : Bool) (d f c : Nat) (hg : (d, f, c) ∈ schedule) :
    PieceOK hDE TP (StairHostsSchedule.hostedGroup hp divide d f c) := by
  refine okTP (hostedGroup39 divide d f c hg) ?_
  obtain ⟨hd, hf, hc⟩ := schedule_bounds _ hg
  obtain ⟨disj, nr, nh, hlen, -⟩ := hostFacts _ hg
  simp only at hd hf hc disj nr nh hlen
  rw [← group_dir divide] at disj nh hlen
  have hh : ∀ h ∈ hp.group divide d f c, NDE h := by
    rw [group_dir divide]
    intro h hm
    exact deB_spec (List.all_eq_true.mp (List.all_eq_true.mp hosts_de _ hg) h hm)
  intro x hx
  unfold StairHostsSchedule.hostedGroup at hx
  rcases rebind_mem _ _ _ (hostsFresh divide d f c hg) disj nr nh hlen x hx with hm | ⟨hP, hnr⟩
  · exact hh x hm
  · change x ∈ wires (renameProgram (OB5.sig 511) (StairGroups.groups divide d f c)) at hP
    rw [renameProgram_support] at hP
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨j, hj1, hj2, hjw⟩ := seq_mem divide (StairGroups.packet divide d) c f w hw
    unfold StairGroups.packet at hjw
    rw [renameProgram_support] at hjw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hjw
    have hjr : j ∈ List.range' 1 101 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
    obtain ⟨nt, -⟩ := basePacket_tgt divide d j hjr hd z hz
    apply de_of_notRole
    rw [← List.take_append_drop d StairSchedule.exclusiveRoles, List.mem_append]
    rintro (hr | hr)
    · exact nt hr
    · exact hnr hr

theorem groupsDE : ∀ g ∈ entryGroups,
    PieceOK hDE TP (StairHostsSchedule.hostedGroup hp true g.1 g.2.1 g.2.2) := by
  intro g hg
  exact hostedGroupDE true g.1 g.2.1 g.2.2 (by
    simp only [entryGroups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem groupsExitDE : ∀ g ∈ exitGroups,
    PieceOK hDE TP (StairHostsSchedule.hostedGroup hp false g.1 g.2.1 g.2.2) := by
  intro g hg
  exact hostedGroupDE false g.1 g.2.1 g.2.2 (by
    simp only [exitGroups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem canonDE : PieceOK hDE TP StairConcrete.bestLoans.canon :=
  okTP canon39 (fun x hx => de_of_notHole (fun m => StairBoundaryLoan.canon760Loan_avoids x m hx))

theorem centerDE : PieceOK hDE TP StairConcrete.bestLoans.center :=
  okTP center39 (fun x hx => de_of_notHole (fun m => StairBoundaryLoan.center760Loan_avoids x m hx))

theorem multEnd_de : multEndL.all (fun y => k5roleB y || deB (OB5.sig 511 y)) = true := by
  decide +kernel

section
attribute [local irreducible] ECDSAAdd.wires

theorem endpointMultDE : PieceOK hDE TP (StairHostsSchedule.hostedEndpoint hp false 68) := by
  refine okTP endpointMult39 ?_
  intro x hx
  have e : StairConcrete.bestLoans.endPacket false 68 =
      StairEndpointLoan44.endPacket760Loan44 false := by
    simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true,
      if_false, if_true]
  rw [StairHostsSchedule.hostedEndpoint, StairSchedule.placedEndPacket, e,
    renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  have notRole : ¬ RoleI y := fun m =>
    StairEndpointLoan44.endPacket760Loan44_avoids y (roleI_mem m) hy
  have t := List.all_eq_true.mp multEnd_de y
    (endPacket760_false_mem y (StairEndpointLoan44.endPacket760Loan44_support hy))
  rw [Bool.or_eq_true] at t
  exact deB_spec (t.resolve_left (fun m => notRole (k5_roleB y m)))

theorem divEnd_de_tab : DecoderBiasReuse.fixedLayout.wires.all (fun w =>
    k5roleB w || deB (OB5.sig 511 (Equiv.swap (base 760) (base 717)
      (shifted Placement5.pi0 (Equiv.swap (base 719) (base 510) w))))) = true := by
  decide +kernel

theorem divEnd_de (y : Wire)
    (hy : y ∈ wires CompareDecoder.BoundaryLoan.endPacket760DivLoan) : NDE (OB5.sig 511 y) := by
  unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hy
  rw [renameProgram_support] at hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
  rw [renameProgram_support] at ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hb) with h | h
  · rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl
    · exact deB_spec (by decide +kernel)
    · exact deB_spec (by decide +kernel)
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    rw [wires_append, Finset.mem_union] at hz
    rcases hz with hz | hz
    · have hl := List.mem_toFinset.mp
        (CompareDecoder.support (CompareDecoder.BoundaryLoan.Inclusion.cellDecoderLoan_sub hz))
      have t := List.all_eq_true.mp divEnd_de_tab z hl
      rw [Bool.or_eq_true] at t
      exact deB_spec (t.resolve_left (fun m => k5_loan_avoids z (roleI_mem (k5_roleB z m)) hz))
    · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
      rw [Finset.mem_singleton] at hc
      rw [hc]
      exact deB_spec (by decide +kernel)

theorem endpointDivDE : PieceOK hDE TP
    (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint) := by
  refine okTP endpointDiv39 ?_
  intro x hx
  rw [renameProgram_support, StairConcrete.bestLoans_divEndpoint] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact divEnd_de y hy

end

/-! ## Leaves that hold for every sub-list of the 44 physical holes -/

theorem copyNDE : PieceOK hDE TP HalfFieldOB5.copyN := ok_of_all hDE_sub copyN_all
theorem scratchClearDE : PieceOK hDE lowPlace FourScratchWindow.clearProgram :=
  ok_of_all hDE_sub scratchClear_all
theorem scratchUnprefixDE : PieceOK hDE lowPlace FourScratchWindow.unprefix :=
  ok_of_all hDE_sub scratchUnprefix_all
theorem paritySetupDE : PieceOK hDE KP StairSchedule.paritySetup := ok_of_all hDE_sub paritySetup_all
theorem hostedXDE : PieceOK hDE KP StairSchedule.hostedX := ok_of_all hDE_sub hostedX_all
theorem firstPacketEntryDE : PieceOK hDE lowPlace
    (StairLoan.rebindMany StairSchedule.exclusiveRoles (hp.firstPacket true)
      (Rolling1588.placedFirstPacket true)) :=
  StairFirstPacketHosted.hostedFirstPacket_pieceOK hDE hDE_sub true
theorem firstPacketExitDE : PieceOK hDE lowPlace
    (StairLoan.rebindMany StairSchedule.exclusiveRoles (hp.firstPacket false)
      (Rolling1588.placedFirstPacket false)) :=
  StairFirstPacketHosted.hostedFirstPacket_pieceOK hDE hDE_sub false

/-! ## The two kernels (copies of `entryInner_ok` / `exitInner_ok`) -/

theorem entryTailPrefixDE : PieceOK hDE TP (StairHostsSchedule.entryTailPrefix pr hp) := by
  have pk := packEnd_rows
  unfold StairHostsSchedule.entryTailPrefix
  refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
    ?_).append ?_).append ?_).append ?_).append ?_)
  · exact groupsDE (0, 1, 84) (by decide)
  · exact forwardSegment_ok hDE_sub 87 62 (by decide) (by decide) (by decide) pk.1
  · exact groupsDE (11, 85, 5) (by decide)
  · exact forwardSegment_ok hDE_sub 62 47 (by decide) (by decide) (by decide) pk.2.1
  · exact groupsDE (20, 90, 3) (by decide)
  · exact forwardSegment_ok hDE_sub 47 32 (by decide) (by decide) (by decide) pk.2.2.1
  · exact groupsDE (28, 93, 3) (by decide)
  · exact forwardSegment_ok hDE_sub 32 22 (by decide) (by decide) (by decide) pk.2.2.2.1
  · exact groupsDE (34, 96, 2) (by decide)
  · exact forwardSegment_ok hDE_sub 22 12 (by decide) (by decide) (by decide) pk.2.2.2.2
  · exact groupsDE (39, 98, 2) (by decide)
  · exact forwardLast_ok hDE_sub

theorem exitHeadSuffixDE : PieceOK hDE TP (StairHostsSchedule.exitHeadSuffix pr hp) := by
  have up := unpackEnd_rows
  unfold StairHostsSchedule.exitHeadSuffix
  refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
    ?_).append ?_).append ?_).append ?_).append ?_)
  · exact reverseLast_ok hDE_sub
  · exact groupsExitDE (39, 98, 2) (by decide)
  · exact reverseSegment_ok hDE_sub 22 12 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.2
  · exact groupsExitDE (34, 96, 2) (by decide)
  · exact reverseSegment_ok hDE_sub 32 22 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.1
  · exact groupsExitDE (28, 93, 3) (by decide)
  · exact reverseSegment_ok hDE_sub 47 32 (by decide) (by decide) (by decide) (by decide)
      up.2.2.1
  · exact groupsExitDE (20, 90, 3) (by decide)
  · exact reverseSegment_ok hDE_sub 62 47 (by decide) (by decide) (by decide) (by decide)
      up.2.1
  · exact groupsExitDE (11, 85, 5) (by decide)
  · exact reverseSegment_ok hDE_sub 87 62 (by decide) (by decide) (by decide) (by decide) up.1
  · exact groupsExitDE (0, 1, 84) (by decide)

theorem entryInnerDE : PieceOK hDE KP entryInner := by
  unfold entryInner
  refine (PieceOK.append (PieceOK.append ?_ ?_) ?_)
  · apply ok_phase
    unfold StairSchedule.stackForward6
    exact entryTicksDE.append entryFirstPackDE
  · unfold StairHostsSchedule.entryFieldHosted
    refine ((((PieceOK.append ?_ paritySetupDE).append hostedXDE).append ?_).append hostedXDE).append
      paritySetupDE
    · apply ok_field
      unfold StairHostsSchedule.entryLowPrefix
      refine ((firstPacketEntryDE.append scratchClearDE).append ?_).append scratchUnprefixDE
      exact ok_borrow entryTailPrefixDE
    · apply ok_field
      unfold StairHostsSchedule.entryLowSuffix
      refine (scratchClearDE.append ?_).append scratchUnprefixDE
      apply ok_borrow
      unfold StairHostsSchedule.entryTailSuffix
      exact ((groupsDE (44, 100, 2) (by decide)).append endpointDivDE |>.append copyNDE).append
        canonDE
  · exact ok_phase entryLastDE

/-- `p7` before its outer placement: `exitInner` without `x1N`. -/
theorem exitBodyDE : PieceOK hDE KP
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false) ++
      StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan ++
      renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.stackReverse15 checkpointPrimitives)) := by
  refine (PieceOK.append (PieceOK.append ?_ ?_) ?_)
  · exact ok_phase exitTailDE
  · unfold StairHostsSchedule.exitFieldHosted
    refine ((((paritySetupDE.append hostedXDE).append ?_).append paritySetupDE).append hostedXDE).append ?_
    · apply ok_field
      unfold StairHostsSchedule.exitLowPrefix
      refine (scratchClearDE.append ?_).append scratchUnprefixDE
      apply ok_borrow
      unfold StairHostsSchedule.exitHeadPrefix
      exact ((centerDE.append copyNDE).append endpointMultDE).append
        (groupsExitDE (44, 100, 2) (by decide))
    · apply ok_field
      unfold StairHostsSchedule.exitLowSuffix
      exact ((scratchClearDE.append (ok_borrow exitHeadSuffixDE)).append
        scratchUnprefixDE).append firstPacketExitDE
  · apply ok_phase
    unfold StairSchedule.stackReverse15
    exact exitFirstUnpackDE.append exitTicksDE

theorem p5DE : PieceOK hDE fG (hostedEntryRest L0) := by
  have h := ok_kernel entryInnerDE
  rw [← hostedEntryRest_eq] at h
  exact h

theorem p7DE : PieceOK hDE fK
    (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.tailPhase false) ++
      StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan ++
      renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.stackReverse15 checkpointPrimitives)) :=
  exitBodyDE

end Sites41

open Sites41

theorem notIn5_wD : wD ∉ wires p5 := notIn_of_ok p5DE (by decide)
theorem notIn5_wE : wE ∉ wires p5 := notIn_of_ok p5DE (by decide)
theorem notIn7_wD : wD ∉ wires p7 := notIn_of_ok p7DE (by decide)
theorem notIn7_wE : wE ∉ wires p7 := notIn_of_ok p7DE (by decide)

end ECDSAAdd.Entrant.Rehost
