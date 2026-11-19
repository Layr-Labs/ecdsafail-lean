import ECDSAAdd.Submission.Entrant.Rehost.CleanExitS2
/-!
# S2 rehost: static facts of the caller pieces (S1)

`wZ = 4112` is not a wire of p0 .. p4 and p8; `wA = 4835` is not a wire of p9 .. p13. Port of the record-era
`Sites41` caller section: every piece is covered by a short list of logical sites, placed by a closed-form
placement and checked once by `decide +kernel`. S1 changes: p4 and p8 carry the rival's swaps
(`pmapR 721 <-> pmapR 300`, `base 723 <-> base 300`); the hosts `pmapR 300` / `base 300` are placed on 4415.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed BalancedField
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy

namespace StaticsS2

attribute [local irreducible] ECDSAAdd.wires Baselines.layout

/-- `y` is none of `ws`, kernel-fast. -/
def avoidB (ws : List Nat) (y : Nat) : Bool := ws.all (fun w => !(Nat.beq y w))

theorem avoidB_spec {ws : List Nat} {y : Nat} (h : avoidB ws y = true) : ∀ w ∈ ws, y ≠ w := by
  intro w hw e
  subst e
  have t := List.all_eq_true.mp h y hw
  simp at t

/-- A program whose labels lie in `S`, placed by `f` (closed form `g`), avoids every `w ∈ ws`. -/
theorem notIn_list {f : Wire → Wire} (g : Nat → Nat) (hg : ∀ x, f x = g x) {P : Program}
    (S : List Wire) (hP : ∀ x ∈ wires P, x ∈ S) (ws : List Nat)
    (hS : S.all (fun x => avoidB ws (g x)) = true) :
    ∀ w ∈ ws, w ∉ wires (renameProgram f P) := by
  intro w hw hm
  rw [renameProgram_support] at hm
  obtain ⟨x, hx, e⟩ := Finset.mem_image.mp hm
  have t := List.all_eq_true.mp hS x (hP x hx)
  exact avoidB_spec t w hw (by rw [← hg]; exact e)

/-- Two nested renames. -/
theorem notIn_list2 {f h : Wire → Wire} (g : Nat → Nat) (hg : ∀ x, f (h x) = g x) {P : Program}
    (S : List Wire) (hP : ∀ x ∈ wires P, x ∈ S) (ws : List Nat)
    (hS : S.all (fun x => avoidB ws (g x)) = true) :
    ∀ w ∈ ws, w ∉ wires (renameProgram f (renameProgram h P)) := by
  intro w hw hm
  rw [renameProgram_support] at hm
  obtain ⟨y, hy, e⟩ := Finset.mem_image.mp hm
  rw [renameProgram_support] at hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have t := List.all_eq_true.mp hS x (hP x hx)
  exact avoidB_spec t w hw (by rw [← hg]; exact e)

theorem fU_fast (x : Wire) : fU x = StairPlaceFast.uB x := U_fast x
theorem fG_fast (x : Wire) : fG x = StairPlaceFast.ugB x := UG_fast x

/-! ### Finite stage (`U`): the port list `stageList` (wD, wZ, wA; it contains `pkW` = wE) -/

theorem stage_tab : stageList.all (fun x => avoidB [4112, 4835] (StairPlaceFast.uB x)) = true := by
  decide +kernel

/-- K4 (record): covers are stated for a variable program, so that the unifier never evaluates `wires`
of a closed program. -/
theorem cover_of_sub {P : Program} {S : List Wire} (h : wires P ⊆ S.toFinset) : ∀ x ∈ wires P, x ∈ S :=
  fun _ hx => List.mem_toFinset.mp (h hx)

theorem cover_of_aux {P : Program} (h : wires P ⊆ ControlPointEncodingDevelop.auxPorts) :
    ∀ x ∈ wires P, x ∈ stageList :=
  fun _ hx => aux_stageList (h hx)

theorem stage_cover (C : Point) :
    ∀ x ∈ wires (FlagTop.stageNew Baselines.layout C (FlagEntry.pkW Baselines.layout)), x ∈ stageList := by
  cases C with
  | zero => exact cover_of_sub z0_stageList
  | some hc => exact cover_of_sub (stagePorts_eq ▸ ControlStageSupportDevelop.stage_support hc)

theorem encode_cover (C : Point) : ∀ x ∈ wires (AboveFieldPointDevelop.encode C), x ∈ stageList := by
  cases C with
  | zero => exact cover_of_aux AboveFieldTagDevelop.z0_encoding_support.1
  | some hc => exact cover_of_aux (AboveFieldTagDevelop.encoding_support hc).1

theorem decode_cover (C : Point) : ∀ x ∈ wires (AboveFieldPointDevelop.decode C), x ∈ stageList := by
  cases C with
  | zero => exact cover_of_aux AboveFieldTagDevelop.z0_encoding_support.2
  | some hc => exact cover_of_aux (AboveFieldTagDevelop.encoding_support hc).2

theorem stage_avoid {P : Program} (hP : ∀ x ∈ wires P, x ∈ stageList) :
    ∀ w ∈ [4112, 4835], w ∉ wires (renameProgram fU P) :=
  notIn_list _ fU_fast stageList hP _ stage_tab

/-! ### Output stage (`U` after the `doubleSelect ↔ pool 511` swap): `outList` (wA, wC) -/

theorem out_tab : outList.all (fun x =>
    avoidB [4835] (StairPlaceFast.uB (StairPlaceFast.swB 9815 4626 x))) = true := by
  decide +kernel

theorem out_cover (C : Point) : ∀ x ∈ wires (OutFlag.outNew Baselines.layout C), x ∈ outList := by
  cases C with
  | zero => exact cover_of_sub z0_outList
  | some hc => exact cover_of_sub (outPorts_eq ▸ OutSpareDevelop.output_support hc)

theorem borrowOut_avoid (C : Point) : ∀ w ∈ [4835], w ∉ wires (p13 C) := by
  unfold p13 ControlPointEncodingDevelop.borrowOut
  exact notIn_list2 _ (fun x => outSwap_fast x) outList (out_cover C) _ out_tab

/-! ### Generic block Y entry / exit (`UG`): `yList` (wE, wD, wZ, wA) -/

theorem y_tab : yList.all (fun x => avoidB [4112, 4835] (StairPlaceFast.ugB x)) = true := by
  decide +kernel

theorem entryY_avoid (c : Fp) : ∀ w ∈ [4112, 4835],
    w ∉ wires (renameProgram fG (ParityUniform.entryYAll L0 c)) := by
  refine notIn_list _ fG_fast yList (fun x hx => ?_) _ y_tab
  have h1 := ParityUniform.entryYAll_wires Baselines.layout Baselines.layout_widths c hx
  have h2 := EntryFuse.fusedY_support Baselines.layout Baselines.layout_widths c h1
  exact yList_mem h2

theorem exitY_avoid (c : Fp) : ∀ w ∈ [4112, 4835],
    w ∉ wires (renameProgram fG (ParityUniform.exitYAll L0 c)) := by
  refine notIn_list _ fG_fast yList (fun x hx => ?_) _ y_tab
  have h1 := ParityUniform.exitYAll_wires Baselines.layout Baselines.layout_widths c hx
  have h2 := ExitFusionResearch.exitY_support Baselines.layout Baselines.layout_widths c h1
  exact yList_mem h2

/-! ### X entry (`UG ∘ pmapR` on `tSites`, plus `pkW`): wZ and the host of wD (4380) -/

/-- Wires the X entry must avoid: wZ. -/
abbrev xWs : List Nat := [4112]

theorem x_tab : xList.all (fun q => avoidB xWs (StairPlaceFast.kernelPlaceB (e1B q))) = true := by
  decide +kernel

theorem x_placed {P : Program} (h : wires P ⊆ (tSites base (base 2400)).toFinset) :
    ∀ x ∈ wires (renameProgram (E1QubitPlacement.pmapR Baselines.layout) P), ∀ w ∈ xWs, UG x ≠ w := by
  intro x hx w hw
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  rw [xplace_fast]
  exact avoidB_spec (List.all_eq_true.mp x_tab y (List.mem_toFinset.mp (h hy))) w hw

theorem x_swp : ∀ x ∈ wires (FlagEntry.swp (FlagEntry.pkW Baselines.layout)
    (E1QubitPlacement.pmapR Baselines.layout (base 514))), ∀ w ∈ xWs, UG x ≠ w := by
  intro x hx w hw
  have h514 : UG (E1QubitPlacement.pmapR Baselines.layout (base 514)) ≠ w := by
    rw [xplace_fast]
    exact avoidB_spec (List.all_eq_true.mp x_tab _ (in_tSites base (base 2400) 514 (by omega))) w hw
  have hpk : UG (FlagEntry.pkW Baselines.layout) ≠ w := by
    rw [UG_fast]
    exact avoidB_spec (by decide +kernel) w hw
  simp only [FlagEntry.swp, wires, Instr.wires, Finset.union_empty, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl) | (rfl | rfl)
  · exact hpk
  · exact h514
  · exact h514
  · exact hpk

/-- S1's X entry (`entryXNew = rename (swap (pmapR 721) (pmapR 300)) entryXNew0`) avoids wZ. -/
theorem entryX_avoid (c : Fp) :
    (4112 : Wire) ∉ wires (renameProgram fG (FlagEntry.entryXNew L0 (FlagEntry.pkW L0) c)) := by
  intro hm
  rw [renameProgram_support] at hm
  obtain ⟨x, hx, e⟩ := Finset.mem_image.mp hm
  revert e
  change UG x ≠ 4112
  unfold FlagEntry.entryXNew at hx
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  by_cases e1 : y = E1QubitPlacement.pmapR Baselines.layout (base 721)
  · rw [e1, Equiv.swap_apply_left, xplace_fast]
    decide +kernel
  · by_cases e2 : y = E1QubitPlacement.pmapR Baselines.layout (base 300)
    · exact absurd (e2 ▸ hy) (FlagEntry.host300_fresh Baselines.layout Baselines.layout_widths
        Baselines.layout_nodup _ (FlagEntry.pk_ne_300 Baselines.layout Baselines.layout_widths
          Baselines.layout_nodup) c)
    · rw [Equiv.swap_apply_of_ne_of_ne e1 e2]
      unfold FlagEntry.entryXNew0 at hy
      split_ifs at hy
      · rw [wires_append, Finset.mem_union] at hy
        rcases hy with hy | hy
        · exact x_swp y hy 4112 (by simp)
        · exact x_placed (tailX_tight base (base 2400) c.val) y hy 4112 (by simp)
      · rw [wires_append, wires_append, Finset.mem_union, Finset.mem_union] at hy
        rcases hy with hy | hy | hy
        · exact x_placed ccx_tight y hy 4112 (by simp)
        · exact x_swp y hy 4112 (by simp)
        · exact x_placed (evenTail_tight c.val) y hy 4112 (by simp)

/-! ### `x1N` (`fP ∘ pi` on `tSites`): wZ and the host of wD (4381); the park -/

/-- `ParityXExitInverse23Kernel.pi`, kernel-fast. -/
def piB (x : Nat) : Nat :=
  StairPlaceFast.swB 1813 527 (StairPlaceFast.swB 738 740 (StairPlaceFast.swB 737 739
    (StairPlaceFast.swB 527 741 x)))

theorem pi_eqB (x : Wire) : ParityXExitInverse23Kernel.pi x = piB x := by
  show E1QubitPlacement.nativeSwap (E1QubitPlacement.rho x) = _
  unfold E1QubitPlacement.nativeSwap E1QubitPlacement.rho piB
  simp only [Equiv.trans_apply, StairPlaceFast.swap_eq_sw, StairPlaceFast.swB_eq]
  rfl

theorem fP_pi_fast (x : Wire) :
    fP (ParityXExitInverse23Kernel.pi x) = StairPlaceFast.phasePlaceB (piB x) := by
  rw [pi_eqB]
  exact StairPlaceFast.phasePlace_eqB _

theorem n_tab : xList.all (fun q => avoidB [4112] (StairPlaceFast.phasePlaceB (piB q))) = true := by
  decide +kernel

theorem pi_300 : ParityXExitInverse23Kernel.pi (base 300) = base 300 := by
  rw [ParityXExitInverse23Kernel.pi_base]
  rfl

/-- S1's X-exit body (`p8`, with the rival's `base 723 <-> base 300` swap) avoids wZ. -/
theorem prefix_avoid (k : Nat) : (4112 : Wire) ∉ wires (renameProgram fP
    (renameProgram (Equiv.swap (base 723) (base 300))
      (renameProgram ParityXExitInverse23Kernel.pi (ParityXExit.prefixAll base (base 2400) k)))) := by
  intro hm
  rw [renameProgram_support] at hm
  obtain ⟨y, hy, e⟩ := Finset.mem_image.mp hm
  rw [renameProgram_support] at hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rw [renameProgram_support] at hz
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
  have tb : b ∈ tSites base (base 2400) := List.mem_toFinset.mp (exitMerge_tight base (base 2400) k
    (ParityXExit.programAll_wires _ _ k (ParityXExit.prefix_sub _ _ k hb)))
  by_cases e1 : ParityXExitInverse23Kernel.pi b = base 723
  · rw [e1, Equiv.swap_apply_left, ← pi_300, fP_pi_fast] at e
    revert e
    decide +kernel
  · by_cases e2 : ParityXExitInverse23Kernel.pi b = base 300
    · rw [← pi_300] at e2
      have := ParityXExitInverse23Kernel.pi.injective e2
      subst this
      exact T723Core.base300_not_tSites tb
    · rw [Equiv.swap_apply_of_ne_of_ne e1 e2, fP_pi_fast] at e
      exact avoidB_spec (List.all_eq_true.mp n_tab b tb) 4112 (by simp) e

end StaticsS2

open StaticsS2

section
attribute [local irreducible] ECDSAAdd.wires Baselines.layout

theorem notIn0_wZ (C : Point) : wZ ∉ wires (p0 C) := stage_avoid (stage_cover C) _ (by decide)
theorem notIn1_wZ (C : Point) : wZ ∉ wires (p1 C) := stage_avoid (encode_cover C) _ (by decide)
theorem notIn2_wZ : wZ ∉ wires p2 :=
  stage_avoid (cover_of_aux AboveFieldPointDevelop.marker_support.1) _ (by decide)
theorem notIn3_wZ (cy : Fp) : wZ ∉ wires (p3 cy) := entryY_avoid _ _ (by decide)
theorem notIn4_wZ (cx : Fp) : wZ ∉ wires (p4 cx) := entryX_avoid _
theorem notIn8_wZ (cx : Fp) : wZ ∉ wires (p8 cx) := prefix_avoid _
theorem notIn9_wA : wA ∉ wires p9 := ExitAux.notIn9_of_park wA (by decide) (by decide)
theorem notIn10_wA (cy : Fp) : wA ∉ wires (p10 cy) := exitY_avoid _ _ (by decide)
theorem notIn11_wA : wA ∉ wires p11 :=
  stage_avoid (cover_of_aux AboveFieldPointDevelop.marker_support.2) _ (by decide)
theorem notIn12_wA (C : Point) : wA ∉ wires (p12 C) := stage_avoid (decode_cover C) _ (by decide)
theorem notIn13_wA (C : Point) : wA ∉ wires (p13 C) := borrowOut_avoid C _ (by decide)

end

end ECDSAAdd.Entrant.Rehost
