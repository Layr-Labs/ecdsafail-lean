import ECDSAAdd.Submission.Entrant.Rehost.Flat
/-!
# S2 rehost: E1 and E9, the X entry and the X exit leave pool 724 (wE = 4839) clean

Both facts are syntactic: the last write of the label that is placed on 4839 is a `measureX`, and nothing
after it touches the label. They hold from every state and on every record (`AlwaysClean`), which is what
`Facts.clean4` / `Facts.clean8` ask for.

* p4 (X entry, S1): `entryXNew = rename (swap (pmapR 721) (pmapR 300)) entryXNew0`; the label is
  `pmapR (base 722)` (fixed by the swap), measured in `postX` (record E1 proof, `CleanEntry`).
* p8 (X exit before its park, S1): `rename fP (rename (swap 723 300) (rename pi prefixAll))`; the label is
  `base 722` of `prefixAll`, measured by `addPartInit`'s last instruction; `rotateLeft kR` and `parBack`
  never touch it. `pi (base 722) = base 724`, fixed by the swap and by `phaseHost`, placed on 4839.
-/
set_option autoImplicit false

namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed
open StairConcreteAssembly

namespace CleanS2

/-- `q` is false after `p`, from every state and on every measurement record. -/
def AlwaysClean (p : Program) (q : Wire) : Prop :=
  ∀ (m : List Bool) (s : State), (run p m s).basis q = false

theorem measure_single (t : Wire) (c0 c1 : List Correction) : AlwaysClean [.measureX t c0 c1] t := by
  intro m s
  simp [run, measureAndCorrect, writeBit]

theorem append_right {P Q : Program} {q : Wire} (h : AlwaysClean Q q) : AlwaysClean (P ++ Q) q := by
  intro m s
  rw [run_append]
  exact h _ _

theorem append_left {P Q : Program} {q : Wire} (h : AlwaysClean P q) (hq : q ∉ wires Q) :
    AlwaysClean (P ++ Q) q := by
  intro m s
  rw [run_append, run_preserves_outside _ _ _ _ hq]
  exact h _ _

theorem rename {f : Wire → Wire} (hf : Function.Injective f) {P : Program} {q : Wire}
    (h : AlwaysClean P q) : AlwaysClean (renameProgram f P) (f q) := by
  intro m s
  have e : (run (renameProgram f P) m s).basis (f q) = (run P m (pullState f s)).basis q :=
    congrArg (fun t : State => t.basis q) (run_rename f hf P m s)
  rw [e]
  exact h _ _

theorem rename_pool {f : Wire → Wire} {S : Finset Wire} (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    {P : Program} (hP : wires P ⊆ S) {q : Wire} (hq : q ∈ S) (h : AlwaysClean P q) :
    AlwaysClean (renameProgram f P) (f q) := by
  intro m s
  rw [(run_rename_pool f S hf P hP m (pullState f s) s rfl (fun _ _ => rfl)).2 q hq]
  exact h _ _

theorem fG_injective : Function.Injective fG := StairSquareSites.UG_inj

section
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

theorem not_blk722 (a n : Nat) (h : 722 < a ∨ a + n ≤ 722) : base 722 ∉ wireBlock base a n := by
  intro H
  obtain ⟨j, hj, e⟩ := List.mem_map.mp H
  have := base_injective e
  simp only [List.mem_range'_1] at hj
  omega

theorem loadT_no722 (k : Nat) : base 722 ∉ wires (E1Merge.loadT base (base 2400) k) := by
  unfold E1Merge.loadT
  rw [wires_append]
  intro H
  rcases Finset.mem_union.mp H with H | H <;>
  · rcases List.mem_cons.mp (List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ H)) with e | e
    · exact absurd (base_injective e) (by omega)
    · exact not_blk722 1029 256 (by omega) e

/-- E1 at label level: `postX` measures `base 722` and never touches it again (record proof). -/
theorem postX_clean722 (k : Nat) : AlwaysClean (ParityXEntry.postX base (base 2400) k) (base 722) := by
  unfold ParityXEntry.postX
  refine append_left (append_left (append_left (append_left (append_left (append_left (append_left
    (append_right (measure_single _ _ _)) ?_) ?_) ?_) (loadT_no722 k)) ?_) (loadT_no722 k)) ?_
  · rw [copyRegister_wires none _ _ (by simp [E1Merge.hpR, wireBlock_length])]
    split
    · exact Finset.notMem_empty _
    · intro H
      simp only [Option.toList_none, List.nil_append, List.mem_toFinset, List.mem_append] at H
      rcases H with H | H
      · exact not_blk722 770 257 (by omega) H
      · exact not_blk722 1 257 (by omega) H
  · intro H
    have H1 : base 722 ∈ wires (mappedAdd (E1Merge.dBits base) (E1Merge.hpR base) (E1Merge.hC2 base) (base 1797)) :=
      E1Merge.hAddT_wires base H
    have H2 := mappedAdd_wires_subset _ _ _ _ H1
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at H2
    rcases H2 with ((H2 | H2) | H2) | H2
    · exact absurd (base_injective (E1Merge.dBits_wire base _ H2)) (by omega)
    · exact not_blk722 1 257 (by omega) H2
    · exact not_blk722 1540 256 (by omega) H2
    · exact absurd (base_injective H2) (by omega)
  · simp [wires, Instr.wires, base]
  · intro H
    have H2 := eraseLtChain_wires_subset _ _ _ _ _ H
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at H2
    rcases H2 with ((H2 | H2) | H2) | H2 | H2
    · exact not_blk722 1 256 (by omega) H2
    · exact not_blk722 1029 256 (by omega) H2
    · exact not_blk722 1540 255 (by omega) H2
    · exact absurd (base_injective H2) (by omega)
    · exact absurd (base_injective H2) (by omega)
  · simp [wires, Instr.wires, correctionWires, base]

theorem S_mem722 : base 722 ∈ E1QubitPlacement.S := by
  unfold E1QubitPlacement.S
  exact List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 722 (by omega))

/-- The record X entry (any `pk`) leaves `pmapR (base 722)` clean. -/
theorem entryXNew0_clean (pk : Wire) (k : Fp) :
    AlwaysClean (FlagEntry.entryXNew0 L0 pk k) (E1QubitPlacement.pmapR L0 (base 722)) := by
  have inj := E1QubitPlacement.pmap_inj L0 Baselines.layout_widths Baselines.layout_nodup
  unfold FlagEntry.entryXNew0
  split_ifs
  · exact append_right (rename_pool inj (FlagEntry.tailX_S _) S_mem722
      (by unfold ParityXEntry.tailX; exact append_right (postX_clean722 _)))
  · exact append_right (append_right (rename_pool inj (FlagEntry.evenTail_S _) S_mem722
      (by unfold ParityXEntry.evenTail; exact append_right (postX_clean722 _))))

/-- **E1** (S1): p4 leaves wE = 4839 clean. -/
theorem clean4 (cx : Fp) (m : List Bool) (s : State) : (run (p4 cx) m s).basis wE = false := by
  have sw : Equiv.swap (E1QubitPlacement.pmapR L0 (base 721)) (E1QubitPlacement.pmapR L0 (base 300))
      (E1QubitPlacement.pmapR L0 (base 722)) = E1QubitPlacement.pmapR L0 (base 722) := by
    rw [← FlagTop.pk_eq L0]
    exact Equiv.swap_apply_of_ne_of_ne
      (FlagEntry.pk_ne_high L0 Baselines.layout_widths Baselines.layout_nodup)
      (FlagEntry.pk_ne_300 L0 Baselines.layout_widths Baselines.layout_nodup)
  have e : fG (E1QubitPlacement.pmapR L0 (base 722)) = wE := by
    show StairSiteAvoidance.UG _ = _
    rw [StairSiteEasy.xplace_fast]
    decide
  have h := rename fG_injective (rename (Equiv.swap (E1QubitPlacement.pmapR L0 (base 721))
    (E1QubitPlacement.pmapR L0 (base 300))).injective (entryXNew0_clean (FlagEntry.pkW L0) (-cx)))
  rw [sw, e] at h
  exact h m s

/-! ## E9: the X exit before its park -/

theorem rot_no722 : base 722 ∉ wires (rotateLeft (E1Merge.kR base)) := by
  rw [(rotate_wires (E1Merge.kR base)).2]
  split_ifs
  · exact Finset.notMem_empty _
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    omega

theorem parBack_no722 (k : Nat) : base 722 ∉ wires (ExitMerge.parBack base (base 2400) k) := by
  unfold ExitMerge.parBack
  split_ifs <;> simp [wires, Instr.wires, MappedCompressed.base]

theorem addPart_clean722 (k : Nat) : AlwaysClean (ExitMerge.addPart base (base 2400) k) (base 722) := by
  rw [ExitMerge.addPart_split]
  refine append_left ?_ (by simp [wires, Instr.wires, correctionWires, MappedCompressed.base])
  unfold ExitMerge.addPartInit
  exact append_right (measure_single _ _ _)

theorem prefix_clean722 (k : Nat) : AlwaysClean (ParityXExit.prefixAll base (base 2400) k) (base 722) := by
  unfold ParityXExit.prefixAll
  exact append_left (append_left (append_right (addPart_clean722 k)) rot_no722) (parBack_no722 k)

end

theorem phaseHost_pkP :
    Rolling1588Lifetime.phaseHost ParityXExitInverse23Kernel.pkP = ParityXExitInverse23Kernel.pkP := by
  decide

attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run Rolling1588Lifetime.phaseHost
  ParityXExitInverse23Kernel.pi ParityXExit.prefixAll InverseFive23.stackReverse15
  Rolling1588.exitFieldHosted Rolling1588TickGap.firstPhase

/-- The label part of p8 lies in the kernel's logical sites. -/
theorem p8_logical (k : Nat) :
    wires (renameProgram Rolling1588Lifetime.phaseHost (renameProgram (Equiv.swap (base 723) (base 300))
      (renameProgram ParityXExitInverse23Kernel.pi (ParityXExit.prefixAll base (base 2400) k)))) ⊆
      OB5Support.logicalSites := by
  refine Finset.Subset.trans ?_ (ParityXExitInverse23Kernel.kernelXN_support k)
  have h1 : wires (renameProgram Rolling1588Lifetime.phaseHost (renameProgram (Equiv.swap (base 723) (base 300))
      (renameProgram ParityXExitInverse23Kernel.pi (ParityXExit.prefixAll base (base 2400) k)))) ⊆
      wires (renameProgram Rolling1588Lifetime.phaseHost (ParityXExitInverse23Kernel.x1N k)) := by
    unfold ParityXExitInverse23Kernel.x1N ParityXExitInverse23Kernel.x1N0 ParityXExit.programN
    simp only [renameProgram_append, wires_append]
    exact Finset.subset_union_left
  refine h1.trans ?_
  unfold ParityXExitInverse23Kernel.kernelXN ParityXExitInverse23Kernel.lastXN
  simp only [renameProgram_append, wires_append]
  exact Finset.subset_union_right.trans (Finset.subset_union_right.trans Finset.subset_union_right)

/-- **E9** (S1): p8 leaves wE = 4839 clean. -/
theorem clean8 (cx : Fp) (m : List Bool) (s : State) : (run (p8 cx) m s).basis wE = false := by
  have h1 := rename ParityXExitInverse23Kernel.pi.injective (prefix_clean722 cx.val)
  rw [ParityXExitInverse23Kernel.pi_722] at h1
  have h2 := rename (Equiv.swap (base 723) (base 300)).injective h1
  have sw : Equiv.swap (base 723) (base 300) ParityXExitInverse23Kernel.pkP = ParityXExitInverse23Kernel.pkP :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  rw [sw] at h2
  have h3 := rename Rolling1588Lifetime.phaseHost.injective h2
  rw [phaseHost_pkP] at h3
  rcases placement2 L0 Baselines.layout_widths Baselines.layout_nodup with
    ⟨injective, -, -, -, -, -, -, -⟩
  have pkD : ParityXExitInverse23Kernel.pkP ∈ OB5Support.logicalSites := by
    have := E1QubitPlacement.sw_logical 724 (by unfold E1QubitPlacement.Rng; omega)
    simpa [E1QubitPlacement.sw, ParityXExitInverse23Kernel.pkP] using this
  have h4 := rename_pool (f := wireFn2 L0) (fun a ha b hb eq => injective a (ArithmeticOB5.logical_sub_old ha) b
    (ArithmeticOB5.logical_sub_old hb) eq) (p8_logical cx.val) pkD h3
  rw [ParityXExitInverse23Kernel.pk_wire L0] at h4
  have h5 := rename fG_injective h4
  have e : fG (FlagEntry.pkW L0) = wE := by
    show StairSiteAvoidance.UG _ = _
    rw [StairSiteEasy.UG_fast]
    decide +kernel
  rw [e] at h5
  have eq : p8 cx = renameProgram fG (renameProgram (wireFn2 L0) (renameProgram Rolling1588Lifetime.phaseHost
      (renameProgram (Equiv.swap (base 723) (base 300))
        (renameProgram ParityXExitInverse23Kernel.pi (ParityXExit.prefixAll base (base 2400) cx.val))))) := by
    unfold p8
    rw [fP_eq, fK_eq]
  rw [eq]
  exact h5 m s

end CleanS2

end ECDSAAdd.Entrant.Rehost
