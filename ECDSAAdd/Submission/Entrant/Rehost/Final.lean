import ECDSAAdd.Submission.Entrant.Rehost.Flat
/-!
# S2 rehost: retire physical wire 4839 (pool 724) of S1 by piecewise top-level swaps

`flatR` is S1's flat program with piece `j` renamed by

| pieces | map | why |
|---|---|---|
| p0 .. p4 | `sA = wE <-> wZ` (4839 <-> 4112) | wZ untouched by p0 .. p4 |
| p5, p6, p7 | identity | they do not touch wE (p6: the S2 square re-host) |
| p8 | `sA` | wZ untouched by p8 |
| p9 .. p13 | `sB = wE <-> wA` (4839 <-> 4835) | wA untouched by p9 .. p13 |

Where the map changes, the wires it moves are zero in the run of S1's own program (`Inv`, `inv_switch`).
Hence `flatR` runs exactly like S1's program on every encoded input (`flatR_run`), has the same counts and
physicality, and its support is S1's minus wE (`flatR_qubits`). `rehost_certificate` turns S1's (or S2's,
40 holes) certificate with Q = 1546 into one for `rehostEntry` with Q = 1545.

Every fact that is not generic is a field of `Facts`; `Facts` is discharged in separate modules.
-/
set_option autoImplicit false

namespace ECDSAAdd.Entrant.Rehost
open ECDSAAdd Arithmetic Challenge Secp256k1 MappedCompressed
open StairConcreteAssembly

theorem run_nil' (m : List Bool) (s : State) : run [] m s = s := rfl

attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13

/-! ## Swaps of two wires -/

theorem sw_sw (a b q : Wire) : sw a b (sw a b q) = q := by
  unfold sw
  by_cases h1 : q = a
  · subst h1
    by_cases h2 : b = q
    · simp [h2]
    · simp [h2]
  · by_cases h2 : q = b
    · subst h2
      simp [h1]
    · simp [h1, h2]

theorem sw_inj (a b : Wire) : Function.Injective (sw a b) :=
  injective_of_involutive _ (sw_sw a b)

theorem sw_basis (t : State) (a b q : Wire) (ha : t.basis a = false) (hb : t.basis b = false) :
    t.basis (sw a b q) = t.basis q := by
  unfold sw
  by_cases h1 : q = a
  · subst h1
    simp only [if_true]
    rw [hb, ha]
  · by_cases h2 : q = b
    · subst h2
      simp only [h1, if_false, if_true]
      rw [ha, hb]
    · simp only [h1, h2, if_false]

/-- The map of pieces 0 .. 4 and 8. -/
def sA : Wire → Wire := sw wE wZ
/-- The map of pieces 9 .. 13. -/
def sB : Wire → Wire := sw wE wA

/-! ## The re-hosted program and entry -/

section
variable (C : Point) (cx cy : Fp)

def flatR : Program :=
  renameProgram sA (p0 C) ++ renameProgram sA (p1 C) ++ renameProgram sA p2 ++ renameProgram sA (p3 cy) ++
    renameProgram sA (p4 cx) ++ p5 ++ p6 cx ++ p7 ++ renameProgram sA (p8 cx) ++ renameProgram sB p9 ++
    renameProgram sB (p10 cy) ++ renameProgram sB p11 ++ renameProgram sB (p12 C) ++
    renameProgram sB (p13 C)

end

/-- The re-hosted program: S1's for `C = 0` (empty), `flatR` for a finite `C`. -/
def rehostProgram (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc => flatR (.some hc) cx cy

def rehostEntry : Challenge.Entry := fun C => Baselines.normalizeProgram (rehostProgram C)

/-! ## The open facts -/

/-- Everything `rehost_certificate` needs about S2's pieces. Static: `wZ` / `wA` untouched by the pieces
they host, `wE` untouched by p5 .. p7. Semantic: `wE` is zero after
p4 and after p8 (each piece measures it last), `wZ` is zero after p7. -/
structure Facts : Prop where
  z0 : ∀ C, wZ ∉ wires (p0 C)
  z1 : ∀ C, wZ ∉ wires (p1 C)
  z2 : wZ ∉ wires p2
  z3 : ∀ cy, wZ ∉ wires (p3 cy)
  z4 : ∀ cx, wZ ∉ wires (p4 cx)
  z8 : ∀ cx, wZ ∉ wires (p8 cx)
  a9 : wA ∉ wires p9
  a10 : ∀ cy, wA ∉ wires (p10 cy)
  a11 : wA ∉ wires p11
  a12 : ∀ C, wA ∉ wires (p12 C)
  a13 : ∀ C, wA ∉ wires (p13 C)
  e5 : wE ∉ wires p5
  e6 : ∀ cx, wE ∉ wires (p6 cx)
  e7 : wE ∉ wires p7
  /-- E1: the X entry measures pool 724 last. -/
  clean4 : ∀ cx (m : List Bool) (s : State), (run (p4 cx) m s).basis wE = false
  /-- E9: the X exit (before its park) measures pool 724 last. -/
  clean8 : ∀ cx (m : List Bool) (s : State), (run (p8 cx) m s).basis wE = false
  /-- Z8: 4112 is zero after the multiplication kernel's reverse walk. -/
  zClean8 : ∀ {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy), CleanAt hc 8 wZ

/-! ## Run equality -/

theorem inv_first {f : Wire → Wire} (hf : ∀ q, f (f q) = q) {s : State}
    (h : Inv f [] [] s) (P : Program) : Inv f P (renameProgram f P) s := by
  have h' := inv_step hf h P
  simpa only [List.nil_append] using h'

theorem inv_step_id {A B : Program} {s : State} (h : Inv (fun q => q) A B s) (P : Program) :
    Inv (fun q => q) (A ++ P) (B ++ P) s := by
  refine ⟨?_, fun m => ?_⟩
  · rw [measurementCount_append, measurementCount_append, h.1]
  · rw [run_append, run_append, h.1, h.2]
    rfl

theorem clean_after (A P : Program) (q : Wire) (h : ∀ (m : List Bool) (t : State), (run P m t).basis q = false)
    (s : State) (m : List Bool) : (run (A ++ P) m s).basis q = false := by
  rw [run_append]
  exact h _ _

theorem clean_first (P : Program) (s : State) (w : Wire) (hw : w ∉ wires P) (h : s.basis w = false) :
    ∀ m, (run P m s).basis w = false := by
  intro m
  rw [run_preserves_outside _ _ _ _ hw]
  exact h

theorem sw_agree {a b : Wire} {A : Program} {s : State}
    (ha : ∀ m, (run A m s).basis a = false) (hb : ∀ m, (run A m s).basis b = false) :
    ∀ m q, (run A m s).basis (sw a b q) = (run A m s).basis q :=
  fun m q => sw_basis _ a b q (ha m) (hb m)

section Run
variable (F : Facts) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
include F

/-- `flatR` runs exactly like S1's flat program on every encoded input whose output is clean on wE, wA. -/
theorem flatR_run (b : Bool) (R : Point) (s : State) (hs : encodes b R s.basis)
    (hout : ∀ m, (run (flat (.some hc) cx cy) m s).basis wE = false ∧
      (run (flat (.some hc) cx cy) m s).basis wA = false) (m : List Bool) :
    run (flatR (.some hc) cx cy) m s = run (flat (.some hc) cx cy) m s := by
  have cl := hs.2.2
  have iE : s.basis wE = false := cl wE (by decide)
  have iZ : s.basis wZ = false := cl wZ (by decide)
  have hA : ∀ q, sA (sA q) = q := sw_sw wE wZ
  have hB : ∀ q, sB (sB q) = q := sw_sw wE wA
  set C : Point := .some hc with hC
  -- boundary 0: switch from the identity to sA
  have I0 : Inv sA [] [] s := inv_switch (inv_nil s) (fun m q => by
    rw [run_nil']
    exact (sw_basis _ wE wZ q iE iZ).symm)
  -- pieces 0 .. 4 under sA
  have I5 := inv_step hA (inv_step hA (inv_step hA (inv_step hA (inv_first hA I0 (p0 C)) (p1 C)) p2) (p3 cy))
    (p4 cx)
  -- boundary 5: wE (E1) and wZ (untouched by p0 .. p4) are zero
  have z1 := clean_first (p0 C) s wZ (F.z0 C) iZ
  have z2 := clean_forward _ _ s wZ (F.z1 C) z1
  have z3 := clean_forward _ _ s wZ F.z2 z2
  have z4 := clean_forward _ _ s wZ (F.z3 cy) z3
  have z5 := clean_forward _ _ s wZ (F.z4 cx) z4
  have e5 : ∀ m, (run (p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx) m s).basis wE = false :=
    fun m => clean_after _ _ wE (F.clean4 cx) s m
  have J5 : Inv (fun q => q) (p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx) _ s :=
    inv_switch I5 (sw_agree e5 z5)
  -- pieces 5 .. 7 unchanged
  have J8 := inv_step_id (inv_step_id (inv_step_id J5 p5) (p6 cx)) p7
  -- boundary 8: wE (forward from 5) and wZ (Z8) are zero
  have e8 := clean_forward _ _ s wE F.e7 (clean_forward _ _ s wE (F.e6 cx) (clean_forward _ _ s wE F.e5 e5))
  have z8 : ∀ m, (run (p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7) m s).basis wZ = false :=
    fun m => F.zClean8 hc b R s hs m
  have I8 : Inv sA _ _ s := inv_switch J8 (fun m q => (sw_agree e8 z8 m q).symm)
  -- piece 8 under sA
  have I9 := inv_step hA I8 (p8 cx)
  -- boundary 9: wE (E9), wZ (forward), wA (backward from the output) are zero
  have e9 : ∀ m, (run (p0 C ++ p1 C ++ p2 ++ p3 cy ++ p4 cx ++ p5 ++ p6 cx ++ p7 ++ p8 cx) m s).basis wE =
      false := fun m => clean_after _ _ wE (F.clean8 cx) s m
  have z9 := clean_forward _ _ s wZ (F.z8 cx) z8
  have a14 : ∀ m, (run (flat C cx cy) m s).basis wA = false := fun m => (hout m).2
  have a13 := clean_backward _ _ s wA (F.a13 C) a14
  have a12 := clean_backward _ _ s wA (F.a12 C) a13
  have a11 := clean_backward _ _ s wA F.a11 a12
  have a10 := clean_backward _ _ s wA (F.a10 cy) a11
  have a9 := clean_backward _ _ s wA F.a9 a10
  have J9 : Inv sB _ _ s := inv_switch I9 (fun m q => by
    show (run _ m s).basis (sw wE wZ q) = (run _ m s).basis (sw wE wA q)
    rw [sw_basis _ wE wZ q (e9 m) (z9 m), sw_basis _ wE wA q (e9 m) (a9 m)])
  -- pieces 9 .. 13 under sB
  have I14 := inv_step hB (inv_step hB (inv_step hB (inv_step hB (inv_step hB J9 p9) (p10 cy)) p11) (p12 C))
    (p13 C)
  -- output: switch back to the identity
  have K : Inv (fun q => q) (flat C cx cy) (flatR C cx cy) s :=
    inv_switch I14 (sw_agree (fun m => (hout m).1) a14)
  exact inv_run_eq K m

/-- Transfer of the Hoare triple. -/
theorem flatR_triple (b : Bool) (R : Point) (Q : BasisState → Prop) (hQ : ∀ t, Q t → clean t)
    (base : Triple (encodes b R) (flat (.some hc) cx cy) Q) :
    Triple (encodes b R) (flatR (.some hc) cx cy) Q := by
  intro s m hs
  have hout : ∀ m', (run (flat (.some hc) cx cy) m' s).basis wE = false ∧
      (run (flat (.some hc) cx cy) m' s).basis wA = false := fun m' =>
    ⟨hQ _ (base s m' hs).2 wE (by decide), hQ _ (base s m' hs).2 wA (by decide)⟩
  rw [flatR_run F hc b R s hs hout m]
  exact base s m hs

end Run

/-! ## Counts, physicality and support of a renamed program -/

theorem normalizeProgram_append (a b : Program) :
    Baselines.normalizeProgram (a ++ b) = Baselines.normalizeProgram a ++ Baselines.normalizeProgram b := by
  simp only [Baselines.normalizeProgram, List.map_append]

theorem normalize_rename (f : Wire → Wire) (hf : Function.Injective f) (P : Program) :
    Baselines.normalizeProgram (renameProgram f P) = renameProgram f (Baselines.normalizeProgram P) := by
  have hc : ∀ c : Correction, Baselines.normalizeCorrection (renameCorrection f c) =
      renameCorrection f (Baselines.normalizeCorrection c) := by
    intro c
    cases c with
    | Z t => rfl
    | CZ a b =>
      by_cases h : a = b
      · subst h
        simp [Baselines.normalizeCorrection, renameCorrection]
      · have h' : f a ≠ f b := fun e => h (hf e)
        simp [Baselines.normalizeCorrection, renameCorrection, h, h']
  unfold Baselines.normalizeProgram renameProgram
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  cases i with
  | X t => rfl
  | CX a t => rfl
  | CCX a b t =>
    by_cases h : a = b
    · subst h
      simp [Baselines.normalizeInstr, renameInstr]
    · have h' : f a ≠ f b := fun e => h (hf e)
      simp [Baselines.normalizeInstr, renameInstr, h, h']
  | measureX t c0 c1 =>
    simp only [Function.comp_apply, Baselines.normalizeInstr, renameInstr, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro c _
      exact hc c
    · apply List.map_congr_left
      intro c _
      exact hc c

/-- All instructions valid. -/
def AllValid (P : Program) : Prop := ∀ i ∈ P, instructionValid i

theorem allValid_append (a b : Program) : AllValid (a ++ b) ↔ AllValid a ∧ AllValid b := by
  simp only [AllValid, List.mem_append, or_imp, forall_and]

theorem allValid_rename (f : Wire → Wire) (hf : Function.Injective f) (P : Program) :
    AllValid (renameProgram f P) ↔ AllValid P := by
  have hc : ∀ c : Correction, correctionValid (renameCorrection f c) ↔ correctionValid c := by
    intro c
    cases c with
    | Z t => exact Iff.rfl
    | CZ a b => exact ⟨fun h e => h (congrArg f e), fun h e => h (hf e)⟩
  have hi : ∀ i : Instr, instructionValid (renameInstr f i) ↔ instructionValid i := by
    intro i
    cases i with
    | X t => exact Iff.rfl
    | CX a t => exact ⟨fun h e => h (congrArg f e), fun h e => h (hf e)⟩
    | CCX a b t =>
      simp only [instructionValid, renameInstr]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun e => h1 (congrArg f e), fun e => h2 (congrArg f e),
        fun e => h3 (congrArg f e)⟩, fun ⟨h1, h2, h3⟩ => ⟨fun e => h1 (hf e), fun e => h2 (hf e),
        fun e => h3 (hf e)⟩⟩
    | measureX t c0 c1 =>
      simp only [instructionValid, renameInstr, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, hc]
  simp only [AllValid, renameProgram, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, hi]

theorem nA (P : Program) :
    Baselines.normalizeProgram (renameProgram sA P) = renameProgram sA (Baselines.normalizeProgram P) :=
  normalize_rename sA (sw_inj _ _) P

theorem nB (P : Program) :
    Baselines.normalizeProgram (renameProgram sB P) = renameProgram sB (Baselines.normalizeProgram P) :=
  normalize_rename sB (sw_inj _ _) P

theorem vA (P : Program) : AllValid (renameProgram sA P) ↔ AllValid P := allValid_rename sA (sw_inj _ _) P
theorem vB (P : Program) : AllValid (renameProgram sB P) ↔ AllValid P := allValid_rename sB (sw_inj _ _) P

section Counts
variable (C : Point) (cx cy : Fp)

theorem flatR_toffoli : toffoliCount (Baselines.normalizeProgram (flatR C cx cy)) =
    toffoliCount (Baselines.normalizeProgram (flat C cx cy)) := by
  simp only [flatR, flat, normalizeProgram_append, nA, nB, toffoliCount_append, (renameProgram_counts _ _).1]

theorem flatR_measurements : measurementCount (Baselines.normalizeProgram (flatR C cx cy)) =
    measurementCount (Baselines.normalizeProgram (flat C cx cy)) := by
  simp only [flatR, flat, normalizeProgram_append, nA, nB, measurementCount_append,
    (renameProgram_counts _ _).2]

theorem flatR_slots : gateSlots (Baselines.normalizeProgram (flatR C cx cy)) =
    gateSlots (Baselines.normalizeProgram (flat C cx cy)) := by
  simp only [flatR, flat, normalizeProgram_append, nA, nB, gateSlots_append, Baselines.rename_gateSlots]

theorem flatR_physical (h : AllValid (Baselines.normalizeProgram (flat C cx cy))) :
    AllValid (Baselines.normalizeProgram (flatR C cx cy)) := by
  simp only [flatR, flat, normalizeProgram_append, nA, nB, allValid_append, vA, vB] at h ⊢
  exact h

end Counts

/-- A wire of a piece renamed by a swap with a host the piece does not touch. -/
theorem sw_case {a h x : Wire} {P : Program} {T : Finset Wire} (hah : a ≠ h) (hh : h ∉ wires P)
    (hP : wires P ⊆ T) (hx : x ∈ wires (renameProgram (sw a h) P)) : x ≠ a ∧ (x ∈ T ∨ x = h) := by
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  unfold sw
  by_cases e1 : y = a
  · rw [if_pos e1]
    exact ⟨Ne.symm hah, Or.inr rfl⟩
  · by_cases e2 : y = h
    · exact absurd (e2 ▸ hy) hh
    · rw [if_neg e1, if_neg e2]
      exact ⟨e1, Or.inl (hP hy)⟩

theorem id_case {a x : Wire} {P : Program} {T : Finset Wire} (ha : a ∉ wires P) (hP : wires P ⊆ T)
    (hx : x ∈ wires P) : x ≠ a ∧ x ∈ T := by
  refine ⟨?_, hP hx⟩
  rintro rfl
  exact ha hx

section Support
variable (F : Facts) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
include F

/-- Every wire of `flatR` is a wire of S1's program or one of the two hosts, and never wE. -/
theorem flatR_wires : ∀ x ∈ wires (flatR (.some hc) cx cy),
    x ≠ wE ∧ (x ∈ wires (flat (.some hc) cx cy) ∨ x = wZ ∨ x = wA) := by
  have zE : wE ≠ wZ := by decide
  have aE : wE ≠ wA := by decide
  have s0 : wires (p0 (.some hc)) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s1 : wires (p1 (.some hc)) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s2 : wires (p2) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s3 : wires (p3 cy) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s4 : wires (p4 cx) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s5 : wires (p5) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s6 : wires (p6 cx) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s7 : wires (p7) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s8 : wires (p8 cx) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s9 : wires (p9) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s10 : wires (p10 cy) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s11 : wires (p11) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s12 : wires (p12 (.some hc)) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  have s13 : wires (p13 (.some hc)) ⊆ wires (flat (.some hc) cx cy) := by
    simp only [flat, wires_append]
    repeat (first | exact Finset.subset_union_right | exact Finset.Subset.refl _ |
      refine Finset.Subset.trans ?_ Finset.subset_union_left)
  intro x hx
  simp only [flatR, wires_append, Finset.mem_union] at hx
  rcases hx with (((((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11) | h12) | h13)
  · obtain ⟨n, h⟩ := sw_case zE (F.z0 _) s0 h0
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inl e))⟩
  · obtain ⟨n, h⟩ := sw_case zE (F.z1 _) s1 h1
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inl e))⟩
  · obtain ⟨n, h⟩ := sw_case zE (F.z2) s2 h2
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inl e))⟩
  · obtain ⟨n, h⟩ := sw_case zE (F.z3 cy) s3 h3
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inl e))⟩
  · obtain ⟨n, h⟩ := sw_case zE (F.z4 cx) s4 h4
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inl e))⟩
  · obtain ⟨n, h⟩ := id_case (F.e5) s5 h5
    exact ⟨n, Or.inl h⟩
  · obtain ⟨n, h⟩ := id_case (F.e6 cx) s6 h6
    exact ⟨n, Or.inl h⟩
  · obtain ⟨n, h⟩ := id_case (F.e7) s7 h7
    exact ⟨n, Or.inl h⟩
  · obtain ⟨n, h⟩ := sw_case zE (F.z8 cx) s8 h8
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inl e))⟩
  · obtain ⟨n, h⟩ := sw_case aE (F.a9) s9 h9
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inr e))⟩
  · obtain ⟨n, h⟩ := sw_case aE (F.a10 cy) s10 h10
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inr e))⟩
  · obtain ⟨n, h⟩ := sw_case aE (F.a11) s11 h11
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inr e))⟩
  · obtain ⟨n, h⟩ := sw_case aE (F.a12 _) s12 h12
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inr e))⟩
  · obtain ⟨n, h⟩ := sw_case aE (F.a13 _) s13 h13
    exact ⟨n, h.elim Or.inl (fun e => Or.inr (Or.inr e))⟩

end Support

/-! ## The qubit bound: S1's hole placement plus pool 724 -/

theorem finalHoles_eq : StairOpenWiring.finalHoles = StairOpenWiring.finalHoleIndices.map (fun i => 4115 + i) := by
  unfold StairOpenWiring.finalHoles
  apply List.map_congr_left
  intro i hi
  apply StairHoleSupport.poolWire_eq
  simp only [StairOpenWiring.finalHoleIndices, List.mem_append, List.mem_range'_1] at hi
  rcases hi with hi | hi
  · omega
  · have := StairCertificate.extraIdx_window i hi; omega

theorem notFinal (w : Wire) (h : ∀ i ∈ StairOpenWiring.finalHoleIndices, 4115 + i ≠ w) :
    w ∉ StairOpenWiring.finalHoles := by
  rw [finalHoles_eq]
  intro hw
  obtain ⟨i, hi, e⟩ := List.mem_map.mp hw
  exact h i hi e

theorem wE_notFinal : wE ∉ StairOpenWiring.finalHoles :=
  notFinal wE (fun i hi e => by
    have hi' : i ≠ 724 := by
      intro h; subst h; revert hi; decide
    exact hi' (by unfold wE at e; omega))

theorem wZ_notFinal : wZ ∉ StairOpenWiring.finalHoles :=
  notFinal wZ (fun i _ e => by unfold wZ at e; omega)

theorem wA_notFinal : wA ∉ StairOpenWiring.finalHoles :=
  notFinal wA (fun i hi e => by
    have hi' : i ≠ 720 := by
      intro h; subst h; revert hi; decide
    exact hi' (by unfold wA at e; omega))

theorem arena_mem (w : Wire) (h : w = 4112 ∨ w = 4835) : w ∈ StairHoleSupport.recordArena.toFinset := by
  rw [List.mem_toFinset, StairHoleSupport.recordArena_eqN]
  rcases h with rfl | rfl <;>
  · simp only [List.mem_append, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
    decide

theorem notOld (w : Wire) (h : w = 4112 ∨ w = 4835) : w ∉ StairHoleSupport.oldHoles := by
  have e : StairHoleSupport.oldHoles = StairPhysicalLayout.oldHolesNat := StairPhysicalLayout.oldHoles_eq
  rw [e]
  rcases h with rfl | rfl <;> decide

/-- The 41-hole list: S1's 40 and pool 724. -/
abbrev holes41 : List Wire := StairOpenWiring.finalHoles ++ [wE]

theorem holes41_list : StairCertificate.HoleList holes41 := by
  apply StairCertificate.holeList_of_physical_sub
  · exact List.nodup_append.mpr ⟨StairOpenWiring.finalHoles_nodup, List.nodup_singleton _,
      fun a ha b hb e => by
        rw [List.mem_singleton] at hb
        subst hb e
        exact wE_notFinal ha⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact StairOpenWiring.finalHoles_sub q hq
    · rw [List.mem_singleton] at hq
      subst hq
      rw [StairPhysicalLayout.physicalHoles_eq_nat]
      decide

theorem flatR_placement (F : Facts) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hp : StairCertificate.HolePlacement StairOpenWiring.finalHoles (flat (.some hc) cx cy)) :
    StairCertificate.HolePlacement holes41 (flatR (.some hc) cx cy) where
  insideArena := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hp.insideArena (Finset.mem_union_left _ h)
    · rcases (flatR_wires F hc x h).2 with h' | rfl | rfl
      · exact hp.insideArena (Finset.mem_union_right _ h')
      · exact arena_mem _ (Or.inl rfl)
      · exact arena_mem _ (Or.inr rfl)
  oldFree := by
    intro q hq h
    rcases (flatR_wires F hc q h).2 with h' | rfl | rfl
    · exact hp.oldFree q hq h'
    · exact notOld _ (Or.inl rfl) hq
    · exact notOld _ (Or.inr rfl) hq
  holesFree := by
    intro q hq h
    have w := flatR_wires F hc q h
    rcases List.mem_append.mp hq with hq | hq
    · rcases w.2 with h' | rfl | rfl
      · exact hp.holesFree q hq h'
      · exact wZ_notFinal hq
      · exact wA_notFinal hq
    · rw [List.mem_singleton] at hq
      exact w.1 hq

theorem holes41_length : 1586 - holes41.length = 1545 := by
  simp only [holes41, List.length_append, List.length_singleton, StairOpenWiring.finalHoles,
    List.length_map, StairOpenWiring.finalHoleIndices, List.length_range']
  decide

theorem flatR_qubits (F : Facts) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)
    (hp : StairCertificate.HolePlacement StairOpenWiring.finalHoles (flat (.some hc) cx cy)) :
    qubits (flatR (.some hc) cx cy) ≤ 1545 := by
  have h := StairCertificate.qubits_le_holes holes41 holes41_list _ (flatR_placement F hc hp)
  rw [holes41_length] at h
  exact h

/-! ## The certificate -/

theorem concrete_eq {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    concreteAssembly.program (.some hc) = flat (.some hc) cx cy := concreteProgram_flat hc

/-- S2's certificate (Q = 1545) from S1's (or S2's 40-hole) certificate (any Q), its hole placement
(`(StairOpenWiring.stairOpen_of_remaining StairOpenWiring.remaining).site_avoidance`) and the open `Facts`. -/
theorem rehost_certificate (F : Facts) {T M Q S : Nat}
    (base : Challenge.Certificate (StairCertificate.stairEntry concreteAssembly) ⟨T, M, Q, S⟩)
    (hopen : ∀ C, StairCertificate.HolePlacement StairOpenWiring.finalHoles (concreteAssembly.program C)) :
    Challenge.Certificate rehostEntry ⟨T, M, 1545, S⟩ where
  correct C b R := by
    cases C with
    | zero => exact base.correct .zero b R
    | @some cx cy hc =>
      have h := base.correct (.some hc) b R
      change Triple _ (Baselines.normalizeProgram (concreteAssembly.program (.some hc))) _ at h
      rw [Baselines.normalize_triple, concrete_eq hc] at h
      change Triple _ (Baselines.normalizeProgram (flatR (.some hc) cx cy)) _
      rw [Baselines.normalize_triple]
      exact flatR_triple F hc b R _ (fun t ht => ht.2.2) h
  physical C := by
    cases C with
    | zero => exact base.physical .zero
    | @some cx cy hc =>
      have h := base.physical (.some hc)
      change AllValid (Baselines.normalizeProgram (concreteAssembly.program (.some hc))) at h
      rw [concrete_eq hc] at h
      exact flatR_physical (.some hc) cx cy h
  toffoli_le C := by
    cases C with
    | zero => exact base.toffoli_le .zero
    | @some cx cy hc =>
      have h := base.toffoli_le (.some hc)
      change toffoliCount (Baselines.normalizeProgram (concreteAssembly.program (.some hc))) ≤ T at h
      rw [concrete_eq hc] at h
      change toffoliCount (Baselines.normalizeProgram (flatR (.some hc) cx cy)) ≤ T
      rw [flatR_toffoli]
      exact h
  measurements_le C := by
    cases C with
    | zero => exact base.measurements_le .zero
    | @some cx cy hc =>
      have h := base.measurements_le (.some hc)
      change measurementCount (Baselines.normalizeProgram (concreteAssembly.program (.some hc))) ≤ M at h
      rw [concrete_eq hc] at h
      change measurementCount (Baselines.normalizeProgram (flatR (.some hc) cx cy)) ≤ M
      rw [flatR_measurements]
      exact h
  qubits_le C := by
    cases C with
    | zero =>
      change qubits (Baselines.normalizeProgram []) ≤ 1545
      simp [Baselines.normalizeProgram, qubits, ioWires, wires]
    | @some cx cy hc =>
      have h := hopen (.some hc)
      rw [concrete_eq hc] at h
      change qubits (Baselines.normalizeProgram (flatR (.some hc) cx cy)) ≤ 1545
      rw [Baselines.normalize_qubits]
      exact flatR_qubits F hc h
  gateSlots_le C := by
    cases C with
    | zero => exact base.gateSlots_le .zero
    | @some cx cy hc =>
      have h := base.gateSlots_le (.some hc)
      change gateSlots (Baselines.normalizeProgram (concreteAssembly.program (.some hc))) ≤ S at h
      rw [concrete_eq hc] at h
      change gateSlots (Baselines.normalizeProgram (flatR (.some hc) cx cy)) ≤ S
      rw [flatR_slots]
      exact h

end ECDSAAdd.Entrant.Rehost
