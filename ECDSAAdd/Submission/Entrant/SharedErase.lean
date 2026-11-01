import ECDSAAdd.Submission.Entrant.FusedBoundaryFinal
import ECDSAAdd.Submission.Entrant.EraseLast

/-! Measured erasure of the two last-writer Toffolis of the closing classifier.

The final `shared` stage XORs the three class flags back to zero.  The bit test that
clears `core.generic` (renamed to the park site) and the one that clears
`doubleSelect` are the last writes to those wires in the whole program, and the
output contract makes both wires clean.  `EraseLast.rel_triple` therefore turns
each of them into `measureX t [] [CZ a b]`, saving two Toffolis for every `C`. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.SharedErase
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout RecordedQuantum EraseLast
  MeasuredCodec5 MappedCompressed CompressedPointDialog

/-! ## Erased building blocks -/

def bitTestE (w y t : Wire) (a : Bool) : Program :=
  if a then [.measureX t [] [.CZ w y]] else [.X y, .measureX t [] [.CZ w y], .X y]

theorem bitTest_rel (w y t : Wire) (a : Bool) (hw : w ≠ t) (hy : y ≠ t) :
    EraseRel t (bitTest w y t a) (bitTestE w y t a) := by
  cases a
  · refine ⟨[.X y], [.X y], w, y, hw, hy, ?_, rfl, rfl⟩
    exact noWrite_cons.mpr ⟨hy, noWrite_nil t⟩
  · exact rel_base w y t hw hy

theorem bitTest_noWrite (w y t' : Wire) (a : Bool) (t : Wire) (hy : y ≠ t) (ht : t' ≠ t) :
    NoWrite t (bitTest w y t' a) := by
  cases a <;> intro i hi <;> simp [bitTest, zeroFlag] at hi <;>
    rcases hi with rfl | rfl | rfl <;> simp [tgt, hy, ht]

theorem bitTestE_noWrite (w y t' : Wire) (a : Bool) (t : Wire) (hy : y ≠ t) (ht : t' ≠ t) :
    NoWrite t (bitTestE w y t' a) := by
  cases a <;> intro i hi <;> simp [bitTestE] at hi <;>
    rcases hi with rfl | rfl | rfl <;> simp [tgt, hy, ht]

theorem chainErase_noWrite (c a t' t : Wire) (ha : a ≠ t) (ht : t' ≠ t) :
    NoWrite t (chainErase c a t') := by
  intro i hi; simp [chainErase] at hi
  rcases hi with rfl | rfl | rfl <;> simp [tgt, ha, ht]

theorem cx2_noWrite (p q w t : Wire) (hw : w ≠ t) : NoWrite t [.CX p w, .CX q w] := by
  intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp [tgt, hw]

def pairTailE1 (y t₁ t₂ : Wire) (e₁ a₁ e₂ a₂ : Bool) (w : Wire) : Program :=
  if tailFused e₁ a₁ e₂ a₂ then .CX t₁ t₂ :: (bitTestE w y t₁ a₁ ++ [.CX t₁ t₂, .CX w t₂])
  else (if e₁ then bitTestE w y t₁ a₁ else []) ++ (if e₂ then bitTest w y t₂ a₂ else [])

theorem pairTail_rel1 (y t₁ t₂ : Wire) (a₁ e₂ a₂ : Bool) (w : Wire)
    (hw : w ≠ t₁) (hy : y ≠ t₁) (h2 : t₂ ≠ t₁) :
    EraseRel t₁ (pairTail y t₁ t₂ true a₁ e₂ a₂ w) (pairTailE1 y t₁ t₂ true a₁ e₂ a₂ w) := by
  unfold pairTail pairTailE1
  by_cases hf : tailFused true a₁ e₂ a₂ = true
  · rw [if_pos hf, if_pos hf]
    exact rel_left [.CX t₁ t₂] (rel_right _ (bitTest_rel w y t₁ a₁ hw hy)
      (cx2_noWrite t₁ w t₂ t₁ h2))
  · rw [if_neg hf, if_neg hf]
    cases e₂
    · simp only [plainTail, if_true, Bool.false_eq_true, if_false, List.append_nil]
      exact bitTest_rel w y t₁ a₁ hw hy
    · simp only [plainTail, if_true]
      exact rel_right _ (bitTest_rel w y t₁ a₁ hw hy) (bitTest_noWrite w y t₂ a₂ t₁ hy h2)

/-! ## Generic classifier skeleton -/

def suffixG (T : Wire → Program) (c r : Wire) (bs : List ZeroBit) (a b : Nat) : Program :=
  affineClassSelect r (bs.map ZeroBit.input) a b ++ zeroWith T c bs ++
  affineClassSelect r (bs.map ZeroBit.input) a b

def inputG (Tl : Wire → Wire → Wire → Program) (Same : Wire → Program) :
    Wire → List ZeroBit → Nat → Nat → Program
  | c, [], _, _ => Same c
  | c, q::qs, a, b =>
    (if a % 2 = 1 then [.X q.input] else []) ++
    (if a % 2 = b % 2 then
      chainAnd c q.input q.work ++ inputG Tl Same q.work qs (a/2) (b/2) ++
      chainErase c q.input q.work
    else suffixG (Tl q.input q.work) c q.input qs (a/2) (b/2)) ++
    (if a % 2 = 1 then [.X q.input] else [])

def Tl0 (y t₁ t₂ t₃ wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) (r wa h : Wire) : Program :=
  affineClassTail r y t₁ t₂ t₃ wa wb e₁ a₁ e₂ a₂ a₃ h

def Tl3 (y t₁ t₂ t₃ wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) (r wa h : Wire) : Program :=
  chainAnd h r wa ++ [.CX h wb, .CX wa wb] ++
  pairTail y t₁ t₂ e₁ a₁ e₂ a₂ wa ++ bitTestE wb y t₃ a₃ ++
  [.CX wa wb, .CX h wb] ++ chainErase h r wa

def Tl13 (y t₁ t₂ t₃ wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) (r wa h : Wire) : Program :=
  chainAnd h r wa ++ [.CX h wb, .CX wa wb] ++
  pairTailE1 y t₁ t₂ e₁ a₁ e₂ a₂ wa ++ bitTestE wb y t₃ a₃ ++
  [.CX wa wb, .CX h wb] ++ chainErase h r wa

def Same3 (y t₁ t₂ t₃ : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) (h : Wire) : Program :=
  pairTail y t₁ t₂ e₁ a₁ e₂ a₂ h ++ bitTestE h y t₃ a₃

def Same13 (y t₁ t₂ t₃ : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) (h : Wire) : Program :=
  pairTailE1 y t₁ t₂ e₁ a₁ e₂ a₂ h ++ bitTestE h y t₃ a₃

theorem inputG_orig (y t₁ t₂ t₃ wb : Wire) (e₁ a₁ e₂ a₂ a₃ : Bool) :
    ∀ (c : Wire) (bs : List ZeroBit) (a b : Nat),
    affineInputWith y t₁ t₂ t₃ wb e₁ a₁ e₂ a₂ a₃ c bs a b =
      inputG (Tl0 y t₁ t₂ t₃ wb e₁ a₁ e₂ a₂ a₃) (affineClassSameTail y t₁ t₂ t₃ e₁ a₁ e₂ a₂ a₃)
        c bs a b
  | c, [], a, b => rfl
  | c, q::qs, a, b => by
    simp only [affineInputWith, inputG, inputG_orig y t₁ t₂ t₃ wb e₁ a₁ e₂ a₂ a₃ q.work qs]
    rfl

theorem zeroWith_rel (t : Wire) (T T' : Wire → Program) (hT : ∀ h, EraseRel t (T h) (T' h)) :
    ∀ (c : Wire) (bs : List ZeroBit), (∀ q ∈ bs, q.input ≠ t ∧ q.work ≠ t) →
    EraseRel t (zeroWith T c bs) (zeroWith T' c bs)
  | c, [], _ => hT c
  | c, q::qs, hq => by
    have h1 := hq q (by simp)
    have ih := zeroWith_rel t T T' hT q.work qs (fun d hd => hq d (by simp [hd]))
    exact rel_right _ (rel_left _ ih) (chainErase_noWrite c q.input q.work t h1.1 h1.2)

theorem select_noWrite (r : Wire) (bs : List ZeroBit) (a b : Nat) (t : Wire) (hr : r ≠ t)
    (hq : ∀ q ∈ bs, q.input ≠ t ∧ q.work ≠ t) :
    NoWrite t (affineClassSelect r (bs.map ZeroBit.input) a b) := by
  apply noWrite_of_not_mem
  intro ht
  have h := affineClassSelect_wires r (bs.map ZeroBit.input) a b ht
  simp only [List.mem_toFinset, List.mem_cons, List.mem_map] at h
  rcases h with h | ⟨q, hq', e⟩
  · exact hr h.symm
  · exact (hq q hq').1 e

theorem inputG_rel (t : Wire) (Tl Tl' : Wire → Wire → Wire → Program) (Same Same' : Wire → Program)
    (hT : ∀ r wa h, r ≠ t → wa ≠ t → EraseRel t (Tl r wa h) (Tl' r wa h))
    (hS : ∀ h, h ≠ t → EraseRel t (Same h) (Same' h)) :
    ∀ (c : Wire) (bs : List ZeroBit) (a b : Nat), c ≠ t → (∀ q ∈ bs, q.input ≠ t ∧ q.work ≠ t) →
    EraseRel t (inputG Tl Same c bs a b) (inputG Tl' Same' c bs a b)
  | c, [], a, b, hc, _ => hS c hc
  | c, q::qs, a, b, hc, hq => by
    have h1 := hq q (by simp)
    have hqs : ∀ d ∈ qs, d.input ≠ t ∧ d.work ≠ t := fun d hd => hq d (by simp [hd])
    have hflip : NoWrite t (if a % 2 = 1 then [.X q.input] else []) := by
      split_ifs
      · exact noWrite_cons.mpr ⟨h1.1, noWrite_nil t⟩
      · exact noWrite_nil t
    simp only [inputG]
    refine rel_right _ (rel_left _ ?_) hflip
    split_ifs
    · have ih := inputG_rel t Tl Tl' Same Same' hT hS q.work qs (a/2) (b/2) h1.2 hqs
      exact rel_right _ (rel_left _ ih) (chainErase_noWrite c q.input q.work t h1.1 h1.2)
    · unfold suffixG
      exact rel_right _ (rel_left _ (zeroWith_rel t _ _ (fun h => hT q.input q.work h h1.1 h1.2)
        c qs hqs)) (select_noWrite q.input qs _ _ t h1.1 hqs)

/-! ## The two erasures inside the classifier -/

section
variable (y t₁ t₂ t₃ wb : Wire) (a₁ e₂ a₂ a₃ : Bool)

theorem tl_rel3 (hy : y ≠ t₃) (hwb : wb ≠ t₃) (e₁ : Bool) :
    ∀ r wa h, r ≠ t₃ → wa ≠ t₃ →
      EraseRel t₃ (Tl0 y t₁ t₂ t₃ wb e₁ a₁ e₂ a₂ a₃ r wa h) (Tl3 y t₁ t₂ t₃ wb e₁ a₁ e₂ a₂ a₃ r wa h) := by
  intro r wa h hr hwa
  unfold Tl0 Tl3 affineClassTail
  exact rel_right _ (rel_right _ (rel_left _ (bitTest_rel wb y t₃ a₃ hwb hy))
    (cx2_noWrite wa h wb t₃ hwb)) (chainErase_noWrite h r wa t₃ hr hwa)

theorem same_rel3 (hy : y ≠ t₃) (e₁ : Bool) :
    ∀ h, h ≠ t₃ →
      EraseRel t₃ (affineClassSameTail y t₁ t₂ t₃ e₁ a₁ e₂ a₂ a₃ h) (Same3 y t₁ t₂ t₃ e₁ a₁ e₂ a₂ a₃ h) := by
  intro h hh
  exact rel_left _ (bitTest_rel h y t₃ a₃ hh hy)

theorem tl_rel1 (hy : y ≠ t₁) (h2 : t₂ ≠ t₁) (h3 : t₃ ≠ t₁) (hwb : wb ≠ t₁) :
    ∀ r wa h, r ≠ t₁ → wa ≠ t₁ →
      EraseRel t₁ (Tl3 y t₁ t₂ t₃ wb true a₁ e₂ a₂ a₃ r wa h) (Tl13 y t₁ t₂ t₃ wb true a₁ e₂ a₂ a₃ r wa h) := by
  intro r wa h hr hwa
  unfold Tl3 Tl13
  exact rel_right _ (rel_right _ (rel_right _ (rel_left _ (pairTail_rel1 y t₁ t₂ a₁ e₂ a₂ wa hwa hy h2))
    (bitTestE_noWrite wb y t₃ a₃ t₁ hy h3)) (cx2_noWrite wa h wb t₁ hwb))
    (chainErase_noWrite h r wa t₁ hr hwa)

theorem same_rel1 (hy : y ≠ t₁) (h2 : t₂ ≠ t₁) (h3 : t₃ ≠ t₁) :
    ∀ h, h ≠ t₁ →
      EraseRel t₁ (Same3 y t₁ t₂ t₃ true a₁ e₂ a₂ a₃ h) (Same13 y t₁ t₂ t₃ true a₁ e₂ a₂ a₃ h) := by
  intro h hh
  exact rel_right _ (pairTail_rel1 y t₁ t₂ a₁ e₂ a₂ h hh hy h2) (bitTestE_noWrite h y t₃ a₃ t₁ hy h3)

end

/-! ## The closing classifier -/

def shared3 (L : ControlledPointLayout) (C : Point) : Program :=
  inputG (Tl3 (yLow L) L.core.generic L.core.equalNegY L.doubleSelect (L.core.poolWire 513)
      true (yBit C) (exceptionBit C) (yBit (-C)) (yBit (C+C)))
    (Same3 (yLow L) L.core.generic L.core.equalNegY L.doubleSelect
      true (yBit C) (exceptionBit C) (yBit (-C)) (yBit (C+C)))
    L.control (pairPorts L) (pairCode C) (pairCode (C+C))

def shared13 (L : ControlledPointLayout) (C : Point) : Program :=
  inputG (Tl13 (yLow L) L.core.generic L.core.equalNegY L.doubleSelect (L.core.poolWire 513)
      true (yBit C) (exceptionBit C) (yBit (-C)) (yBit (C+C)))
    (Same13 (yLow L) L.core.generic L.core.equalNegY L.doubleSelect
      true (yBit C) (exceptionBit C) (yBit (-C)) (yBit (C+C)))
    L.control (pairPorts L) (pairCode C) (pairCode (C+C))

section
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hw hn

theorem shared_distinct :
    let y := yLow L; let g := L.core.generic; let e := L.core.equalNegY
    let d := L.doubleSelect; let wb := L.core.poolWire 513
    (L.control ≠ g ∧ y ≠ g ∧ e ≠ g ∧ d ≠ g ∧ wb ≠ g ∧
      (∀ q ∈ pairPorts L, q.input ≠ g ∧ q.work ≠ g)) ∧
    (L.control ≠ d ∧ y ≠ d ∧ wb ≠ d ∧ (∀ q ∈ pairPorts L, q.input ≠ d ∧ q.work ≠ d)) := by
  have nd := Edges.shared_nodup L hw hn
  simp only [List.nodup_cons, List.mem_cons, not_or] at nd
  obtain ⟨⟨c1,c2,c3,c4,c5,_⟩, ⟨y1,y2,y3,y4,_⟩, ⟨g1,g2,g3,g4⟩, ⟨e1,e2,e3⟩, ⟨d1,d4⟩, _⟩ := nd
  have port (w : Wire) (hw : w ∉ (pairPorts L).flatMap ZeroBit.wires) :
      ∀ q ∈ pairPorts L, q.input ≠ w ∧ q.work ≠ w := by
    intro q hq
    constructor <;> intro e <;> apply hw <;>
      exact List.mem_flatMap.mpr ⟨q, hq, by simp [ZeroBit.wires, e]⟩
  exact ⟨⟨c2, y1, Ne.symm g1, Ne.symm g2, Ne.symm g3, port _ g4⟩,
    ⟨c4, y3, Ne.symm d1, port _ d4⟩⟩

theorem shared_rel3 (C : Point) :
    EraseRel L.doubleSelect (Edges.shared L C) (shared3 L C) := by
  obtain ⟨-, hc, hy, hwb, hq⟩ := shared_distinct L hw hn
  rw [Edges.shared, inputG_orig]
  exact inputG_rel _ _ _ _ _ (tl_rel3 _ _ _ _ _ _ _ _ _ hy hwb true) (same_rel3 _ _ _ _ _ _ _ _ hy true)
    _ _ _ _ hc hq

theorem shared_rel1 (C : Point) :
    EraseRel L.core.generic (shared3 L C) (shared13 L C) := by
  obtain ⟨⟨hc, hy, h2, h3, hwb, hq⟩, -⟩ := shared_distinct L hw hn
  exact inputG_rel _ _ _ _ _ (tl_rel1 _ _ _ _ _ _ _ _ _ hy h2 h3 hwb)
    (same_rel1 _ _ _ _ _ _ _ _ hy h2 h3) _ _ _ _ hc hq

end

/-! ## Lifting to the full program -/

def finiteS (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen S : Program) : Program :=
  inputClass L C cy ++ FusedFlags.prefixProgram L C ++
  renameProgram (swapD L) (renameProgram (swapE L) (renameProgram (tauM L) Gen)) ++
  FusedFlags.suffixProgram L C ++
  renameProgram (sigP L) (corners2 L C ++ S) ++
  chainErase L.control L.point.finite L.genericSelect

def wrapperS (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen S : Program) : Program :=
  renameProgram (Wrapper5.U L) (finiteS L C cy (renameProgram (Wrapper5.U L) Gen) S)

theorem wrapper_eq (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) :
    FusedFlags.wrapper L C cy Gen = wrapperS L C cy Gen (Edges.shared L C) := rfl

theorem sigP_injective (L : ControlledPointLayout) : Function.Injective (sigP L) := by
  have : sigP L = Equiv.swap L.core.generic (parkWire L) := by
    funext q; simp [sigP, Equiv.swap_apply_def]
  rw [this]; exact Equiv.injective _

theorem wrapperS_rel (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen S S' : Program)
    (t : Wire) (h : EraseRel t S S') (h1 : L.point.finite ≠ sigP L t)
    (h2 : L.genericSelect ≠ sigP L t) :
    EraseRel (Wrapper5.U L (sigP L t)) (wrapperS L C cy Gen S) (wrapperS L C cy Gen S') := by
  unfold wrapperS finiteS
  exact rel_rename _ (Wrapper5.U L).injective (rel_right _ (rel_left _
    (rel_rename _ (sigP_injective L) (rel_left _ h))) (chainErase_noWrite _ _ _ _ h1 h2))

/-! ## Final entrant -/

open FiniteFlagInterval in
def program1 (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      wrapperS layout C cy (FiniteFlagInterval.gen layout cx cy) (shared3 layout C)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      wrapperS layout C cy (FiniteFlagInterval.gen layout cx cy) (shared13 layout C)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2151795,1499140,1588,50167451⟩

def tD : Wire := Wrapper5.U layout (sigP layout layout.doubleSelect)
def tG : Wire := Wrapper5.U layout (sigP layout layout.core.generic)

theorem tD_val : tD = 9815 := by decide
theorem tG_val : tG = 4629 := by decide

theorem layout_facts :
    layout.point.finite ≠ sigP layout layout.doubleSelect ∧
    layout.genericSelect ≠ sigP layout layout.doubleSelect ∧
    layout.point.finite ≠ sigP layout layout.core.generic ∧
    layout.genericSelect ≠ sigP layout layout.core.generic := by
  decide

theorem rel_a {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    EraseRel tD (FusedBoundaryFinal.program (.some hc)) (program1 (.some hc)) := by
  have f := layout_facts
  exact wrapperS_rel layout _ cy _ _ _ _ (shared_rel3 layout layout_widths layout_nodup _) f.1 f.2.1

theorem rel_b {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    EraseRel tG (program1 (.some hc)) (program (.some hc)) := by
  have f := layout_facts
  exact wrapperS_rel layout _ cy _ _ _ _ (shared_rel1 layout layout_widths layout_nodup _)
    f.2.2.1 f.2.2.2

theorem clean_of_encodes (b : Bool) (R : Point) (w : Wire) (hw : 514 ≤ w) :
    ∀ st, encodes b R st → st w = false := fun _ h => h.2.2 w hw

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    have h := FusedBoundaryFinal.program_correct .zero b R
    exact h
  | @some cx cy hc =>
    have h0 := FusedBoundaryFinal.program_correct (.some hc) b R
    have hD : 514 ≤ tD := by rw [tD_val]; decide
    have hG : 514 ≤ tG := by rw [tG_val]; decide
    have h1 := rel_triple (rel_a hc) h0 (clean_of_encodes _ _ tD hD)
    exact rel_triple (rel_b hc) h1 (clean_of_encodes _ _ tG hG)

theorem program_metrics (C : Point) :
    toffoliCount (program C) ≤ 2151795 ∧ measurementCount (program C) ≤ 1499140 ∧
    gateSlots (program C) ≤ 50167451 ∧ qubits (program C) ≤ 1588 ∧ GatePhysical (program C) := by
  have t0 := FusedBoundaryFinal.program_toffoli C
  have m0 := FusedBoundaryFinal.program_measurements C
  have s0 := FusedBoundaryFinal.program_gateSlots C
  have q0 := FusedBoundaryFinal.program_qubits C
  have p0 := FusedBoundaryFinal.program_physical C
  cases C with
  | zero =>
    change toffoliCount [] ≤ 2151795 ∧ measurementCount [] ≤ 1499140 ∧ gateSlots [] ≤ 50167451 ∧
      qubits [] ≤ 1588 ∧ GatePhysical []
    refine ⟨by simp [toffoliCount], by simp [measurementCount], by simp [gateSlots], ?_,
      by simp [GatePhysical]⟩
    rw [qubits_empty]; decide
  | @some cx cy hc =>
    have a := rel_counts (rel_a hc)
    have b := rel_counts (rel_b hc)
    refine ⟨by omega, by omega, by omega, ?_, rel_physical (rel_b hc) (rel_physical (rel_a hc) p0)⟩
    unfold qubits at q0 ⊢
    rw [b.2.2.2, a.2.2.2]; exact q0

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_metrics C).2.2.2.2
  toffoli_le C := (normalize_toffoli _).trans (program_metrics C).1
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499140
    rw [normalize_measurements]; exact (program_metrics C).2.1
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits]; exact (program_metrics C).2.2.2.1
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50167451
    rw [normalize_slots]; exact (program_metrics C).2.2.1

end ECDSAAdd.Entrant.SharedErase
