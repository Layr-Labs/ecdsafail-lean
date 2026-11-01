import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Framework.Hoare
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical

/-! Last-writer measured erasure.

If the last instruction that writes wire `t` is `CCX a b t`, and the postcondition
forces `t = 0`, then the Toffoli is a pure uncompute: just before it, `t = a ∧ b`.
Replacing it by `measureX t [] [CZ a b]` gives the same state and phase for every
measurement record.  The record used by the new measurement is spliced out of the
record list when the original triple is invoked. -/

set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EraseLast
open Arithmetic RecordedQuantum Challenge

def tgt : Instr → Wire
  | .X t => t
  | .CX _ t => t
  | .CCX _ _ t => t
  | .measureX t _ _ => t

/-- No instruction of `B` writes `t` (controls and corrections may read it). -/
def NoWrite (t : Wire) (B : Program) : Prop := ∀ i ∈ B, tgt i ≠ t

theorem noWrite_nil (t : Wire) : NoWrite t [] := by intro i hi; simp at hi

theorem noWrite_append {t : Wire} {P Q : Program} :
    NoWrite t (P ++ Q) ↔ NoWrite t P ∧ NoWrite t Q := by
  constructor
  · intro h; exact ⟨fun i hi => h i (List.mem_append_left _ hi),
      fun i hi => h i (List.mem_append_right _ hi)⟩
  · rintro ⟨h1,h2⟩ i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact h1 i hi
    · exact h2 i hi

theorem noWrite_cons {t : Wire} {i : Instr} {P : Program} :
    NoWrite t (i :: P) ↔ tgt i ≠ t ∧ NoWrite t P := by
  constructor
  · intro h; exact ⟨h i (by simp), fun j hj => h j (by simp [hj])⟩
  · rintro ⟨h1,h2⟩ j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact h1
    · exact h2 j hj

theorem tgt_mem_wires (i : Instr) : tgt i ∈ i.wires := by
  cases i <;> simp [tgt, Instr.wires]

theorem mem_wires_of_mem {i : Instr} {P : Program} (h : i ∈ P) : i.wires ⊆ wires P := by
  induction P with
  | nil => simp at h
  | cons j P ih =>
    rcases List.mem_cons.mp h with rfl | h
    · intro q hq; simp [wires, hq]
    · intro q hq; simp only [wires, Finset.mem_union]; exact Or.inr (ih h hq)

theorem noWrite_of_not_mem {t : Wire} {P : Program} (h : t ∉ wires P) : NoWrite t P := by
  intro i hi e
  exact h (mem_wires_of_mem hi (e ▸ tgt_mem_wires i))

theorem run_noWrite (t : Wire) (B : Program) (hB : NoWrite t B) (m : List Bool) (s : State) :
    (run B m s).basis t = s.basis t := by
  induction B generalizing m s with
  | nil => rfl
  | cons i B ih =>
    have h := noWrite_cons.mp hB
    cases i with
    | X q =>
      simp only [run]; rw [ih h.2]
      have : q ≠ t := h.1
      simp [writeBit, Function.update_apply, Ne.symm this]
    | CX c q =>
      simp only [run]; rw [ih h.2]
      have : q ≠ t := h.1
      simp [writeBit, Function.update_apply, Ne.symm this]
    | CCX a b q =>
      simp only [run]; rw [ih h.2]
      have : q ≠ t := h.1
      simp [writeBit, Function.update_apply, Ne.symm this]
    | measureX q c0 c1 =>
      simp only [run]; rw [ih h.2]
      have : q ≠ t := h.1
      simp [measureAndCorrect, writeBit, Function.update_apply, Ne.symm this]

theorem noWrite_rename (f : Wire → Wire) (hf : Function.Injective f) {t : Wire} {P : Program}
    (h : NoWrite t P) : NoWrite (f t) (renameProgram f P) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  have := h j hj
  cases j <;> simpa [renameInstr, tgt, hf.ne_iff] using this

/-- `P'` is `P` with one last-writer Toffoli on `t` replaced by its measured erasure. -/
def EraseRel (t : Wire) (P P' : Program) : Prop :=
  ∃ (A B : Program) (a b : Wire), a ≠ t ∧ b ≠ t ∧ NoWrite t B ∧
    P = A ++ .CCX a b t :: B ∧ P' = A ++ .measureX t [] [.CZ a b] :: B

theorem rel_base (a b t : Wire) (ha : a ≠ t) (hb : b ≠ t) :
    EraseRel t [.CCX a b t] [.measureX t [] [.CZ a b]] :=
  ⟨[], [], a, b, ha, hb, noWrite_nil t, rfl, rfl⟩

theorem rel_left {t : Wire} {P P' : Program} (Q : Program) (h : EraseRel t P P') :
    EraseRel t (Q ++ P) (Q ++ P') := by
  obtain ⟨A,B,a,b,ha,hb,hB,rfl,rfl⟩ := h
  exact ⟨Q ++ A, B, a, b, ha, hb, hB, by simp, by simp⟩

theorem rel_right {t : Wire} {P P' : Program} (Q : Program) (h : EraseRel t P P')
    (hQ : NoWrite t Q) : EraseRel t (P ++ Q) (P' ++ Q) := by
  obtain ⟨A,B,a,b,ha,hb,hB,rfl,rfl⟩ := h
  exact ⟨A, B ++ Q, a, b, ha, hb, noWrite_append.mpr ⟨hB,hQ⟩, by simp, by simp⟩

theorem rel_rename (f : Wire → Wire) (hf : Function.Injective f) {t : Wire} {P P' : Program}
    (h : EraseRel t P P') : EraseRel (f t) (renameProgram f P) (renameProgram f P') := by
  obtain ⟨A,B,a,b,ha,hb,hB,rfl,rfl⟩ := h
  refine ⟨renameProgram f A, renameProgram f B, f a, f b, hf.ne ha, hf.ne hb,
    noWrite_rename f hf hB, ?_, ?_⟩ <;>
    simp [renameProgram, renameInstr, renameCorrection]

theorem rel_counts {t : Wire} {P P' : Program} (h : EraseRel t P P') :
    toffoliCount P = toffoliCount P' + 1 ∧
    measurementCount P' = measurementCount P + 1 ∧
    gateSlots P' = gateSlots P + 1 ∧ wires P' = wires P := by
  obtain ⟨A,B,a,b,ha,hb,hB,rfl,rfl⟩ := h
  refine ⟨?_,?_,?_,?_⟩
  · simp [toffoliCount_append, toffoliCount]; omega
  · simp [measurementCount_append, measurementCount]; omega
  · simp [gateSlots, instructionSlots]; omega
  · simp only [wires_append, wires, Instr.wires, correctionWires]
    congr 1
    ext q; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty]; tauto

theorem rel_physical {t : Wire} {P P' : Program} (h : EraseRel t P P')
    (hp : GatePhysical P) : GatePhysical P' := by
  obtain ⟨A,B,a,b,ha,hb,hB,rfl,rfl⟩ := h
  simp only [gatePhysical_append] at hp ⊢
  refine ⟨hp.1, ?_⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · simp [PhysicalInstr]
  · exact hp.2 i (List.mem_cons_of_mem _ hi)

theorem take_splice : ∀ (k : Nat) (m : List Bool),
    (m.take k ++ m.drop (k+1)).take k = m.take k
  | 0, m => by simp
  | k+1, [] => by simp
  | k+1, x :: m => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    rw [take_splice k m]

theorem drop_splice : ∀ (k : Nat) (m : List Bool),
    (m.take k ++ m.drop (k+1)).drop k = m.drop (k+1)
  | 0, m => by simp
  | k+1, [] => by simp
  | k+1, x :: m => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    exact drop_splice k m

theorem rel_triple {t : Wire} {P P' : Program} (h : EraseRel t P P')
    {Pre Post : BasisState → Prop} (hT : Triple Pre P Post)
    (hclean : ∀ st, Post st → st t = false) : Triple Pre P' Post := by
  obtain ⟨A,B,a,b,ha,hb,hB,rfl,rfl⟩ := h
  intro s m hs
  let k := measurementCount A
  let sA := run A (m.take k) s
  let sC : State := ⟨sA.phase, writeBit sA.basis t (sA.basis t ^^ (sA.basis a && sA.basis b))⟩
  have hO := hT s (m.take k ++ m.drop (k+1)) hs
  have eO : run (A ++ .CCX a b t :: B) (m.take k ++ m.drop (k+1)) s =
      run B (m.drop (k+1)) sC := by
    rw [run_append, take_splice, drop_splice]; rfl
  rw [eO] at hO
  have hz : sC.basis t = false := by
    have := hclean _ hO.2
    rwa [run_noWrite t B hB] at this
  have hv : sA.basis t = (sA.basis a && sA.basis b) := by
    have : (sA.basis t ^^ (sA.basis a && sA.basis b)) = false := by
      simpa [sC, writeBit] using hz
    revert this; cases sA.basis t <;> cases (sA.basis a && sA.basis b) <;> simp
  have eN : run (A ++ .measureX t [] [.CZ a b] :: B) m s = run B (m.drop (k+1)) sC := by
    rw [run_append]
    change run B (m.drop k).tail (measureAndCorrect t [] [.CZ a b] ((m.drop k).headD false) sA) = _
    rw [List.tail_drop]
    congr 1
    simp only [measureAndCorrect, sC]
    cases (m.drop k).headD false
    · simp [correct]
      funext q; by_cases hq : q = t
      · subst hq; simp [writeBit, hv]
      · simp [writeBit, Function.update_apply, hq]
    · simp only [if_true, correct, writeBit, Function.update_apply, if_neg ha, if_neg hb]
      rw [hv]
      congr 1
      · cases sA.phase <;> cases sA.basis a <;> cases sA.basis b <;> rfl
      · funext q; by_cases hq : q = t
        · subst hq; simp [hv]
        · simp [hq]
  rw [eN]
  exact hO

end ECDSAAdd.Entrant.EraseLast
