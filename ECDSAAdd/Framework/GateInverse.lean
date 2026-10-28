import ECDSAAdd.Framework.Cost

namespace ECDSAAdd

/-- The instruction is a basis-state permutation whose target is distinct
from every control.  Measurement instructions are deliberately excluded. -/
def ProperGate : Instr → Prop
  | .X _ => True
  | .CX c t => c ≠ t
  | .CCX a b t => a ≠ t ∧ b ≠ t
  | .measureX _ _ _ => False

def ProperProgram (p : Program) : Prop := ∀i∈p,ProperGate i

theorem properProgram_append (p q : Program) :
    ProperProgram (p++q) ↔ ProperProgram p ∧ ProperProgram q := by
  constructor
  · intro h
    constructor
    · intro i hi; exact h i (List.mem_append_left q hi)
    · intro i hi; exact h i (List.mem_append_right p hi)
  · rintro ⟨hp,hq⟩ i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact hp i hi
    · exact hq i hi

theorem properProgram_reverse (p : Program) :
    ProperProgram p → ProperProgram p.reverse := by
  intro h i hi
  exact h i (List.mem_reverse.mp hi)

theorem properGate_measurementCount (i : Instr) (h : ProperGate i) :
    measurementCount [i]=0 := by
  cases i <;> simp_all [ProperGate,measurementCount]

theorem properGate_involution (i : Instr) (h : ProperGate i)
    (s : State) (m₁ m₂ : List Bool) :
    run [i] m₂ (run [i] m₁ s)=s := by
  cases i with
  | X t =>
      cases s with
      | mk phase basis =>
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t <;> simp [run,writeBit,hq]
  | CX c t =>
      change c≠t at h
      cases s with
      | mk phase basis =>
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t
        · subst q
          cases hc : basis c <;> cases ht : basis t <;>
            simp [run,writeBit,h,hc,ht]
        · simp [run,writeBit,hq]
  | CCX a b t =>
      cases s with
      | mk phase basis =>
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t
        · subst q
          cases ha : basis a <;> cases hb : basis b <;> cases ht : basis t <;>
            simp [ProperGate] at h
          all_goals simp [run,writeBit,h.1,h.2,ha,hb,ht]
        · simp [run,writeBit,hq]
  | measureX t c₀ c₁ => contradiction

theorem properProgram_measurementCount (p : Program)
    (h : ∀i∈p,ProperGate i) : measurementCount p=0 := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      have hi := h i (by simp)
      have hp : ∀j∈p,ProperGate j := by intro j hj; exact h j (by simp [hj])
      cases i <;> simp_all [ProperGate,measurementCount]

theorem measurementCount_reverse (p : Program) :
    measurementCount p.reverse=measurementCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      cases i <;> simp [measurementCount,ih,Nat.add_comm]

theorem toffoliCount_reverse (p : Program) :
    toffoliCount p.reverse=toffoliCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      cases i <;> simp [toffoliCount,ih,Nat.add_comm]

theorem wires_reverse (p : Program) : wires p.reverse=wires p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
      simp [wires,ih,Finset.union_comm]

/-- Reversing a proper gate-only stream gives its exact inverse on the whole
state, including phase.  Since the stream has no measurements, the two record
lists are completely independent. -/
theorem run_reverse_proper (p : Program) (h : ∀i∈p,ProperGate i)
    (s : State) (m₁ m₂ : List Bool) :
    run p.reverse m₂ (run p m₁ s)=s := by
  induction p generalizing s m₁ m₂ with
  | nil => rfl
  | cons i p ih =>
      have hi : ProperGate i := h i (by simp)
      have hp : ∀j∈p,ProperGate j := by intro j hj; exact h j (by simp [hj])
      have pm : measurementCount p=0 := properProgram_measurementCount p hp
      have prm : measurementCount p.reverse=0 := by
        rw [measurementCount_reverse]
        exact pm
      have runCons : run (i::p) m₁ s=run p m₁ (run [i] [] s) := by
        cases i <;> simp_all [ProperGate,run]
      simp only [List.reverse_cons,run_append,prm,List.take_zero,List.drop_zero,runCons]
      rw [ih hp]
      exact properGate_involution i hi s [] m₂

/-- A proper gate-only program depends only on its declared wire support.
States agreeing there and in phase still agree there after execution. -/
theorem run_proper_congr (p : Program) (hp : ProperProgram p)
    (s t : State) (m₁ m₂ : List Bool) (hphase : s.phase=t.phase)
    (hbasis : ∀q∈wires p,s.basis q=t.basis q) :
    (run p m₁ s).phase=(run p m₂ t).phase ∧
      ∀q∈wires p,(run p m₁ s).basis q=(run p m₂ t).basis q := by
  induction p generalizing s t m₁ m₂ with
  | nil => exact ⟨hphase,by simp [wires]⟩
  | cons i p ih =>
    have hi := hp i (by simp)
    have hpt : ProperProgram p := by intro j hj; exact hp j (by simp [hj])
    have tailMem (q : Wire) (hq : q∈wires p) : s.basis q=t.basis q :=
      hbasis q (Finset.mem_union_right _ hq)
    cases i with
    | X x =>
      let s' : State := ⟨s.phase,writeBit s.basis x (!s.basis x)⟩
      let t' : State := ⟨t.phase,writeBit t.basis x (!t.basis x)⟩
      have hx : s.basis x=t.basis x := hbasis x (by simp [wires,Instr.wires])
      have htail (q : Wire) (hq : q∈wires p) : s'.basis q=t'.basis q := by
        by_cases e : q=x
        · subst q; simp [s',t',writeBit,hx]
        · simp [s',t',writeBit,e,tailMem q hq]
      have hrec := ih hpt s' t' m₁ m₂ hphase htail
      refine ⟨hrec.1,?_⟩
      intro q hq
      simp only [wires,Finset.mem_union] at hq
      rcases hq with hq|hq
      · by_cases hqp : q∈wires p
        · exact hrec.2 q hqp
        · have hqeq : s'.basis q=t'.basis q := by
            simp only [Instr.wires,Finset.mem_singleton] at hq
            subst q
            simp [s',t',writeBit,hx]
          exact (run_preserves_outside p m₁ s' q hqp).trans
            (hqeq.trans (run_preserves_outside p m₂ t' q hqp).symm)
      · exact hrec.2 q hq
    | CX c x =>
      have hcx : c≠x := hi
      let s' : State := ⟨s.phase,writeBit s.basis x (s.basis x^^s.basis c)⟩
      let t' : State := ⟨t.phase,writeBit t.basis x (t.basis x^^t.basis c)⟩
      have hc : s.basis c=t.basis c := hbasis c (by simp [wires,Instr.wires])
      have hx : s.basis x=t.basis x := hbasis x (by simp [wires,Instr.wires])
      have htail (q : Wire) (hq : q∈wires p) : s'.basis q=t'.basis q := by
        by_cases e : q=x
        · subst q; simp [s',t',writeBit,hx,hc]
        · simp [s',t',writeBit,e,tailMem q hq]
      have hrec := ih hpt s' t' m₁ m₂ hphase htail
      refine ⟨hrec.1,?_⟩
      intro q hq
      simp only [wires,Finset.mem_union] at hq
      rcases hq with hq|hq
      · by_cases hqp : q∈wires p
        · exact hrec.2 q hqp
        · have hqeq : s'.basis q=t'.basis q := by
            simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl|rfl
            · simp [s',t',writeBit,hcx,hc]
            · simp [s',t',writeBit,hx,hc]
          exact (run_preserves_outside p m₁ s' q hqp).trans
            (hqeq.trans (run_preserves_outside p m₂ t' q hqp).symm)
      · exact hrec.2 q hq
    | CCX a b x =>
      have hax : a≠x := hi.1
      have hbx : b≠x := hi.2
      let s' : State := ⟨s.phase,writeBit s.basis x (s.basis x^^(s.basis a&&s.basis b))⟩
      let t' : State := ⟨t.phase,writeBit t.basis x (t.basis x^^(t.basis a&&t.basis b))⟩
      have ha : s.basis a=t.basis a := hbasis a (by simp [wires,Instr.wires])
      have hb : s.basis b=t.basis b := hbasis b (by simp [wires,Instr.wires])
      have hx : s.basis x=t.basis x := hbasis x (by simp [wires,Instr.wires])
      have htail (q : Wire) (hq : q∈wires p) : s'.basis q=t'.basis q := by
        by_cases e : q=x
        · subst q; simp [s',t',writeBit,hx,ha,hb]
        · simp [s',t',writeBit,e,tailMem q hq]
      have hrec := ih hpt s' t' m₁ m₂ hphase htail
      refine ⟨hrec.1,?_⟩
      intro q hq
      simp only [wires,Finset.mem_union] at hq
      rcases hq with hq|hq
      · by_cases hqp : q∈wires p
        · exact hrec.2 q hqp
        · have hqeq : s'.basis q=t'.basis q := by
            simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
            rcases hq with rfl|rfl|rfl
            · simp [s',t',writeBit,hax,ha,hb]
            · simp [s',t',writeBit,hbx,ha,hb]
            · simp [s',t',writeBit,hx,ha,hb]
          exact (run_preserves_outside p m₁ s' q hqp).trans
            (hqeq.trans (run_preserves_outside p m₂ t' q hqp).symm)
      · exact hrec.2 q hq
    | measureX x c₀ c₁ => contradiction

end ECDSAAdd
