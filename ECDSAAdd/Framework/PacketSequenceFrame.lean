import ECDSAAdd.Framework.WireRename
import Mathlib.Tactic
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.PacketSequence
attribute [local irreducible] run measurementCount

def program (forward : Bool) (p : Nat → Program) : Nat → Nat → Program
  | _,0 => []
  | j,n+1 => if forward then p j++program forward p (j+1) n
      else program forward p (j+1) n++p j

def payload {α : Type} (forward : Bool) (step : Nat → α → α) : Nat → Nat → α → α
  | _,0,Q => Q
  | j,n+1,Q => if forward then payload forward step (j+1) n (step j Q)
      else step j (payload forward step (j+1) n Q)

theorem counts_equal (forward : Bool) (p r : Nat → Program)
    (same : ∀j,measurementCount (p j)=measurementCount (r j)) (j n : Nat) :
    measurementCount (program forward p j n)=measurementCount (program forward r j n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases forward <;> simp only [program,Bool.false_eq_true,if_false,if_true,
      measurementCount_append,same,ih]

/-- Generic composition is instantiated only with proved actual packet
contracts. Every record is partitioned by the emitted measurement count. -/
theorem frame {α : Type} (forward : Bool) (p r : Nat → Program)
    (step : Nat → α → α) (F : α → State → Prop) (N : Nat)
    (counts : ∀j,measurementCount (p j)=measurementCount (r j))
    (packet : ∀j,j < N → ∀Q s m,F Q s →
      run (p j) m s=run (r j) m s ∧ (run (p j) m s).phase=s.phase ∧
      F (step j Q) (run (p j) m s)) (j n : Nat) (bound : j+n ≤ N)
    (Q : α) (s : State) (m : List Bool) (input : F Q s) :
    let out := run (program forward p j n) m s
    out=run (program forward r j n) m s ∧ out.phase=s.phase ∧
      F (payload forward step j n Q) out := by
  induction n generalizing j Q s m with
  | zero => simpa only [program,run,payload] using
      (show s=s ∧ s.phase=s.phase ∧ F Q s from ⟨rfl,rfl,input⟩)
  | succ n ih =>
    have hj : j < N := by omega
    cases forward
    · let later := program false p (j+1) n
      let t := run later (m.take (measurementCount later)) s
      let V := payload false step (j+1) n Q
      have rest := ih (j+1) (by omega) Q s (m.take (measurementCount later)) input
      have first := packet j hj V t (m.drop (measurementCount later)) rest.2.2
      have mc : measurementCount (program false r (j+1) n)=measurementCount later :=
        (counts_equal false p r counts (j+1) n).symm
      have eq : run (program false p j (n+1)) m s=run (program false r j (n+1)) m s := by
        simp only [program,Bool.false_eq_true,if_false,run_append]
        rw [mc,←rest.1]
        exact first.1
      refine ⟨eq,?_,?_⟩
      · simpa only [program,Bool.false_eq_true,if_false,run_append,later,t] using first.2.1.trans rest.2.1
      · simpa only [program,Bool.false_eq_true,if_false,run_append,payload,V,later,t] using first.2.2
    · let head := p j
      let t := run head (m.take (measurementCount head)) s
      have first := packet j hj Q s (m.take (measurementCount head)) input
      have rest := ih (j+1) (by omega) (step j Q) t (m.drop (measurementCount head)) first.2.2
      have eq : run (program true p j (n+1)) m s=run (program true r j (n+1)) m s := by
        simp only [program,if_true,run_append]
        rw [←counts j,←first.1]
        exact rest.1
      refine ⟨eq,?_,?_⟩
      · simpa only [program,if_true,run_append,head,t] using rest.2.1.trans first.2.1
      · simpa only [program,if_true,run_append,payload,head,t] using rest.2.2

end ECDSAAdd.PacketSequence
#print axioms ECDSAAdd.PacketSequence.frame
