import ECDSAAdd.Arithmetic.RecordedRailApply258Step

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailDefer ECDSAAdd.Math.RecordedCarryWordMirror

private theorem none_debt (n : Nat) (m cs : List Bool) :
    ECDSAAdd.Math.RecordedCarryWordMirror.debt (List.replicate n none) m cs=false := by
  induction n generalizing cs with
  | zero => rfl
  | succ n ih => cases cs <;> simp [List.replicate_succ,ECDSAAdd.Math.RecordedCarryWordMirror.debt,ih]
private theorem none_filter (n : Nat) : (List.replicate n (none : Option Nat)).filterMap id=[] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]

def WrappedReady (a b bank : List Wire) (incoming : Wire) (bits : BasisState) : Prop :=
  0<a.length ∧ b.length=a.length ∧ bank.length=a.length-2 ∧
    ([incoming]++a++b++bank).Nodup ∧ (∀q∈bank,bits q=false)

theorem wrapped_result (a b bank : List Wire) (incoming : Wire) (bits : BasisState)
    (phase : Bool) (m : List Bool) (cursor : Nat) (ready : WrappedReady a b bank incoming bits) :
    RecordedRailRipple.UnsignedResult a b bank (some incoming) bits phase
      (runWithTape (RecordedRailRipple.ripple a b (some incoming) bank
        (List.replicate (a.length-2) none)) m cursor ⟨phase,bits⟩) := by
  obtain ⟨positive,width,bankWidth,nd,clean⟩ := ready
  have aligned : RecordedRailRipple.Aligned a b bank (List.replicate (a.length-2) none) :=
    ⟨positive,width,bankWidth,by simp [bankWidth]⟩
  have shape := RecordedRailRipple.aligned_shape _ _ _ _ aligned
  have noPhase : RecordedRailRipple.phaseDebt a b (bits incoming)
      (List.replicate (a.length-2) none) bits m=false := by
    rw [RecordedRailRipple.phaseDebt_word a b bank _ shape]
    exact none_debt _ m _
  have result := RecordedRailRipple.unsignedContract_of_aligned _ _ _ _ aligned (some incoming)
    bits phase m cursor ⟨aligned,nd,clean,by simp [none_filter]⟩
  simpa only [RecordedRailRipple.incomingValue,noPhase,Bool.xor_false] using result

theorem finish_state (a b bank : List Wire) (incoming : Wire) (bits : BasisState)
    (phase : Bool) (m : List Bool) (cursor : Nat) (ready : WrappedReady a b bank incoming bits) :
    let r := runWithTape (RecordedRailRipple.ripple a b (some incoming) bank
      (List.replicate (a.length-2) none)) m cursor ⟨phase,bits⟩
    runWithTape (finish a b bank incoming) m cursor ⟨phase,bits⟩=
      ⟨phase ^^ (m.getD (cursor+(a.length-2)) false && bits incoming),writeBit r.basis incoming false⟩ := by
  obtain ⟨positive,width,bankWidth,nd,clean⟩ := ready
  have takeAll : bank.take (a.length-2)=bank := by rw [←bankWidth,List.take_length]
  have result := wrapped_result a b bank incoming bits phase m cursor ⟨positive,width,bankWidth,nd,clean⟩
  obtain ⟨hp,ha,hvalue,houtside,hwork⟩ := result
  have hni : incoming∉b := by
    have first := List.nodup_cons.mp (by simpa only [List.singleton_append,List.append_assoc] using nd)
    intro h
    exact first.1 (by simp [h])
  have aligned : RecordedRailRipple.Aligned a b bank (List.replicate (a.length-2) none) :=
    ⟨positive,width,bankWidth,by simp [bankWidth]⟩
  have counts := RecordedRailRipple.aligned_counts _ _ _ _ aligned (some incoming)
  dsimp only
  rw [finish,takeAll,runWithTape_append,counts.2,bare_state,hp,houtside incoming hni]

def PrefixWrappedReady (a0 b0 a1 b1 bank : List Wire) (cin q0 q1 : Wire)
    (original : BasisState) (s : State) : Prop :=
  a0.length=b0.length ∧ 0<a1.length ∧ b1.length=a1.length ∧ bank.length=a1.length-2 ∧
    ([cin,q0,q1]++a0++b0++a1++b1++bank).Nodup ∧
    (∀q∈bank,s.basis q=false) ∧ original q0=false ∧
    regValue (b0++[q0]) s.basis=regValue a0 original+regValue b0 original+(original cin).toNat ∧
    (∀q,q∉b0++[q0] → s.basis q=original q)

end ECDSAAdd.Arithmetic.RecordedRailApply258
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.finish_state
