import ECDSAAdd.Arithmetic.RecordedRailVentedProgram
import ECDSAAdd.Arithmetic.Reduction

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailVented
open RecordedRailCarry RecordedRailRipple

/-- Register decomposition uses Bool.toNat explicitly, avoiding any dependence
on the reducibility of the register fold's conditional. -/
theorem reg_cons (q : Wire) (r : List Wire) (st : BasisState) :
    regValue (q::r) st=(st q).toNat+2*regValue r st := by
  cases hq : st q <;> simp [regValue,hq]

theorem bit_sum (a b incoming : Bool) :
    ((b ^^ a) ^^ incoming).toNat+2*(carryFn a b incoming).toNat=
      a.toNat+b.toNat+incoming.toNat := by
  cases a <;> cases b <;> cases incoming <;> decide

theorem wide_step (a b incoming : Bool) (X Y : Nat) :
    ((b ^^ a) ^^ incoming).toNat+2*(X+Y+(carryFn a b incoming).toNat)=
      (a.toNat+2*X)+(b.toNat+2*Y)+incoming.toNat := by
  have h := bit_sum a b incoming
  omega

/-- Literal one-bit vented base retains the arithmetic carry in cout, restores
the source and carry-in, and preserves every other basis bit and input phase. -/
theorem top_state (a b cout : Wire) (prev : Option Wire)
    (nd : (prev.toList++[a,b,cout]).Nodup) (bits : BasisState) (phase : Bool)
    (m : List Bool) (cursor : Nat) (hc : bits cout=false) :
    runWithTape (top a b cout prev) m cursor ⟨phase,bits⟩=
      ⟨phase,writeBit (writeBit bits b ((bits b ^^ bits a) ^^ incomingValue prev bits))
        cout (carryFn (bits a) (bits b) (incomingValue prev bits))⟩ := by
  rw [top,runWithTape_embedRecorded]
  cases prev with
  | none =>
    simp only [Option.toList_none,List.nil_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
    obtain ⟨⟨hab,hac⟩,hbc⟩ := nd
    have hba := Ne.symm hab
    have hca := Ne.symm hac
    have hcb := Ne.symm hbc
    apply State.extensionality
    · rfl
    · funext q
      by_cases hqa : q=a <;> by_cases hqb : q=b <;> by_cases hqc : q=cout <;>
        cases hA : bits a <;> cases hB : bits b <;>
        simp_all [carryStep,topFinish,run,carryFn,incomingValue,writeBit,Function.update]
  | some p =>
    simp only [Option.toList_some,List.singleton_append,List.nodup_cons,List.mem_cons,
      List.not_mem_nil,List.nodup_nil,not_or,not_false_eq_true,and_true] at nd
    obtain ⟨⟨hpa,hpb,hpc⟩,⟨hab,hac⟩,hbc⟩ := nd
    have hap := Ne.symm hpa
    have hbp := Ne.symm hpb
    have hcp := Ne.symm hpc
    have hba := Ne.symm hab
    have hca := Ne.symm hac
    have hcb := Ne.symm hbc
    apply State.extensionality
    · rfl
    · funext q
      by_cases hqa : q=a <;> by_cases hqb : q=b <;> by_cases hqc : q=cout <;>
        cases hA : bits a <;> cases hB : bits b <;> cases hP : bits p <;>
        simp_all [carryStep,topFinish,run,carryFn,incomingValue,writeBit,Function.update]

theorem top_frame (a b cout : Wire) (prev : Option Wire)
    (nd : (prev.toList++[a,b,cout]).Nodup) (bits : BasisState) (phase : Bool)
    (m : List Bool) (cursor : Nat) (hc : bits cout=false) :
    let out := runWithTape (top a b cout prev) m cursor ⟨phase,bits⟩
    out.phase=phase ∧ regValue [b,cout] out.basis=
      regValue [a] bits+regValue [b] bits+(incomingValue prev bits).toNat ∧
    (∀q,q∉([b,cout] : List Wire) → out.basis q=bits q) := by
  dsimp only
  rw [top_state a b cout prev nd bits phase m cursor hc]
  have hn := suffix_nodup prev.toList [a,b,cout] nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  have hbc : b≠cout := hn.2
  have hcb := Ne.symm hbc
  refine ⟨rfl,?_,?_⟩
  · cases hA : bits a <;> cases hB : bits b <;>
      cases hI : incomingValue prev bits <;>
      simp [regValue,writeBit,Function.update,carryFn,hbc,hcb,hA,hB,hI]
  · intro q hq
    have hqb : q≠b := by intro h; exact hq (by simp [h])
    have hqc : q≠cout := by intro h; exact hq (by simp [h])
    simp [writeBit,Function.update,hqb,hqc]

/-- Structural head/tail extraction includes cout among real tail sites. -/
theorem step_layout (a b c cout : Wire) (A B work : List Wire) (prev : Option Wire)
    (nd : (prev.toList++(a::A)++(b::B)++(c::work)++[cout]).Nodup) :
    (prev.toList++[a,b,c]).Nodup ∧
    ([c]++A++B++work++[cout]).Nodup ∧
    a∉B++[cout] ∧ b∉B++[cout] ∧ c∉B++[cout] ∧
    (∀q∈A++B++work++[cout],q≠a ∧ q≠b ∧ q≠c) ∧
    (∀p∈prev.toList,p∉B++[cout]) := by
  have rearranged : ((prev.toList++[a,b,c])++(A++B++work++[cout])).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have split := List.nodup_append'.mp rearranged
  have away : ∀q∈A++B++work++[cout],∀r∈prev.toList++[a,b,c],q≠r := by
    intro q hq r hr e
    exact List.disjoint_left.mp split.2.2 hr (e ▸ hq)
  have target_mem : ∀q∈B++[cout],q∈A++B++work++[cout] := by
    intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  refine ⟨split.1,?_,?_,?_,?_,?_,?_⟩
  · apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  · intro h; exact away a (target_mem a h) a (by simp) rfl
  · intro h; exact away b (target_mem b h) b (by simp) rfl
  · intro h; exact away c (target_mem c h) c (by simp) rfl
  · intro q hq
    exact ⟨away q hq a (by simp),away q hq b (by simp),away q hq c (by simp)⟩
  · intro p hp h
    exact away p (target_mem p h) p (by simp [hp]) rfl

end ECDSAAdd.Arithmetic.RecordedRailVented
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.top_state
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.top_frame
#print axioms ECDSAAdd.Arithmetic.RecordedRailVented.step_layout
