import ECDSAAdd.Framework.GateInverse

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd

/-- Exact gate control with one reusable clean conjunction bit. -/
def controlInstr (c scratch : Wire) : Instr → Program
  | .X t => [.CX c t]
  | .CX a t => [.CCX c a t]
  | .CCX a b t => [.CCX c a scratch,.CCX scratch b t,.CCX c a scratch]
  | .measureX _ _ _ => []

def controlUnitary (c scratch : Wire) (p : Program) : Program :=
  p.flatMap (controlInstr c scratch)

theorem controlInstr_measurementCount (c scratch : Wire) (i : Instr) :
    measurementCount (controlInstr c scratch i)=0 := by
  cases i <;> rfl

theorem controlInstr_run (c scratch : Wire) (i : Instr) (hi : ProperGate i)
    (hc : c∉i.wires) (ht : scratch∉i.wires) (hct : c≠scratch)
    (s : State) (m : List Bool) (hz : s.basis scratch=false) :
    run (controlInstr c scratch i) m s=
      if s.basis c then run [i] m s else s := by
  cases s with
  | mk phase bits =>
    change bits scratch=false at hz
    cases i with
    | X t =>
      cases sc : bits c <;> simp only [controlInstr,run,sc,if_false,if_true]
      all_goals
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t <;> simp [writeBit,hq]
    | CX a t =>
      cases sc : bits c <;>
        simp only [controlInstr,run,sc,if_false,if_true,Bool.false_and,Bool.true_and]
      all_goals
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t <;> simp [writeBit,hq]
    | CCX a b t =>
      simp only [ProperGate] at hi
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton,not_or] at hc ht
      cases sc : bits c <;> simp only [controlInstr,run,sc,if_false,if_true]
      all_goals
        apply congrArg (State.mk phase)
        funext q
        by_cases hq : q=t
        · subst q
          simp [writeBit,ht.1,ht.2.1,ht.2.2,Ne.symm ht.1,Ne.symm ht.2.1,
            Ne.symm ht.2.2,hct,hi.1,hi.2,hc.2.2,hz,sc]
        · by_cases hqs : q=scratch
          · subst q
            simp [writeBit,ht.1,ht.2.1,ht.2.2,Ne.symm ht.1,Ne.symm ht.2.1,
              hct,hi.1,hc.2.2,hz,sc]
          · simp [writeBit,hq,hqs,ht.1,ht.2.1,Ne.symm ht.1,Ne.symm ht.2.1,
              hct,hi.1,hc.2.2,hz,sc]
    | measureX t z o => contradiction

theorem controlUnitary_measurementCount (c scratch : Wire) (p : Program) :
    measurementCount (controlUnitary c scratch p)=0 := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [controlUnitary,List.flatMap_cons,measurementCount_append]
    rw [controlInstr_measurementCount]
    simpa only [controlUnitary,Nat.zero_add] using ih

theorem controlUnitary_run (c scratch : Wire) (p : Program)
    (hp : ProperProgram p) (hc : c∉wires p) (ht : scratch∉wires p)
    (hct : c≠scratch) (s : State) (m : List Bool) (hz : s.basis scratch=false) :
    run (controlUnitary c scratch p) m s=
      if s.basis c then run p m s else s := by
  induction p generalizing s m with
  | nil => cases s.basis c <;> rfl
  | cons i p ih =>
    have hi := hp i (by simp)
    have hpt : ProperProgram p := by intro j hj; exact hp j (by simp [hj])
    simp only [wires,Finset.mem_union,not_or] at hc ht
    have hci : c∉i.wires := hc.1
    have hcp : c∉wires p := hc.2
    have hti : scratch∉i.wires := ht.1
    have htp : scratch∉wires p := ht.2
    let u := if s.basis c then run [i] m s else s
    have uControl : u.basis c=s.basis c := by
      cases sc : s.basis c
      · simp [u,sc]
      · simp only [u,sc,if_true]
        exact (run_preserves_outside [i] m s c (by simpa [wires] using hci)).trans sc
    have uScratch : u.basis scratch=false := by
      cases sc : s.basis c
      · simpa [u,sc] using hz
      · simp only [u,sc,if_true]
        exact (run_preserves_outside [i] m s scratch
          (by simpa [wires] using hti)).trans hz
    have first := controlInstr_run c scratch i hi hci hti hct s m hz
    change run (controlInstr c scratch i++controlUnitary c scratch p) m s=_
    rw [run_append,run_take,controlInstr_measurementCount,List.drop_zero,first]
    change run (controlUnitary c scratch p) m u=_
    rw [ih hpt hcp htp u m uScratch,uControl]
    cases sc : s.basis c
    · simp [sc,u]
    · simp only [sc,if_true,u]
      have im := properGate_measurementCount i hi
      have exec : run (i::p) m s=run p m (run [i] m s) := by
        change run ([i]++p) m s=_
        rw [run_append,run_take,im,List.drop_zero]
      exact exec.symm

def cnotCount : Program → Nat
  | [] => 0
  | .CX _ _::p => 1+cnotCount p
  | _::p => cnotCount p

@[simp] theorem cnotCount_append (p q : Program) :
    cnotCount (p++q)=cnotCount p+cnotCount q := by
  induction p with
  | nil => simp [cnotCount]
  | cons i p ih => cases i <;> simp [cnotCount,ih,Nat.add_assoc]

theorem cnotCount_reverse (p : Program) : cnotCount p.reverse=cnotCount p := by
  induction p with
  | nil => rfl
  | cons i p ih => cases i <;> simp [cnotCount,ih,Nat.add_comm]

theorem controlUnitary_toffoliCount (c scratch : Wire) (p : Program) :
    toffoliCount (controlUnitary c scratch p)=3*toffoliCount p+cnotCount p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    simp only [controlUnitary] at ih
    cases i <;> simp [controlUnitary,controlInstr,toffoliCount_append,
      toffoliCount,cnotCount,ih] <;> omega

theorem controlInstr_wires_subset (c scratch : Wire) (i : Instr) :
    wires (controlInstr c scratch i)⊆{c,scratch}∪i.wires := by
  cases i <;> intro q hq <;>
    simp only [controlInstr,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] at hq ⊢ <;> tauto

theorem controlUnitary_wires_subset (c scratch : Wire) (p : Program) :
    wires (controlUnitary c scratch p)⊆{c,scratch}∪wires p := by
  induction p with
  | nil => simp [controlUnitary,wires]
  | cons i p ih =>
    intro q hq
    simp only [controlUnitary,List.flatMap_cons,wires_append,
      Finset.mem_union] at hq
    change q∈{c,scratch}∪(i.wires∪wires p)
    rcases hq with hq|hq
    · have h := controlInstr_wires_subset c scratch i hq
      simp only [Finset.mem_union] at h ⊢
      tauto
    · have h := ih hq
      simp only [Finset.mem_union] at h ⊢
      tauto

end ECDSAAdd
