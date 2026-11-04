import ECDSAAdd.Submission.Entrant.HighOutputTailStructuredDraft
import ECDSAAdd.Arithmetic.DisjointPrograms

/-! Private source-only extension of the actually checked zero-top leaf.
No caller range/placement theorem is assumed established, and no certificate exists here. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.HighOutputFlagResearch
open Arithmetic RecordedQuantum Challenge HighOutputTailStructuredResearch

/-- The existing zero-top leaf conjugated by a Clifford controlled by an
immutable outside flag. This is a fixed gate list, not a quantum branch. -/
def newFlagAt (flag a b c A B : Wire) : Program :=
  [.CX flag B] ++ newLeafAt false a b c A B ++ [.CX flag B]

private theorem cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

private theorem commute_cat (p q C : Program)
    (hp : ∀ (s : State) (m : List Bool),run p m (run C [] s)=run C [] (run p m s))
    (hq : ∀ (s : State) (m : List Bool),run q m (run C [] s)=run C [] (run q m s))
    (s : State) (m : List Bool) :
    run (p++q) m (run C [] s)=run C [] (run (p++q) m s) := by
  calc
    run (p++q) m (run C [] s)=
        run q (m.drop (measurementCount p)) (run p m (run C [] s)) := cat _ _ _ _
    _ = run q (m.drop (measurementCount p)) (run C [] (run p m s)) :=
      congrArg (run q (m.drop (measurementCount p))) (hp s m)
    _ = run C [] (run q (m.drop (measurementCount p)) (run p m s)) := hq _ _
    _ = run C [] (run (p++q) m s) := congrArg (run C []) (cat p q m s).symm

private theorem same_target (u v flag B : Wire) (hu : u≠B) (hv : v≠B) (hf : flag≠B)
    (s : State) (m : List Bool) :
    run [.CX u B,.CX v B] m (run [.CX flag B] [] s)=
      run [.CX flag B] [] (run [.CX u B,.CX v B] m s) := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=B <;>
    simp_all [writeBit,Function.update,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

/-- The external flag-CX commutes with the old measured leaf. The three
remaining blocks are disjoint; the two high-output CX gates share a target. -/
theorem old_flag_commute (flag a b c A B z : Wire)
    (nd : [flag,a,b,c,A,B,z].Nodup) (s : State) (m : List Bool) :
    run (oldLeafAt a b c A B z) m (run [.CX flag B] [] s)=
      run [.CX flag B] [] (run (oldLeafAt a b c A B z) m s) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  let C : Program := [.CX flag B]
  have dP : Disjoint (wires (majority a b c z)) (wires C) := by
    simp_all [C,majority,wires,Instr.wires,ne_comm]
  have dR : Disjoint (wires (eraseCarry a b c z)) (wires C) := by
    simp_all [C,eraseCarry,wires,Instr.wires,correctionWires,ne_comm]
  have dL : Disjoint (wires [.CX a b,.CX c b]) (wires C) := by
    simp_all [C,wires,Instr.wires,ne_comm]
  have hp (s : State) (m : List Bool) :
      run (majority a b c z) m (run C [] s)=run C [] (run (majority a b c z) m s) :=
    run_disjoint_commute _ _ dP m [] s
  have hr (s : State) (m : List Bool) :
      run (eraseCarry a b c z) m (run C [] s)=run C [] (run (eraseCarry a b c z) m s) :=
    run_disjoint_commute _ _ dR m [] s
  have hl (s : State) (m : List Bool) :
      run [.CX a b,.CX c b] m (run C [] s)=run C [] (run [.CX a b,.CX c b] m s) :=
    run_disjoint_commute _ _ dL m [] s
  have hAB : A≠B := by tauto
  have hzB : z≠B := by tauto
  have hfB : flag≠B := by tauto
  have hq (s : State) (m : List Bool) :
      run [.CX A B,.CX z B] m (run C [] s)=run C [] (run [.CX A B,.CX z B] m s) :=
    same_target A z flag B hAB hzB hfB s m
  exact commute_cat _ _ C hp (commute_cat _ _ C hq (commute_cat _ _ C hr hl)) s m

private theorem cx_cancel (flag B : Wire) (hfB : flag≠B) (s : State) :
    run [.CX flag B] [] (run [.CX flag B] [] s)=s := by
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=B <;> simp_all [run,writeBit,Function.update]

private theorem xor_flag_zero (a b k f : Bool) (h : ((a^^b)^^k)=f) :
    ((a^^(b^^f))^^k)=false := by
  cases a <;> cases b <;> cases k <;> cases f <;> simp_all

/-- Exact complete-State equality, inherited from the public zero-top theorem.
The flag must be an immutable seventh port; the premise is the actual OLD
leaf's final high-output bit, before any proposed replacement is executed. -/
theorem top_equals_flag (flag a b c A B z : Wire)
    (nd : [flag,a,b,c,A,B,z].Nodup) (s : State) (m n : List Bool)
    (clean : s.basis z=false)
    (same : ((s.basis A^^s.basis B)^^carryBit (s.basis a) (s.basis b) (s.basis c))=s.basis flag) :
    run (oldLeafAt a b c A B z) m s=run (newFlagAt flag a b c A B) n s := by
  have nd6 : [a,b,c,A,B,z].Nodup := (List.nodup_cons.mp nd).2
  have ndf := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndf
  have hfB : flag≠B := by tauto
  have hzB : z≠B := by tauto
  have haB : a≠B := by tauto
  have hbB : b≠B := by tauto
  have hcB : c≠B := by tauto
  have hAB : A≠B := by tauto
  let C : Program := [.CX flag B]
  have preparedClean : (run C [] s).basis z=false := by
    simp [C,run,writeBit,Function.update,hzB,clean]
  have preparedReady : ReadyAt false a b c A B (run C [] s).basis := by
    simpa [C,ReadyAt,run,writeBit,Function.update,haB,hbB,hcB,hAB] using
      xor_flag_zero (s.basis A) (s.basis B)
        (carryBit (s.basis a) (s.basis b) (s.basis c)) (s.basis flag) same
  have zero := HighOutputTailStructuredResearch.full_state false a b c A B z nd6
    (run C [] s) m n preparedClean preparedReady
  have comm := old_flag_commute flag a b c A B z nd s m
  calc
    run (oldLeafAt a b c A B z) m s=
        run C [] (run C [] (run (oldLeafAt a b c A B z) m s)) :=
      (cx_cancel flag B hfB _).symm
    _ = run C [] (run (oldLeafAt a b c A B z) m (run C [] s)) := by rw [comm]
    _ = run C [] (run (newLeafAt false a b c A B) n (run C [] s)) := by rw [zero]
    _ = run (newFlagAt flag a b c A B) n s := by
      symm
      rw [newFlagAt,cat,cat]
      rfl

theorem counts (flag a b c A B : Wire) :
    toffoliCount (newFlagAt flag a b c A B)=0 ∧
    measurementCount (newFlagAt flag a b c A B)=1 ∧
    gateSlots (newFlagAt flag a b c A B)=9 := by
  exact ⟨rfl,rfl,rfl⟩

theorem support (flag a b c A B : Wire) :
    wires (newFlagAt flag a b c A B)={flag,a,b,c,A,B} := by
  ext q
  (simp [newFlagAt,newLeafAt,eraseCarry,wires,Instr.wires,correctionWires]; tauto)

theorem retired (flag a b c A B z : Wire) (nd : [flag,a,b,c,A,B,z].Nodup) :
    z∉wires (newFlagAt flag a b c A B) := by
  rw [support]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [ne_comm]

theorem physical (flag a b c A B z : Wire) (nd : [flag,a,b,c,A,B,z].Nodup) :
    GatePhysical (newFlagAt flag a b c A B) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newFlagAt,newLeafAt,eraseCarry,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

/-- Source-only complete-adder splice. No theorem about callers or this
recursive whole adder has yet been compiled. The final carry port is omitted. -/
def addTopFlag (flag : Wire) : List Wire → List Wire → List Wire → Wire → Program
  | [a,A],[b,B],[_],cin => newFlagAt flag a b cin A B
  | a::a'::as,b::b'::bs,z::cs,cin =>
      majority a b cin z ++ addTopFlag flag (a'::as) (b'::bs) cs z ++
        eraseCarry a b cin z ++ [.CX a b,.CX cin b]
  | [a],[b],_,cin => [.CX a b,.CX cin b]
  | _,_,_,_ => []

def addTopZero : List Wire → List Wire → List Wire → Wire → Program
  | [a,A],[b,B],[_],cin => newLeafAt false a b cin A B
  | a::a'::as,b::b'::bs,z::cs,cin =>
      majority a b cin z ++ addTopZero (a'::as) (b'::bs) cs z ++
        eraseCarry a b cin z ++ [.CX a b,.CX cin b]
  | [a],[b],_,cin => [.CX a b,.CX cin b]
  | _,_,_,_ => []

/-- Optional stronger exit variant. The highest three FINAL sum bits must be
zero: the two preceding carry producers use the next known zero sum as an
immutable affine witness. Only the final host is retired by this definition. -/
def addTopZeros3 : List Wire → List Wire → List Wire → Wire → Program
  | [a,A],[b,B],[_],cin => newLeafAt false a b cin A B
  | a::a'::as,b::b'::bs,z::cs,cin =>
      (if as.length≤2 then [.CX a' z,.CX b' z] else majority a b cin z) ++
        addTopZeros3 (a'::as) (b'::bs) cs z ++
        eraseCarry a b cin z ++ [.CX a b,.CX cin b]
  | [a],[b],_,cin => [.CX a b,.CX cin b]
  | _,_,_,_ => []

def kAddFlag (w : Nat → Wire) : Program :=
  addTopFlag (w 1028) (wireBlock w 0 258) (wireBlock w 770 258)
    (wireBlock w 1540 257) (w 1797)

def kAddZero (w : Nat → Wire) : Program :=
  addTopZero (wireBlock w 0 258) (wireBlock w 770 258)
    (wireBlock w 1540 257) (w 1797)

def kAddZeros3 (w : Nat → Wire) : Program :=
  addTopZeros3 (wireBlock w 0 258) (wireBlock w 770 258)
    (wireBlock w 1540 257) (w 1797)

end ECDSAAdd.Entrant.HighOutputFlagResearch
