import ECDSAAdd.Arithmetic.InPlaceAdder
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Challenge.Contract

/-! Private SOURCE_ONLY leaf proof draft. No Lean execution or certificate claim.
The assumptions are the literal two-bit reachable output relation and one clean
old carry. No arithmetic-caller range or global1796 support premise is assumed proved.
-/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.HighOutputTailStructuredResearch
open Arithmetic RecordedQuantum Challenge

/-- The original two-bit terminal suffix. `z` is the retired clean carry. -/
def oldLeafAt (a b c A B z : Wire) : Program :=
  majority a b c z ++ [.CX A B,.CX z B] ++
  eraseCarry a b c z ++ [.CX a b,.CX c b]

/-- The high output temporarily holds the carry, including the original immediate
measured phase correction. After measurement it is either zero or copied from the
now-final lower sum. The old carry `z` does not occur. -/
def newLeafAt (copy : Bool) (a b c A B : Wire) : Program :=
  [.CX A B] ++ (if copy then [.CX a B,.CX b B,.CX c B] else []) ++
  eraseCarry a b c B ++ [.CX a b,.CX c b] ++
  (if copy then [.CX b B] else [])

/-- A condition on input bits, equivalent to the OLD leaf's final high-output
bit being zero, or equal to the next final-sum bit. It is not assumed for all inputs. -/
def ReadyAt (copy : Bool) (a b c A B : Wire) (s : BasisState) : Prop :=
  ((s A ^^ s B) ^^ carryBit (s a) (s b) (s c)) =
    (if copy then sumBit (s a) (s b) (s c) else false)

/-- Compatibility aliases for the original finite six-port research notation. -/
def oldLeaf : Program := oldLeafAt 0 1 2 3 4 5
def newLeaf (copy : Bool) : Program := newLeafAt copy 0 1 2 3 4

theorem oldLeafAt_add (a b c A B z : Wire) :
    oldLeafAt a b c A B z = addInPlace [a,A] [b,B] [z] c := by
  rfl

private theorem run_cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s = run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

private theorem cx2 (x y t : Wire) (hx : x≠t) (hy : y≠t) (s : State) (m : List Bool) :
    run [.CX x t,.CX y t] m s =
      ⟨s.phase,writeBit s.basis t ((s.basis t ^^ s.basis x) ^^ s.basis y)⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=t <;> simp_all [writeBit,Function.update]

private theorem cx3 (x y z t : Wire) (hx : x≠t) (hy : y≠t) (hz : z≠t)
    (s : State) (m : List Bool) :
    run [.CX x t,.CX y t,.CX z t] m s =
      ⟨s.phase,writeBit s.basis t (((s.basis t ^^ s.basis x) ^^ s.basis y) ^^ s.basis z)⟩ := by
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=t <;> simp_all [writeBit,Function.update]

private theorem write_restore (bits : BasisState) (z B : Wire) (hzB : z≠B)
    (K U : Bool) (clean : bits z=false) :
    writeBit (writeBit (writeBit bits z K) B U) z false = writeBit bits B U := by
  funext q
  by_cases hqz : q=z
  · subst q
    simp [writeBit,Function.update,hzB,clean]
  · by_cases hqB : q=B <;> simp_all [writeBit,Function.update]

private theorem write_idem (bits : BasisState) (q : Wire) (x y : Bool) :
    writeBit (writeBit bits q x) q y = writeBit bits q y := by
  funext w
  by_cases hw : w=q <;> simp_all [writeBit,Function.update]

private def post (a b c B : Wire) (s : State) (hi : Bool) : State :=
  ⟨s.phase,writeBit (writeBit s.basis B hi) b (sumBit (s.basis a) (s.basis b) (s.basis c))⟩

private theorem lower (a b c B : Wire) (hab : a≠b) (hcb : c≠b)
    (haB : a≠B) (hbB : b≠B) (hcB : c≠B) (s : State) (U : Bool) (m : List Bool) :
    run [.CX a b,.CX c b] m ⟨s.phase,writeBit s.basis B U⟩ = post a b c B s U := by
  rw [cx2 a c b hab hcb]
  simp [post,writeBit,Function.update,haB,hbB,hcB,sumBit,
    Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

private theorem old_run (a b c A B z : Wire) (nd : [a,b,c,A,B,z].Nodup)
    (s : State) (m : List Bool) (clean : s.basis z=false) :
    run (oldLeafAt a b c A B z) m s =
      post a b c B s ((s.basis B ^^ s.basis A) ^^ carryBit (s.basis a) (s.basis b) (s.basis c)) := by
  have nd4 : [a,b,c,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd ⊢
    tauto
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haz⟩,⟨hbc,hbA,hbB,hbz⟩,
    ⟨hcA,hcB,hcz⟩,⟨hAB,hAz⟩,hBz⟩ := nd
  let K := carryBit (s.basis a) (s.basis b) (s.basis c)
  let U := (s.basis B ^^ s.basis A) ^^ K
  let s1 : State := ⟨s.phase,writeBit s.basis z K⟩
  let s2 : State := ⟨s.phase,writeBit (writeBit s.basis z K) B U⟩
  let s3 : State := ⟨s.phase,writeBit s.basis B U⟩
  have first (tape : List Bool) : run (majority a b c z) tape s = s1 := by
    rw [majority_correct a b c z nd4]
    simp only [s1,K,clean,Bool.false_xor]
  have second (tape : List Bool) : run [.CX A B,.CX z B] tape s1 = s2 := by
    rw [cx2 A z B hAB (Ne.symm hBz)]
    simp [s1,s2,U,writeBit,Function.update,hBz,hAz]
  have relation : s2.basis z = carryBit (s2.basis a) (s2.basis b) (s2.basis c) := by
    simp [s2,K,writeBit,Function.update,Ne.symm hBz,haz,haB,hbz,hbB,hcz,hcB]
  have third (tape : List Bool) : run (eraseCarry a b c z) tape s2 = s3 := by
    rw [eraseCarry_correct a b c z haz hbz hcz s2 relation]
    simpa only [s2,s3] using congrArg (State.mk s.phase)
      (write_restore s.basis z B (Ne.symm hBz) K U clean)
  have fourth (tape : List Bool) : run [.CX a b,.CX c b] tape s3 = post a b c B s U := by
    exact lower a b c B hab (Ne.symm hbc) haB hbB hcB s U tape
  simp only [oldLeafAt,run_cat,first,second,third,fourth,U,K]

private def lead (copy : Bool) (a b c A B : Wire) : Program :=
  [.CX A B] ++ (if copy then [.CX a B,.CX b B,.CX c B] else [])

private theorem lead_run (copy : Bool) (a b c A B : Wire)
    (haB : a≠B) (hbB : b≠B) (hcB : c≠B) (s : State) (m : List Bool) :
    run (lead copy a b c A B) m s =
      ⟨s.phase,writeBit s.basis B ((s.basis B ^^ s.basis A) ^^
        (if copy then sumBit (s.basis a) (s.basis b) (s.basis c) else false))⟩ := by
  cases copy
  · simp [lead,run]
  · simp only [lead,if_true,run_cat,cx3 a b c B haB hbB hcB]
    simp only [run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=B <;>
      simp_all [writeBit,Function.update,sumBit,Bool.xor_assoc]

private theorem new_run (copy : Bool) (a b c A B z : Wire)
    (nd : [a,b,c,A,B,z].Nodup) (s : State) (m : List Bool)
    (ready : ReadyAt copy a b c A B s.basis) :
    run (newLeafAt copy a b c A B) m s =
      post a b c B s (if copy then sumBit (s.basis a) (s.basis b) (s.basis c) else false) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haz⟩,⟨hbc,hbA,hbB,hbz⟩,
    ⟨hcA,hcB,hcz⟩,⟨hAB,hAz⟩,hBz⟩ := nd
  let K := carryBit (s.basis a) (s.basis b) (s.basis c)
  let S := sumBit (s.basis a) (s.basis b) (s.basis c)
  let T := if copy then S else false
  have hi : ((s.basis B ^^ s.basis A) ^^ K) = T := by
    unfold ReadyAt at ready
    rw [Bool.xor_comm (s.basis A) (s.basis B)] at ready
    exact ready
  have recover : ((s.basis B ^^ s.basis A) ^^ T) = K := by
    rw [← hi]
    simp only [← Bool.xor_assoc,Bool.xor_self,Bool.false_xor]
  let s1 : State := ⟨s.phase,writeBit s.basis B K⟩
  let s2 : State := ⟨s.phase,writeBit s.basis B false⟩
  let s3 : State := post a b c B s false
  have first (tape : List Bool) : run (lead copy a b c A B) tape s = s1 := by
    rw [lead_run copy a b c A B haB hbB hcB]
    change (⟨s.phase,writeBit s.basis B ((s.basis B ^^ s.basis A) ^^ T)⟩ : State) =
      ⟨s.phase,writeBit s.basis B K⟩
    rw [recover]
  have relation : s1.basis B = carryBit (s1.basis a) (s1.basis b) (s1.basis c) := by
    simp [s1,K,writeBit,Function.update,haB,hbB,hcB]
  have second (tape : List Bool) : run (eraseCarry a b c B) tape s1 = s2 := by
    rw [eraseCarry_correct a b c B haB hbB hcB s1 relation]
    simpa only [s1,s2] using congrArg (State.mk s.phase)
      (write_idem s.basis B K false)
  have third (tape : List Bool) : run [.CX a b,.CX c b] tape s2 = s3 := by
    exact lower a b c B hab (Ne.symm hbc) haB hbB hcB s false tape
  have fourth (tape : List Bool) : run (if copy then [.CX b B] else []) tape s3 = post a b c B s T := by
    cases hcopy : copy
    · simp [T,hcopy,s3,run]
    · simp only [hcopy,if_true,run]
      apply congrArg (State.mk s.phase)
      funext q
      by_cases hqB : q=B
      · subst q
        simp [s3,post,T,S,hcopy,writeBit,Function.update,Ne.symm hbB]
      · by_cases hqb : q=b <;>
          simp_all [s3,post,T,S,hcopy,writeBit,Function.update]
  change run (lead copy a b c A B ++ eraseCarry a b c B ++
    [.CX a b,.CX c b] ++ (if copy then [.CX b B] else [])) m s = _
  simp only [run_cat,first,second,third,fourth,T,S]

/-- Structural proof: majority_correct and eraseCarry_correct eliminate all
measurement records before the final Boolean XOR/frame comparison. -/
theorem full_state (copy : Bool) (a b c A B z : Wire)
    (nd : [a,b,c,A,B,z].Nodup) (s : State) (m n : List Bool)
    (clean : s.basis z = false) (ready : ReadyAt copy a b c A B s.basis) :
    run (oldLeafAt a b c A B z) m s = run (newLeafAt copy a b c A B) n s := by
  rw [old_run a b c A B z nd s m clean,new_run copy a b c A B z nd s n ready]
  apply congrArg (post a b c B s)
  unfold ReadyAt at ready
  rw [Bool.xor_comm (s.basis A) (s.basis B)] at ready
  exact ready

/-- Exact zero-top leaf obligation for an arithmetic caller. -/
theorem top_zero (a b c A B z : Wire) (nd : [a,b,c,A,B,z].Nodup)
    (s : State) (m n : List Bool) (clean : s.basis z = false)
    (zero : ((s.basis A ^^ s.basis B) ^^
      carryBit (s.basis a) (s.basis b) (s.basis c)) = false) :
    run (oldLeafAt a b c A B z) m s = run (newLeafAt false a b c A B) n s := by
  apply full_state false a b c A B z nd s m n clean
  simpa only [ReadyAt,Bool.false_eq_true,if_false] using zero

private theorem adder_nd (a b c A B z : Wire) (nd : [a,b,c,A,B,z].Nodup) :
    (c :: [a,A] ++ [b,B] ++ [z]).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem support (copy : Bool) (a b c A B z : Wire) :
    wires (oldLeafAt a b c A B z) = {a,b,c,A,B,z} ∧
    wires (newLeafAt copy a b c A B) = {a,b,c,A,B} := by
  constructor
  · ext q
    (simp [oldLeafAt,majority,eraseCarry,wires,Instr.wires,correctionWires]; tauto)
  · cases copy <;> ext q <;>
      simp [newLeafAt,eraseCarry,wires,Instr.wires,correctionWires] <;> tauto

theorem retired (copy : Bool) (a b c A B z : Wire)
    (nd : [a,b,c,A,B,z].Nodup) : z ∉ wires (newLeafAt copy a b c A B) := by
  rw [(support copy a b c A B z).2]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [ne_comm]

theorem counts (copy : Bool) (a b c A B z : Wire) :
    toffoliCount (oldLeafAt a b c A B z) = 1 ∧
    toffoliCount (newLeafAt copy a b c A B) = 0 ∧
    measurementCount (oldLeafAt a b c A B z) = 1 ∧
    measurementCount (newLeafAt copy a b c A B) = 1 := by
  cases copy <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem slots (copy : Bool) (a b c A B z : Wire) :
    gateSlots (oldLeafAt a b c A B z) = 14 ∧
    gateSlots (newLeafAt copy a b c A B) = (if copy then 11 else 7) := by
  cases copy <;> exact ⟨rfl,rfl⟩

theorem physical (copy : Bool) (a b c A B z : Wire)
    (nd : [a,b,c,A,B,z].Nodup) :
    GatePhysical (oldLeafAt a b c A B z) ∧ GatePhysical (newLeafAt copy a b c A B) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  cases copy <;>
    simp_all [oldLeafAt,newLeafAt,majority,eraseCarry,GatePhysical,PhysicalInstr,ProperGate,
      ne_comm]

/-- A measured/recorded use consumes exactly the same one record ordinal in
both programs. The arbitrary suffix tape is retained by the original interpreter. -/
theorem record_count_preserved (copy : Bool) (a b c A B z : Wire) :
    measurementCount (oldLeafAt a b c A B z) =
      measurementCount (newLeafAt copy a b c A B) := by
  exact (counts copy a b c A B z).2.2.1.trans (counts copy a b c A B z).2.2.2.symm

end ECDSAAdd.Entrant.HighOutputTailStructuredResearch
