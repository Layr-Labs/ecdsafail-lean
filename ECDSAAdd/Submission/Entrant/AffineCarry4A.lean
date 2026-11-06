import ECDSAAdd.Submission.Entrant.AffineCarry3A
import ECDSAAdd.Arithmetic.DisjointPrograms

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 400

namespace Verifier.Leaf4
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open Verifier.Leaf3 (cval oldLeaf3At old3_run old3_counts)

/-- The four-bit terminal suffix: three retired clean carries `z`, `z'`, `z''`. -/
def oldLeaf4At (a b c A B A' B' A'' B'' z z' z'' : Wire) : Program :=
  addInPlace [a,A,A',A''] [b,B,B',B''] [z,z',z''] c

/-- Zero-Toffoli replacement. `B''`, `B'`, `B` are measured strictly top-down:
each correction list names a wire that is still live. -/
def newLeaf4At (a b c A B A' B' A'' B'' : Wire) : Program :=
  [.measureX B'' [] [.Z A', .Z B', .Z A'', .CZ A' B'],
   .measureX B'  [] [.Z A,  .Z B,  .Z A',  .CZ A  B],
   .measureX B   [] [.Z A, .CZ a b, .CZ a c, .CZ b c],
   .CX a b, .CX c b]

/-- Output bits 255, 256 and 257 of the sum are zero. -/
def Ready4 (a b c A B A' B' A'' B'' : Wire) (s : BasisState) : Prop :=
  ((s A ^^ s B) ^^ carryBit (s a) (s b) (s c)) = false ∧
  ((s A' ^^ s B') ^^ carryBit (s A) (s B) (carryBit (s a) (s b) (s c))) = false ∧
  ((s A'' ^^ s B'') ^^
     carryBit (s A') (s B') (carryBit (s A) (s B) (carryBit (s a) (s b) (s c)))) = false

/-! ### Structural checks -/

theorem old4_unfold (a b c A B A' B' A'' B'' z z' z'' : Wire) :
    oldLeaf4At a b c A B A' B' A'' B'' z z' z''
      = majority a b c z ++ oldLeaf3At A B z A' B' A'' B'' z' z''
          ++ eraseCarry a b c z ++ [.CX a b, .CX c b] := rfl

theorem old4_counts (a b c A B A' B' A'' B'' z z' z'' : Wire) :
    toffoliCount (oldLeaf4At a b c A B A' B' A'' B'' z z' z'')=3
      ∧ measurementCount (oldLeaf4At a b c A B A' B' A'' B'' z z' z'')=3 := by
  constructor <;> rfl

theorem new4_counts (a b c A B A' B' A'' B'' : Wire) :
    toffoliCount (newLeaf4At a b c A B A' B' A'' B'')=0
      ∧ measurementCount (newLeaf4At a b c A B A' B' A'' B'')=3 := by
  constructor <;> rfl

/-! ### Boolean content of the three correction lists.

Each is a pure `Bool` identity on the nine leaf values, closed by `decide`
over the 512-point cube.  The point of the construction is that all three stay
degree two: on the restricted domain the degree-three majority collapses. -/

private theorem corr_top : ∀ (va vb vc vA vB vA' vB' vA'' vB'' : Bool),
    ((vA' ^^ vB') ^^ carryBit vA vB (carryBit va vb vc)) = false →
    ((vA'' ^^ vB'') ^^
      carryBit vA' vB' (carryBit vA vB (carryBit va vb vc))) = false →
    vB'' = (vA' ^^ (vB' ^^ (vA'' ^^ (vA' && vB')))) := by decide

private theorem corr_mid : ∀ (va vb vc vA vB vA' vB' : Bool),
    ((vA ^^ vB) ^^ carryBit va vb vc) = false →
    ((vA' ^^ vB') ^^ carryBit vA vB (carryBit va vb vc)) = false →
    vB' = (vA ^^ (vB ^^ (vA' ^^ (vA && vB)))) := by decide

private theorem corr_low : ∀ (va vb vc vA vB : Bool),
    ((vA ^^ vB) ^^ carryBit va vb vc) = false →
    vB = (vA ^^ ((va && vb) ^^ ((va && vc) ^^ (vb && vc)))) := by decide

/-! ### Reusable run-level helpers (mirrors of the three-bit module's privates). -/

private theorem correct_eq (cs : List Correction) (s : State) :
    correct cs s = ⟨s.phase ^^ cval cs s.basis, s.basis⟩ := by
  induction cs generalizing s with
  | nil => simp [correct,cval]
  | cons d cs ih =>
    cases d <;>
      simp [correct,cval,ih,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

private theorem meas_clean (t : Wire) (cs : List Correction) (s : State) (m : List Bool)
    (h : s.basis t = cval cs (writeBit s.basis t false)) :
    run [.measureX t [] cs] m s = ⟨s.phase, writeBit s.basis t false⟩ := by
  simp only [run,measureAndCorrect]
  cases hm : m.headD false
  · simp [correct,cval]
  · simp only [Bool.true_and,if_true,correct_eq,←h]
    simp [Bool.xor_assoc]

private theorem st_eq {p q : Bool} {f g : BasisState}
    (hp : p = q) (hf : ∀ w, f w = g w) : (⟨p,f⟩ : State) = ⟨q,g⟩ := by
  subst hp; exact congrArg _ (funext hf)

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

/-- Common final state: `b` holds the low sum, all three high outputs are zeroed,
phase is untouched. -/
private def post4 (a b c B B' B'' : Wire) (s : State) : State :=
  ⟨s.phase,
   writeBit (writeBit (writeBit (writeBit s.basis B'' false) B' false) B false) b
     (sumBit (s.basis a) (s.basis b) (s.basis c))⟩

theorem new4_run (a b c A B A' B' A'' B'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B''].Nodup)
    (s : State) (m : List Bool) (ready : Ready4 a b c A B A' B' A'' B'' s.basis) :
    run (newLeaf4At a b c A B A' B' A'' B'') m s = post4 a b c B B' B'' s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB''⟩,
          ⟨hBA',hBB',hBA'',hBB''⟩,
          ⟨hA'B',hA'A'',hA'B''⟩,
          ⟨hB'A'',hB'B''⟩,hA''B''⟩ := nd
  obtain ⟨r1,r2,r3⟩ := ready
  -- top measurement: B''
  have h1 : s.basis B''
      = cval [.Z A',.Z B',.Z A'',.CZ A' B'] (writeBit s.basis B'' false) := by
    simp only [cval,writeBit,Function.update_of_ne hA'B'',Function.update_of_ne hB'B'',
      Function.update_of_ne hA''B'',Bool.xor_false]
    exact corr_top _ _ _ _ _ _ _ _ _ r2 r3
  have e1 := meas_clean B'' [.Z A',.Z B',.Z A'',.CZ A' B'] s m h1
  -- middle measurement: B'
  have h2 : (⟨s.phase,writeBit s.basis B'' false⟩ : State).basis B'
      = cval [.Z A,.Z B,.Z A',.CZ A B]
          (writeBit (⟨s.phase,writeBit s.basis B'' false⟩ : State).basis B' false) := by
    simp only [cval,writeBit,
      Function.update_of_ne hAB',Function.update_of_ne hAB'',
      Function.update_of_ne hBB',Function.update_of_ne hBB'',
      Function.update_of_ne hA'B',Function.update_of_ne hA'B'',
      Function.update_of_ne hB'B'',Bool.xor_false]
    exact corr_mid _ _ _ _ _ _ _ r1 r2
  have e2 := meas_clean B' [.Z A,.Z B,.Z A',.CZ A B]
    ⟨s.phase,writeBit s.basis B'' false⟩
    (m.drop (measurementCount [Instr.measureX B'' [] [.Z A',.Z B',.Z A'',.CZ A' B']])) h2
  -- low measurement: B
  have h3 : (⟨s.phase,writeBit (writeBit s.basis B'' false) B' false⟩ : State).basis B
      = cval [.Z A,.CZ a b,.CZ a c,.CZ b c]
          (writeBit (⟨s.phase,writeBit (writeBit s.basis B'' false) B' false⟩ : State).basis
            B false) := by
    simp only [cval,writeBit,
      Function.update_of_ne hAB,Function.update_of_ne hAB',Function.update_of_ne hAB'',
      Function.update_of_ne haB,Function.update_of_ne haB',Function.update_of_ne haB'',
      Function.update_of_ne hbB,Function.update_of_ne hbB',Function.update_of_ne hbB'',
      Function.update_of_ne hcB,Function.update_of_ne hcB',Function.update_of_ne hcB'',
      Function.update_of_ne hBB',Function.update_of_ne hBB'',Bool.xor_false]
    exact corr_low _ _ _ _ _ r1
  have e3 := meas_clean B [.Z A,.CZ a b,.CZ a c,.CZ b c]
    ⟨s.phase,writeBit (writeBit s.basis B'' false) B' false⟩
    ((m.drop (measurementCount [Instr.measureX B'' [] [.Z A',.Z B',.Z A'',.CZ A' B']])).drop
      (measurementCount [Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]])) h3
  show run ([Instr.measureX B'' [] [.Z A',.Z B',.Z A'',.CZ A' B']]
      ++ ([Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]]
      ++ ([Instr.measureX B [] [.Z A,.CZ a b,.CZ a c,.CZ b c]]
      ++ [.CX a b,.CX c b]))) m s = post4 a b c B B' B'' s
  rw [run_cat,e1,run_cat,e2,run_cat,e3,cx2 a c b hab (Ne.symm hbc)]
  refine st_eq rfl (fun w => ?_)
  simp only [post4,writeBit,
    Function.update_of_ne haB,Function.update_of_ne haB',Function.update_of_ne haB'',
    Function.update_of_ne hbB,Function.update_of_ne hbB',Function.update_of_ne hbB'',
    Function.update_of_ne hcB,Function.update_of_ne hcB',Function.update_of_ne hcB'',sumBit]
  by_cases hw : w = b
  · subst w
    simp only [Function.update_self]
    exact Bool.xor_comm _ _ ▸ (by
      cases s.basis a <;> cases s.basis b <;> cases s.basis c <;> decide)
  · simp only [Function.update_of_ne hw]

#print axioms new4_run

/-- Closed form of the four-bit in-place adder leaf, reusing the three-bit result
for the inner suffix.  `z` is written and erased invisibly. -/
theorem old4_run (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup)
    (s : State) (m : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false) (cz'' : s.basis z'' = false) :
    run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') m s =
      ⟨s.phase,
       writeBit (writeBit (writeBit (writeBit (writeBit (writeBit s.basis
         z'' (carryBit (s.basis A') (s.basis B')
               (carryBit (s.basis A) (s.basis B)
                 (carryBit (s.basis a) (s.basis b) (s.basis c)))))
         B'' ((s.basis B'' ^^ s.basis A'') ^^
               carryBit (s.basis A') (s.basis B')
                 (carryBit (s.basis A) (s.basis B)
                   (carryBit (s.basis a) (s.basis b) (s.basis c)))))
         z'' false)
         B' ((s.basis B' ^^ s.basis A') ^^
               carryBit (s.basis A) (s.basis B)
                 (carryBit (s.basis a) (s.basis b) (s.basis c))))
         B (sumBit (s.basis A) (s.basis B)
               (carryBit (s.basis a) (s.basis b) (s.basis c))))
         b (sumBit (s.basis a) (s.basis b) (s.basis c))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB'',haz,haz',haz''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB'',hbz,hbz',hbz''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB'',hcz,hcz',hcz''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB'',hAz,hAz',hAz''⟩,
          ⟨hBA',hBB',hBA'',hBB'',hBz,hBz',hBz''⟩,
          ⟨hA'B',hA'A'',hA'B'',hA'z,hA'z',hA'z''⟩,
          ⟨hB'A'',hB'B'',hB'z,hB'z',hB'z''⟩,
          ⟨hA''B'',hA''z,hA''z',hA''z''⟩,
          ⟨hB''z,hB''z',hB''z''⟩,
          ⟨hzz',hzz''⟩,
          hz'z''⟩ := nd
  set K1 := carryBit (s.basis a) (s.basis b) (s.basis c) with hK1
  set K2 := carryBit (s.basis A) (s.basis B) K1 with hK2
  set K3 := carryBit (s.basis A') (s.basis B') K2 with hK3
  have n1 : [a,b,c,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]; exact ⟨⟨hab,hac,haz⟩,⟨hbc,hbz⟩,hcz⟩
  have nd9 : [A,B,z,A',B',A'',B'',z',z''].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨hAB,hAz,hAA',hAB',hAA'',hAB'',hAz',hAz''⟩,
           ⟨hBz,hBA',hBB',hBA'',hBB'',hBz',hBz''⟩,
           ⟨Ne.symm hA'z,Ne.symm hB'z,Ne.symm hA''z,Ne.symm hB''z,hzz',hzz''⟩,
           ⟨hA'B',hA'A'',hA'B'',hA'z',hA'z''⟩,
           ⟨hB'A'',hB'B'',hB'z',hB'z''⟩,
           ⟨hA''B'',hA''z',hA''z''⟩,
           ⟨hB''z',hB''z''⟩,hz'z''⟩
  have pz' : (⟨s.phase,writeBit s.basis z K1⟩ : State).basis z' = false := by
    simp only [writeBit,Function.update_of_ne (Ne.symm hzz')]; exact cz'
  have pz'' : (⟨s.phase,writeBit s.basis z K1⟩ : State).basis z'' = false := by
    simp only [writeBit,Function.update_of_ne (Ne.symm hzz'')]; exact cz''
  show run (majority a b c z ++ (oldLeaf3At A B z A' B' A'' B'' z' z''
      ++ (eraseCarry a b c z ++ [Instr.CX a b,.CX c b]))) m s = _
  rw [run_cat,majority_correct a b c z n1]
  simp only [cz,Bool.false_xor,←hK1]
  rw [run_cat,old3_run A B z A' B' A'' B'' z' z'' nd9 ⟨s.phase,writeBit s.basis z K1⟩ _ pz' pz'']
  simp only [writeBit,
    Function.update_of_ne (Ne.symm hAz),Function.update_of_ne (Ne.symm hBz),
    Function.update_of_ne (Ne.symm hA'z),Function.update_of_ne (Ne.symm hB'z),
    Function.update_of_ne (Ne.symm hA''z),Function.update_of_ne (Ne.symm hB''z),
    Function.update_self,←hK2,←hK3]
  rw [run_cat,eraseCarry_correct a b c z haz hbz hcz _ (by
    simp only [writeBit,
      Function.update_of_ne (Ne.symm hBz),Function.update_of_ne (Ne.symm hB'z),
      Function.update_of_ne (Ne.symm hB''z),Function.update_of_ne hzz'',
      Function.update_self,
      Function.update_of_ne haB,Function.update_of_ne haB',Function.update_of_ne haB'',
      Function.update_of_ne haz'',Function.update_of_ne haz,
      Function.update_of_ne hbB,Function.update_of_ne hbB',Function.update_of_ne hbB'',
      Function.update_of_ne hbz'',Function.update_of_ne hbz,
      Function.update_of_ne hcB,Function.update_of_ne hcB',Function.update_of_ne hcB'',
      Function.update_of_ne hcz'',Function.update_of_ne hcz,←hK1])]
  rw [cx2 a c b hab (Ne.symm hbc)]
  have q1 := Ne.symm hzz'; have q2 := Ne.symm hzz''; have q3 := Ne.symm hz'z''
  have q4 := Ne.symm hbz; have q5 := Ne.symm hbz'; have q6 := Ne.symm hbz''
  have q7 := Ne.symm hbB; have q8 := Ne.symm hbB'; have q9 := Ne.symm hbB''
  have q10 := Ne.symm hBz; have q11 := Ne.symm hBz'; have q12 := Ne.symm hBz''
  have q13 := Ne.symm hB'z; have q14 := Ne.symm hB'z'; have q15 := Ne.symm hB'z''
  have q16 := Ne.symm hB''z; have q17 := Ne.symm hB''z'; have q18 := Ne.symm hB''z''
  have q19 := Ne.symm hAz; have q20 := Ne.symm hAz'; have q21 := Ne.symm hAz''
  have q22 := Ne.symm hA'z; have q23 := Ne.symm hA'z'; have q24 := Ne.symm hA'z''
  have q25 := Ne.symm hA''z; have q26 := Ne.symm hA''z'; have q27 := Ne.symm hA''z''
  have q28 := Ne.symm haz; have q29 := Ne.symm hcz; have q30 := Ne.symm haB
  have q31 := Ne.symm haB'; have q32 := Ne.symm haB''; have q33 := Ne.symm hcB
  have q34 := Ne.symm hcB'; have q35 := Ne.symm hcB''; have q36 := Ne.symm hAB
  have q37 := Ne.symm hAB'; have q38 := Ne.symm hAB''; have q39 := Ne.symm hA'B'
  have q40 := Ne.symm hA'B''; have q41 := Ne.symm hA''B''; have q42 := Ne.symm hBB'
  have q43 := Ne.symm hBB''; have q44 := Ne.symm hB'B''; have q45 := Ne.symm hBA'
  have q46 := Ne.symm hBA''; have q47 := Ne.symm hB'A''; have q48 := Ne.symm hAA'
  have q49 := Ne.symm hAA''; have q50 := Ne.symm hA'A''
  refine st_eq rfl (fun w => ?_)
  by_cases hwz : w = z <;> by_cases hwz'' : w = z'' <;>
    by_cases hwb : w = b <;> by_cases hwB : w = B <;>
    by_cases hwB' : w = B' <;> by_cases hwB'' : w = B'' <;>
    subst_vars <;>
    simp_all [writeBit,Function.update,sumBit,
      Bool.xor_comm,Bool.xor_assoc,Bool.xor_left_comm]

#print axioms old4_run

/-- Erasing a scratch wire that was clean on entry leaves no trace, even across an
intervening write to a different wire. -/
private theorem drop_scratch (f : BasisState) (u v : Wire) (huv : u ≠ v) {k x : Bool}
    (hf : f u = false) :
    writeBit (writeBit (writeBit f u k) v x) u false = writeBit f v x := by
  funext w
  by_cases h1 : w = u <;> by_cases h2 : w = v <;>
    simp_all [writeBit,Function.update]

/-- **Main result.** On the restriction that output bits 255, 256 and 257 are zero,
the three-Toffoli four-bit leaf and the zero-Toffoli replacement agree as complete
States -- phase included -- for arbitrary and independent measurement records. -/
theorem full_state4 (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup) (s : State) (m n : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false) (cz'' : s.basis z'' = false)
    (ready : Ready4 a b c A B A' B' A'' B'' s.basis) :
    run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') m s
      = run (newLeaf4At a b c A B A' B' A'' B'') n s := by
  have nd' := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd'
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB'',haz,haz',haz''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB'',hbz,hbz',hbz''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB'',hcz,hcz',hcz''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB'',hAz,hAz',hAz''⟩,
          ⟨hBA',hBB',hBA'',hBB'',hBz,hBz',hBz''⟩,
          ⟨hA'B',hA'A'',hA'B'',hA'z,hA'z',hA'z''⟩,
          ⟨hB'A'',hB'B'',hB'z,hB'z',hB'z''⟩,
          ⟨hA''B'',hA''z,hA''z',hA''z''⟩,
          ⟨hB''z,hB''z',hB''z''⟩,
          ⟨hzz',hzz''⟩,
          hz'z''⟩ := nd'
  have nd9 : [a,b,c,A,B,A',B',A'',B''].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB''⟩,
           ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB''⟩,
           ⟨hcA,hcB,hcA',hcB',hcA'',hcB''⟩,
           ⟨hAB,hAA',hAB',hAA'',hAB''⟩,
           ⟨hBA',hBB',hBA'',hBB''⟩,
           ⟨hA'B',hA'A'',hA'B''⟩,
           ⟨hB'A'',hB'B''⟩,hA''B''⟩
  obtain ⟨r1,r2,r3⟩ := ready
  have v1 : (s.basis B'' ^^ s.basis A'' ^^
      carryBit (s.basis A') (s.basis B')
        (carryBit (s.basis A) (s.basis B)
          (carryBit (s.basis a) (s.basis b) (s.basis c)))) = false := by
    simpa [Bool.xor_comm] using r3
  have v2 : (s.basis B' ^^ s.basis A' ^^
      carryBit (s.basis A) (s.basis B)
        (carryBit (s.basis a) (s.basis b) (s.basis c))) = false := by
    simpa [Bool.xor_comm] using r2
  have v3 : sumBit (s.basis A) (s.basis B)
      (carryBit (s.basis a) (s.basis b) (s.basis c)) = false := r1
  rw [old4_run a b c A B A' B' A'' B'' z z' z'' nd s m cz cz' cz'',
      new4_run a b c A B A' B' A'' B'' nd9 s n ⟨r1,r2,r3⟩]
  simp only [post4]
  rw [v1]
  rw [v2]
  rw [v3]
  rw [drop_scratch s.basis z'' B'' (Ne.symm hB''z'') cz'']

#print axioms full_state4

/-! ### Wrapper: substitution inside a surrounding program. -/

/-- The three high output bits of the whole program determine `Ready4` at the leaf boundary. -/
theorem prefix_leaf4_high (P R : Program) (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false) (cz'' : s.basis z''=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hz''P : z''∉wires P)
    (hBR : B∉wires R) (hB'R : B'∉wires R) (hB''R : B''∉wires R)
    (topB   : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B = false)
    (topB'  : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B' = false)
    (topB'' : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B'' = false) :
    Ready4 a b c A B A' B' A'' B'' (run P m s).basis := by
  have nd' := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd'
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haA'',haB'',haz,haz',haz''⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbA'',hbB'',hbz,hbz',hbz''⟩,
          ⟨hcA,hcB,hcA',hcB',hcA'',hcB'',hcz,hcz',hcz''⟩,
          ⟨hAB,hAA',hAB',hAA'',hAB'',hAz,hAz',hAz''⟩,
          ⟨hBA',hBB',hBA'',hBB'',hBz,hBz',hBz''⟩,
          ⟨hA'B',hA'A'',hA'B'',hA'z,hA'z',hA'z''⟩,
          ⟨hB'A'',hB'B'',hB'z,hB'z',hB'z''⟩,
          ⟨hA''B'',hA''z,hA''z',hA''z''⟩,
          ⟨hB''z,hB''z',hB''z''⟩,
          ⟨hzz',hzz''⟩,
          hz'z''⟩ := nd'
  have tz   : (run P [] s).basis z   = false := (run_preserves_outside P [] s z hzP).trans cz
  have tz'  : (run P [] s).basis z'  = false := (run_preserves_outside P [] s z' hz'P).trans cz'
  have tz'' : (run P [] s).basis z'' = false := (run_preserves_outside P [] s z'' hz''P).trans cz''
  have hB0 : (run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') []
      (run P [] s)).basis B = false := by
    have h := topB
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B hBR] at h
    exact h
  have hB'0 : (run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') []
      (run P [] s)).basis B' = false := by
    have h := topB'
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B' hB'R] at h
    exact h
  have hB''0 : (run (oldLeaf4At a b c A B A' B' A'' B'' z z' z'') []
      (run P [] s)).basis B'' = false := by
    have h := topB''
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B'' hB''R] at h
    exact h
  rw [old4_run a b c A B A' B' A'' B'' z z' z'' nd (run P [] s) [] tz tz' tz''] at hB0 hB'0 hB''0
  simp only [writeBit, Function.update] at hB0 hB'0 hB''0
  simp only [hbB, hBz'', hBB', hBB'', hbB', hbB'', hB'z'', hB''z'', hB'B'',
    eq_self_iff_true, if_true, if_false,
    Ne.symm hbB, Ne.symm hBz'', Ne.symm hBB', Ne.symm hBB'', Ne.symm hbB',
    Ne.symm hbB'', Ne.symm hB'z'', Ne.symm hB''z'', Ne.symm hB'B''] at hB0 hB'0 hB''0
  have pb : (run P m s).basis = (run P [] s).basis := run_basis_records P s s m [] rfl
  refine ⟨?_,?_,?_⟩
  · rw [pb]
    simpa only [sumBit] using hB0
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A') ((run P [] s).basis B')]; exact hB'0
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A'') ((run P [] s).basis B'')]; exact hB''0

/-- Whole-program zero-top replacement for the FOUR-bit leaf: three Toffolis removed. -/
theorem whole_zero4 (P R : Program) (a b c A B A' B' A'' B'' z z' z'' : Wire)
    (nd : [a,b,c,A,B,A',B',A'',B'',z,z',z''].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false) (cz'' : s.basis z''=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hz''P : z''∉wires P)
    (hBR : B∉wires R) (hB'R : B'∉wires R) (hB''R : B''∉wires R)
    (topB   : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B = false)
    (topB'  : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B' = false)
    (topB'' : (run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) [] s).basis B'' = false) :
    run (P++oldLeaf4At a b c A B A' B' A'' B'' z z' z''++R) m s
      = run (P++newLeaf4At a b c A B A' B' A'' B''++R) m s := by
  have tz   : (run P m s).basis z   = false := (run_preserves_outside P m s z hzP).trans cz
  have tz'  : (run P m s).basis z'  = false := (run_preserves_outside P m s z' hz'P).trans cz'
  have tz'' : (run P m s).basis z'' = false := (run_preserves_outside P m s z'' hz''P).trans cz''
  have ready := prefix_leaf4_high P R a b c A B A' B' A'' B'' z z' z'' nd s m
    cz cz' cz'' hzP hz'P hz''P hBR hB'R hB''R topB topB' topB''
  have eqn := full_state4 a b c A B A' B' A'' B'' z z' z'' nd (run P m s)
    (m.drop (measurementCount P)) (m.drop (measurementCount P)) tz tz' tz'' ready
  simpa only [run_cat, measurementCount_append,
    (old4_counts a b c A B A' B' A'' B'' z z' z'').2, (new4_counts a b c A B A' B' A'' B'').2,
    List.drop_drop, Nat.add_comm] using
    congrArg (run R ((m.drop (measurementCount P)).drop 3)) eqn

#print axioms prefix_leaf4_high
#print axioms whole_zero4

/-! ### Instantiation at the KAdd indices -/
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

/-- Mirror of `add_split`, peeling FOUR bits. -/
theorem add_split4 (xs ys cs : List Wire) (cin a A A' A'' b B B' B'' z z' z'' : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    addInPlace (xs++[a,A,A',A'']) (ys++[b,B,B',B'']) (cs++[z,z',z'']) cin=
      adderPrefix xs ys cs cin
        ++ oldLeaf4At a b (lastCarry cs cin) A B A' B' A'' B'' z z' z''
        ++ adderSuffix xs ys cs cin := by
  induction xs generalizing ys cs cin with
  | nil =>
    have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
    have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
    subst ys; subst cs; rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have hy' : xs.length=ys.length := by simpa using hy
        have hc' : xs.length=cs.length := by simpa using hc
        have step : addInPlace ((x::xs)++[a,A,A',A'']) ((y::ys)++[b,B,B',B''])
            ((c::cs)++[z,z',z'']) cin=
            majority x y cin c++addInPlace (xs++[a,A,A',A'']) (ys++[b,B,B',B'']) (cs++[z,z',z'']) c++
              eraseCarry x y cin c++[.CX x y,.CX cin y] := by
          cases xs <;> cases ys <;> rfl
        rw [step,ih ys cs c hy' hc']
        simp only [adderPrefix,adderSuffix,lastCarry,List.append_assoc]

def P4 (w : Nat→Wire) : Program :=
  adderPrefix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)
def R4 (w : Nat→Wire) : Program :=
  adderSuffix (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797)

private theorem lastCarry_cat4 (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs ++ ys) cin = lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append,lastCarry] using ih x

theorem literal_split4 (w : Nat→Wire) :
    literalKAdd w = P4 w
      ++ oldLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
           (w 257) (w 1027) (w 1794) (w 1795) (w 1796)
      ++ R4 w := by
  have hx : wireBlock w 0 258=wireBlock w 0 254++[w 254,w 255,w 256,w 257] := by
    rw [←wireBlock_append w 0 254 4]; rfl
  have hy : wireBlock w 770 258=wireBlock w 770 254++[w 1024,w 1025,w 1026,w 1027] := by
    rw [←wireBlock_append w 770 254 4]; rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 254++[w 1794,w 1795,w 1796] := by
    rw [←wireBlock_append w 1540 254 3]; rfl
  have lastBlock : wireBlock w 1540 254 = wireBlock w 1540 253 ++ [w 1793] := by
    rw [←wireBlock_append w 1540 253 1]; rfl
  have last : lastCarry (wireBlock w 1540 254) (w 1797)=w 1793 := by
    rw [lastBlock,lastCarry_cat4]; rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [P4,R4,last] using add_split4
    (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254)
    (w 1797) (w 254) (w 255) (w 256) (w 257) (w 1024) (w 1025) (w 1026) (w 1027)
    (w 1794) (w 1795) (w 1796)
    (by simp [wireBlock_length]) (by simp [wireBlock_length])

def zero4KAdd (w : Nat→Wire) : Program :=
  P4 w ++ newLeaf4At (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027)
    ++ R4 w

/-- Counts: the four-bit zero replacement costs 254 Toffolis, three fewer than the literal. -/
theorem zero4_counts (w : Nat→Wire)
    (hlit : toffoliCount (literalKAdd w)=257 ∧ measurementCount (literalKAdd w)=257) :
    toffoliCount (zero4KAdd w)=254 ∧ measurementCount (zero4KAdd w)=257 := by
  have hs := literal_split4 w
  have ho := old4_counts (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026)
    (w 257) (w 1027) (w 1794) (w 1795) (w 1796)
  have hn := new4_counts (w 254) (w 1024) (w 1793) (w 255) (w 1025) (w 256) (w 1026) (w 257) (w 1027)
  rw [hs] at hlit
  simp only [toffoliCount_append, measurementCount_append, ho.1, ho.2] at hlit
  simp only [zero4KAdd, toffoliCount_append, measurementCount_append, hn.1, hn.2]
  omega

#print axioms zero4_counts

/-! ### Side conditions for `whole_zero4` at the KAdd indices -/

theorem low_avoid4 (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) :
    w i ∉ spinePorts (wireBlock w 0 254) (wireBlock w 770 254) (wireBlock w 1540 254) (w 1797) := by
  intro h
  simp only [spinePorts,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h
  · have e:=hinj h; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega
  · obtain ⟨j,hj,hji⟩:=List.mem_map.mp h
    have e:=hinj hji; subst j
    simp only [List.mem_range'_1] at hj; omega

attribute [local irreducible] ECDSAAdd.wires in
theorem P4_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) : w i∉wires (P4 w) := by
  intro h
  exact low_avoid4 w hinj i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section R4SupportOpaque
attribute [local irreducible] ECDSAAdd.wires
theorem R4_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1794 ∨ i=1795 ∨ i=1796 ∨ i=1025 ∨ i=1026 ∨ i=1027) : w i∉wires (R4 w) := by
  intro h
  have support := suffix_support (wireBlock w 0 254) (wireBlock w 770 254)
    (wireBlock w 1540 254) (w 1797)
  exact low_avoid4 w hinj i hi (List.mem_toFinset.mp (support h))
end R4SupportOpaque

theorem tail4_nd (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 254,w 1024,w 1793,w 255,w 1025,w 256,w 1026,w 257,w 1027,w 1794,w 1795,w 1796].Nodup :=
  List.Nodup.map hinj
    (by decide : [254,1024,1793,255,1025,256,1026,257,1027,1794,1795,1796].Nodup)

#print axioms P4_avoid
#print axioms R4_avoid
#print axioms tail4_nd

/-! ### Extracting the three zero output bits from the word value -/

theorem bit255_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^255%2=flag.toNat) :
    s (w 1025)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 255 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 255 0=w 1025 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1025) <;> cases flag <;> simp [hs] at h ⊢

/-- For the exit caller the word is `Y/2 < 2^255`, so ALL THREE high bits vanish. -/
theorem exit_three_zero (w : Nat→Wire) (s : BasisState) (W : Nat) (hW : W<2^255)
    (postWord : regValue (wireBlock w 770 258) s=W) :
    s (w 1025)=false ∧ s (w 1026)=false ∧ s (w 1027)=false := by
  have d5 : W/2^255=0 := Nat.div_eq_of_lt hW
  have h255 : W/2^255%2=(false : Bool).toNat := by rw [d5]; rfl
  exact ⟨bit255_from_div w s W false postWord h255,
    (Verifier.Leaf3.exit_two_zero w s W hW postWord).1,
    (Verifier.Leaf3.exit_two_zero w s W hW postWord).2⟩

#print axioms bit255_from_div
#print axioms exit_three_zero

end Verifier.Leaf4
