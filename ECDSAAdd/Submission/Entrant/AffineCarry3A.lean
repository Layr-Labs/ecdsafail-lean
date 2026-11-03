import ECDSAAdd.Submission.Entrant.KAddCallerStructureDraft
import ECDSAAdd.Submission.Entrant.E1CallerValueFactsDraft
import ECDSAAdd.Arithmetic.DisjointPrograms

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option linter.unusedVariables false

namespace Verifier.Leaf3
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge

/-- The three-bit terminal suffix: two retired clean carries `z`, `z'`. -/
def oldLeaf3At (a b c A B A' B' z z' : Wire) : Program :=
  addInPlace [a,A,A'] [b,B,B'] [z,z'] c

/-- Mirror of the two-bit leaf, for the nesting check. -/
def oldLeafAt (a b c A B z : Wire) : Program :=
  majority a b c z ++ [.CX A B,.CX z B] ++ eraseCarry a b c z ++ [.CX a b,.CX c b]

/-- Zero-Toffoli replacement. Order is load-bearing: B' is measured while B is live. -/
def newLeaf3At (a b c A B A' B' : Wire) : Program :=
  [.measureX B' [] [.Z A, .Z B, .Z A', .CZ A B],
   .measureX B  [] [.Z A, .CZ a b, .CZ a c, .CZ b c],
   .CX a b, .CX c b]

/-- Output bits 256 and 257 of the sum are zero. Bit 255 is not needed. -/
def Ready3 (a b c A B A' B' : Wire) (s : BasisState) : Prop :=
  ((s A ^^ s B) ^^ carryBit (s a) (s b) (s c)) = false ∧
  ((s A' ^^ s B') ^^
     carryBit (s A) (s B) (carryBit (s a) (s b) (s c))) = false

-- structural checks
theorem old3_unfold (a b c A B A' B' z z' : Wire) :
    oldLeaf3At a b c A B A' B' z z'
      = majority a b c z ++ oldLeafAt A B z A' B' z'
        ++ eraseCarry a b c z ++ [.CX a b,.CX c b] := by rfl

theorem old3_counts (a b c A B A' B' z z' : Wire) :
    toffoliCount (oldLeaf3At a b c A B A' B' z z') = 2 ∧
    measurementCount (oldLeaf3At a b c A B A' B' z z') = 2 := by
  exact ⟨rfl, rfl⟩

theorem new3_counts (a b c A B A' B' : Wire) :
    toffoliCount (newLeaf3At a b c A B A' B') = 0 ∧
    measurementCount (newLeaf3At a b c A B A' B') = 2 := by
  exact ⟨rfl, rfl⟩


/-- Common final state: `b` holds the low sum, both high outputs are zeroed,
phase is untouched. -/
private def post3 (a b c B B' : Wire) (s : State) : State :=
  ⟨s.phase,
   writeBit (writeBit (writeBit s.basis B' false) B false) b
     (sumBit (s.basis a) (s.basis b) (s.basis c))⟩

/-- Boolean value a correction list contributes to the phase. -/
def cval : List Correction → BasisState → Bool
  | [], _ => false
  | .Z t :: cs, f => f t ^^ cval cs f
  | .CZ x y :: cs, f => (f x && f y) ^^ cval cs f

private theorem correct_eq (cs : List Correction) (s : State) :
    correct cs s = ⟨s.phase ^^ cval cs s.basis, s.basis⟩ := by
  induction cs generalizing s with
  | nil => simp [correct,cval]
  | cons d cs ih =>
    cases d <;>
      simp [correct,cval,ih,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

/-- A measurement whose correction list reproduces the measured value on the
post-zeroing basis leaves the phase untouched, for either outcome. -/
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

theorem new3_run (a b c A B A' B' : Wire) (nd : [a,b,c,A,B,A',B'].Nodup)
    (s : State) (m : List Bool) (ready : Ready3 a b c A B A' B' s.basis) :
    run (newLeaf3At a b c A B A' B') m s = post3 a b c B B' s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB'⟩,⟨hbc,hbA,hbB,hbA',hbB'⟩,
    ⟨hcA,hcB,hcA',hcB'⟩,⟨hAB,hAA',hAB'⟩,⟨hBA',hBB'⟩,hA'B'⟩ := nd
  obtain ⟨r1,r2⟩ := ready
  have h1 : s.basis B' = cval [.Z A,.Z B,.Z A',.CZ A B] (writeBit s.basis B' false) := by
    simp only [cval,writeBit,Function.update_of_ne hAB',Function.update_of_ne hBB',
      Function.update_of_ne hA'B',Bool.xor_false]
    revert r1 r2
    simp only [carryBit]
    cases s.basis a <;> cases s.basis b <;> cases s.basis c <;>
      cases s.basis A <;> cases s.basis B <;> cases s.basis A' <;>
      cases s.basis B' <;> decide
  have e1 := meas_clean B' [.Z A,.Z B,.Z A',.CZ A B] s m h1
  have h2 : (⟨s.phase,writeBit s.basis B' false⟩ : State).basis B
      = cval [.Z A,.CZ a b,.CZ a c,.CZ b c]
          (writeBit (⟨s.phase,writeBit s.basis B' false⟩ : State).basis B false) := by
    simp only [cval,writeBit,Function.update_of_ne hAB,Function.update_of_ne hAB',
      Function.update_of_ne haB,Function.update_of_ne haB',
      Function.update_of_ne hbB,Function.update_of_ne hbB',
      Function.update_of_ne hcB,Function.update_of_ne hcB',
      Function.update_of_ne hBB',Bool.xor_false]
    revert r1
    simp only [carryBit]
    cases s.basis a <;> cases s.basis b <;> cases s.basis c <;>
      cases s.basis A <;> cases s.basis B <;> decide
  have e2 := meas_clean B [.Z A,.CZ a b,.CZ a c,.CZ b c] ⟨s.phase,writeBit s.basis B' false⟩
    (m.drop (measurementCount [Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]])) h2
  show run ([Instr.measureX B' [] [.Z A,.Z B,.Z A',.CZ A B]]
      ++ ([Instr.measureX B [] [.Z A,.CZ a b,.CZ a c,.CZ b c]] ++ [.CX a b,.CX c b])) m s
    = post3 a b c B B' s
  rw [run_cat,e1,run_cat,e2,cx2 a c b hab (Ne.symm hbc)]
  refine st_eq rfl (fun w => ?_)
  simp only [post3,writeBit,
    Function.update_of_ne haB,Function.update_of_ne haB',
    Function.update_of_ne hbB,Function.update_of_ne hbB',
    Function.update_of_ne hcB,Function.update_of_ne hcB',sumBit]
  by_cases hw : w = b
  · subst w
    simp only [Function.update_self]
    exact Bool.xor_comm _ _ ▸ (by
      cases s.basis a <;> cases s.basis b <;> cases s.basis c <;> decide)
  · simp only [Function.update_of_ne hw]

theorem old3_run (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup)
    (s : State) (m : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false) :
    run (oldLeaf3At a b c A B A' B' z z') m s =
      ⟨s.phase,
       writeBit (writeBit (writeBit (writeBit (writeBit s.basis
         z' (carryBit (s.basis A) (s.basis B)
               (carryBit (s.basis a) (s.basis b) (s.basis c))))
         B' ((s.basis B' ^^ s.basis A') ^^
               carryBit (s.basis A) (s.basis B)
                 (carryBit (s.basis a) (s.basis b) (s.basis c))))
         z' false)
         B ((s.basis B ^^ s.basis A) ^^
               carryBit (s.basis a) (s.basis b) (s.basis c)))
         b (sumBit (s.basis a) (s.basis b) (s.basis c))⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haz,haz'⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbz,hbz'⟩,
          ⟨hcA,hcB,hcA',hcB',hcz,hcz'⟩,
          ⟨hAB,hAA',hAB',hAz,hAz'⟩,
          ⟨hBA',hBB',hBz,hBz'⟩,
          ⟨hA'B',hA'z,hA'z'⟩,
          ⟨hB'z,hB'z'⟩,hzz'⟩ := nd
  set K := carryBit (s.basis a) (s.basis b) (s.basis c) with hK
  set K' := carryBit (s.basis A) (s.basis B) K with hK'
  show run (majority a b c z ++ (majority A B z z' ++ ([Instr.CX A' B',.CX z' B'] ++
      (eraseCarry A B z z' ++ ([Instr.CX A B,.CX z B] ++
      (eraseCarry a b c z ++ [Instr.CX a b,.CX c b])))))) m s = _
  have n1 : [a,b,c,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]; exact ⟨⟨hab,hac,haz⟩,⟨hbc,hbz⟩,hcz⟩
  have n2 : [A,B,z,z'].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]; exact ⟨⟨hAB,hAz,hAz'⟩,⟨hBz,hBz'⟩,hzz'⟩
  rw [run_cat,majority_correct a b c z n1]
  simp only [cz,Bool.false_xor,←hK]
  rw [run_cat,majority_correct A B z z' n2]
  simp only [writeBit,Function.update_of_ne hAz,Function.update_of_ne hBz,
    Function.update_self,Function.update_of_ne (Ne.symm hzz'),cz',Bool.false_xor,←hK']
  rw [run_cat,cx2 A' z' B' hA'B' (Ne.symm hB'z')]
  simp only [writeBit,Function.update_of_ne hA'z,Function.update_of_ne (Ne.symm hA'z'),
    Function.update_self,Function.update_of_ne hB'z,Function.update_of_ne hB'z']
  rw [run_cat,eraseCarry_correct A B z z' hAz' hBz' hzz' _ (by
    simp only [writeBit,
      Function.update_of_ne (Ne.symm hB'z'),Function.update_self,
      Function.update_of_ne hAB',Function.update_of_ne hAz',Function.update_of_ne hAz,
      Function.update_of_ne hBB',Function.update_of_ne hBz',Function.update_of_ne hBz,
      Function.update_of_ne (Ne.symm hB'z),Function.update_of_ne hzz',←hK'])]
  rw [run_cat,cx2 A z B hAB (Ne.symm hBz)]
  rw [run_cat,eraseCarry_correct a b c z haz hbz hcz _ (by
    simp only [writeBit,
      Function.update_of_ne (Ne.symm hBz),Function.update_of_ne hzz',
      Function.update_of_ne (Ne.symm hB'z),Function.update_self,
      Function.update_of_ne haB,Function.update_of_ne haz',Function.update_of_ne haB',
      Function.update_of_ne haz,
      Function.update_of_ne hbB,Function.update_of_ne hbz',Function.update_of_ne hbB',
      Function.update_of_ne hbz,
      Function.update_of_ne hcB,Function.update_of_ne hcz',Function.update_of_ne hcB',
      Function.update_of_ne hcz,←hK])]
  rw [cx2 a c b hab (Ne.symm hbc)]
  have q1 := Ne.symm hB'z; have q2 := Ne.symm hBz; have q3 := Ne.symm hzz'
  have q4 := Ne.symm hbz; have q5 := Ne.symm hB'z'; have q6 := Ne.symm hBz'
  have q7 := Ne.symm hbz'; have q8 := Ne.symm hbB; have q9 := Ne.symm hbB'
  have q10 := Ne.symm hA'z; have q11 := Ne.symm hA'z'; have q12 := Ne.symm hAz
  have q13 := Ne.symm hAz'; have q14 := Ne.symm haz; have q15 := Ne.symm haz'
  have q16 := Ne.symm hcz; have q17 := Ne.symm hcz'; have q18 := Ne.symm haB
  have q19 := Ne.symm haB'; have q20 := Ne.symm hcB; have q21 := Ne.symm hcB'
  have q22 := Ne.symm hAB'; have q23 := Ne.symm hA'B'; have q24 := Ne.symm hBA'
  have q25 := Ne.symm hAA'; have q26 := Ne.symm hAB; have q27 := Ne.symm hBB'
  refine st_eq rfl (fun w => ?_)
  by_cases hwz : w = z <;> by_cases hwb : w = b <;>
    by_cases hwB : w = B <;> by_cases hwB' : w = B' <;> by_cases hwz' : w = z' <;>
    subst_vars <;>
    simp_all [writeBit,Function.update,sumBit,
      Bool.xor_comm,Bool.xor_assoc,Bool.xor_left_comm]

/-- **Main result.** On the restriction that output bits 256 and 257 are zero,
the two-Toffoli three-bit leaf and the zero-Toffoli replacement agree as complete
States — phase included — for arbitrary and independent measurement records. -/
theorem full_state3 (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup) (s : State) (m n : List Bool)
    (cz : s.basis z = false) (cz' : s.basis z' = false)
    (ready : Ready3 a b c A B A' B' s.basis) :
    run (oldLeaf3At a b c A B A' B' z z') m s
      = run (newLeaf3At a b c A B A' B') n s := by
  have nd7 : [a,b,c,A,B,A',B'].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd ⊢
    tauto
  rw [old3_run a b c A B A' B' z z' nd s m cz cz',
      new3_run a b c A B A' B' nd7 s n ready]
  obtain ⟨r1,r2⟩ := ready
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haz,haz'⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbz,hbz'⟩,
          ⟨hcA,hcB,hcA',hcB',hcz,hcz'⟩,
          ⟨hAB,hAA',hAB',hAz,hAz'⟩,
          ⟨hBA',hBB',hBz,hBz'⟩,
          ⟨hA'B',hA'z,hA'z'⟩,
          ⟨hB'z,hB'z'⟩,hzz'⟩ := nd
  have v2 : (s.basis B ^^ s.basis A) ^^
      carryBit (s.basis a) (s.basis b) (s.basis c) = false := by
    simpa [Bool.xor_comm] using r1
  have v1 : (s.basis B' ^^ s.basis A') ^^
      carryBit (s.basis A) (s.basis B)
        (carryBit (s.basis a) (s.basis b) (s.basis c)) = false := by
    simpa [Bool.xor_comm] using r2
  have q5 := Ne.symm hB'z'; have q7 := Ne.symm hbz'; have q6 := Ne.symm hBz'
  have q8 := Ne.symm hbB; have q9 := Ne.symm hbB'; have q27 := Ne.symm hBB'
  refine st_eq rfl (fun w => ?_)
  by_cases hwz' : w = z' <;> by_cases hwb : w = b <;>
    by_cases hwB : w = B <;> by_cases hwB' : w = B' <;>
    subst_vars <;>
    simp_all [writeBit,Function.update,post3,v1,v2]

/-! ### Wrapper: substitution inside a surrounding program. -/

/-- The two high output bits of the whole program determine `Ready3` at the leaf boundary. -/
theorem prefix_leaf3_high (P R : Program) (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hBR : B∉wires R) (hB'R : B'∉wires R)
    (topB  : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B = false)
    (topB' : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B' = false) :
    Ready3 a b c A B A' B' (run P m s).basis := by
  have nd' := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd'
  obtain ⟨⟨hab,hac,haA,haB,haA',haB',haz,haz'⟩,
          ⟨hbc,hbA,hbB,hbA',hbB',hbz,hbz'⟩,
          ⟨hcA,hcB,hcA',hcB',hcz,hcz'⟩,
          ⟨hAB,hAA',hAB',hAz,hAz'⟩,
          ⟨hBA',hBB',hBz,hBz'⟩,
          ⟨hA'B',hA'z,hA'z'⟩,
          ⟨hB'z,hB'z'⟩,hzz'⟩ := nd'
  have tz  : (run P [] s).basis z  = false := (run_preserves_outside P [] s z hzP).trans cz
  have tz' : (run P [] s).basis z' = false := (run_preserves_outside P [] s z' hz'P).trans cz'
  have hB0 : (run (oldLeaf3At a b c A B A' B' z z') [] (run P [] s)).basis B = false := by
    have h := topB
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B hBR] at h
    exact h
  have hB'0 : (run (oldLeaf3At a b c A B A' B' z z') [] (run P [] s)).basis B' = false := by
    have h := topB'
    simp only [run_cat, List.drop_nil] at h
    rw [run_preserves_outside R [] _ B' hB'R] at h
    exact h
  rw [old3_run a b c A B A' B' z z' nd (run P [] s) [] tz tz'] at hB0 hB'0
  simp only [writeBit, Function.update] at hB0 hB'0
  simp only [hbB, hBz', hBB', hbB', hB'z', eq_self_iff_true, if_true, if_false,
    Ne.symm hbB, Ne.symm hBz', Ne.symm hBB', Ne.symm hbB', Ne.symm hB'z'] at hB0 hB'0
  have pb : (run P m s).basis = (run P [] s).basis := run_basis_records P s s m [] rfl
  constructor
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A) ((run P [] s).basis B)]; exact hB0
  · rw [pb]; rw [Bool.xor_comm ((run P [] s).basis A') ((run P [] s).basis B')]; exact hB'0

/-- Whole-program zero-top replacement for the THREE-bit leaf: two Toffolis removed. -/
theorem whole_zero3 (P R : Program) (a b c A B A' B' z z' : Wire)
    (nd : [a,b,c,A,B,A',B',z,z'].Nodup) (s : State) (m : List Bool)
    (cz : s.basis z=false) (cz' : s.basis z'=false)
    (hzP : z∉wires P) (hz'P : z'∉wires P) (hBR : B∉wires R) (hB'R : B'∉wires R)
    (topB  : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B = false)
    (topB' : (run (P++oldLeaf3At a b c A B A' B' z z'++R) [] s).basis B' = false) :
    run (P++oldLeaf3At a b c A B A' B' z z'++R) m s
      = run (P++newLeaf3At a b c A B A' B'++R) m s := by
  have tz  : (run P m s).basis z  = false := (run_preserves_outside P m s z hzP).trans cz
  have tz' : (run P m s).basis z' = false := (run_preserves_outside P m s z' hz'P).trans cz'
  have ready := prefix_leaf3_high P R a b c A B A' B' z z' nd s m cz cz' hzP hz'P hBR hB'R topB topB'
  have eqn := full_state3 a b c A B A' B' z z' nd (run P m s)
    (m.drop (measurementCount P)) (m.drop (measurementCount P)) tz tz' ready
  simpa only [run_cat, measurementCount_append,
    (old3_counts a b c A B A' B' z z').2, (new3_counts a b c A B A' B').2,
    List.drop_drop, Nat.add_comm] using
    congrArg (run R ((m.drop (measurementCount P)).drop 2)) eqn

#print axioms prefix_leaf3_high
#print axioms whole_zero3

/-! ### Instantiation at the KAdd indices -/
open ECDSAAdd.Entrant.AdderSpineBridgeResearch ECDSAAdd.Entrant.KAddCallerBridgeResearch

/-- Mirror of `add_split`, peeling THREE bits. -/
theorem add_split3 (xs ys cs : List Wire) (cin a A A' b B B' z z' : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    addInPlace (xs++[a,A,A']) (ys++[b,B,B']) (cs++[z,z']) cin=
      adderPrefix xs ys cs cin
        ++ oldLeaf3At a b (lastCarry cs cin) A B A' B' z z'
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
        have step : addInPlace ((x::xs)++[a,A,A']) ((y::ys)++[b,B,B']) ((c::cs)++[z,z']) cin=
            majority x y cin c++addInPlace (xs++[a,A,A']) (ys++[b,B,B']) (cs++[z,z']) c++
              eraseCarry x y cin c++[.CX x y,.CX cin y] := by
          cases xs <;> cases ys <;> rfl
        rw [step,ih ys cs c hy' hc']
        simp only [adderPrefix,adderSuffix,lastCarry,List.append_assoc]

def P3 (w : Nat→Wire) : Program :=
  adderPrefix (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255) (w 1797)
def R3 (w : Nat→Wire) : Program :=
  adderSuffix (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255) (w 1797)

private theorem lastCarry_cat3 (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs ++ ys) cin = lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => exact ih x

/-- Peel the top THREE bits of the real KAdd adder. -/
theorem literal_split3 (w : Nat→Wire) :
    literalKAdd w = P3 w
      ++ oldLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796)
      ++ R3 w := by
  have hx : wireBlock w 0 258=wireBlock w 0 255++[w 255,w 256,w 257] := by
    rw [←wireBlock_append w 0 255 3]; rfl
  have hy : wireBlock w 770 258=wireBlock w 770 255++[w 1025,w 1026,w 1027] := by
    rw [←wireBlock_append w 770 255 3]; rfl
  have hc : wireBlock w 1540 257=wireBlock w 1540 255++[w 1795,w 1796] := by
    rw [←wireBlock_append w 1540 255 2]; rfl
  have lastBlock : wireBlock w 1540 255 = wireBlock w 1540 254 ++ [w 1794] := by
    rw [←wireBlock_append w 1540 254 1]; rfl
  have last : lastCarry (wireBlock w 1540 255) (w 1797)=w 1794 := by
    rw [lastBlock,lastCarry_cat3]; rfl
  rw [literalKAdd,read_add,hx,hy,hc]
  simpa only [P3,R3,last] using add_split3
    (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255)
    (w 1797) (w 255) (w 256) (w 257) (w 1025) (w 1026) (w 1027) (w 1795) (w 1796)
    (by simp [wireBlock_length]) (by simp [wireBlock_length])

/-- The three-bit zero replacement of the whole KAdd adder: 255 Toffolis. -/
def zero3KAdd (w : Nat→Wire) : Program :=
  P3 w ++ newLeaf3At (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) ++ R3 w


/-- Counts: the three-bit zero replacement costs 255 Toffolis, two fewer than the literal. -/
theorem zero3_counts (w : Nat→Wire)
    (hlit : toffoliCount (literalKAdd w)=257 ∧ measurementCount (literalKAdd w)=257) :
    toffoliCount (zero3KAdd w)=255 ∧ measurementCount (zero3KAdd w)=257 := by
  have hs := literal_split3 w
  have ho := old3_counts (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027) (w 1795) (w 1796)
  have hn := new3_counts (w 255) (w 1025) (w 1794) (w 256) (w 1026) (w 257) (w 1027)
  rw [hs] at hlit
  simp only [toffoliCount_append, measurementCount_append, ho.1, ho.2] at hlit
  simp only [zero3KAdd, toffoliCount_append, measurementCount_append, hn.1, hn.2]
  omega

#print axioms zero3_counts


/-! ### Side conditions for `whole_zero3` at the KAdd indices -/

theorem low_avoid3 (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) :
    w i ∉ spinePorts (wireBlock w 0 255) (wireBlock w 770 255) (wireBlock w 1540 255) (w 1797) := by
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
theorem P3_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) : w i∉wires (P3 w) := by
  intro h
  exact low_avoid3 w hinj i hi (List.mem_toFinset.mp (prefix_support _ _ _ _ h))

section R3SupportOpaque
attribute [local irreducible] ECDSAAdd.wires
theorem R3_avoid (w : Nat→Wire) (hinj : Function.Injective w) (i : Nat)
    (hi : i=1795 ∨ i=1796 ∨ i=1026 ∨ i=1027) : w i∉wires (R3 w) := by
  intro h
  have support := suffix_support (wireBlock w 0 255) (wireBlock w 770 255)
    (wireBlock w 1540 255) (w 1797)
  exact low_avoid3 w hinj i hi (List.mem_toFinset.mp (support h))
end R3SupportOpaque

theorem tail3_nd (w : Nat→Wire) (hinj : Function.Injective w) :
    [w 255,w 1025,w 1794,w 256,w 1026,w 257,w 1027,w 1795,w 1796].Nodup :=
  List.Nodup.map hinj (by decide : [255,1025,1794,256,1026,257,1027,1795,1796].Nodup)

#print axioms P3_avoid
#print axioms R3_avoid
#print axioms tail3_nd


/-! ### Extracting the two zero output bits from the word value (mirrors `top_from_div`) -/

theorem bit256_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^256%2=flag.toNat) :
    s (w 1026)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 256 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 256 0=w 1026 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1026) <;> cases flag <;> simp [hs] at h ⊢

theorem bit257_from_div (w : Nat→Wire) (s : BasisState) (W : Nat) (flag : Bool)
    (postWord : regValue (wireBlock w 770 258) s=W) (hdiv : W/2^257%2=flag.toNat) :
    s (w 1027)=flag := by
  have h:=regValue_bit (wireBlock w 770 258) 257 0 s (by simp [wireBlock_length])
  have port : (wireBlock w 770 258).getD 257 0=w 1027 := by rfl
  rw [port,postWord,hdiv] at h
  cases hs : s (w 1027) <;> cases flag <;> simp [hs] at h ⊢

/-- For the exit caller the word is `Y/2 < 2^255`, so BOTH high bits vanish. -/
theorem exit_two_zero (w : Nat→Wire) (s : BasisState) (W : Nat) (hW : W<2^255)
    (postWord : regValue (wireBlock w 770 258) s=W) :
    s (w 1026)=false ∧ s (w 1027)=false := by
  have l6 : (2:Nat)^255 ≤ 2^256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have l7 : (2:Nat)^255 ≤ 2^257 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have d6 : W/2^256=0 := Nat.div_eq_of_lt (lt_of_lt_of_le hW l6)
  have d7 : W/2^257=0 := Nat.div_eq_of_lt (lt_of_lt_of_le hW l7)
  have h256 : W/2^256%2=(false : Bool).toNat := by rw [d6]; rfl
  have h257 : W/2^257%2=(false : Bool).toNat := by rw [d7]; rfl
  exact ⟨bit256_from_div w s W false postWord h256, bit257_from_div w s W false postWord h257⟩

#print axioms bit256_from_div
#print axioms bit257_from_div
#print axioms exit_two_zero


end Verifier.Leaf3
