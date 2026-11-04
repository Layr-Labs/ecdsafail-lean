import ECDSAAdd.Submission.Entrant.HighOutputFlagDraft
import ECDSAAdd.Arithmetic.MappedSources

/-! Private source-only whole-adder bridge. No full candidate certificate.
The complete program retains its actual majority adderPrefix and measured unwind. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.AdderSpineBridgeResearch
open Arithmetic RecordedQuantum Challenge HighOutputTailStructuredResearch

private theorem cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

/-- Same elementary read-source identity as MainB's public read_add proof.
Reproved here to avoid importing the entire 31 MainB into an isolated probe. -/
theorem read_add (xs ys carry : List Wire) (cin : Wire) :
    mappedAdd (mappedRead xs false) ys carry cin=addInPlace xs ys carry cin := by
  induction xs generalizing ys carry cin with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases xs with
    | nil => cases ys with
      | nil => rfl
      | cons y ys => cases ys <;> rfl
    | cons a' xs =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        cases ys with
        | nil => rfl
        | cons b' ys =>
          cases carry with
          | nil => rfl
          | cons c cs =>
            simp only [mappedRead,List.map_cons,mappedAdd,mappedMajority,
              mappedEraseCarry,mappedSum,Bool.false_eq_true,if_false,addInPlace]
            rw [←ih (b'::ys) cs c]
            rfl

def lastCarry : List Wire → Wire → Wire
  | [],cin => cin
  | z::zs,_ => lastCarry zs z

def adderPrefix : List Wire → List Wire → List Wire → Wire → Program
  | a::as,b::bs,z::zs,cin => majority a b cin z++adderPrefix as bs zs z
  | _,_,_,_ => []

def adderSuffix : List Wire → List Wire → List Wire → Wire → Program
  | a::as,b::bs,z::zs,cin => adderSuffix as bs zs z++eraseCarry a b cin z++[.CX a b,.CX cin b]
  | _,_,_,_ => []

def spinePorts (xs ys cs : List Wire) (cin : Wire) : List Wire := cin::xs++ys++cs

/-- Exact syntax decomposition; no correctness/range assumption is hidden.
The high two-bit leaf is literally the checked oldLeafAt. -/
theorem add_split (xs ys cs : List Wire) (cin a A b B z : Wire)
    (hy : xs.length=ys.length) (hc : xs.length=cs.length) :
    addInPlace (xs++[a,A]) (ys++[b,B]) (cs++[z]) cin=
      adderPrefix xs ys cs cin++oldLeafAt a b (lastCarry cs cin) A B z++adderSuffix xs ys cs cin := by
  induction xs generalizing ys cs cin with
  | nil =>
    have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
    have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
    subst ys;subst cs
    rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have hy' : xs.length=ys.length := by simpa using hy
        have hc' : xs.length=cs.length := by simpa using hc
        have step : addInPlace ((x::xs)++[a,A]) ((y::ys)++[b,B]) ((c::cs)++[z]) cin=
            majority x y cin c++addInPlace (xs++[a,A]) (ys++[b,B]) (cs++[z]) c++
              eraseCarry x y cin c++[.CX x y,.CX cin y] := by
          cases xs <;> cases ys <;> rfl
        rw [step,ih ys cs c hy' hc']
        simp only [adderPrefix,adderSuffix,lastCarry,List.append_assoc]

theorem prefix_support (xs ys cs : List Wire) (cin : Wire) :
    wires (adderPrefix xs ys cs cin)⊆(spinePorts xs ys cs cin).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => simp [adderPrefix,wires]
  | cons a as ih =>
    cases ys with
    | nil => simp [adderPrefix,wires]
    | cons b bs =>
      cases cs with
      | nil => simp [adderPrefix,wires]
      | cons z zs =>
        intro q hq
        simp only [adderPrefix,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · simp only [majority,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
            Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
          simp only [spinePorts,List.mem_toFinset,List.mem_cons,List.mem_append]
          tauto
        · have h := ih bs zs z hq
          simp only [spinePorts,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          tauto

theorem suffix_support (xs ys cs : List Wire) (cin : Wire) :
    wires (adderSuffix xs ys cs cin)⊆(spinePorts xs ys cs cin).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => simp [adderSuffix,wires]
  | cons a as ih =>
    cases ys with
    | nil => simp [adderSuffix,wires]
    | cons b bs =>
      cases cs with
      | nil => simp [adderSuffix,wires]
      | cons z zs =>
        intro q hq
        simp only [adderSuffix,wires_append,Finset.mem_union] at hq
        rcases hq with (hq|hq)|hq
        · have h := ih bs zs z hq
          simp only [spinePorts,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          tauto
        · simp only [eraseCarry,wires,Instr.wires,correctionWires,Finset.mem_union,
            Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
          simp only [spinePorts,List.mem_toFinset,List.mem_cons,List.mem_append]
          tauto
        · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
            Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
          simp only [spinePorts,List.mem_toFinset,List.mem_cons,List.mem_append]
          tauto

/-- Only the old leaf's high output is exposed; majority_correct restores its
inputs, and its measured/lower adderSuffix does not touch B. No tape cases occur. -/
theorem old_high (a b c A B z : Wire) (nd : [a,b,c,A,B,z].Nodup)
    (s : State) (m : List Bool) (clean : s.basis z=false) :
    (run (oldLeafAt a b c A B z) m s).basis B=
      ((s.basis B^^s.basis A)^^carryBit (s.basis a) (s.basis b) (s.basis c)) := by
  have nd4 : [a,b,c,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd ⊢
    tauto
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  let K := carryBit (s.basis a) (s.basis b) (s.basis c)
  let t : State := ⟨s.phase,writeBit s.basis z K⟩
  have first (tape : List Bool) : run (majority a b c z) tape s=t := by
    rw [majority_correct a b c z nd4]
    simp only [t,K,clean,Bool.false_xor]
  have away : B∉wires (eraseCarry a b c z++[.CX a b,.CX c b]) := by
    simp_all [eraseCarry,wires,Instr.wires,correctionWires,ne_comm]
  have regroup : oldLeafAt a b c A B z =
      (majority a b c z ++ [.CX A B,.CX z B]) ++
        (eraseCarry a b c z ++ [.CX a b,.CX c b]) := by
    simp only [oldLeafAt,List.append_assoc]
  rw [regroup,cat,run_preserves_outside _ _ _ B away,cat,first]
  simp_all [run,t,K,writeBit,Function.update,ne_comm]

/-- Move a proved whole-adder high-output value back to the actual leaf
boundary, for an arbitrary adderPrefix tape. Basis behavior is record-independent,
while the complete-State replacement below retains the original tape model. -/
theorem prefix_leaf_high (P R : Program) (a b c A B z : Wire)
    (nd : [a,b,c,A,B,z].Nodup) (s : State) (m : List Bool) (value : Bool)
    (clean : s.basis z=false) (hzP : z∉wires P) (hBR : B∉wires R)
    (top : (run (P++oldLeafAt a b c A B z++R) [] s).basis B=value) :
    let t:=run P m s
    ((t.basis B^^t.basis A)^^carryBit (t.basis a) (t.basis b) (t.basis c))=value := by
  let t:=run P m s
  let t0:=run P [] s
  have tc : t.basis z=false := (run_preserves_outside P m s z hzP).trans clean
  have top0 : (run (oldLeafAt a b c A B z) [] t0).basis B=value := by
    have h:=top
    simp only [cat,List.drop_nil] at h
    rw [run_preserves_outside R [] _ B hBR] at h
    exact h
  have pb : t.basis=t0.basis := run_basis_records P s s m [] rfl
  have lb := run_basis_records (oldLeafAt a b c A B z) t t0 [] [] pb
  have high := (congrArg (fun bits : BasisState => bits B) lb).trans top0
  rw [old_high a b c A B z nd t [] tc] at high
  exact high

/-- Whole-State, same-record-ordinal zero-top replacement under a proved
whole-program high bit. Prefix, unwind and all other syntax remain literal. -/
theorem whole_zero (P R : Program) (a b c A B z : Wire)
    (nd : [a,b,c,A,B,z].Nodup) (s : State) (m : List Bool)
    (clean : s.basis z=false) (hzP : z∉wires P) (hBR : B∉wires R)
    (top : (run (P++oldLeafAt a b c A B z++R) [] s).basis B=false) :
    run (P++oldLeafAt a b c A B z++R) m s=
      run (P++newLeafAt false a b c A B++R) m s := by
  let t:=run P m s
  have tc : t.basis z=false := (run_preserves_outside P m s z hzP).trans clean
  have hi:=prefix_leaf_high P R a b c A B z nd s m false clean hzP hBR top
  have ready : ReadyAt false a b c A B t.basis := by
    simpa only [ReadyAt,Bool.false_eq_true,if_false,Bool.xor_comm (t.basis A) (t.basis B)] using hi
  have eqn:=HighOutputTailStructuredResearch.full_state false a b c A B z nd t
    (m.drop (measurementCount P)) (m.drop (measurementCount P)) tc ready
  have co:= (HighOutputTailStructuredResearch.counts false a b c A B z).2.2.1
  have cn:= (HighOutputTailStructuredResearch.counts false a b c A B z).2.2.2
  simpa only [cat,measurementCount_append,co,cn,List.drop_drop,Nat.add_comm,t] using
    congrArg (run R ((m.drop (measurementCount P)).drop 1)) eqn

theorem whole_flag (P R : Program) (flag a b c A B z : Wire)
    (nd : [flag,a,b,c,A,B,z].Nodup) (s : State) (m : List Bool)
    (clean : s.basis z=false) (hzP : z∉wires P) (hfP : flag∉wires P) (hBR : B∉wires R)
    (top : (run (P++oldLeafAt a b c A B z++R) [] s).basis B=s.basis flag) :
    run (P++oldLeafAt a b c A B z++R) m s=
      run (P++HighOutputFlagResearch.newFlagAt flag a b c A B++R) m s := by
  let t:=run P m s
  have tc : t.basis z=false := (run_preserves_outside P m s z hzP).trans clean
  have tf : t.basis flag=s.basis flag := run_preserves_outside P m s flag hfP
  have nd6:= (List.nodup_cons.mp nd).2
  have hi:=prefix_leaf_high P R a b c A B z nd6 s m (s.basis flag) clean hzP hBR top
  have ready : ((t.basis A^^t.basis B)^^carryBit (t.basis a) (t.basis b) (t.basis c))=t.basis flag := by
    simpa only [Bool.xor_comm (t.basis A) (t.basis B)] using hi.trans tf.symm
  have eqn:=HighOutputFlagResearch.top_equals_flag flag a b c A B z nd t
    (m.drop (measurementCount P)) (m.drop (measurementCount P)) tc ready
  have co:= (HighOutputTailStructuredResearch.counts false a b c A B z).2.2.1
  have cn:= (HighOutputFlagResearch.counts flag a b c A B).2.1
  simpa only [cat,measurementCount_append,co,cn,List.drop_drop,Nat.add_comm,t] using
    congrArg (run R ((m.drop (measurementCount P)).drop 1)) eqn

end ECDSAAdd.Entrant.AdderSpineBridgeResearch
