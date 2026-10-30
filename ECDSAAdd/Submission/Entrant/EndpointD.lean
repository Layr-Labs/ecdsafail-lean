import ECDSAAdd.Submission.Entrant.MainBasis
set_option Elab.async false

-- ENDPOINT COMPONENT EndpointCheck.lean
-- ===== EndpointKnownCarry =====
/-! Divide endpoint: its output equals the source word, so every unnormalize carry is the
XOR of the current bit, the known magnitude bit and the literal bit (CNOTs, no Toffoli). -/
section
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EndKnown
open ECDSAAdd.Arithmetic

/-- Carry copied from the known output bit `z'` (and the output sign `sg`). -/
def carryK (x' z' sg cout : Wire) (bit : Bool) : Program :=
  [.CX x' cout,.CX z' cout,.CX sg cout]++(if bit then [.X cout] else [])

/-- Literal adder whose carries are copied from a known output word. -/
def addK : List Wire → List Wire → List Wire → Wire → Wire → Wire → Nat → Program
  | x::x'::xs,_::z'::zs,c::cs,sg,cin,one,k =>
      literalConstSum (decide (k%2=1)) x cin++carryK x' z' sg c (decide ((k/2)%2=1))++
        addK (x'::xs) (z'::zs) cs sg c one (k/2)++literalConstErase (decide (k%2=1)) x cin c one
  | [x],_,_,_,cin,_,k => literalConstSum (decide (k%2=1)) x cin
  | _,_,_,_,_,_,_ => []

theorem regValue_xor (zs : List Wire) (b : BasisState) (c : Bool) :
    regValue zs (fun q => b q ^^ c)=if c then 2^zs.length-1-regValue zs b else regValue zs b := by
  induction zs with
  | nil => cases c <;> simp [regValue]
  | cons z zs ih =>
    have lt := regValue_lt zs b
    change (if (b z ^^ c) then 1 else 0)+2*regValue zs (fun q => b q ^^ c)=
      if c then 2^(zs.length+1)-1-((if b z then 1 else 0)+2*regValue zs b)
      else (if b z then 1 else 0)+2*regValue zs b
    rw [ih]
    cases c <;> cases b z <;> simp [pow_succ] <;> omega

private theorem split2 (k : Nat) : (decide (k%2=1)).toNat+2*(k/2)=k := by
  have h := Nat.mod_add_div k 2
  have hm := Nat.mod_lt k (by decide : 0<2)
  by_cases ho : k%2=1 <;> simp [ho] <;> omega

theorem carryK_run (x' z' sg cout : Wire) (bit : Bool) (h2 : z'≠cout) (h3 : sg≠cout)
    (s : State) (m : List Bool) :
    run (carryK x' z' sg cout bit) m s=
      ⟨s.phase,writeBit s.basis cout (s.basis cout ^^ (s.basis x' ^^ s.basis z' ^^ s.basis sg ^^ bit))⟩ := by
  cases bit <;> cases hc : s.basis cout <;> cases hx : s.basis x' <;> cases hz : s.basis z' <;>
    cases hs : s.basis sg <;>
    simp only [carryK,List.cons_append,List.nil_append,run,Bool.false_eq_true,if_false,if_true] <;>
    (apply congrArg (State.mk s.phase); funext q; by_cases hq : q=cout <;>
      simp_all [writeBit,Function.update])

theorem addK_measurements : ∀ (xs zs carry : List Wire) (sg cin one : Wire) (k : Nat),
    zs.length=xs.length →
    measurementCount (addK xs zs carry sg cin one k)=measurementCount (literalConstAdd xs carry cin one k) ∧
    toffoliCount (addK xs zs carry sg cin one k)=0
  | [],_,_,_,_,_,_,_ => by simp [addK,literalConstAdd,measurementCount,toffoliCount]
  | [x],_,_,_,cin,_,k,_ => by
      cases h : decide (k%2=1) <;> simp [addK,literalConstAdd,literalConstSum,h,measurementCount,toffoliCount]
  | x::x'::xs,[],_,_,_,_,_,hz => by simp at hz
  | x::x'::xs,[_],_,_,_,_,_,hz => by simp at hz
  | x::x'::xs,_::_::_,[],_,_,_,_,_ => by simp [addK,literalConstAdd,measurementCount,toffoliCount]
  | x::x'::xs,z::z'::zs,c::cs,sg,cin,one,k,hz => by
      have ih := addK_measurements (x'::xs) (z'::zs) cs sg c one (k/2) (by simpa using hz)
      have cells := literalConstCell_counts (decide (k%2=1)) x cin c one
      have ck : measurementCount (carryK x' z' sg c (decide ((k/2)%2=1)))=0 ∧
          toffoliCount (carryK x' z' sg c (decide ((k/2)%2=1)))=0 := by
        cases decide ((k/2)%2=1) <;> simp [carryK,measurementCount,toffoliCount]
      have e1 : addK (x::x'::xs) (z::z'::zs) (c::cs) sg cin one k=
          literalConstSum (decide (k%2=1)) x cin++carryK x' z' sg c (decide ((k/2)%2=1))++
            addK (x'::xs) (z'::zs) cs sg c one (k/2)++literalConstErase (decide (k%2=1)) x cin c one := rfl
      have e2 : literalConstAdd (x::x'::xs) (c::cs) cin one k=
          literalConstStep (decide (k%2=1)) x cin c++literalConstAdd (x'::xs) cs c one (k/2)++
            literalConstErase (decide (k%2=1)) x cin c one := rfl
      rw [e1,e2]
      simp only [measurementCount_append,toffoliCount_append]
      have sm : measurementCount (literalConstSum (decide (k%2=1)) x cin)=0 ∧
          toffoliCount (literalConstSum (decide (k%2=1)) x cin)=0 := ⟨cells.2.2.2.2.2,cells.2.2.2.2.1⟩
      omega


private theorem carry_fact (a z sg K bit' : Bool) (v B kk : Nat) (n : Nat) (hn : 1 ≤ n)
    (hb : bit'=decide (kk%2=1))
    (h : ((if a then 1 else 0)+2*v+kk+K.toNat)%2^n=(if (z ^^ sg) then 1 else 0)+2*B) :
    K=(a ^^ z ^^ sg ^^ bit') := by
  have d : 2∣2^n := by
    obtain ⟨j,rfl⟩ : ∃ j, n=j+1 := ⟨n-1,by omega⟩
    exact ⟨2^j,by ring⟩
  have h2 := congrArg (fun w => w%2) h
  simp only [Nat.mod_mod_of_dvd _ d] at h2
  subst hb
  have hk := Nat.mod_lt kk (by decide : 0<2)
  cases a <;> cases z <;> cases sg <;> cases K <;> by_cases e : kk%2=1 <;>
    simp [e] at h2 ⊢ <;> omega

theorem addK_eq : ∀ (xs zs carry : List Wire) (sg cin one : Wire) (k : Nat),
    (one::cin::(xs++carry)).Nodup → carry.length+1=xs.length → zs.length=xs.length →
    (∀q∈sg::zs,q∉cin::(xs++carry)) →
    ∀ (s : State) (m : List Bool), (∀q∈carry,s.basis q=false) →
    (regValue xs s.basis+k+(s.basis cin).toNat)%2^xs.length=
      regValue zs (fun q => s.basis q ^^ s.basis sg) →
    run (addK xs zs carry sg cin one k) m s=run (literalConstAdd xs carry cin one k) m s
  | [],_,_,_,_,_,_,_,hc,_,_,_,_,_,_ => by simp at hc
  | [x],_,_,_,cin,_,k,_,_,_,_,_,_,_,_ => by simp [addK,literalConstAdd]
  | x::x'::xs,[],_,_,_,_,_,_,_,hz,_,_,_,_,_ => by simp at hz
  | x::x'::xs,[_],_,_,_,_,_,_,_,hz,_,_,_,_,_ => by simp at hz
  | x::x'::xs,_::_::_,[],_,_,_,_,_,hc,_,_,_,_,_,_ => by simp at hc
  | x::x'::xs,z::z'::zs,c::cs,sg,cin,one,k,hn,hc,hz,hzs,s,m,hclean,hout => by
      have count := List.nodup_iff_count.mp hn
      have nd : [x,cin,c].Nodup := by
        apply List.nodup_iff_count.mpr
        intro q; have hh := count q
        simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
        omega
      have tailND : (one::c::((x'::xs)++cs)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q; have hh := count q
        simp only [List.count_cons,List.count_append] at hh ⊢
        omega
      have nd' := nd
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
        not_or,not_false_eq_true,and_true] at nd'
      obtain ⟨⟨hxi,hxc⟩,hic⟩ := nd'
      have away (q : Wire) (hq : q∈x'::xs) : q≠x ∧ q≠c := by
        have h := count q
        have hp := List.count_pos_iff.mpr hq
        constructor <;> intro e <;> subst e <;>
          simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h hp <;>
          omega
      have caway (q : Wire) (hq : q∈cs) : q≠x ∧ q≠c := by
        have h := count q
        have hp := List.count_pos_iff.mpr hq
        constructor <;> intro e <;> subst e <;>
          simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h hp <;>
          omega
      have zaway (q : Wire) (hq : q∈sg::z'::zs) : q≠x ∧ q≠c := by
        have h := hzs q (by simp only [List.mem_cons] at hq ⊢; tauto)
        exact ⟨fun e => h (by rw [e]; simp),fun e => h (by rw [e]; simp)⟩
      set bit := decide (k%2=1) with hbit
      set bit' := decide ((k/2)%2=1) with hbit'
      set S := sumBit (s.basis x) bit (s.basis cin) with hS
      set K := carryBit (s.basis x) bit (s.basis cin) with hK
      let s1 : State := ⟨s.phase,writeBit (writeBit s.basis x S) c K⟩
      have keep (q : Wire) (hqx : q≠x) (hqc : q≠c) : s1.basis q=s.basis q := by
        simp [s1,writeBit,hqx,hqc]
      -- arithmetic at this bit
      set f : BasisState := fun q => s.basis q ^^ s.basis sg with hf
      have hv := sum_value_step (s.basis x) bit (s.basis cin) (regValue (x'::xs) s.basis) (k/2)
        (x'::xs).length
      rw [← hS,← hK,split2 k] at hv
      have lhs : regValue (x::x'::xs) s.basis=(s.basis x).toNat+2*regValue (x'::xs) s.basis := by
        cases h : s.basis x <;> simp [regValue,h]
      have rhs : regValue (z::z'::zs) f=(f z).toNat+2*regValue (z'::zs) f := by
        cases h : f z <;> simp [regValue,h]
      have hout1 : (regValue (x'::xs) s.basis+k/2+K.toNat)%2^(x'::xs).length=regValue (z'::zs) f := by
        have hs : (S).toNat≤1 := by cases S <;> decide
        have hf1 : (f z).toNat≤1 := by cases f z <;> decide
        have e := hout
        have hl : (x::x'::xs).length=(x'::xs).length+1 := rfl
        rw [lhs,rhs,hl] at e
        omega
      have kfact : K=(s.basis x' ^^ s.basis z' ^^ s.basis sg ^^ bit') := by
        have e := hout1
        have ex : regValue (x'::xs) s.basis=(if s.basis x' then 1 else 0)+2*regValue xs s.basis := rfl
        have ez : regValue (z'::zs) f=(if (s.basis z' ^^ s.basis sg) then 1 else 0)+2*regValue zs f := rfl
        rw [ex,ez] at e
        exact carry_fact (s.basis x') (s.basis z') (s.basis sg) K bit' (regValue xs s.basis)
          (regValue zs f) (k/2) (x'::xs).length (by simp) rfl e
      -- the two first steps agree
      have oldStep (r : List Bool) : run (literalConstStep bit x cin c) r s=s1 :=
        literalConstStep_correct bit x cin c nd s r (hclean c (by simp))
      have newStep (r : List Bool) : run (literalConstSum bit x cin++carryK x' z' sg c bit') r s=s1 := by
        rw [run_append]
        rw [literalConstSum_correct bit x cin hxi]
        have za := zaway z' (by simp)
        have sa := zaway sg (by simp)
        rw [carryK_run x' z' sg c bit' za.2 sa.2]
        have xa := away x' (by simp)
        apply congrArg (State.mk s.phase)
        simp only [writeBit,Function.update_of_ne (Ne.symm hxc),Function.update_of_ne xa.1,
          Function.update_of_ne za.1,Function.update_of_ne sa.1,hclean c (by simp),Bool.false_xor]
        rw [← kfact]
      -- recursive call
      have clean1 : ∀q∈cs,s1.basis q=false := fun q hq =>
        (keep q (caway q hq).1 (caway q hq).2).trans (hclean q (by simp [hq]))
      have reg1 : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
        regValue_congr _ _ _ (fun q hq => keep q (away q hq).1 (away q hq).2)
      have c1 : s1.basis c=K := by simp [s1,writeBit]
      have sg1 : s1.basis sg=s.basis sg := keep sg (zaway sg (by simp)).1 (zaway sg (by simp)).2
      have f1 : regValue (z'::zs) (fun q => s1.basis q ^^ s1.basis sg)=regValue (z'::zs) f := by
        apply regValue_congr
        intro q hq
        have za := zaway q (by simp only [List.mem_cons] at hq ⊢; tauto)
        simp only [f,sg1,keep q za.1 za.2]
      have hzs1 : ∀q∈sg::z'::zs,q∉c::((x'::xs)++cs) := by
        intro q hq hm
        have h := hzs q (by simp only [List.mem_cons] at hq ⊢; tauto)
        apply h
        simp only [List.mem_cons,List.mem_append] at hm ⊢
        tauto
      have ih := addK_eq (x'::xs) (z'::zs) cs sg c one (k/2) tailND (by simpa using hc)
        (by simpa using hz) hzs1 s1
      have mcK := (addK_measurements (x'::xs) (z'::zs) cs sg c one (k/2) (by simpa using hz)).1
      have e1 : addK (x::x'::xs) (z::z'::zs) (c::cs) sg cin one k=
          (literalConstSum bit x cin++carryK x' z' sg c bit')++
            (addK (x'::xs) (z'::zs) cs sg c one (k/2)++literalConstErase bit x cin c one) := by
        simp only [addK,List.append_assoc]; rfl
      have e2 : literalConstAdd (x::x'::xs) (c::cs) cin one k=
          literalConstStep bit x cin c++
            (literalConstAdd (x'::xs) cs c one (k/2)++literalConstErase bit x cin c one) := by
        simp only [literalConstAdd,List.append_assoc]; rfl
      have m0 : measurementCount (literalConstSum bit x cin++carryK x' z' sg c bit')=0 := by
        cases bit <;> cases bit' <;> simp [literalConstSum,carryK,measurementCount]
      have m0' : measurementCount (literalConstStep bit x cin c)=0 :=
        (literalConstCell_counts bit x cin c one).2.1
      have L : run (addK (x::x'::xs) (z::z'::zs) (c::cs) sg cin one k) m s=
          run (addK (x'::xs) (z'::zs) cs sg c one (k/2)++literalConstErase bit x cin c one) m s1 := by
        rw [e1,run_append,m0,newStep,List.drop_zero]
      have R : run (literalConstAdd (x::x'::xs) (c::cs) cin one k) m s=
          run (literalConstAdd (x'::xs) cs c one (k/2)++literalConstErase bit x cin c one) m s1 := by
        rw [e2,run_append,m0',oldStep,List.drop_zero]
      rw [L,R,run_append,run_append,mcK,ih (m.take (measurementCount (literalConstAdd (x'::xs) cs c one (k/2))))
          clean1 (by rw [reg1,c1,f1]; exact hout1)]

theorem eraseCarry_basis (a b cin c : Wire) (r : List Bool) (t : State) (q : Wire) :
    (run (eraseCarry a b cin c) r t).basis q=if q=c then false else t.basis q := by
  cases hm : r.headD false <;> by_cases hq : q=c <;>
    simp [eraseCarry,run,measureAndCorrect,correct_basis,writeBit,Function.update,hq,hm]

/-- Every chain carry is measured last, so the cheap-top comparator leaves them clean. -/
theorem compareChainTop_carry : ∀ (y x carry : List Wire) (cin target : Wire),
    carry.length=y.length → x.length=y.length → carry.Nodup →
    ∀ (s : State) (m : List Bool) (q : Wire), q∈carry →
    (run (TopCarry.compareChainTop x y carry cin target) m s).basis q=false
  | [],_,carry,_,_,hc,_,_,_,_,q,hq => by
      have : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
      subst this; simp at hq
  | _::_,[],_,_,_,_,hx,_,_,_,_,_ => by simp at hx
  | _::_,_::_,[],_,_,_,_,_,_,_,_,hq => by simp at hq
  | b::bs,a::as,c::cs,cin,target,hc,hx,hn,s,m,q,hq => by
      have e : TopCarry.compareChainTop (a::as) (b::bs) (c::cs) cin target=
          (if as=[] then [.X target,.CX target c,.CX c target]
            else majority a b cin c++TopCarry.compareChainTop as bs cs c target)++
            eraseCarry a b cin c := rfl
      rw [e,run_append,eraseCarry_basis]
      by_cases qc : q=c
      · simp [qc]
      · rw [if_neg qc]
        have qs : q∈cs := by simpa [qc] using hq
        by_cases ha : as=[]
        · subst ha
          have : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hx.symm)
          subst this
          have : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst this
          simp at qs
        · rw [if_neg ha,run_append]
          exact compareChainTop_carry bs as cs c target (by simpa using hc) (by simpa using hx)
            (List.nodup_cons.mp hn).2 _ _ q qs

/-- The borrowed-top comparator also measures every spine carry last. -/
theorem compareHeadTop_carry (a b c cin target : Wire) (xs ys cs : List Wire)
    (hc : (cs++[cin]).length=ys.length) (hx : xs.length=ys.length) (hn : (c::(cs++[cin])).Nodup)
    (haway : ∀q∈c::cs,q∉cin::b::ys)
    (s : State) (m : List Bool) (q : Wire) (hq : q∈c::cs) :
    (run (TopCarryBorrow.compareHeadTop a b c cin target xs ys cs) m s).basis q=false := by
  have away : q∉wires (notRegister (cin::b::ys)) := by
    rw [notRegister_wires]
    exact fun h => haway q hq (List.mem_toFinset.mp h)
  have qcin : q≠cin := fun e => haway q hq (by simp [e])
  have e : TopCarryBorrow.compareHeadTop a b c cin target xs ys cs=
      notRegister (cin::b::ys)++(majority a b cin c++[.X cin]++TopCarry.compareChainTop xs ys (cs++[cin]) c target++
        [.X cin]++eraseCarry a b cin c)++notRegister (cin::b::ys) := rfl
  rw [e,run_append,run_preserves_outside _ _ _ _ away,run_append,run_append,eraseCarry_basis]
  by_cases qc : q=c
  · simp [qc]
  · rw [if_neg qc]
    have qs : q∈cs := by simpa [qc] using hq
    have xr (r : List Bool) (t : State) : (run [Instr.X cin] r t).basis q=t.basis q := by
      simp [run,writeBit,Function.update,qcin]
    rw [run_append,xr,run_append]
    exact compareChainTop_carry ys xs (cs++[cin]) c target hc hx (List.nodup_cons.mp hn).2 _ _ q
      (by simp [qs])

/-- The literal adder returns its `One` wire unchanged on every input. -/
theorem literalConstAdd_one : ∀ (xs carry : List Wire) (cin one : Wire) (k : Nat),
    (one::cin::(xs++carry)).Nodup → ∀ (s : State) (m : List Bool),
    (run (literalConstAdd xs carry cin one k) m s).basis one=s.basis one
  | [],_,_,_,_,_,s,m => by simp [literalConstAdd,run]
  | [x],_,cin,one,k,hn,s,m => by
      have ox : one≠x := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
      have oc : one≠cin := fun e => (List.nodup_cons.mp hn).1 (by simp [e])
      by_cases hk : k%2=1 <;> simp [literalConstAdd,literalConstSum,run,writeBit,Function.update,ox,hk]
  | _::_::_,[],_,_,_,_,s,m => by simp [literalConstAdd,run]
  | x::x'::xs,c::cs,cin,one,k,hn,s,m => by
      have count := List.nodup_iff_count.mp hn
      have oa (q : Wire) (hq : q∈[x,cin,c]) : one≠q := by
        intro e; subst e; have h := count one
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
        rcases hq with rfl|rfl|rfl <;>
          simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h <;> omega
      have tailND : (one::c::((x'::xs)++cs)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q; have hh := count q
        simp only [List.count_cons,List.count_append] at hh ⊢
        omega
      have stepAway : one∉wires (literalConstStep (decide (k%2=1)) x cin c) := by
        by_cases hk : k%2=1 <;>
          simp [literalConstStep,literalConstSum,literalConstCarry,wires,Instr.wires,hk,
            oa x (by simp),oa cin (by simp),oa c (by simp)]
      have e : literalConstAdd (x::x'::xs) (c::cs) cin one k=
          literalConstStep (decide (k%2=1)) x cin c++literalConstAdd (x'::xs) cs c one (k/2)++
            literalConstErase (decide (k%2=1)) x cin c one := rfl
      rw [e,run_append,run_append]
      have ih := literalConstAdd_one (x'::xs) cs c one (k/2) tailND
      have oc := oa c (by simp)
      generalize ew : run (literalConstAdd (x'::xs) cs c one (k/2)) _ _=w
      have hw : w.basis one=s.basis one := by
        rw [←ew,ih,run_preserves_outside _ _ _ _ stepAway]
      generalize (List.drop (measurementCount (literalConstStep (decide (k % 2 = 1)) x cin c ++
          literalConstAdd (x' :: xs) cs c one (k / 2))) m)=r
      by_cases hk : k%2=1 <;> cases hm : r.headD false <;>
        simp [literalConstErase,run,measureAndCorrect,correct_basis,writeBit,Function.update,
          Ne.symm oc,oc,hw,hm,hk]

theorem step_carry_mem (bit : Bool) (x cin c : Wire) : c∈wires (literalConstStep bit x cin c) := by
  cases bit <;> simp [literalConstStep,literalConstSum,literalConstCarry,wires,Instr.wires]

theorem head_mem (x : Wire) (xs cs : List Wire) (c one : Wire) (k : Nat) (hc : cs.length+1=(x::xs).length) :
    x∈wires (literalConstAdd (x::xs) cs c one k) := by
  match xs,cs,hc with
  | [],_,_ => by_cases hk : k%2=1 <;> simp [literalConstAdd,literalConstSum,wires,Instr.wires,hk]
  | _::_,d::ds,_ =>
    by_cases hk : k%2=1 <;>
      simp [literalConstAdd,literalConstStep,literalConstSum,wires,Instr.wires,wires_append,hk]
  | _::_,[],hc => simp at hc

theorem addK_wires : ∀ (xs zs carry : List Wire) (sg cin one : Wire) (k : Nat),
    carry.length+1=xs.length →
    wires (addK xs zs carry sg cin one k)⊆wires (literalConstAdd xs carry cin one k)∪(sg::zs).toFinset
  | [],_,_,_,_,_,_,_ => by simp [addK,wires]
  | [x],_,_,_,cin,_,k,_ => by simp only [addK,literalConstAdd]; exact Finset.subset_union_left
  | _::_::_,[],_,_,_,_,_,_ => by simp [addK,wires]
  | _::_::_,[_],_,_,_,_,_,_ => by simp [addK,wires]
  | _::_::_,_::_::_,[],_,_,_,_,hc => by simp at hc
  | x::x'::xs,z::z'::zs,c::cs,sg,cin,one,k,hc => by
      have ih := addK_wires (x'::xs) (z'::zs) cs sg c one (k/2) (by simpa using hc)
      have hx' := head_mem x' xs cs c one (k/2) (by simpa using hc)
      have hcs := step_carry_mem (decide (k%2=1)) x cin c
      have e1 : addK (x::x'::xs) (z::z'::zs) (c::cs) sg cin one k=
          literalConstSum (decide (k%2=1)) x cin++carryK x' z' sg c (decide ((k/2)%2=1))++
            addK (x'::xs) (z'::zs) cs sg c one (k/2)++literalConstErase (decide (k%2=1)) x cin c one := rfl
      have e2 : literalConstAdd (x::x'::xs) (c::cs) cin one k=
          literalConstStep (decide (k%2=1)) x cin c++literalConstAdd (x'::xs) cs c one (k/2)++
            literalConstErase (decide (k%2=1)) x cin c one := rfl
      have sumSub : wires (literalConstSum (decide (k%2=1)) x cin)⊆
          wires (literalConstStep (decide (k%2=1)) x cin c) := by
        simp only [literalConstStep,wires_append]; exact Finset.subset_union_left
      rw [e1,e2]
      intro q hq
      simp only [wires_append,Finset.mem_union,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset] at hq ⊢
      rcases hq with ((h|h)|h)|h
      · exact Or.inl (Or.inl (Or.inl (sumSub h)))
      · have hh : q=x' ∨ q=c ∨ q=z' ∨ q=sg := by
          cases hb : decide ((k/2)%2=1) <;> simp [carryK,wires,Instr.wires,hb] at h <;> tauto
        rcases hh with rfl|rfl|rfl|rfl
        · exact Or.inl (Or.inl (Or.inr hx'))
        · exact Or.inl (Or.inl (Or.inl hcs))
        · exact Or.inr (Or.inr (by simp))
        · exact Or.inr (Or.inl rfl)
      · have h' := ih h
        simp only [Finset.mem_union,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
          List.mem_cons] at h'
        rcases h' with h'|h'|h'|h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (by simp [h']))
        · exact Or.inr (Or.inr (by simp [h']))
      · exact Or.inl (Or.inr h)

open RecordedQuantum in
theorem addK_physical : ∀ (xs zs carry : List Wire) (sg cin one : Wire) (k : Nat),
    (cin::xs++carry).Nodup → (∀q∈sg::zs,q∉carry) → GatePhysical (addK xs zs carry sg cin one k)
  | [],_,_,_,_,_,_,_,_ => by simp [addK,GatePhysical]
  | [x],_,_,_,cin,_,k,hn,_ => by
      have ne : cin≠x := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
      by_cases hk : k%2=1 <;> simp [addK,literalConstSum,GatePhysical,PhysicalInstr,ProperGate,ne,hk]
  | _::_::_,[],_,_,_,_,_,_,_ => by simp [addK,GatePhysical]
  | _::_::_,[_],_,_,_,_,_,_,_ => by simp [addK,GatePhysical]
  | _::_::_,_::_::_,[],_,_,_,_,_,_ => by simp [addK,GatePhysical]
  | x::x'::xs,z::z'::zs,c::cs,sg,cin,one,k,hn,hz => by
      have count := List.nodup_iff_count.mp hn
      have small : [x,cin,c].Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := count w
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
      have tail : (c::(x'::xs)++cs).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := count w
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have x'c : x'≠c := by
        intro e; subst e; have h := count x'
        simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
        omega
      have z'c : z'≠c := fun e => hz z' (by simp) (by simp [e])
      have sgc : sg≠c := fun e => hz sg (by simp) (by simp [e])
      have cells := literalCells_physical (decide (k%2=1)) x cin c one small
      have sumP : GatePhysical (literalConstSum (decide (k%2=1)) x cin) := by
        have h := cells.1
        simp only [literalConstStep,gatePhysical_append] at h
        exact h.1
      have ckP : GatePhysical (carryK x' z' sg c (decide ((k/2)%2=1))) := by
        cases decide ((k/2)%2=1) <;>
          simp [carryK,GatePhysical,PhysicalInstr,ProperGate,x'c,z'c,sgc]
      have recs := addK_physical (x'::xs) (z'::zs) cs sg c one (k/2) tail
        (fun q hq hm => hz q (by simp only [List.mem_cons] at hq ⊢; tauto) (by simp [hm]))
      have e1 : addK (x::x'::xs) (z::z'::zs) (c::cs) sg cin one k=
          literalConstSum (decide (k%2=1)) x cin++carryK x' z' sg c (decide ((k/2)%2=1))++
            addK (x'::xs) (z'::zs) cs sg c one (k/2)++literalConstErase (decide (k%2=1)) x cin c one := rfl
      rw [e1]
      simp only [gatePhysical_append]
      exact ⟨⟨⟨sumP,ckP⟩,recs⟩,cells.2⟩

theorem addK_gateSlots_le : ∀ (xs zs carry : List Wire) (sg cin one : Wire) (k : Nat),
    Challenge.gateSlots (addK xs zs carry sg cin one k)≤12*xs.length
  | [],_,_,_,_,_,_ => by simp [addK]
  | [x],_,_,_,cin,_,k => by
      have h := (Baselines.literalCells_gateSlots_le (decide (k%2=1)) x cin cin cin).2.2
      simpa only [addK,List.length_singleton] using h.trans (by decide : 2 ≤ 12)
  | _::_::_,[],_,_,_,_,_ => by simp [addK]
  | _::_::_,[_],_,_,_,_,_ => by simp [addK]
  | _::_::_,_::_::_,[],_,_,_,_ => by simp [addK]
  | x::x'::xs,z::z'::zs,c::cs,sg,cin,one,k => by
      have ih := addK_gateSlots_le (x'::xs) (z'::zs) cs sg c one (k/2)
      have h := Baselines.literalCells_gateSlots_le (decide (k%2=1)) x cin c one
      have ck : Challenge.gateSlots (carryK x' z' sg c (decide ((k/2)%2=1)))≤4 := by
        cases decide ((k/2)%2=1) <;> simp [carryK,Baselines.gateSlots_cons,Challenge.instructionSlots]
      have e1 : addK (x::x'::xs) (z::z'::zs) (c::cs) sg cin one k=
          literalConstSum (decide (k%2=1)) x cin++carryK x' z' sg c (decide ((k/2)%2=1))++
            addK (x'::xs) (z'::zs) cs sg c one (k/2)++literalConstErase (decide (k%2=1)) x cin c one := rfl
      rw [e1]
      simp only [Challenge.gateSlots_append,List.length_cons] at *
      omega

theorem prepareCompare_away (L : BalancedCleanup.Layout) (hw : L.Widths) (q : Wire)
    (hr : q∉L.r) (hy : q∉L.y) (hs : q≠L.sign) (hl : q≠L.lower) :
    q∉wires (BalancedCleanup.prepareCompare L) := by
  have acS : q∉wires (signComplement L.sign L.y) := by
    intro h; have hh := signComplement_wires_subset L.sign L.y h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact hs h
    · exact hy h
  have acY : q∉wires (signComplement L.lower L.y) := by
    intro h; have hh := signComplement_wires_subset L.lower L.y h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact hl h
    · exact hy h
  have rot : q∉wires (rotateLeft L.r) := by
    rw [(rotate_wires L.r).2,(BalancedCleanup.widths L hw).2.1]
    simpa using hr
  have ar0 : q≠L.r0 := fun e => hr (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
  have arm : q≠L.rmsb := fun e => hr (by simp [BalancedCleanup.Layout.r,e])
  have aym : q≠L.ymsb := fun e => hy (by simp [BalancedCleanup.Layout.y,e])
  simp [BalancedCleanup.prepareCompare,wires_append,wires,Instr.wires,acS,acY,rot,ar0,arm,aym,hs,hl]

end ECDSAAdd.Entrant.EndKnown
end

section
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FifthCarry2
open ECDSAAdd.Arithmetic BalancedCircuit BalancedField

/-- Unnormalize whose carries are copied from a known magnitude word `|Y|`. -/
def unnormalizeE (L : BalancedCleanup.Layout) : Program :=
  [.X L.lower]++EndKnown.addK L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral++[.X L.lower]

def cleanupRestE (L : BalancedCircuit.Layout) : Program :=
  (BalancedCleanup.prepareCompare L.toLayout).reverse++
    (unnormalizeE L.toLayout++(BalancedCleanup.prepareSign L.toLayout).reverse)

def cleanupE (L : BalancedCircuit.Layout) : Program :=
  BalancedCleanup.prepareCompare L.toLayout++TopCarryBorrow.program L++cleanupRestE L

def forwardCoreE (L : BalancedCircuit.Layout) : Program := forwardPrefix L++cleanupE L

/-- Forward kernel for an output already known to equal the source word. -/
def forwardE (L : BalancedCircuit.Layout) : Program := forwardCoreE L++[.measureX L.one [] []]

theorem magnitude_word (L : BalancedCleanup.Layout) (hw : L.Widths) (Y : Int) (hy : Centered Y)
    (u : BasisState) (hyw : regValue L.y u=encodeWord 256 Y) :
    regValue L.ylow (fun q => u q ^^ u L.ymsb)=(magnitude Y).toNat := by
  have mag := BalancedCleanup.magnitude_encoded Y hy
  have hl : L.ylow.length=255 := hw.2.1
  rw [EndKnown.regValue_xor,hl]
  have split : regValue L.y u=regValue L.ylow u+2^255*(if u L.ymsb then 1 else 0) := by
    rw [BalancedCleanup.Layout.y,regValue_append,hl]
    cases hb : u L.ymsb <;> simp [regValue,hb]
  have lt := regValue_lt L.ylow u
  rw [hl] at lt
  have hp := constants
  unfold Centered at hy
  have enc : ((encodeWord 256 Y : Nat) : Int)=if Y<0 then Y+2^256 else Y := by
    unfold encodeWord
    split_ifs with hn
    · have e : Y%((2^256 : Nat) : Int)=Y+2^256 := by
        norm_num at hp ⊢; omega
      rw [e]; norm_num at hp ⊢; omega
    · have e : Y%((2^256 : Nat) : Int)=Y := by
        apply Int.emod_eq_of_lt <;> norm_num at hp ⊢ <;> omega
      rw [e]; omega
  rw [hyw] at split
  by_cases hn : Y<0
  · have neg : negative Y=true := by simp [negative,hn]
    rw [neg,if_pos rfl] at mag
    rw [if_pos hn] at enc
    cases hb : u L.ymsb
    · simp only [hb,Bool.false_eq_true,if_false] at split ⊢
      norm_num at hp; omega
    · simp only [hb,if_true] at split ⊢
      norm_num at hp; omega
  · have pos : negative Y=false := by simp [negative,hn]
    rw [pos] at mag
    simp only [Bool.false_eq_true,if_false] at mag
    rw [if_neg hn] at enc
    cases hb : u L.ymsb
    · simp only [hb,Bool.false_eq_true,if_false] at split ⊢
      norm_num at hp; omega
    · simp only [hb,if_true] at split ⊢
      norm_num at hp; omega

theorem unnormalizeE_eq (L : BalancedCleanup.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (Y : Int) (hy : Centered Y) (u : State) (r : List Bool)
    (hcarry : ∀q∈L.carry.take 254,u.basis q=false)
    (hyw : regValue L.y u.basis=encodeWord 256 Y)
    (hout : (regValue L.low u.basis+BalancedCleanup.positiveLiteral+(!u.basis L.lower).toNat)%2^255=
      (magnitude Y).toNat) :
    run (unnormalizeE L) r u=run (BalancedCleanup.unnormalize L) r u := by
  have w := BalancedCleanup.widths L hw
  have nd := L.normND hn
  have la : L.lower∉L.low := fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])
  have cl (q : Wire) (hq : q∈L.carry) : q≠L.lower := by
    intro e; exact L.flagAway hn L.lower (by simp) (by simp [←e,hq])
  let u' : State := ⟨u.phase,writeBit u.basis L.lower (!u.basis L.lower)⟩
  have yaway (q : Wire) (hq : q∈L.y) : q≠L.lower := fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])
  have hzs : ∀q∈L.ymsb::L.ylow,q∉L.lower::(L.low++L.carry.take 254) := by
    intro q hq hm
    have qy : q∈L.y := by
      simp only [List.mem_cons] at hq
      rcases hq with rfl|h
      · simp [BalancedCleanup.Layout.y]
      · simp [BalancedCleanup.Layout.y,h]
    simp only [List.mem_cons,List.mem_append] at hm
    rcases hm with e|hl|hc
    · exact yaway q qy e
    · have d := List.nodup_append'.mp (L.dataND hn)
      exact List.disjoint_left.mp d.2.2 (show q∈L.r by simp [BalancedCleanup.Layout.r,hl]) (by simp [qy])
    · have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).2.1
      exact List.disjoint_left.mp d.2.2 qy (List.mem_of_mem_take hc)
  have clean' : ∀q∈L.carry.take 254,u'.basis q=false := by
    intro q hq
    simp [u',writeBit,cl q (List.mem_of_mem_take hq),hcarry q hq]
  have low' : regValue L.low u'.basis=regValue L.low u.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u',writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
  have ymag : regValue L.ylow (fun q => u'.basis q ^^ u'.basis L.ymsb)=(magnitude Y).toNat := by
    have yv : regValue L.y u'.basis=encodeWord 256 Y :=
      (regValue_congr _ _ _ (fun q hq => by simp [u',writeBit,yaway q hq])).trans hyw
    exact magnitude_word L hw Y hy u'.basis yv
  have eq := EndKnown.addK_eq L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral nd (by omega) (by rw [hw.2.1,w.1]) hzs u'
  have mc := (EndKnown.addK_measurements L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral (by rw [hw.2.1,w.1])).1
  have first : run [.X L.lower] [] u=u' := rfl
  have e1 : unnormalizeE L=[.X L.lower]++(EndKnown.addK L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
      BalancedCleanup.positiveLiteral++[.X L.lower]) := by simp [unnormalizeE]
  have e2 : BalancedCleanup.unnormalize L=[.X L.lower]++(literalConstAdd L.low (L.carry.take 254) L.lower L.one
      BalancedCleanup.positiveLiteral++[.X L.lower]) := by simp [BalancedCleanup.unnormalize]
  rw [e1,e2,run_append,run_append]
  simp only [show measurementCount [Instr.X L.lower]=0 from rfl,List.take_zero,List.drop_zero]
  rw [first,run_append,run_append,mc,eq _ clean' (by
    rw [low',w.1,ymag]
    simpa [u',writeBit] using hout)]
  all_goals rfl

theorem unnormalize_one (L : BalancedCleanup.Layout) (hn : L.wires.Nodup) (u : State) (r : List Bool) :
    (run (BalancedCleanup.unnormalize L) r u).basis L.one=u.basis L.one := by
  have nd := L.normND hn
  have ol : L.one≠L.lower := fun e => (List.nodup_cons.mp nd).1 (by simp [e])
  simp only [BalancedCleanup.unnormalize,run_append]
  have a := EndKnown.literalConstAdd_one L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.positiveLiteral nd
  simp only [run,writeBit,Function.update_of_ne ol]
  rw [a]
  simp [writeBit,Function.update_of_ne ol]

theorem signComplement_mem (c : Wire) (xs : List Wire) (q : Wire) (hq : q∈xs) :
    q∈wires (signComplement c xs) := by
  induction xs with
  | nil => simp at hq
  | cons a xs ih =>
    simp only [List.mem_cons] at hq
    simp only [signComplement,List.map_cons,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton]
    rcases hq with rfl|h
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (by simpa [signComplement] using ih h)

theorem unnormalize_take_correct (L : BalancedCleanup.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry.take 254,s.basis q=false) :
    let t := run (BalancedCleanup.unnormalize L) m s
    regValue L.low t.basis=(regValue L.low s.basis+BalancedCleanup.positiveLiteral+(!s.basis L.lower).toNat)%2^255 ∧
    ∀q,q∉L.low → t.basis q=s.basis q := by
  let u : State := ⟨s.phase,writeBit s.basis L.lower (!s.basis L.lower)⟩
  have nd := L.normND hn
  have la : L.lower∉L.low := fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])
  have ol : L.one≠L.lower := by
    intro e; exact (List.nodup_cons.mp nd).1 (by simp [e])
  have cl (q : Wire) (hq : q∈L.carry) : q≠L.lower := by
    intro e; exact L.flagAway hn L.lower (by simp) (by simp [←e,hq])
  have clean : ∀q∈L.carry.take 254,u.basis q=false := by
    intro q hq; simp [u,writeBit,cl q (List.mem_of_mem_take hq),hc q hq]
  have hu : regValue L.low u.basis=regValue L.low s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
  have w := BalancedCleanup.widths L hw
  have add := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral
    nd (by omega) u m (by simp [u,writeBit,ol,ho]) clean
  let v := run (literalConstAdd L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral) m u
  have vl : v.basis L.lower=!s.basis L.lower := by rw [add.2.1 L.lower la]; simp [u,writeBit]
  have execute : run (BalancedCleanup.unnormalize L) m s=run [.X L.lower]
      (m.drop (measurementCount (literalConstAdd L.low (L.carry.take 254) L.lower L.one
        BalancedCleanup.positiveLiteral))) v := by
    simp only [BalancedCleanup.unnormalize,List.append_assoc,run_append,run_take,measurementCount,List.drop_zero]
    rfl
  show regValue L.low (run (BalancedCleanup.unnormalize L) m s).basis=_ ∧ _
  rw [execute]
  refine ⟨?_,?_⟩
  · have last (ms : List Bool) : regValue L.low (run [.X L.lower] ms v).basis=regValue L.low v.basis :=
      regValue_congr _ _ _ (fun q hq => by simp [run,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
    rw [last,add.2.2,hu,w.1]
    simp [u,writeBit]
  · intro q hq
    by_cases e : q=L.lower
    · subst q
      have hx (ms : List Bool) : (run [.X L.lower] ms v).basis L.lower=!v.basis L.lower := by
        simp only [run,writeBit,Function.update_self]
      rw [hx,vl]
      simp
    · simp only [run,writeBit,Function.update_of_ne e]
      exact (add.2.1 q hq).trans (by simp [u,writeBit,e])

theorem program_carry (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (q : Wire) (hq : q∈L.carry.take 255) :
    (run (TopCarryBorrow.program L) m s).basis q=false := by
  have w := BalancedCleanup.widths L.toLayout hw
  have cnd : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have all := L.toLayout.allND cnd
  have count := List.nodup_iff_count.mp all
  have clen : (L.carry.take 255).length=255 := by simp [List.length_take,hw.2.2]
  have ylen := w.2.2.1
  have rlen := w.2.1
  have tsub : (L.carry.take 255).Sublist L.carry := List.take_sublist 255 L.carry
  have oneAway : L.one∉L.carry := fun h => L.toLayout.flagAway cnd L.one (by simp) (by simp [h])
  show (run (TopCarryBorrow.compare L.y L.r (L.carry.take 255) L.one L.parity) m s).basis q=false
  generalize ey : L.y=yy at ylen
  generalize er : L.r=rr at rlen
  generalize ec : L.carry.take 255=cc at clen hq tsub
  match yy,rr,cc,ylen,rlen,clen,hq,tsub with
  | a::xs,b::ys,c::cs,ylen,rlen,clen,hq,tsub =>
    have cn : (c::cs).Nodup := tsub.nodup (List.nodup_append'.mp (List.nodup_append'.mp
      (L.toLayout.dataND cnd)).2.1).2.1
    have cOne : L.one∉c::cs := fun h => oneAway (tsub.subset h)
    have hn' : (c::(cs++[L.one])).Nodup := by
      apply List.nodup_iff_count.mpr
      intro t
      have h1 := List.nodup_iff_count.mp cn t
      rw [show c::(cs++[L.one])=(c::cs)++[L.one] from rfl,List.count_append]
      by_cases e : t=L.one
      · have h2 : List.count t (c::cs)=0 := List.count_eq_zero.mpr (e ▸ cOne)
        rw [h2]; simp [e]
      · have h3 : List.count t [L.one]=0 := by simp [List.count_cons,Ne.symm e]
        omega
    have haway : ∀t∈c::cs,t∉L.one::b::ys := by
      intro t ht hm
      have tc : t∈L.carry := tsub.subset ht
      simp only [List.mem_cons] at hm
      rcases hm with e|e|e
      · exact cOne (e ▸ ht)
      · have : t∈L.r := by rw [er]; simp [e]
        exact List.disjoint_left.mp (List.nodup_append'.mp (L.toLayout.dataND cnd)).2.2 this (by simp [tc])
      · have : t∈L.r := by rw [er]; simp [e]
        exact List.disjoint_left.mp (List.nodup_append'.mp (L.toLayout.dataND cnd)).2.2 this (by simp [tc])
    exact EndKnown.compareHeadTop_carry a b c L.one L.parity xs ys cs
      (by simp at clen rlen ⊢; omega) (by simp at ylen rlen ⊢; omega) hn' haway s m q hq
  | [],_,_,ylen,_,_,_,_ => simp at ylen
  | _::_,[],_,_,rlen,_,_,_ => simp at rlen
  | _::_,_::_,[],_,_,clen,_,_ => simp at clen

theorem forwardCoreE_eq (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hyw : regValue L.y s.basis=encodeWord 256 Y)
    (hc : ∀q∈work L,s.basis q=false) (hend : halfResult (rawSum B X Y)=Y) :
    run (forwardCoreE L) m s=run (forwardCore L) m s := by
  have cnd : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have hw' : L.toLayout.Widths := hw
  have w := BalancedCleanup.widths L.toLayout hw
  have old := FifthCarry.forward_correct L hw hn B X Y hx hy s m hs hr hyr hc
  rw [←forwardCore_eq L hw hn B X Y hx hy s m hs hr hyr hc,hend] at old
  let A0 := forwardPrefix L++BalancedCleanup.prepareCompare L.toLayout++TopCarryBorrow.program L
  let PCR := (BalancedCleanup.prepareCompare L.toLayout).reverse
  let U := BalancedCleanup.unnormalize L.toLayout
  let Q := (BalancedCleanup.prepareSign L.toLayout).reverse
  have hF : forwardCore L=(A0++PCR)++(U++Q) := by
    simp only [forwardCore,cleanup,cleanupRest,A0,PCR,U,Q,List.append_assoc]
  have hE : forwardCoreE L=(A0++PCR)++(unnormalizeE L.toLayout++Q) := by
    simp only [forwardCoreE,cleanupE,cleanupRestE,A0,PCR,Q,List.append_assoc]
  have carryAt (m' : List Bool) (s' : State) (q : Wire) (hq : q∈L.carry.take 255) :
      (run (A0++PCR) m' s').basis q=false := by
    have qc : q∈L.carry := List.mem_of_mem_take hq
    have qr : q∉L.r := fun h => List.disjoint_left.mp
      (List.nodup_append'.mp (L.toLayout.dataND cnd)).2.2 h (by simp [qc])
    have qy : q∉L.y := fun h => List.disjoint_left.mp
      (List.nodup_append'.mp (List.nodup_append'.mp (L.toLayout.dataND cnd)).2.1).2.2 h qc
    have qs : q≠L.sign := fun e => L.toLayout.flagAway cnd L.sign (by simp) (by simp [←e,qc])
    have ql : q≠L.lower := fun e => L.toLayout.flagAway cnd L.lower (by simp) (by simp [←e,qc])
    have away : q∉wires PCR := by
      simp only [PCR,wires_reverse]
      exact EndKnown.prepareCompare_away L.toLayout hw q qr qy qs ql
    rw [run_append,run_preserves_outside _ _ _ _ away,run_append]
    exact program_carry L hw hn _ _ q hq
  have sub254 (q : Wire) (hq : q∈L.carry.take 254) : q∈L.carry.take 255 := by
    have e : L.carry.take 254=(L.carry.take 255).take 254 := by simp [List.take_take]
    rw [e] at hq
    exact List.mem_of_mem_take hq
  have tEq0 : run (forwardCore L) m s=run Q (List.drop (measurementCount U)
      (List.drop (measurementCount (A0++PCR)) m))
      (run U (List.take (measurementCount U) (List.drop (measurementCount (A0++PCR)) m))
        (run (A0++PCR) (m.take (measurementCount (A0++PCR))) s)) := by
    rw [hF,run_append,run_append]
  rw [hE,hF,run_append,run_append]
  generalize eu : run (A0++PCR) (m.take (measurementCount (A0++PCR))) s=u at tEq0 ⊢
  generalize em1 : m.drop (measurementCount (A0++PCR))=m1 at tEq0 ⊢
  have uc : ∀q∈L.carry.take 254,u.basis q=false := fun q hq => by
    rw [←eu]; exact carryAt _ _ q (sub254 q hq)
  have tEq := tEq0
  generalize ev : run U (m1.take (measurementCount U)) u=v
  rw [ev] at tEq
  generalize et : run (forwardCore L) m s=t at old tEq
  have oneQ : L.one∉wires Q := by
    simp only [Q,wires_reverse,BalancedCleanup.prepareSign,wires_append]
    intro h
    rcases Finset.mem_union.mp h with h|h
    · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at h
      rcases h with e|e
      · exact L.toLayout.flagAway cnd L.one (by simp) (by simp [e,BalancedCleanup.Layout.r])
      · have nd := L.toLayout.flagsND cnd
        simp at nd; tauto
    · have hh := signComplement_wires_subset L.lower L.r h
      simp only [List.mem_toFinset,List.mem_cons] at hh
      rcases hh with e|e
      · have nd := L.toLayout.flagsND cnd
        simp at nd; tauto
      · exact L.toLayout.flagAway cnd L.one (by simp) (by simp [e])
  have tOne : t.basis L.one=false := old.2.2.1 L.one (by simp [work])
  have vOne : v.basis L.one=false := by
    rw [←tOne,tEq,run_preserves_outside _ _ _ _ oneQ]
  have uOne : u.basis L.one=false := by
    rw [←vOne,←ev]; exact (unnormalize_one L.toLayout cnd u _).symm
  have un := unnormalize_take_correct L.toLayout hw' cnd u (m1.take (measurementCount U)) uOne uc
  rw [ev] at un
  have vt : v=run (BalancedCleanup.prepareSign L.toLayout) [] t := by
    rw [tEq]
    have h := run_reverse_proper Q (properProgram_reverse _ (BalancedCleanup.prepareSign_proper L.toLayout cnd))
      v (m1.drop (measurementCount U)) []
    simpa only [Q,List.reverse_reverse] using h.symm
  have tLower : t.basis L.lower=false := old.2.2.1 L.lower (by simp [work])
  have pv := BalancedCleanup.prepareSign_value L.toLayout hw' cnd Y hy t [] old.2.1 tLower
  rw [←vt] at pv
  have vlow : regValue L.low v.basis=(magnitude Y).toNat := by
    have split := regValue_append L.low [L.rmsb] v.basis
    have hr' : L.low++[L.rmsb]=L.r := rfl
    rw [hr',pv.1,w.1] at split
    have mb := magnitude_bounds Y hy
    have hp := constants
    have lt := regValue_lt [L.rmsb] v.basis
    have cast := Int.toNat_of_nonneg mb.1
    simp only [List.length_singleton,pow_one] at lt
    norm_num at hp
    omega
  have yAway (q : Wire) (hq : q∈L.y) : q∉L.r := fun h => List.disjoint_left.mp
    (List.nodup_append'.mp (L.toLayout.dataND cnd)).2.2 h (by simp [hq])
  have yLow (q : Wire) (hq : q∈L.y) : q∉L.low := fun h => yAway q hq (by simp [BalancedCleanup.Layout.r,h])
  have yQ (q : Wire) (hq : q∈L.y) : q∉wires Q := by
    simp only [Q,wires_reverse,BalancedCleanup.prepareSign,wires_append]
    intro h
    rcases Finset.mem_union.mp h with h|h
    · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at h
      rcases h with e|e
      · exact yAway q hq (by simp [e,BalancedCleanup.Layout.r])
      · exact L.toLayout.flagAway cnd L.lower (by simp) (by simp [←e,hq])
    · have hh := signComplement_wires_subset L.lower L.r h
      simp only [List.mem_toFinset,List.mem_cons] at hh
      rcases hh with e|e
      · exact L.toLayout.flagAway cnd L.lower (by simp) (by simp [←e,hq])
      · exact yAway q hq e
  have uy : regValue L.y u.basis=encodeWord 256 Y := by
    rw [←hyw]
    apply regValue_congr
    intro q hq
    rw [←un.2 q (yLow q hq),←run_preserves_outside _ _ _ _ (yQ q hq),←tEq]
    exact old.2.2.2 q (yAway q hq)
  have hout : (regValue L.low u.basis+BalancedCleanup.positiveLiteral+(!u.basis L.lower).toNat)%2^255=
      (magnitude Y).toNat := by
    rw [←vlow,un.1]
  have same (r : List Bool) : run (unnormalizeE L.toLayout) r u=run U r u :=
    unnormalizeE_eq L.toLayout hw' cnd Y hy u r uc uy hout
  have mcU : measurementCount (unnormalizeE L.toLayout)=measurementCount U := by
    simp only [unnormalizeE,U,BalancedCleanup.unnormalize,measurementCount_append,
      (EndKnown.addK_measurements L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
        BalancedCleanup.positiveLiteral (by rw [hw.2.1,w.1])).1]
  rw [run_append,run_append,mcU,same]
  subst em1
  subst eu
  rfl

theorem forwardCoreE_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    measurementCount (forwardCoreE L)=measurementCount (forwardCore L) ∧
    toffoliCount (forwardCoreE L)+254=toffoliCount (forwardCore L) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have u := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.positiveLiteral (by omega)
  have a := EndKnown.addK_measurements L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral (by rw [hw.2.1,w.1])
  rw [w.1] at u
  simp only [forwardCoreE,forwardCore,cleanupE,cleanup,cleanupRestE,cleanupRest,unnormalizeE,
    BalancedCleanup.unnormalize,toffoliCount_append,measurementCount_append,a.1,a.2,u.1,u.2]
  constructor <;> first | trivial | omega

theorem forwardE_eq (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hyw : regValue L.y s.basis=encodeWord 256 Y)
    (hc : ∀q∈work L,s.basis q=false) (hend : halfResult (rawSum B X Y)=Y) :
    run (forwardE L) m s=run (forward L) m s := by
  unfold forwardE forward
  rw [run_append,run_append,(forwardCoreE_counts L hw).1,
    forwardCoreE_eq L hw hn B X Y hx hy s _ hs hr hyr hyw hc hend]

theorem forwardE_counts (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (forwardE L)=766 ∧ measurementCount (forwardE L)=1021 := by
  have k := kernel_counts L hw
  have c := forwardCoreE_counts L hw
  have k1 := k.1
  have k2 := k.2.1
  simp only [forward,toffoliCount_append,measurementCount_append] at k1 k2
  simp only [forwardE,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem forwardE_wires (L : BalancedCircuit.Layout) (hw : L.Widths) : wires (forwardE L)⊆wires (forward L) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have aw := EndKnown.addK_wires L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral (by omega)
  have ymem (q : Wire) (hq : q∈L.ymsb::L.ylow) : q∈wires (BalancedCleanup.prepareCompare L.toLayout) := by
    have hy : q∈L.y := by
      simp only [List.mem_cons] at hq
      rcases hq with rfl|h
      · simp [BalancedCleanup.Layout.y]
      · simp [BalancedCleanup.Layout.y,h]
    simp only [BalancedCleanup.prepareCompare,wires_append,Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (signComplement_mem L.sign L.y q hy)))
  generalize eP : forwardPrefix L=P
  generalize eT : TopCarryBorrow.program L=T
  have hF : forward L=((P++BalancedCleanup.prepareCompare L.toLayout++T)++
      (BalancedCleanup.prepareCompare L.toLayout).reverse)++
      (([.X L.lower]++literalConstAdd L.low (L.carry.take 254) L.lower L.one
        BalancedCleanup.positiveLiteral++[.X L.lower])++(BalancedCleanup.prepareSign L.toLayout).reverse)++
      [.measureX L.one [] []] := by
    simp only [forward,forwardCore,cleanup,cleanupRest,BalancedCleanup.unnormalize,eP,eT,List.append_assoc]
  have hE : forwardE L=((P++BalancedCleanup.prepareCompare L.toLayout++T)++
      (BalancedCleanup.prepareCompare L.toLayout).reverse)++
      (([.X L.lower]++EndKnown.addK L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
        BalancedCleanup.positiveLiteral++[.X L.lower])++(BalancedCleanup.prepareSign L.toLayout).reverse)++
      [.measureX L.one [] []] := by
    simp only [forwardE,forwardCoreE,cleanupE,cleanupRestE,unnormalizeE,eP,eT,List.append_assoc]
  rw [hE,hF]
  intro q hq
  simp only [wires_append,Finset.mem_union] at hq ⊢
  by_cases hA : q∈wires (EndKnown.addK L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
      BalancedCleanup.positiveLiteral)
  · have h' := aw hA
    simp only [Finset.mem_union,List.mem_toFinset] at h'
    rcases h' with h'|h'
    · tauto
    · have := ymem q h'
      tauto
  · tauto

open RecordedQuantum in
theorem forwardE_physical (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (forwardE L) := by
  have old := forward_physical L hw hn
  have cnd : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have nd := L.toLayout.normND cnd
  have hzc : ∀q∈L.ymsb::L.ylow,q∉L.carry.take 254 := by
    intro q hq hm
    have qy : q∈L.y := by
      simp only [List.mem_cons] at hq
      rcases hq with rfl|h
      · simp [BalancedCleanup.Layout.y]
      · simp [BalancedCleanup.Layout.y,h]
    have d := List.nodup_append'.mp (List.nodup_append'.mp (L.toLayout.dataND cnd)).2.1
    exact List.disjoint_left.mp d.2.2 qy (List.mem_of_mem_take hm)
  have ak := EndKnown.addK_physical L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral (List.nodup_cons.mp nd).2 hzc
  have x : GatePhysical [.X L.lower] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [forward,forwardCore,cleanup,cleanupRest,BalancedCleanup.unnormalize,gatePhysical_append] at old
  simp only [forwardE,forwardCoreE,cleanupE,cleanupRestE,unnormalizeE,gatePhysical_append]
  tauto

end ECDSAAdd.Entrant.FifthCarry2
end

section
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FifthCarry2
open ECDSAAdd.Arithmetic ECDSAAdd.Challenge ECDSAAdd.Baselines
theorem forwardE_slots (L : BalancedCircuit.Layout) (hw : L.Widths) :
    gateSlots (forwardE L) ≤ 24000 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have kw := BalancedCircuit.widths L hw
  have hb : (ShortBiasedFold.lowBits L).length=255 := by exact ShortBiasedFold.lowBits_length L
  have a := (FifthCarry.raw_slots L hw).1
  have r := (rotate_gateSlots_le (BalancedCircuit.rawTarget L)).1
  have l := (rotate_gateSlots_le L.r).2
  have m := mappedAdd_gateSlots_le (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
  have u := EndKnown.addK_gateSlots_le L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral
  have c := TopCarryBorrow.program_slots L hw
  rw [kw.2.1] at r
  rw [w.2.1] at l
  rw [hb] at m
  rw [w.1] at u
  simp only [forwardE,forwardCoreE,forwardPrefix,cleanupE,cleanupRestE,unnormalizeE,GuardCompression.seed,
    OneReuse.remainder,OneReuse.newPrepare,OneReuse.foldWindow,
    BiasedCircuit.flipBias,GuardCompression.seed,
    BalancedCleanup.prepareSign,BalancedCleanup.prepareCompare,
    gateSlots_append,reverse_gateSlots,signComplement_gateSlots,
    gateSlots_cons,gateSlots_nil,instructionSlots,kw.1,w.2.1,w.2.2.1,List.length_cons,List.length_nil]
  omega
end ECDSAAdd.Entrant.FifthCarry2
end




-- ENDPOINT COMPONENT ForwardE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6Endpoint
open Arithmetic Arithmetic.BalancedField BalancedCircuit Q6ComparatorBorrow Arithmetic.Q6LowerExposure Q6CleanupBorrow
attribute [local irreducible] run

def cleanupWith (L : Layout) (a : Wire) (R : Program) : Program :=
  BalancedCleanup.prepareCompare L.toLayout++borrowed a L.lower L.sign L.r0 (TopCarryBorrow.program L)++R

def oldCleanupWith (L : Layout) (R : Program) : Program :=
  BalancedCleanup.prepareCompare L.toLayout++TopCarryBorrow.program L++R

theorem cleanupWith_eq (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.carry) (R : Program) (s : State) (m : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (bound : regValue L.r s.basis<2^255)
    (hp : (run (CarryBorrow.cleanup L) m s).basis L.parity=false) :
    run (cleanupWith L a R) m s=run (oldCleanupWith L R) m s := by
  let v := run (BalancedCleanup.prepareCompare L.toLayout) [] s
  have ready:=CarryBorrow.prepareCompare_clean L hw hn s [] ho hc
  have oldShape : CarryBorrow.cleanup L=BalancedCleanup.prepareCompare L.toLayout++
      (CarryBorrow.program L++FifthCarry2.cleanupRest L) := by
    simp only [CarryBorrow.cleanup,FifthCarry2.cleanupRest,List.append_assoc]
  have out : run (CarryBorrow.cleanup L) m s=run (FifthCarry2.cleanupRest L)
      (m.drop (measurementCount (CarryBorrow.program L))) (run (CarryBorrow.program L) m v) := by
    rw [oldShape,run_append,prepare_M,List.take_zero,List.drop_zero,run_append,run_take]
  have fin : (run (CarryBorrow.program L) m v).basis L.parity=false := by
    rw [out,run_preserves_outside _ _ _ _ (FifthCarry2.cleanupRest_free L hw hn)] at hp
    exact hp
  have eqOld:=CarryBorrow.program_eq L hw hn v m ready.1 ready.2
  have w:=BalancedCleanup.widths L.toLayout hw
  have cmp:=compareLt_correct none L.y L.r L.carry L.one L.parity
    (L.toLayout.compareND (List.nodup_append'.mp hn).2.1) (by simp)
    (w.2.2.1.trans w.2.1.symm) (hw.2.2.trans w.2.1.symm) v m ready.1 ready.2
  rw [eqOld,cmp.2.2] at fin
  simp only [controlValue,Bool.true_and] at fin
  have par : v.basis L.parity=decide (regValue L.y v.basis<regValue L.r v.basis) := by
    revert fin
    cases v.basis L.parity <;> cases decide (regValue L.y v.basis<regValue L.r v.basis) <;> decide
  have relation := prepareCompare_low_relation L.toLayout hw (List.nodup_append'.mp hn).2.1
    (regValue L.r s.basis) bound s [] rfl
  have eq:=actual_forward_compare_borrow L hw hn a ha v m ready.1 ready.2 relation par
  have count := (borrowed_counts a L.lower L.sign L.r0 (TopCarryBorrow.program L)).2
  simp only [cleanupWith,oldCleanupWith,List.append_assoc,run_append,run_take,
    prepare_M,List.drop_zero,List.take_zero,count]
  have takeB:=run_take (borrowed a L.lower L.sign L.r0 (TopCarryBorrow.program L)) m v
  rw [count] at takeB
  rw [takeB,eq]

def cleanupE (L : Layout) (a : Wire) : Program := cleanupWith L a (FifthCarry2.cleanupRestE L)
def coreE (L : Layout) (a : Wire) : Program := Q6Cell.forwardPrefix L a++cleanupE L a
def forwardE (L : Layout) (a : Wire) : Program := coreE L a++[.measureX L.one [] []]

theorem cleanupE_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.carry) (s : State) (m : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (bound : regValue L.r s.basis<2^255)
    (hp : (run (CarryBorrow.cleanup L) m s).basis L.parity=false) :
    run (cleanupE L a) m s=run (FifthCarry2.cleanupE L) m s := by
  simpa only [cleanupE,oldCleanupWith,FifthCarry2.cleanupE,List.append_assoc] using
    cleanupWith_eq L hw hn a ha (FifthCarry2.cleanupRestE L) s m ho hc bound hp
theorem coreE_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.carry) (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    run (coreE L a) m s=run (FifthCarry2.forwardCoreE L) m s := by
  have preEq:=Q6Cell.forwardPrefix_eq L hw hn a ha s m hc
  have preClean:=FifthCarry.forward_prefix_clean L hw hn B X Y hx hy s (false::m) hs hr hyr hc
  rw [←FifthCarry2.forwardPrefix_shifted L hw hn s m hc] at preClean
  have bound:=Q6CompareReady.forwardPrefix_bound L hw hn B X Y hx hy s m hs hr hyr hc
  have old:=FifthCarry.forward_correct L hw hn B X Y hx hy s m hs hr hyr hc
  have shape:FifthCarry.forward L=FifthCarry2.forwardPrefix L++CarryBorrow.cleanup L := by
    simp only [FifthCarry.forward,FifthCarry2.forwardPrefix,List.append_assoc]
  rw [shape,run_append,run_take] at old
  have ce:=cleanupE_eq L hw hn a ha (run (FifthCarry2.forwardPrefix L) m s)
    (m.drop (measurementCount (FifthCarry2.forwardPrefix L))) preClean.1 preClean.2 bound
    (old.2.2.1 L.parity (by simp [work]))
  simp only [coreE,FifthCarry2.forwardCoreE,run_append,run_take,(Q6Cell.forwardPrefix_counts L a).2]
  have takeB:=run_take (Q6Cell.forwardPrefix L a) m s
  rw [(Q6Cell.forwardPrefix_counts L a).2] at takeB
  rw [takeB,preEq,ce]


theorem coreE_counts_eq (L : Layout) (a : Wire) :
    toffoliCount (coreE L a)=toffoliCount (FifthCarry2.forwardCoreE L) ∧
    measurementCount (coreE L a)=measurementCount (FifthCarry2.forwardCoreE L) := by
  simp only [coreE,FifthCarry2.forwardCoreE,cleanupE,cleanupWith,FifthCarry2.cleanupE,
    toffoliCount_append,measurementCount_append,(Q6Cell.forwardPrefix_counts L a).1,
    (Q6Cell.forwardPrefix_counts L a).2,(borrowed_counts a L.lower L.sign L.r0 (TopCarryBorrow.program L)).1,
    (borrowed_counts a L.lower L.sign L.r0 (TopCarryBorrow.program L)).2]
  trivial

theorem forwardE_counts (L : Layout) (hw : L.Widths) (a : Wire) :
    toffoliCount (forwardE L a)=766 ∧ measurementCount (forwardE L a)=1021 := by
  have old:=FifthCarry2.forwardE_counts L hw
  simpa only [forwardE,FifthCarry2.forwardE,toffoliCount_append,measurementCount_append,
    (coreE_counts_eq L a).1,(coreE_counts_eq L a).2] using old

theorem forwardE_eq_old (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.carry) (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    run (forwardE L a) m s=run (FifthCarry2.forwardE L) m s := by
  have eq:=coreE_eq L hw hn a ha B X Y hx hy s m hs hr hyr hc
  have count:measurementCount (coreE L a)=measurementCount (FifthCarry2.forwardCoreE L):=(coreE_counts_eq L a).2
  simp only [forwardE,FifthCarry2.forwardE,run_append,run_take,count]
  have takeB:=run_take (coreE L a) m s
  rw [count] at takeB
  rw [takeB,eq]

theorem forwardE_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a : Wire) (ha : a∈L.carry) (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hyw : regValue L.y s.basis=encodeWord 256 Y)
    (hc : ∀q∈work L,s.basis q=false) (hend : halfResult (rawSum B X Y)=Y) :
    run (forwardE L a) m s=run (Q6Cell.forward L a) m s := by
  rw [forwardE_eq_old L hw hn a ha B X Y hx hy s m hs hr hyr hc,
    FifthCarry2.forwardE_eq L hw hn B X Y hx hy s m hs hr hyr hyw hc hend,
    Q6Cell.forward_eq L hw hn a ha B X Y hx hy s m hs hr hyr hc]

end ECDSAAdd.Entrant.Q6Endpoint


-- ENDPOINT COMPONENT StructuralE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointStructural
open Arithmetic Arithmetic.BalancedField BalancedCircuit Q6Structural Arithmetic.Q6LowerExposure

def cleanupE (L : Layout) : Program :=
  BalancedCleanup.prepareCompare L.toLayout++
    (Q6StructuralCell.exposure L++compareForward L++(Q6StructuralCell.exposure L).reverse)++FifthCarry2.cleanupRestE L

def forwardE (L : Layout) : Program :=
  (Q6StructuralCell.forwardPrefix L++cleanupE L)++[.measureX L.one [] []]

theorem forwardE_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    forwardE L=Q6Endpoint.forwardE L (L.carry.getD 254 0) := by
  rw [forwardE,Q6Endpoint.forwardE,Q6Endpoint.coreE,Q6StructuralCell.forwardPrefix,
    Q6Cell.forwardPrefix,Q6Cell.rawAdd,cleanupE,Q6Endpoint.cleanupE,Q6Endpoint.cleanupWith,
    Q6ComparatorBorrow.borrowed]
  rw [Q6Structural.rawAdd_eq L hw hn,Q6Structural.compareForward_eq L hw hn]
  rfl

theorem rest_layout (L : Layout) (hw : L.Widths) :
    FifthCarry2.cleanupRestE (carryLayout L)=FifthCarry2.cleanupRestE L := by
  have prep : BalancedCleanup.prepareCompare (carryLayout L).toLayout=BalancedCleanup.prepareCompare L.toLayout:=by unfold BalancedCleanup.prepareCompare;rfl
  have sign : BalancedCleanup.prepareSign (carryLayout L).toLayout=BalancedCleanup.prepareSign L.toLayout:=rfl
  simp only [FifthCarry2.cleanupRestE,FifthCarry2.unnormalizeE,prep,sign]
  rw [show (carryLayout L).toLayout.carry.take 254=L.toLayout.carry.take 254 from Q6StructuralCell.carry_take L hw]
  rfl

theorem remainder_layout (L : Layout) (hw : L.Widths) :
    OneReuse.remainder (carryLayout L)=OneReuse.remainder L := by
  simp only [OneReuse.remainder,OneReuse.foldWindow]
  rw [show (carryLayout L).carry.take 254=L.carry.take 254 from Q6StructuralCell.carry_take L hw]
  rfl

theorem forwardE_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (forwardE L)=766 ∧ measurementCount (forwardE L)=1021 := by
  have old:=FifthCarry2.forwardE_counts (carryLayout L) (Q6StructuralCell.carry_widths L hw)
  have seed : GuardCompression.seed (carryLayout L)=GuardCompression.seed L:=by unfold GuardCompression.seed;rfl
  have prep : BalancedCleanup.prepareCompare (carryLayout L).toLayout=BalancedCleanup.prepareCompare L.toLayout:=by unfold BalancedCleanup.prepareCompare;rfl
  simp only [FifthCarry2.forwardE,FifthCarry2.forwardCoreE,FifthCarry2.forwardPrefix,FifthCarry2.cleanupE,
    seed,prep,remainder_layout L hw,rest_layout L hw,toffoliCount_append,measurementCount_append] at old
  simp only [forwardE,Q6StructuralCell.forwardPrefix,cleanupE,Q6Structural.rawAdd,Q6Structural.compareForward,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    Q6StructuralCell.exposure,expose,toffoliCount,measurementCount]
  simpa only [carryLayout,Nat.add_zero,Nat.zero_add,List.length_map] using old

section
attribute [local irreducible] wires FifthCarry.rawAdd OneReuse.remainder GuardCompression.seed
  BalancedCleanup.prepareCompare FifthCarry2.cleanupRestE TopCarryBorrow.program

theorem exposure_support (L : Layout) :
    wires (Q6StructuralCell.exposure L)⊆(carryLayout L).wires.toFinset := by
  intro q h
  simp only [Q6StructuralCell.exposure,expose,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.notMem_empty,or_false] at h
  simp only [List.mem_toFinset,carryLayout,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  tauto

theorem forwardE_support (L : Layout) (hw : L.Widths) :
    wires (forwardE L)⊆(carryLayout L).wires.toFinset := by
  have old:=(FifthCarry2.forwardE_wires (carryLayout L) (Q6StructuralCell.carry_widths L hw)).trans
    (FifthCarry2.forward_support (carryLayout L) (Q6StructuralCell.carry_widths L hw))
  have seed : GuardCompression.seed (carryLayout L)=GuardCompression.seed L:=by unfold GuardCompression.seed;rfl
  have prep : BalancedCleanup.prepareCompare (carryLayout L).toLayout=BalancedCleanup.prepareCompare L.toLayout:=by unfold BalancedCleanup.prepareCompare;rfl
  have ex:=exposure_support L
  simp only [FifthCarry2.forwardE,FifthCarry2.forwardCoreE,FifthCarry2.forwardPrefix,FifthCarry2.cleanupE,
    wires_append,Finset.union_subset_iff,seed,prep,remainder_layout L hw,rest_layout L hw] at old
  simp only [forwardE,Q6StructuralCell.forwardPrefix,cleanupE,Q6Structural.rawAdd,Q6Structural.compareForward,
    wires_append,wires_reverse,Finset.union_subset_iff]
  tauto
end

theorem retired_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.carry.getD 254 0∉wires (forwardE L) := fun h=>
  Q6StructuralCell.carryLayout_away L hw hn (List.mem_toFinset.mp (forwardE_support L hw h))

theorem forwardE_state_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hyw : regValue L.y s.basis=encodeWord 256 Y)
    (hc : ∀q∈work L,s.basis q=false) (hend : halfResult (rawSum B X Y)=Y) :
    run (forwardE L) m s=run (Q6StructuralCell.forward L) m s := by
  have idx:254<L.carry.length:=by rw [hw.2.2];omega
  have mem:L.carry.getD 254 0∈L.carry:=by
    rw [List.getD_eq_getElem _ _ idx]
    exact List.getElem_mem _
  rw [forwardE_eq L hw hn,Q6StructuralCell.forward_eq L hw hn]
  exact Q6Endpoint.forwardE_eq L hw hn _ mem B X Y hx hy s m hs hr hyr hyw hc hend
end ECDSAAdd.Entrant.Q6EndpointStructural


-- ENDPOINT COMPONENT HalfE.lean
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnQ6Core5
open Arithmetic Secp256k1 BalancedField BalancedCircuit
/-- The endpoint half with the known-output kernel runs exactly like the forward half. -/
theorem halfE_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : ∀q∈work L,base q=false) (X Y : Fp)
    (s : State) (m : List Bool)
    (h : PairFrame L.r L.y base (centerWord X) (centerWord Y) s.basis)
    (hend : (X+(if base L.sign then Y else -Y))/2=Y) :
    run ([.X L.sign]++Q6EndpointStructural.forwardE L++[.X L.sign]) m s=run (half true L) m s := by
  have aw := flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have hk : half true L=[.X L.sign]++Q6StructuralCell.forward L++[.X L.sign] := by
    simp only [half,kernel,if_true]
  rw [hk,List.append_assoc,List.append_assoc]
  apply LaneI.seq_eq _ _ _ _ s m rfl rfl
  generalize eu : run [.X L.sign] (m.take (measurementCount [.X L.sign])) s=u
  have us := BalancedCleanupOffset.x_run L.sign s (m.take (measurementCount [.X L.sign]))
  rw [eu] at us
  have uf (q : Wire) (hq : q≠L.sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ug : u.basis L.sign= !base L.sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 L.sign sa.1 sa.2]
  have uv (r : List Wire) (a : L.sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout hw).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout hw).2.2.1,centerWord_decode]
  have uyw : regValue L.y u.basis=encodeWord 256 (centerFp Y) := by
    rw [uv L.y sa.2,h.2.1]; rfl
  have uc : ∀q∈work L,u.basis q=false := by
    intro q hq
    have a := work_away L hn q hq
    exact (uf q (fun e => sign_work L hn (e ▸ hq))).trans
      ((h.2.2 q a.1 a.2).trans (hc q hq))
  have e : (X+(if (!base L.sign) then -Y else Y))/2=Y := by
    cases hb : base L.sign
    · simp only [hb,Bool.not_false,if_true,Bool.false_eq_true,if_false] at hend ⊢; exact hend
    · simp only [hb,Bool.not_true,Bool.false_eq_true,if_false,if_true] at hend ⊢; exact hend
  have he : halfResult (rawSum (!base L.sign) (centerFp X) (centerFp Y))=centerFp Y := by
    rw [centeredFp_signedHalf,e]
  rw [run_append,run_append]
  have mc : measurementCount (Q6EndpointStructural.forwardE L)=measurementCount (Q6StructuralCell.forward L) := by
    rw [(Q6EndpointStructural.forwardE_counts L hw).2,(Q6StructuralCell.kernel_counts L hw).2.1]
  rw [mc,Q6EndpointStructural.forwardE_state_eq L hw hn (!base L.sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u _ ug ur uy uyw uc he]

end ECDSAAdd.Entrant.OwnQ6Core5


-- ENDPOINT COMPONENT AdaptersE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointStructural
open Arithmetic Arithmetic.BalancedField BalancedCircuit Q6Structural Arithmetic.Q6LowerExposure FifthCarry2
attribute [local irreducible] wires
theorem forwardE_wires (L : BalancedCircuit.Layout) (hw : L.Widths) : wires (forwardE L)⊆wires (Q6StructuralCell.forward L) := by
  have w := BalancedCleanup.widths L.toLayout hw
  have aw := EndKnown.addK_wires L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral (by omega)
  have ymem (q : Wire) (hq : q∈L.ymsb::L.ylow) : q∈wires (BalancedCleanup.prepareCompare L.toLayout) := by
    have hy : q∈L.y := by
      simp only [List.mem_cons] at hq
      rcases hq with rfl|h
      · simp [BalancedCleanup.Layout.y]
      · simp [BalancedCleanup.Layout.y,h]
    simp only [BalancedCleanup.prepareCompare,wires_append,Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (signComplement_mem L.sign L.y q hy)))
  generalize eP : Q6StructuralCell.forwardPrefix L=P
  generalize eT : (Q6StructuralCell.exposure L++Q6Structural.compareForward L++(Q6StructuralCell.exposure L).reverse)=T
  have hF : Q6StructuralCell.forward L=((P++BalancedCleanup.prepareCompare L.toLayout++T)++
      (BalancedCleanup.prepareCompare L.toLayout).reverse)++
      (([.X L.lower]++literalConstAdd L.low (L.carry.take 254) L.lower L.one
        BalancedCleanup.positiveLiteral++[.X L.lower])++(BalancedCleanup.prepareSign L.toLayout).reverse)++
      [.measureX L.one [] []] := by
    simp only [Q6StructuralCell.forward,Q6StructuralCell.cleanup,FifthCarry2.cleanupRest,BalancedCleanup.unnormalize,eP,eT,List.append_assoc]
  have hE : forwardE L=((P++BalancedCleanup.prepareCompare L.toLayout++T)++
      (BalancedCleanup.prepareCompare L.toLayout).reverse)++
      (([.X L.lower]++EndKnown.addK L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
        BalancedCleanup.positiveLiteral++[.X L.lower])++(BalancedCleanup.prepareSign L.toLayout).reverse)++
      [.measureX L.one [] []] := by
    simp only [forwardE,cleanupE,FifthCarry2.cleanupRestE,FifthCarry2.unnormalizeE,eP,eT,List.append_assoc]
  rw [hE,hF]
  intro q hq
  simp only [wires_append,Finset.mem_union] at hq ⊢
  by_cases hA : q∈wires (EndKnown.addK L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
      BalancedCleanup.positiveLiteral)
  · have h' := aw hA
    simp only [Finset.mem_union,List.mem_toFinset] at h'
    rcases h' with h'|h'
    · tauto
    · have := ymem q h'
      tauto
  · tauto

open RecordedQuantum in
theorem forwardE_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (forwardE L) := by
  have old:=OwnQ6Core5.kernel_physical true L hw hn
  simp only [OwnQ6Core5.kernel,if_true,Q6StructuralCell.forward,Q6StructuralCell.cleanup,
    gatePhysical_append] at old
  have endp:=FifthCarry2.forwardE_physical L hw hn
  simp only [FifthCarry2.forwardE,FifthCarry2.forwardCoreE,FifthCarry2.cleanupE,gatePhysical_append] at endp
  simp only [forwardE,cleanupE,gatePhysical_append]
  tauto

theorem forwardE_slots_eq (L : Layout) (hw : L.Widths) :
    Challenge.gateSlots (forwardE L)=Challenge.gateSlots (FifthCarry2.forwardE (carryLayout L))+6 := by
  have seed : GuardCompression.seed (carryLayout L)=GuardCompression.seed L:=rfl
  have prep : BalancedCleanup.prepareCompare (carryLayout L).toLayout=BalancedCleanup.prepareCompare L.toLayout:=rfl
  have es : Challenge.gateSlots (Q6StructuralCell.exposure L)=3:=rfl
  simp only [forwardE,Q6StructuralCell.forwardPrefix,cleanupE,FifthCarry2.forwardE,FifthCarry2.forwardCoreE,
    FifthCarry2.forwardPrefix,FifthCarry2.cleanupE,Q6Structural.rawAdd,Q6Structural.compareForward,
    Challenge.gateSlots_append,Baselines.reverse_gateSlots,es,remainder_layout L hw,rest_layout L hw,seed,prep]
  simp only [carryLayout]
  omega

open Challenge Baselines in
theorem old_forwardE_slots_tight (L : BalancedCircuit.Layout) (hw : L.Widths) :
    gateSlots (FifthCarry2.forwardE L) ≤ 23994 := by
  have w := BalancedCleanup.widths L.toLayout hw
  have kw := BalancedCircuit.widths L hw
  have hb : (ShortBiasedFold.lowBits L).length=255 := by exact ShortBiasedFold.lowBits_length L
  have a := (FifthCarry.raw_slots L hw).1
  have r := (rotate_gateSlots_le (BalancedCircuit.rawTarget L)).1
  have l := (rotate_gateSlots_le L.r).2
  have m := mappedAdd_gateSlots_le (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
  have u := EndKnown.addK_gateSlots_le L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral
  have c := TopCarryBorrow.program_slots L hw
  rw [kw.2.1] at r
  rw [w.2.1] at l
  rw [hb] at m
  rw [w.1] at u
  simp only [FifthCarry2.forwardE,FifthCarry2.forwardCoreE,FifthCarry2.forwardPrefix,FifthCarry2.cleanupE,FifthCarry2.cleanupRestE,FifthCarry2.unnormalizeE,GuardCompression.seed,
    OneReuse.remainder,OneReuse.newPrepare,OneReuse.foldWindow,
    BiasedCircuit.flipBias,GuardCompression.seed,
    BalancedCleanup.prepareSign,BalancedCleanup.prepareCompare,
    gateSlots_append,reverse_gateSlots,signComplement_gateSlots,
    gateSlots_cons,gateSlots_nil,instructionSlots,kw.1,w.2.1,w.2.2.1,List.length_cons,List.length_nil]
  omega

theorem forwardE_slots (L : Layout) (hw : L.Widths) : Challenge.gateSlots (forwardE L)≤24000 := by
  rw [forwardE_slots_eq L hw]
  have old:=old_forwardE_slots_tight (carryLayout L) (Q6StructuralCell.carry_widths L hw)
  omega
end ECDSAAdd.Entrant.Q6EndpointStructural


-- ENDPOINT COMPONENT CellE.lean
-- ===== ECDSAAdd.Submission.Entrant.Q6EndpointCell =====
section

/-! One-bank ports and layout proofs use accepted submission
12159df8-70b5-4718-9aef-847528abd574, commit
b2d461e7c85fef3e9360d1c5bfbb237687ee2578. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false


namespace ECDSAAdd.Entrant.Q6EndpointCell
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedAllocation CompressedFieldSupport
def ports (w : Nat → Wire) (sign : Wire) : BalancedCircuit.Layout :=
  { r0:=w 2056,rtail:=wireBlock w 2057 254,rmsb:=w 2311,
    ylow:=wireBlock w 770 255,ymsb:=w 1025,
    carry:=wireBlock w 512 253++[w 1540,w 1541,w 1026],
    sign:=sign,parity:=w 768,lower:=w 1797,one:=w 1027,
    sourceGuard:=w 765,cout:=w 2312,minus:=w 767,plus:=w 766 }

def ids : List Nat := [765,768,767,766,2312,1797,1027,2311,1025,2056]++
  List.range' 2057 254++List.range' 770 255++List.range' 512 253++[1540,1541,1026]

section
attribute [local irreducible] List.range'
theorem ids_nodup : ids.Nodup := by
  simp only [ids,List.nodup_append']
  repeat' apply And.intro
  all_goals first
  | exact List.nodup_range'
  | (apply List.disjoint_left.mpr
     intro q hq hn
     simp only [List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1] at hq hn
     cases_type* Or
     all_goals omega)
  | decide
end

theorem ids_bound (j : Nat) (hj : j∈ids) : j<2314 := by
  simp only [ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
  omega

theorem ports_widths (w : Nat → Wire) (sign : Wire) : (ports w sign).Widths := by
  simp [BalancedCircuit.Layout.Widths,BalancedCleanup.Layout.Widths,ports,wireBlock]

theorem ports_ylow (w : Nat → Wire) (sign : Wire) : (ports w sign).ylow≠[] := by
  intro h
  have len := (ports_widths w sign).2.1
  rw [h] at len
  contradiction

theorem ports_r (w : Nat → Wire) (sign : Wire) :
    (ports w sign).r=(balancedSharedPorts w sign).r := rfl
theorem ports_y (w : Nat → Wire) (sign : Wire) :
    (ports w sign).y=(balancedSharedPorts w sign).y := rfl
theorem ports_sign (w : Nat → Wire) (sign : Wire) : (ports w sign).sign=sign := rfl

theorem ports_nodup (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hs : sign∉ids.map w) :
    (ports w sign).wires.Nodup := by
  have mapped : (ids.map w).Nodup := by
    apply List.Nodup.map_on
    · intro i hi j hj he
      exact skywalkShared_index_inj w hn i j (ids_bound i hi) (ids_bound j hj) he
    · exact ids_nodup
  have all : (sign::ids.map w).Nodup := List.nodup_cons.mpr ⟨hs,mapped⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp all q
  simp only [ports,ids,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem ports_nodup_injective (w : Nat → Wire) (sign : Wire)
    (hw : Function.Injective w) (hs : sign∉ids.map w) :
    (ports w sign).wires.Nodup := by
  have mapped := List.Nodup.map hw ids_nodup
  have all : (sign::ids.map w).Nodup := List.nodup_cons.mpr ⟨hs,mapped⟩
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp all q
  simp only [ports,ids,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    wireBlock,List.map_append,List.map_cons,List.map_nil,List.count_cons,
    List.count_append,List.count_nil] at h ⊢
  omega

def workIds : List Nat := [765,2312,767,766,768,1797,1027]++List.range' 512 253++[1540,1541,1026]

theorem ports_work (w : Nat → Wire) (sign : Wire) :
    BalancedCircuit.work (ports w sign)=workIds.map w := by
  simp [BalancedCircuit.work,ports,workIds,wireBlock]

private def availableIds : List Nat :=
  List.range' 1540 257++List.range' 1798 256++[1797]++List.range' 512 257++
    [2313,769,1027,2054,2055]

private theorem work_split : ∀ j∈workIds, j=2312 ∨ j=1026 ∨ j∈availableIds := by
  intro j hj
  simp only [workIds,availableIds,List.mem_append,List.mem_cons,List.not_mem_nil,
    List.mem_range'_1,or_false] at hj ⊢
  omega

theorem work_bound (j : Nat) (hj : j∈workIds) : j<2314 := by
  simp only [workIds,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hj
  omega

theorem ports_work_shared (w : Nat → Wire) (sign : Wire) (q : Wire)
    (hq : q∈BalancedCircuit.work (ports w sign)) : q∈skywalkSharedWires w := by
  rw [ports_work] at hq
  exact balancedSharedLayout_mapSubset w workIds work_bound hq

/-- All single-bank scratch is clean under the caller environment and a
clean y-extension site `2312`. -/
theorem clean_of_env_work (w : Nat → Wire) (sign : Wire) (base : BasisState)
    (he : OffsetBorrowedCanonical.Env w base) (hz : base (w 2312)=false) :
    ∀q∈BalancedCircuit.work (ports w sign),base q=false := by
  have available : (skywalkSharedField w).work++skywalkSharedUnused w=availableIds.map w := by
    simp [skywalkSharedField,skywalkSharedUnused,ModInPlaceLayout.work,
      ModAddCoreLayout.work,availableIds,wireBlock,List.map_append,List.append_assoc]
  intro q hq
  rw [ports_work] at hq
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  rcases work_split j hj with h|h|h
  · subst h; exact hz
  · subst h; exact he.2.2
  · have mem : w j∈(skywalkSharedField w).work++skywalkSharedUnused w := by
      rw [available]; exact List.mem_map_of_mem h
    rcases List.mem_append.mp mem with m|m
    · exact (regValue_zero _ _).mp he.1 _ m
    · exact (regValue_zero _ _).mp he.2.1 _ m

theorem ports_transcript (w : Nat → Wire) (b g swap sign effS : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (hoS : effS∉skywalkSharedWires w) :
    BalancedTranscriptLayout (ports w sign) b g swap effS where
  widths := ports_widths w sign
  kernel := ports_nodup w sign hn
    (fun h => ho (balancedSharedLayout_mapSubset w ids ids_bound h))
  controls := hl.controls
  outside := hl.outside
  scratch := ⟨fun h => ho (ports_work_shared w sign _ h),
    fun h => hoS (ports_work_shared w sign _ h)⟩
  swapND := hl.swapND


/-- Only the active bank must be clean. Retired carries can hold history. -/
def Clean (w : Nat → Wire) (origin : BasisState) : Prop :=
  ∀ q∈workIds.map w,origin q=false

theorem clean_work (w : Nat → Wire) (sign : Wire) (origin : BasisState)
    (h : Clean w origin) : ∀q∈BalancedCircuit.work (ports w sign),origin q=false := by
  simpa only [ports_work] using h

theorem clean_of_env (w : Nat → Wire) (origin : BasisState)
    (he : OffsetBorrowedCanonical.Env w origin) (hz : origin (w 2312)=false) :
    Clean w origin := by
  simpa only [ports_work,Clean] using clean_of_env_work w (w 2409) origin he hz









def half (divide : Bool) (w : Nat → Wire) (sign : Wire) : Program :=
  OwnQ6Core5.half divide (ports w sign)

def body (divide : Bool) (w : Nat → Wire) (sign eff : Wire) : Program :=
  if divide then half true w sign++swapRegisters eff (ports w sign).r (ports w sign).y
  else swapRegisters eff (ports w sign).r (ports w sign).y++half false w sign

def cell (divide : Bool) (w : Nat → Wire) (b g sw sign eff : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig
    (transcriptSelectWindow b sw eff is (body divide w sign eff))

/-- Endpoint half: the divide endpoint uses the known-output kernel. -/
def halfE (divide : Bool) (w : Nat → Wire) (sign : Wire) : Program :=
  if divide then [.X sign]++Q6EndpointStructural.forwardE (ports w sign)++[.X sign] else half false w sign

def endpoint (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool) : Program :=
  transcriptSelectWindow b g sign ig (halfE divide w sign)

theorem halfE_true (w : Nat → Wire) (sign : Wire) :
    halfE true w sign=[.X sign]++Q6EndpointStructural.forwardE (ports w sign)++[.X sign] := rfl

theorem halfE_false (w : Nat → Wire) (sign : Wire) : halfE false w sign=half false w sign := rfl

theorem half_true (w : Nat → Wire) (sign : Wire) :
    half true w sign=[.X sign]++Q6StructuralCell.forward (ports w sign)++[.X sign] := rfl


def payload (divide : Bool) (g sw : Bool) (Q : Fp×Fp) : Fp×Fp :=
  if divide then skywalkPayloadCell g sw Q else skywalkPayloadUncell g sw Q

theorem half_frame (divide : Bool) (w : Nat → Wire) (sign : Wire)
    (hn : (ports w sign).wires.Nodup) (origin : BasisState) (hc : Clean w origin) (X Y : Fp) :
    Triple (PairFrame (ports w sign).r (ports w sign).y origin (centerWord X) (centerWord Y))
      (half divide w sign)
      (PairFrame (ports w sign).r (ports w sign).y origin
        (centerWord (if divide then (X+(if origin sign then Y else -Y))/2
          else 2*X+(if origin sign then -Y else Y))) (centerWord Y)) := by
  have hw := ports_widths w sign
  have cl := clean_work w sign origin hc
  intro s m h
  rw [half,OwnQ6Core5.half_eq divide _ hw hn origin cl X Y s m h]
  cases divide
  · exact balancedTranscriptDouble_frame _ hw hn origin cl X Y s m h
  · exact balancedTranscriptHalf_frame _ hw hn origin cl X Y s m h

private theorem swap_frame (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have ca : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem body_frame (divide : Bool) (w : Nat → Wire) (sign eff : Wire)
    (hn : (ports w sign).wires.Nodup)
    (hs : (eff::(ports w sign).r++(ports w sign).y).Nodup)
    (origin : BasisState) (hc : Clean w origin) (X Y : Fp) :
    Triple (PairFrame (ports w sign).r (ports w sign).y origin (centerWord X) (centerWord Y))
      (body divide w sign eff)
      (PairFrame (ports w sign).r (ports w sign).y origin
        (centerWord (payload divide (origin sign) (origin eff) (X,Y)).1)
        (centerWord (payload divide (origin sign) (origin eff) (X,Y)).2)) := by
  let L := ports w sign
  have len := BalancedCleanup.widths L.toLayout (ports_widths w sign)
  cases divide
  · have sw := swap_frame L.r L.y eff (len.2.1.trans len.2.2.1.symm) hs
      origin (centerWord X) (centerWord Y)
    let A := if origin eff then Y else X
    let B := if origin eff then X else Y
    have view : PairFrame L.r L.y origin (centerWord A) (centerWord B) =
        PairFrame L.r L.y origin (if origin eff then centerWord Y else centerWord X)
          (if origin eff then centerWord X else centerWord Y) := by
      cases e : origin eff <;> simp only [A,B,e,Bool.false_eq_true,if_true,if_false]
    rw [←view] at sw
    have dbl := half_frame false w sign hn origin hc A B
    have out : PairFrame L.r L.y origin
        (centerWord (payload false (origin sign) (origin eff) (X,Y)).1)
        (centerWord (payload false (origin sign) (origin eff) (X,Y)).2) =
        PairFrame L.r L.y origin (centerWord (2*A+(if origin sign then -B else B)))
          (centerWord B) := by
      cases e : origin eff <;>
        simp only [payload,skywalkPayloadUncell,A,B,e,Bool.false_eq_true,if_true,if_false]
    change Triple _ _ (PairFrame L.r L.y origin _ _)
    rw [out]
    simpa only [body,Bool.false_eq_true,if_false] using sw.seq dbl
  · have hh := half_frame true w sign hn origin hc X Y
    let T := (X+(if origin sign then Y else -Y))/2
    have sw := swap_frame L.r L.y eff (len.2.1.trans len.2.2.1.symm) hs
      origin (centerWord T) (centerWord Y)
    have view : PairFrame L.r L.y origin
        (centerWord (payload true (origin sign) (origin eff) (X,Y)).1)
        (centerWord (payload true (origin sign) (origin eff) (X,Y)).2) =
        PairFrame L.r L.y origin (if origin eff then centerWord Y else centerWord T)
          (if origin eff then centerWord T else centerWord Y) := by
      cases e : origin eff <;>
        simp only [payload,skywalkPayloadCell,e,Bool.false_eq_true,if_true,if_false,T]
    rw [←view] at sw
    simpa only [body,if_true] using hh.seq sw

private theorem selected_other (base : BasisState) (b source flag q : Wire) (v : Bool)
    (hne : q≠flag) : mixedTranscriptBase base b source flag v q=base q := by
  simp [mixedTranscriptBase,writeBit,Function.update,hne]

theorem cell_frame (divide : Bool) (w : Nat → Wire) (b g sw sign effS : Wire)
    (ig is : Bool) (hl : BalancedTranscriptLayout (ports w sign) b g sw effS)
    (origin : BasisState) (hg0 : origin sign=false) (hs0 : origin effS=false)
    (hc : Clean w origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y)) (cell divide w b g sw sign effS ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
        (centerWord (payload divide (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).1)
        (centerWord (payload divide (mixedTranscriptBit origin b g ig)
          (mixedTranscriptBit origin b sw is) (X,Y)).2)) := by
  let L := ports w sign
  change BalancedTranscriptLayout L b g sw effS at hl
  change origin L.sign=false at hg0
  have hc := clean_work w sign origin hc
  let bg := mixedTranscriptBase origin b g L.sign ig
  let bs := mixedTranscriptBase bg b sw effS is
  have sg : [b,g,L.sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  have ss : [b,sw,effS].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hl.controls q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  have d0 := List.nodup_cons.mp hl.controls
  have d1 := List.nodup_cons.mp d0.2
  have d2 := List.nodup_cons.mp d1.2
  have d3 := List.nodup_cons.mp d2.2
  have ne : effS≠L.sign := Ne.symm (by simpa using d3.1)
  have bn : b≠L.sign := by
    have h := (List.nodup_cons.mp sg).1
    intro e; exact h (by simp [e])
  have sn : sw≠L.sign := by
    intro e
    exact d2.1 (by simp [e])
  have bgS : bg effS=false := (selected_other _ _ _ _ _ _ ne).trans hs0
  have bgB : bg b=origin b := selected_other _ _ _ _ _ _ bn
  have bgSwap : bg sw=origin sw := selected_other _ _ _ _ _ _ sn
  have bsG : bs L.sign=mixedTranscriptBit origin b g ig := by
    rw [show bs L.sign=bg L.sign from selected_other _ _ _ _ _ _ (Ne.symm ne)]
    simp [bg,mixedTranscriptBase,writeBit]
  have bsS : bs effS=mixedTranscriptBit origin b sw is := by
    simp [bs,mixedTranscriptBase,mixedTranscriptBit,writeBit,bgB,bgSwap]
  have clean : ∀q∈BalancedCircuit.work L,bs q=false := by
    intro q hq
    have qg : q≠L.sign := fun e => hl.scratch.1 (e ▸ hq)
    have qs : q≠effS := fun e => hl.scratch.2 (e ▸ hq)
    exact (selected_other _ _ _ _ _ _ qs).trans
      ((selected_other _ _ _ _ _ _ qg).trans (hc q hq))
  have body := body_frame divide w sign effS hl.kernel hl.swapND bs
    (by simpa only [Clean,←ports_work w sign] using clean) X Y
  change bs sign=mixedTranscriptBit origin b g ig at bsG
  rw [bsG,bsS] at body
  have inner := transcriptSelectWindow_pairFrame b sw effS is L.r L.y ss
    (hl.outside b (by simp)) (hl.outside sw (by simp))
    (hl.outside effS (by simp)) bg bgS (centerWord X) (centerWord Y) _ _ _ body
  exact transcriptSelectWindow_pairFrame b g L.sign ig L.r L.y sg
    (hl.outside b (by simp)) (hl.outside g (by simp))
    (hl.outside L.sign (by simp)) origin hg0 _ _ _ _ _ inner

theorem payload_directional (divide g sw : Bool) (Q : Fp×Fp) :
    payload divide g sw Q=directionalPayload (!divide) [(g,sw)] Q := by
  cases divide <;> rfl

section EndKnownHalf
attribute [local irreducible] Q6EndpointStructural.forwardE Q6StructuralCell.forward OwnQ6Core5.kernel

theorem halfE_wires (divide : Bool) (w : Nat → Wire) (sign : Wire) :
    wires (halfE divide w sign)⊆wires (half divide w sign) := by
  cases divide
  · rw [halfE_false]
  · have k := Q6EndpointStructural.forwardE_wires (ports w sign) (ports_widths w sign)
    rw [halfE_true,half_true,wires_append,wires_append,wires_append,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) k)
      (Finset.Subset.refl _)

theorem halfE_frame (divide : Bool) (w : Nat → Wire) (sign : Wire)
    (hn : (ports w sign).wires.Nodup) (origin : BasisState) (hc : Clean w origin) (X Y : Fp)
    (hend : divide=true → (X+(if origin sign then Y else -Y))/2=Y) :
    Triple (PairFrame (ports w sign).r (ports w sign).y origin (centerWord X) (centerWord Y))
      (halfE divide w sign)
      (PairFrame (ports w sign).r (ports w sign).y origin
        (centerWord (if divide then (X+(if origin sign then Y else -Y))/2
          else 2*X+(if origin sign then -Y else Y))) (centerWord Y)) := by
  intro s m h
  have old := half_frame divide w sign hn origin hc X Y s m h
  cases divide
  · rw [halfE_false]; exact old
  · have hw := ports_widths w sign
    have cl := clean_work w sign origin hc
    have eq := OwnQ6Core5.halfE_eq (ports w sign) hw hn origin cl X Y s m h
      (by rw [ports_sign]; exact hend rfl)
    rw [ports_sign] at eq
    rw [halfE_true,eq]
    exact old
end EndKnownHalf

theorem endpoint_frame (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool)
    (hn : (ports w sign).wires.Nodup) (nd : [b,g,sign].Nodup)
    (hb : b∉(ports w sign).r ∧ b∉(ports w sign).y)
    (hg : g∉(ports w sign).r ∧ g∉(ports w sign).y)
    (hs : sign∉(ports w sign).r ∧ sign∉(ports w sign).y)
    (origin : BasisState) (hz : origin sign=false) (hc : Clean w origin) (X Y : Fp)
    (hend : divide=true → (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2=Y) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y)) (endpoint divide w b g sign ig)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
        (centerWord (if divide then (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit origin b g ig then -Y else Y))) (centerWord Y)) := by
  have ns := OwnQ6Core5.sign_work (ports w sign) hn
  have cl : Clean w (mixedTranscriptBase origin b g sign ig) := by
    intro q hq
    have nq : q≠sign := fun e => ns (by simpa only [ports_work] using e ▸ hq)
    exact (selected_other _ _ _ _ _ _ nq).trans (hc q hq)
  have body := halfE_frame divide w sign hn (mixedTranscriptBase origin b g sign ig) cl X Y
    (by simpa only [mixedTranscriptBase,writeBit,Function.update_self] using hend)
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at body
  exact transcriptSelectWindow_pairFrame b g sign ig _ _ nd hb hg hs origin hz _ _ _ _ _ body

theorem half_counts (divide : Bool) (w : Nat → Wire) (sign : Wire) :
    toffoliCount (half divide w sign)=1020 ∧ measurementCount (half divide w sign)=1021 := by
  have k := OwnQ6Core5.counts divide (ports w sign) (ports_widths w sign)
  simpa only [half,OwnQ6Core5.half,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    Nat.add_zero,Nat.zero_add] using k

theorem body_counts (divide : Bool) (w : Nat → Wire) (sign eff : Wire)
    (hs : (eff::(ports w sign).r++(ports w sign).y).Nodup) :
    toffoliCount (body divide w sign eff)=1276 ∧ measurementCount (body divide w sign eff)=1021 := by
  have len := BalancedCleanup.widths (ports w sign).toLayout (ports_widths w sign)
  have sw := swapRegisters_resources eff (ports w sign).r (ports w sign).y
    (len.2.1.trans len.2.2.1.symm) hs
  have k := half_counts divide w sign
  cases divide <;> simp only [body,Bool.false_eq_true,if_false,if_true,toffoliCount_append,
    measurementCount_append,sw.1,sw.2.1,len.2.1] <;>
    omega

theorem cell_counts (divide : Bool) (w : Nat → Wire) (b g sw sign eff : Wire) (ig is : Bool)
    (hs : (eff::(ports w sign).r++(ports w sign).y).Nodup) :
    toffoliCount (cell divide w b g sw sign eff ig is)=1278 ∧
      measurementCount (cell divide w b g sw sign eff ig is)=1023 := by
  have k := body_counts divide w sign eff hs
  have i := transcriptSelectWindow_counts b sw eff is (body divide w sign eff)
  have o := transcriptSelectWindow_counts b g sign ig
    (transcriptSelectWindow b sw eff is (body divide w sign eff))
  simp only [cell,o.1,o.2,i.1,i.2,k.1,k.2]
  decide

section EndKnownHalf
attribute [local irreducible] Q6EndpointStructural.forwardE Q6StructuralCell.forward OwnQ6Core5.kernel

theorem halfE_counts (divide : Bool) (w : Nat → Wire) (sign : Wire) :
    toffoliCount (halfE divide w sign)=(if divide then 766 else 1020) ∧
      measurementCount (halfE divide w sign)=1021 := by
  cases divide
  · rw [halfE_false]; exact half_counts false w sign
  · have k := Q6EndpointStructural.forwardE_counts (ports w sign) (ports_widths w sign)
    rw [halfE_true,toffoliCount_append,toffoliCount_append,measurementCount_append,
      measurementCount_append,k.1,k.2]
    exact ⟨rfl,rfl⟩
end EndKnownHalf

theorem endpoint_counts (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool) :
    toffoliCount (endpoint divide w b g sign ig)=(if divide then 767 else 1021) ∧
      measurementCount (endpoint divide w b g sign ig)=1022 := by
  have k := halfE_counts divide w sign
  have c := transcriptSelectWindow_counts b g sign ig (halfE divide w sign)
  simp only [endpoint,c.1,c.2,k.1,k.2]
  cases divide <;> decide

section Support
attribute [local irreducible] OwnQ6Core5.kernel

theorem mem_ports_wires (w : Nat → Wire) (sign q : Wire) :
    q∈(ports w sign).wires ↔ q∈sign::ids.map w := by
  simp only [ports,ids,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,wireBlock,
    List.map_append,List.map_cons,List.map_nil,List.mem_append,List.mem_cons,List.not_mem_nil]
  tauto

def sharedIds : List Nat := [765,1026]++balancedSharedIds++List.range' 512 253++[766,767,768]

theorem sharedSites_perm (w : Nat → Wire) (sign : Wire) :
    (sharedSites w sign).Perm (sign::sign::sharedIds.map w) := by
  apply List.perm_iff_count.mpr
  intro q
  simp only [sharedSites,balancedSharedPorts,balancedSharedIds,sharedIds,
    OffsetCleanupBorrowedCaller.carry,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires,wireBlock,List.map_append,List.map_cons,List.map_nil,
    List.count_cons,List.count_append,List.count_nil]
  omega

theorem ids_shared (j : Nat) (hj : j∈ids) : j=2312 ∨ j∈sharedIds := by
  simp only [ids,sharedIds,balancedSharedIds,List.mem_append,List.mem_cons,
    List.not_mem_nil,List.mem_range'_1,or_false] at hj ⊢
  omega

theorem ports_site (w : Nat → Wire) (sign : Wire) (q : Wire) (hq : q∈(ports w sign).wires) :
    q∈sharedSites w sign ∨ q=w 2312 := by
  rcases List.mem_cons.mp ((mem_ports_wires w sign q).mp hq) with h|h
  · left; subst h; simp [sharedSites]
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    rcases ids_shared j hj with e|e
    · right; rw [e]
    · left
      exact (sharedSites_perm w sign).mem_iff.mpr
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem e)))

theorem ports_wires_sub (w : Nat → Wire) (sign : Wire) (W : Finset Wire)
    (hi : (sign::ids.map w).toFinset⊆W) : (ports w sign).wires.toFinset⊆W := by
  intro q hq
  exact hi (List.mem_toFinset.mpr ((mem_ports_wires w sign q).mp (List.mem_toFinset.mp hq)))

private theorem select_support (b source flag : Wire) (v : Bool) (p : Program) :
    wires (transcriptSelectWindow b source flag v p)⊆[b,source,flag].toFinset∪wires p := by
  intro q hq
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil] at hq ⊢ <;> tauto

theorem half_support (divide : Bool) (w : Nat → Wire) (sign : Wire) (W : Finset Wire)
    (hi : (sign::ids.map w).toFinset⊆W) : wires (half divide w sign)⊆W := by
  have k := (OwnQ6Core5.support divide (ports w sign) (ports_widths w sign)).trans
    (ports_wires_sub w sign W hi)
  have sg : sign∈W := hi (by simp)
  simpa only [half,OwnQ6Core5.half,wires_append,wires,Instr.wires,
    Finset.union_empty,Finset.singleton_subset_iff,Finset.union_subset_iff,ports_sign] using
    And.intro (And.intro sg k) sg

theorem body_support (divide : Bool) (w : Nat → Wire) (sign eff : Wire) (W : Finset Wire)
    (hi : (sign::ids.map w).toFinset⊆W) (he : eff∈W) : wires (body divide w sign eff)⊆W := by
  have h := OwnQ6Core5.body_support divide (ports w sign) eff (ports_widths w sign)
  change wires (OwnQ6Core5.body divide (ports w sign) eff)⊆W
  exact h.trans (by
    rw [List.toFinset_cons,Finset.insert_subset_iff]
    exact ⟨he,ports_wires_sub w sign W hi⟩)

theorem cell_support (divide : Bool) (w : Nat → Wire) (b g sw sign eff : Wire) (ig is : Bool)
    (W : Finset Wire) (hi : (sign::ids.map w).toFinset⊆W)
    (hb : b∈W) (hg : g∈W) (hs : sw∈W) (he : eff∈W) :
    wires (cell divide w b g sw sign eff ig is)⊆W := by
  have sg : sign∈W := hi (by simp)
  exact (select_support b g sign ig _).trans (Finset.union_subset
    (by simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_subset_iff,Finset.empty_subset,and_true] using And.intro hb (And.intro hg sg)) ((select_support b sw eff is _).trans
      (Finset.union_subset (by simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_subset_iff,Finset.empty_subset,and_true] using And.intro hb (And.intro hs he)) (body_support divide w sign eff W hi he))))

theorem endpoint_support (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool)
    (W : Finset Wire) (hi : (sign::ids.map w).toFinset⊆W) (hb : b∈W) (hg : g∈W) :
    wires (endpoint divide w b g sign ig)⊆W := by
  have sg : sign∈W := hi (by simp)
  exact (select_support b g sign ig _).trans
    (Finset.union_subset (by simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_subset_iff,Finset.empty_subset,and_true] using And.intro hb (And.intro hg sg)) ((halfE_wires divide w sign).trans (half_support divide w sign W hi)))
end Support

section Natural
open FieldRename

theorem ports_map (f w : Wire → Wire) (sign : Wire) :
    mapCircuit f (ports w sign)=ports (f∘w) (f sign) := by
  simp only [mapCircuit,mapCleanup,ports,wireBlock_map,List.map_append,List.map_cons,List.map_nil,Function.comp_def]



















end Natural

section Physical
/-- Checked on the emitted one-bank ports; narrow programs inherit this result. -/
theorem fixed_kernels_physical :
    GatePhysical (BalancedCircuit.program (ports id 2409)) ∧
      GatePhysical (BalancedInverse.program (ports id 2409)) := by
  have hs : 2409∉ids.map id := by
    simp only [List.map_id]
    intro h
    have bound := ids_bound 2409 h
    omega
  have nd := ports_nodup_injective id 2409 (fun _ _ h => h) hs
  exact ⟨OneBankPhysical5.circuit_physical _ (ports_widths id 2409) nd,
    OneBankPhysical5.inverse_physical _ (ports_widths id 2409) nd⟩

theorem kernel_physical (divide : Bool) (w : Nat → Wire) (hw : Function.Injective w) :
    GatePhysical (OwnQ6Core5.kernel divide (ports w (w 2409))) := by
  have hs:w 2409∉ids.map w:=by
    intro h
    obtain ⟨i,hi,e⟩:=List.mem_map.mp h
    have eq:=hw e
    have bound:=ids_bound i hi
    omega
  have nd:=ports_nodup_injective w (w 2409) hw hs
  exact OwnQ6Core5.kernel_physical divide _ (ports_widths w (w 2409)) nd

theorem half_physical (divide : Bool) (w : Nat → Wire) (hw : Function.Injective w) :
    GatePhysical (half divide w (w 2409)) := by
  have x : GatePhysical [.X (w 2409)] := by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  simpa only [half,OwnQ6Core5.half,gatePhysical_append,ports_sign] using
    And.intro (And.intro x (kernel_physical divide w hw)) x

theorem cell_physical (divide : Bool) (w : Nat → Wire) (hw : Function.Injective w)
    (b g sw eff : Wire) (ig is : Bool)
    (nd : [b,g,sw,w 2409,eff].Nodup)
    (hs : (eff::(ports w (w 2409)).r++(ports w (w 2409)).y).Nodup) :
    GatePhysical (cell divide w b g sw (w 2409) eff ig is) := by
  have swap := swapRegisters_physical eff _ _ hs
  have half := half_physical divide w hw
  have body : GatePhysical (body divide w (w 2409) eff) := by
    cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
      gatePhysical_append] <;> first | exact ⟨swap,half⟩ | exact ⟨half,swap⟩
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true] at nd
  exact transcriptWindow_physical _ _ _ _ _ (by tauto) (by tauto)
    (transcriptWindow_physical _ _ _ _ _ (by tauto) (by tauto) body)

section EndKnownHalf
attribute [local irreducible] Q6EndpointStructural.forwardE Q6StructuralCell.forward OwnQ6Core5.kernel

theorem halfE_physical (divide : Bool) (w : Nat → Wire) (hw : Function.Injective w) :
    GatePhysical (halfE divide w (w 2409)) := by
  cases divide
  · rw [halfE_false]; exact half_physical false w hw
  · have hs:w 2409∉ids.map w:=by
      intro h
      obtain ⟨i,hi,e⟩:=List.mem_map.mp h
      have eq:=hw e
      have bound:=ids_bound i hi
      omega
    have nd:=ports_nodup_injective w (w 2409) hw hs
    have k := Q6EndpointStructural.forwardE_physical (ports w (w 2409)) (ports_widths w (w 2409)) nd
    have x : GatePhysical [.X (w 2409)] := by
      simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
    rw [halfE_true,gatePhysical_append,gatePhysical_append]
    exact ⟨⟨x,k⟩,x⟩
end EndKnownHalf

theorem endpoint_physical (divide : Bool) (w : Nat → Wire) (hw : Function.Injective w)
    (b g : Wire) (ig : Bool) (nd : [b,g,w 2409].Nodup) :
    GatePhysical (endpoint divide w b g (w 2409) ig) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true] at nd
  exact transcriptWindow_physical _ _ _ _ _ (by tauto) (by tauto) (halfE_physical divide w hw)
end Physical

section Slots
open Challenge Baselines

theorem half_gateSlots_le (divide : Bool) (w : Nat → Wire) (sign : Wire) :
    gateSlots (half divide w sign)≤25002 := by
  have k := OwnQ6Core5.kernel_gateSlots_le divide (ports w sign) (ports_widths w sign)
  simp only [half,OwnQ6Core5.half,gateSlots_append,gateSlots_cons,gateSlots_nil,instructionSlots]
  split_ifs at k <;> omega

theorem cell_gateSlots_le (divide : Bool) (w : Nat → Wire)
    (b g sw sign eff : Wire) (ig is : Bool) :
    gateSlots (cell divide w b g sw sign eff ig is)≤26000 := by
  have h := half_gateSlots_le divide w sign
  have len := BalancedCleanup.widths (ports w sign).toLayout (ports_widths w sign)
  have swap : gateSlots (swapRegisters eff (ports w sign).r (ports w sign).y)≤768 := by
    rw [swapRegisters_gateSlots]
    rw [len.2.1]
    omega
  have body : gateSlots (body divide w sign eff)≤25770 := by
    cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
      gateSlots_append] <;> omega
  have i := selectWindow_gateSlots_le b sw eff is (Q6EndpointCell.body divide w sign eff)
  have o := selectWindow_gateSlots_le b g sign ig
    (transcriptSelectWindow b sw eff is (Q6EndpointCell.body divide w sign eff))
  change gateSlots (transcriptSelectWindow _ _ _ _ _)≤_
  omega

section EndKnownHalf
attribute [local irreducible] Q6EndpointStructural.forwardE Q6StructuralCell.forward OwnQ6Core5.kernel

theorem halfE_gateSlots_le (divide : Bool) (w : Nat → Wire) (sign : Wire) :
    gateSlots (halfE divide w sign)≤25002 := by
  cases divide
  · rw [halfE_false]; exact half_gateSlots_le false w sign
  · have k := Q6EndpointStructural.forwardE_slots (ports w sign) (ports_widths w sign)
    rw [halfE_true,gateSlots_append,gateSlots_append]
    have x : gateSlots [Instr.X sign]=1 := rfl
    omega
end EndKnownHalf

theorem endpoint_gateSlots_le (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool) :
    gateSlots (endpoint divide w b g sign ig)≤26000 := by
  have h := halfE_gateSlots_le divide w sign
  have k := selectWindow_gateSlots_le b g sign ig (halfE divide w sign)
  change gateSlots (transcriptSelectWindow _ _ _ _ _)≤_
  omega
end Slots

end ECDSAAdd.Entrant.Q6EndpointCell

end




-- ENDPOINT COMPONENT ReplayE.lean
-- ===== ECDSAAdd.Submission.Entrant.Q6EndpointReplay =====
section

/-! One-bank field replay with five-trit history and final late-sign placement.
The one-bank method is attributed in Q6EndpointCell. All codecs and field
placements are the checked local five-trit constructions. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointReplay
open Arithmetic Secp256k1 BalancedField MappedCompressed CompressedFieldSupport OffsetBorrowedCanonical
attribute [local irreducible] run wires toffoliCount measurementCount

structure Context (origin : BasisState) : Prop where
  hn : (skywalkSharedWires base).Nodup
  ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base
  hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base
  hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)
  hg0 : origin (base 2409)=false
  hs0 : origin (base 2410)=false
  env : Env base origin
  legal : History5.RawLegal base 102 origin
  parity : origin (base 2312)=false

def rawReplay (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then
      Q6EndpointCell.cell true base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) l.2.1 l.2.2++rawReplay true ls
    else rawReplay false ls++
      Q6EndpointCell.cell false base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) l.2.1 l.2.2

def body (divide : Bool) (j : Nat) : Program := rawReplay divide (Replay5.letters j)

def basePacket (divide : Bool) (j : Nat) : Program :=
  History5.decode base (5*j)++body divide j++History5.encode base (5*j)

def packet (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacket divide j)

def groups (divide : Bool) (j n : Nat) : Program := PacketSequence.program divide (packet divide) j n

def firstBody (divide : Bool) : Program :=
  if divide then Replay5.firstSwap++rawReplay true Replay5.restLetters
  else rawReplay false Replay5.restLetters++UncompSwap.firstSwapM

def baseFirstPacket (divide : Bool) : Program :=
  History5.decode base 0++firstBody divide++History5.encode base 0

def firstPacket (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacket divide)

def rawEnd (divide : Bool) : Program :=
  Q6EndpointCell.endpoint divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1

def endPacket (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEnd divide)

def logicalReplay (divide : Bool) : Program :=
  if divide then firstPacket true++groups true 1 101++endPacket true
  else endPacket false++groups false 1 101++firstPacket false

def replay (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplay divide)


def fieldSites : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset

def readSites (start : Nat) : Finset Wire := fieldSites ∪ {base 2400,base 2410} ∪
  wires (History5.encode base start)

theorem raw_support (divide : Bool) (ls : List MixedTranscriptLetter) (W : Finset Wire)
    (hi : fieldSites⊆W) (hb : base 2400∈W) (he : base 2410∈W)
    (controls : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) : wires (rawReplay divide ls)⊆W := by
  induction ls with
  | nil => simp [rawReplay,wires]
  | cons l ls ih =>
    have c := Q6EndpointCell.cell_support divide base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
      l.2.1 l.2.2 W hi hb (controls l (by simp)).1 (controls l (by simp)).2 he
    have rest := ih (fun k hk => controls k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,wires_append,
      Finset.union_subset_iff] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆readSites (5*j) := by
  apply raw_support
  · exact fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  · intro l hl
    have c := Replay5.letters_controls j hj l hl
    exact ⟨Finset.mem_union_right _ c.1,Finset.mem_union_right _ c.2⟩

theorem readSites_sub (start : Nat) : readSites start⊆
    History5.groupReadSites base (base 2400) (base 2409) (base 2410) start ∪ {base 2312} := by
  intro q hq
  simp only [readSites,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr h)))
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem body_read_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (body divide j)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) (5*j) ∪ {base 2312} :=
  (body_support divide j hj).trans (readSites_sub (5*j))

theorem firstBody_support (divide : Bool) : wires (firstBody divide)⊆readSites 0 := by
  let W := readSites 0
  have hi : fieldSites⊆W := fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hb : base 2400∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have he : base 2410∈W := Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
  have hs : base 1028∈W := Finset.mem_union_right _ (by
    simpa using (Replay5.history_controls 0 0 (by decide)).2)
  have swap : wires Replay5.firstSwap⊆W := by
    apply DirectSupport.selectWindow _ _ _ _ _ W hb hs he
    have sub : wires (swapRegisters (base 2410) (balancedSharedPorts base (base 2409)).r
        (balancedSharedPorts base (base 2409)).y)⊆wires (Q6EndpointCell.body true base (base 2409) (base 2410)) := by
      simp only [Q6EndpointCell.body,if_true,wires_append,Q6EndpointCell.ports_r,Q6EndpointCell.ports_y]
      exact Finset.subset_union_right
    exact sub.trans (Q6EndpointCell.body_support true base (base 2409) (base 2410) W hi he)
  have rest : wires (rawReplay divide Replay5.restLetters)⊆W := by
    apply raw_support divide Replay5.restLetters W hi hb he
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have bound := List.mem_range'_1.mp hk
    have tape := mixedTape_base_getD k (by omega)
    have controls := Replay5.history_controls 0 k (by omega)
    simp only [Nat.zero_add] at controls
    simpa only [tapeLetter,tape] using
      (show base k∈W ∧ base (1028+k)∈W from
        ⟨Finset.mem_union_right _ controls.1,Finset.mem_union_right _ controls.2⟩)
  have swapM : wires UncompSwap.firstSwapM⊆W := by
    rw [UncompSwap.firstSwapM_wires]; exact swap
  cases divide <;> simp only [firstBody,Bool.false_eq_true,if_false,if_true,wires_append,Finset.union_subset_iff]
  · exact ⟨rest,swapM⟩
  · exact ⟨swap,rest⟩

theorem firstBody_read_support (divide : Bool) :
    wires (firstBody divide)⊆History5.groupReadSites base (base 2400) (base 2409) (base 2410) 0 ∪ {base 2312} :=
  (firstBody_support divide).trans (readSites_sub 0)

theorem rawEnd_support (divide : Bool) : wires (rawEnd divide)⊆fieldSites ∪ {base 2400,base 510} := by
  apply Q6EndpointCell.endpoint_support divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  · exact Finset.subset_union_left
  · exact Finset.mem_union_right _ (by simp)
  · exact Finset.mem_union_right _ (by simp)

theorem rawEnd_read_support (divide : Bool) :
    wires (rawEnd divide)⊆(sharedSites base (base 2409)).toFinset∪{base 2312,base 2400,base 510} := by
  intro q hq
  rcases Finset.mem_union.mp (rawEnd_support divide hq) with h|h
  · have hp := (Q6EndpointCell.mem_ports_wires base (base 2409) q).mpr (List.mem_toFinset.mp h)
    rcases Q6EndpointCell.ports_site base (base 2409) q hp with h|h
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr h)
    · exact Finset.mem_union_right _ (by simp [h])
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    exact Finset.mem_union_right _ (by simp only [Finset.mem_insert,Finset.mem_singleton]; tauto)

theorem rawEnd_disjoint (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base) :
    Disjoint (wires (History5.allEncode base 102)) (wires (rawEnd divide)) := by
  apply Finset.disjoint_left.mpr
  intro q hq used
  obtain ⟨j,hj,member⟩ := History5.allEncode_member base 102 q hq
  obtain ⟨r,rfl⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) q member
  have read := rawEnd_read_support divide used
  rcases Finset.mem_union.mp read with read|read
  · exact History5.history_active_away base (base 2409) hn (hp _ (by simp)) (5*j) (by omega) r
      (List.mem_toFinset.mp read)
  · have bound := History5.historyId_bound (5*j) (by omega) r
    have own : History5.historyMap base (5*j) r∈skywalkPoolWires base := by
      exact List.mem_map.mpr ⟨History5.historyId (5*j) r,by simp only [List.mem_range'_1]; omega,rfl⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at read
    rcases read with eq|eq|eq
    · have same := base_injective eq
      omega
    · exact hp _ (by simp) (eq ▸ own)
    · have same := base_injective eq
      have rr := r.isLt
      unfold History5.historyId at same
      split_ifs at same <;> omega

private theorem letter_layout (origin : BasisState) (ctx : Context origin)
    (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (l : MixedTranscriptLetter) (hl : l∈ls) :
    BalancedTranscriptLayout (Q6EndpointCell.ports base (base 2409))
      (base 2400) l.1.1 l.1.2 (base 2410) :=
  Q6EndpointCell.ports_transcript base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) ctx.hn
    (balancedSharedTranscriptLayout_direct base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) (hf l hl) ctx.ho)
    (ctx.ho _ (by simp)) (ctx.ho _ (by simp))

theorem raw_frame (divide : Bool) (ls : List MixedTranscriptLetter)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawReplay divide ls)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).1)
        (centerWord (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) ls) (X,Y)).2)) := by
  have clean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
  induction ls generalizing X Y with
  | nil =>
    intro s m h
    cases divide <;> simpa only [rawReplay,directionalPayload,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true,mixedTranscriptControls,List.map_nil,skywalkPayloadReplay,
      skywalkPayloadReplayInverse,run] using And.intro (Eq.refl s.phase) h
  | cons l ls ih =>
    have layout := letter_layout origin ctx (l::ls) hf l (by simp)
    have tailLayout := fun k hk => hf k (List.mem_cons_of_mem l hk)
    cases divide
    · let Q := skywalkPayloadReplayInverse (mixedTranscriptControls origin (base 2400) ls) (X,Y)
      have rest := ih tailLayout X Y
      have head := Q6EndpointCell.cell_frame false base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 ctx.hs0 clean Q.1 Q.2
      simpa only [rawReplay,Bool.false_eq_true,if_false,directionalPayload,Bool.not_false,if_true,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplayInverse,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using rest.seq head
    · let Q := skywalkPayloadCell (mixedTranscriptBit origin (base 2400) l.1.1 l.2.1)
        (mixedTranscriptBit origin (base 2400) l.1.2 l.2.2) (X,Y)
      have head := Q6EndpointCell.cell_frame true base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
        l.2.1 l.2.2 layout origin ctx.hg0 ctx.hs0 clean X Y
      have rest := ih tailLayout Q.1 Q.2
      simpa only [rawReplay,if_true,directionalPayload,Bool.not_true,Bool.false_eq_true,if_false,
        mixedTranscriptControls,List.map_cons,skywalkPayloadReplay,Q6EndpointCell.payload,Q,Prod.mk.eta]
        using head.seq rest

private theorem rest_layout
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) Replay5.restLetters := by
  intro l hl
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have bound := List.mem_range'_1.mp hk
  simpa only [Replay5.restLetters,tapeLetter] using
    mixedTape_getD_layout base _ _ _ hf k (by omega)

private theorem first_layout (origin : BasisState) (ctx : Context origin) :
    BalancedTranscriptLayout (balancedSharedPorts base (base 2409))
      (base 2400) (base 0) (base 1028) (base 2410) := by
  have h := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 0 (by decide)) ctx.ho
  rw [mixedTape_base_getD 0 (by decide)] at h
  exact h

theorem packet_frame (divide : Bool) (j : Nat) (hj : j<102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (packet divide j) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).1
        (directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)).2
        (run (packet divide j) m s) := by
  have raw := raw_frame divide (Replay5.letters j) (Replay5.letters_layouts ctx.hf j hj) origin ctx X Y
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp j hj origin X Y _ _ _ (body_read_support divide j hj) raw s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi j) (basePacket divide j)
    (fun q hq => Placement5.pi_outside j q hj hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (packet divide j) m s=run (basePacket divide j) m s := eq
  rw [same]
  exact fresh


theorem groups_frame (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (origin : BasisState) (ctx : Context origin) (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (groups divide j n) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.groupsPayload divide origin j n (X,Y)).1
        (Replay5.groupsPayload divide origin j n (X,Y)).2 (run (groups divide j n) m s) := by
  have result := PacketSequence.frame divide (packet divide) (packet divide)
    (fun k V => directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun V t => History5.EncodedFieldFrame5 base (base 2409) origin V.1 V.2 t) 102 (fun _ => rfl)
    (fun k hk V t records h => ⟨rfl,packet_frame divide k hk origin ctx V.1 V.2 t records h⟩)
    j n bound (X,Y) s m input
  exact result.2

theorem firstBody_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (firstBody divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.firstPayload divide origin (X,Y)).1)
        (centerWord (Replay5.firstPayload divide origin (X,Y)).2)) := by
  let S := mixedTranscriptBit origin (base 2400) (base 1028) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
  have swap := EntrySelectedSwapFrame.selectedSwap_frame base (base 2400) (base 0) (base 1028)
    (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
    (first_layout origin ctx) origin ctx.hs0
  cases divide
  · let V := directionalPayload true (mixedTranscriptControls origin (base 2400) Replay5.restLetters) (X,Y)
    have zero : (if S then V.1 else V.2)=0 := by
      have h := hz rfl
      have k : ∀ (b : Bool) (p : Fp×Fp), (if b then (p.2,p.1) else p).2=(if b then p.1 else p.2) := by
        intro b p; cases b <;> rfl
      simp only [Replay5.firstPayload,Bool.false_eq_true,if_false,k] at h
      exact h
    have swapM := UncompSwap.selectedSwapM_frame base (base 2400) (base 0) (base 1028)
      (base 2409) (base 2410) (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (first_layout origin ctx) origin ctx.hs0 V.1 V.2 zero
    have rest := raw_frame false Replay5.restLetters (rest_layout ctx.hf) origin ctx X Y
    have out := rest.seq swapM
    cases hS : S <;> simpa only [firstBody,UncompSwap.firstSwapM,Replay5.firstPayload,Bool.false_eq_true,
      if_false,Bool.not_false,if_true,S,hS,V] using out
  · have out := (swap X Y).seq (raw_frame true Replay5.restLetters (rest_layout ctx.hf)
      origin ctx (if S then Y else X) (if S then X else Y))
    cases hS : S <;> simpa only [firstBody,Replay5.firstPayload,if_true,Bool.not_true,
      Bool.false_eq_true,if_false,S,hS] using out

theorem firstPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s)
    (hz : divide=false → (Replay5.firstPayload divide origin (X,Y)).2=0) :
    (run (firstPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.firstPayload divide origin (X,Y)).1
        (Replay5.firstPayload divide origin (X,Y)).2 (run (firstPacket divide) m s) := by
  have fresh := FieldFrameOB5.encoded_window_step base (base 2400) (base 2409) (base 2410)
    ctx.hn ctx.hp 0 (by decide) origin X Y _ _ _ (firstBody_read_support divide)
    (firstBody_frame divide origin ctx X Y hz) s m input ctx.legal
  have eq := Replay5.placed_eq (Placement5.pi 0) (baseFirstPacket divide)
    (fun q hq => Placement5.pi_outside 0 q (by decide) hq) s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (firstPacket divide) m s=run (baseFirstPacket divide) m s := eq
  rw [same]
  exact fresh


theorem rawEnd_frame (divide : Bool) (origin : BasisState) (ctx : Context origin) (X Y : Fp)
    (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) :
    Triple (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (rawEnd divide)
      (PairFrame (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y origin
        (centerWord (Replay5.endPayload divide origin (X,Y)).1)
        (centerWord (Replay5.endPayload divide origin (X,Y)).2)) := by
  have layout := balancedSharedTranscriptLayout_direct base (base 2400) _ _ (base 2409) (base 2410)
    (mixedTape_getD_layout base _ _ _ ctx.hf 510 (by decide)) ctx.ho
  rw [mixedTape_base_getD 510 (by decide)] at layout
  have newLayout := Q6EndpointCell.ports_transcript base (base 2400) (base 510) (base 1538)
    (base 2409) (base 2410) ctx.hn layout (ctx.ho _ (by simp)) (ctx.ho _ (by simp))
  have result := Q6EndpointCell.endpoint_frame divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1 newLayout.kernel (by decide)
    (newLayout.outside _ (by simp)) (newLayout.outside _ (by simp))
    (newLayout.outside _ (by simp [Q6EndpointCell.ports])) origin ctx.hg0
    (Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity) X Y (fun h => by
      have e := hend h
      subst h
      simpa only [Replay5.endPayload,if_true] using e)
  simpa only [rawEnd,Replay5.endPayload,Prod.fst,Prod.snd] using result

theorem endPacket_frame (divide : Bool) (origin : BasisState) (ctx : Context origin)
    (X Y : Fp) (hend : divide=true → (Replay5.endPayload divide origin (X,Y)).1=Y) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin X Y s) :
    (run (endPacket divide) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin (Replay5.endPayload divide origin (X,Y)).1
        (Replay5.endPayload divide origin (X,Y)).2 (run (endPacket divide) m s) := by
  have fresh := History5.encoded_disjoint_step base (base 2409)
    (skywalkShared_integer_nodup base ctx.hn) origin X Y _ _ _ (rawEnd_disjoint divide ctx.hn ctx.hp)
    (rawEnd_frame divide origin ctx X Y hend) s m input
  have eq := Replay5.placed_eq Placement5.pi0 (rawEnd divide) Placement5.pi0_outside s m
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal X Y s input)
    (History5.encoded_zero_region base (base 2409) ctx.hn (ctx.hp _ (by simp)) origin ctx.env ctx.legal _ _ _ fresh.2)
  have same : run (endPacket divide) m s=run (rawEnd divide) m s := eq
  rw [same]
  exact fresh

attribute [local irreducible] Replay5.groupsPayload Replay5.firstPayload Replay5.endPayload
  mixedTranscriptUnitTrace SkywalkTrace.trace SkywalkTrace.next Nat.iterate

theorem logical_forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (logicalReplay true) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z Z (run (logicalReplay true) m s) := by
  let Z := if origin (base 2400) then Y/(x:Fp) else Y
  have result := run_three_states (firstPacket true) (groups true 1 101) (endPacket true)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y 0 a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z Z b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := firstPacket_frame true origin ctx Y 0 a m1 h (fun e => absurd e (by decide))
      rw [hab] at first
      have middle := groups_frame true 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have fp := Replay5.forward_payload origin x Y hx0 hx trace
      have last := endPacket_frame true origin ctx _ _ (fun _ => by
        rw [Prod.mk.eta,fp]
        exact (congrArg Prod.snd fp).symm.trans (by simp only [Replay5.endPayload])) c m3 middle.2
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.forward_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,if_true,List.append_assoc] using result input

theorem logical_inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool)
    (input : History5.EncodedFieldFrame5 base (base 2409) origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (logicalReplay false) m s).phase=s.phase ∧
      History5.EncodedFieldFrame5 base (base 2409) origin Z 0 (run (logicalReplay false) m s) := by
  let Z := if origin (base 2400) then Y*(x:Fp) else Y
  have result := run_three_states (endPacket false) (groups false 1 101) (firstPacket false)
    (fun a b => History5.EncodedFieldFrame5 base (base 2409) origin Y Y a →
      b.phase=a.phase ∧ History5.EncodedFieldFrame5 base (base 2409) origin Z 0 b) (by
      intro a b c d m1 m2 m3 hab hbc hcd h
      have first := endPacket_frame false origin ctx Y Y (fun e => absurd e (by decide)) a m1 h
      rw [hab] at first
      have middle := groups_frame false 1 101 (by decide) origin ctx _ _ b m2 first.2
      rw [hbc] at middle
      have last := firstPacket_frame false origin ctx _ _ c m3 middle.2 (fun _ => by
        simp only [Prod.mk.eta]
        exact congrArg Prod.snd (Replay5.inverse_payload origin x Y hx0 hx trace))
      rw [hcd] at last
      refine ⟨last.1.trans (middle.1.trans first.1),?_⟩
      simpa only [Prod.mk.eta,Replay5.inverse_payload origin x Y hx0 hx trace] using last.2) s m
  simpa only [logicalReplay,Bool.false_eq_true,if_false,List.append_assoc] using result input

theorem forward_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y 0 s) :
    let Z := if origin (base 2400) then Y/(x:Fp) else Y
    (run (replay true) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z Z (run (replay true) m s) :=
  FieldFrameOB5.placed_step (logicalReplay true) origin Y 0 _ _
    (logical_forward_frame origin ctx x hx0 hx trace Y) s m input

theorem inverse_frame (origin : BasisState) (ctx : Context origin)
    (x : Nat) (hx0 : 0<x) (hx : x<p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedFieldFrame origin Y Y s) :
    let Z := if origin (base 2400) then Y*(x:Fp) else Y
    (run (replay false) m s).phase=s.phase ∧
      FieldFrameOB5.EncodedFieldFrame origin Z 0 (run (replay false) m s) :=
  FieldFrameOB5.placed_step (logicalReplay false) origin Y Y _ _
    (logical_inverse_frame origin ctx x hx0 hx trace Y) s m input


















section Counts

private theorem swap_nodup (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    (base 2410::(Q6EndpointCell.ports base (base 2409)).r++(Q6EndpointCell.ports base (base 2409)).y).Nodup := by
  have own : base 2410∉balancedSharedIds.map base := fun h =>
    ho (balancedSharedLayout_mapSubset base balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup base (base 2410) hn own
  have aw := BalancedCircuit.flagAway (balancedSharedPorts base (base 2410)) nd (base 2410)
    (by simp [balancedSharedPorts])
  apply List.nodup_cons.mpr
  refine ⟨?_,balancedSharedLayout_pairND base (base 2410) hn⟩
  intro h
  rcases List.mem_append.mp h with h|h
  · have hr : base 2410∈(balancedSharedPorts base (base 2410)).r := by
      simpa only [Q6EndpointCell.ports_r,balancedSharedPorts_r] using h
    exact aw (List.mem_append_left _ (List.mem_append_left _ hr))
  · have hy : base 2410∈(balancedSharedPorts base (base 2410)).y := by
      simpa only [Q6EndpointCell.ports_y,balancedSharedPorts_y] using h
    exact aw (List.mem_append_left _ (List.mem_append_right _ hy))

theorem raw_counts (divide : Bool) (ls : List MixedTranscriptLetter)
    (hs : (base 2410::(Q6EndpointCell.ports base (base 2409)).r++(Q6EndpointCell.ports base (base 2409)).y).Nodup) :
    toffoliCount (rawReplay divide ls)=ls.length*1278 ∧
      measurementCount (rawReplay divide ls)=ls.length*1023 := by
  induction ls with
  | nil => simp [rawReplay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have c := Q6EndpointCell.cell_counts divide base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410)
      l.2.1 l.2.2 hs
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append,List.length_cons] at c ih ⊢
    all_goals constructor <;> omega

theorem packet_counts (divide : Bool) (j : Nat)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (packet divide j)=6410 ∧ measurementCount (packet divide j)=5121 := by
  have raw := raw_counts divide (Replay5.letters j) (swap_nodup hn ho)
  have len : (Replay5.letters j).length=5 := by simp [Replay5.letters]
  rw [len] at raw
  have e := History5.encode_counts base (5*j)
  have d := History5.decode_counts base (5*j)
  have renamed := renameProgram_counts (shifted (Placement5.pi j)) (basePacket divide j)
  change toffoliCount (renameProgram _ (basePacket divide j))=_ ∧
    measurementCount (renameProgram _ (basePacket divide j))=_
  rw [renamed.1,renamed.2]
  simp only [basePacket,toffoliCount_append,measurementCount_append,body] at *
  constructor <;> omega


theorem groups_counts (divide : Bool) (j n : Nat)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (groups divide j n)=n*6410 ∧ measurementCount (groups divide j n)=n*5121 := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,toffoliCount,measurementCount]
  | succ n ih =>
    have head := packet_counts divide j hn ho
    have rest := ih (j+1)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      toffoliCount_append,measurementCount_append] at head rest ⊢
    all_goals constructor <;> omega


theorem firstPacket_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (firstPacket divide)=(if divide then 5389 else 5133) ∧
      measurementCount (firstPacket divide)=(if divide then 4099 else 4355) := by
  have raw := raw_counts divide Replay5.restLetters (swap_nodup hn ho)
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at raw
  have sw := Replay5.firstSwap_counts hn ho
  have swM := UncompSwap.firstSwapM_counts
  have e := History5.encode_counts base 0
  have d := History5.decode_counts base 0
  have renamed := renameProgram_counts (shifted (Placement5.pi 0)) (baseFirstPacket divide)
  change toffoliCount (renameProgram _ (baseFirstPacket divide))=_ ∧
    measurementCount (renameProgram _ (baseFirstPacket divide))=_
  rw [renamed.1,renamed.2]
  cases divide <;> simp only [baseFirstPacket,firstBody,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] at raw ⊢
  all_goals constructor <;> omega


theorem endPacket_counts (divide : Bool) :
    toffoliCount (endPacket divide)=(if divide then 767 else 1021) ∧
      measurementCount (endPacket divide)=1022 := by
  have c := Q6EndpointCell.endpoint_counts divide base (base 2400) (base 510) (base 2409)
    (mixedTranscriptUnitTrace.getD 510 (false,false)).1
  simpa only [endPacket,rawEnd,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2] using c

theorem logicalReplay_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (logicalReplay divide)=(if divide then 653566 else 653564) ∧
      measurementCount (logicalReplay divide)=(if divide then 522342 else 522598) := by
  have first := firstPacket_counts divide hn ho
  have rest := groups_counts divide 1 101 hn ho
  have last := endPacket_counts divide
  cases divide <;> simp only [logicalReplay,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] at first rest last ⊢
  all_goals constructor <;> omega


theorem replay_counts (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (replay divide)=(if divide then 653566 else 653564) ∧
      measurementCount (replay divide)=(if divide then 522342 else 522598) := by
  simpa only [replay,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using
    logicalReplay_counts divide hn ho


end Counts

section Physical

theorem raw_physical (divide : Bool) (ls : List MixedTranscriptLetter)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) ls) :
    GatePhysical (rawReplay divide ls) := by
  induction ls with
  | nil => simp [rawReplay,GatePhysical]
  | cons l ls ih =>
    have nd : [base 2400,l.1.1,l.1.2,base 2409,base 2410].Nodup := by
      simpa only [List.take_succ_cons,List.take_zero] using
        (show ((base 2400::l.1.1::l.1.2::base 2409::base 2410::(skywalkSharedField base).wires).take 5).Nodup
          from (hf l (by simp)).controls.take)
    have cell := Q6EndpointCell.cell_physical divide base base_injective (base 2400) l.1.1 l.1.2 (base 2410)
      l.2.1 l.2.2 nd (swap_nodup hn (ho _ (by simp)))
    have rest := ih (fun k hk => hf k (List.mem_cons_of_mem l hk))
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append] at cell rest ⊢
    · exact ⟨rest,cell⟩
    · exact ⟨cell,rest⟩

theorem packet_physical (divide : Bool) (j : Nat) (hj : j<102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters j)) :
    GatePhysical (packet divide j) := by
  have e := History5.encode_physical base (skywalkShared_integer_nodup base hn) (5*j) (by omega)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base hn) (5*j) (by omega)
  have raw : GatePhysical (body divide j) := raw_physical divide _ hn ho hf
  have p : GatePhysical (basePacket divide j) := by
    simpa only [basePacket,gatePhysical_append] using And.intro (And.intro d raw) e
  exact gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ p

theorem groups_physical (divide : Bool) (j n : Nat) (bound : j+n≤102)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : ∀k,k<102 → MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (Replay5.letters k)) :
    GatePhysical (groups divide j n) := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,GatePhysical]
  | succ n ih =>
    have head := packet_physical divide j (by omega) hn ho (hf j (by omega))
    have rest := ih (j+1) (by omega)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩

theorem firstPacket_physical (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (firstPacket divide) := by
  have swap : GatePhysical Replay5.firstSwap := by
    simp only [Replay5.firstSwap,EntryFieldSeedCancellation.selectedSwap]
    apply transcriptWindow_physical _ _ _ _ _ (by decide) (by decide)
    exact swapRegisters_physical _ _ _ (swap_nodup hn (ho _ (by simp)))
  have swapM : GatePhysical UncompSwap.firstSwapM :=
    UncompSwap.firstSwapM_physical (swap_nodup hn (ho _ (by simp)))
  have rest := raw_physical divide Replay5.restLetters hn ho (rest_layout hf)
  have e := History5.encode_physical base (skywalkShared_integer_nodup base hn) 0 (by decide)
  have d := History5.decode_physical base (skywalkShared_integer_nodup base hn) 0 (by decide)
  have p : GatePhysical (baseFirstPacket divide) := by
    cases divide <;> simp only [baseFirstPacket,firstBody,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
    · exact ⟨⟨d,⟨rest,swapM⟩⟩,e⟩
    · exact ⟨⟨d,⟨swap,rest⟩⟩,e⟩
  exact gatePhysical_rename _ (shifted (Placement5.pi 0)).injective _ p

theorem endPacket_physical (divide : Bool) : GatePhysical (endPacket divide) :=
  gatePhysical_rename _ (shifted Placement5.pi0).injective _
    (Q6EndpointCell.endpoint_physical divide base base_injective (base 2400) (base 510)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 (by decide))

theorem replay_physical (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (replay divide) := by
  have first := firstPacket_physical divide hn ho hf
  have rest := groups_physical divide 1 101 (by decide) hn ho (Replay5.letters_layouts hf)
  have last := endPacket_physical divide
  apply gatePhysical_rename _ (OB5.sig_injective 511 (by decide))
  cases divide <;> simp only [logicalReplay,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨⟨last,rest⟩,first⟩
  · exact ⟨⟨first,rest⟩,last⟩

end Physical

section Slots
open Challenge Baselines
attribute [local irreducible] gateSlots

theorem raw_gateSlots_le (divide : Bool) (ls : List MixedTranscriptLetter) :
    gateSlots (rawReplay divide ls)≤ls.length*26000 := by
  induction ls with
  | nil => simp [rawReplay]
  | cons l ls ih =>
    have c := Q6EndpointCell.cell_gateSlots_le divide base (base 2400) l.1.1 l.1.2 (base 2409) (base 2410) l.2.1 l.2.2
    cases divide <;> simp only [rawReplay,Bool.false_eq_true,if_false,if_true,gateSlots_append,List.length_cons] at c ih ⊢ <;> omega

theorem packet_gateSlots_le (divide : Bool) (j : Nat) : gateSlots (packet divide j)≤130356 := by
  have raw : gateSlots (body divide j)≤5*26000 := by
    simpa only [Replay5.letters,List.length_map,List.length_range] using
      raw_gateSlots_le divide (Replay5.letters j)
  have codec := History5.codec_slots base (5*j)
  simp only [packet,rename_gateSlots,basePacket,gateSlots_append]
  omega

theorem groups_gateSlots_le (divide : Bool) (j n : Nat) : gateSlots (groups divide j n)≤n*130356 := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program]
  | succ n ih =>
    have head := packet_gateSlots_le divide j
    have rest := ih (j+1)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,gateSlots_append] <;> omega

theorem firstPacket_gateSlots_le (divide : Bool) : gateSlots (firstPacket divide)≤105388 := by
  have swapM := UncompSwap.firstSwapM_gateSlots_le
  have raw := raw_gateSlots_le divide Replay5.restLetters
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at raw
  have codec := History5.codec_slots base 0
  have width := (BalancedCleanup.widths (balancedSharedPorts base (base 2409)).toLayout
    (balancedSharedPorts_widths base (base 2409))).2.1
  have swap : gateSlots Replay5.firstSwap≤800 := by
    have h := selectWindow_gateSlots_le (base 2400) (base 1028) (base 2410)
      (mixedTranscriptUnitTrace.getD 0 (false,false)).2
      (swapRegisters (base 2410) (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y)
    rw [swapRegisters_gateSlots,width] at h
    simpa only [Replay5.firstSwap,EntryFieldSeedCancellation.selectedSwap] using h.trans (by decide)
  cases divide <;> simp only [firstPacket,rename_gateSlots,baseFirstPacket,firstBody,
    Bool.false_eq_true,if_false,if_true,gateSlots_append] <;> omega

theorem endPacket_gateSlots_le (divide : Bool) : gateSlots (endPacket divide)≤26000 := by
  simpa only [endPacket,rename_gateSlots,rawEnd] using
    Q6EndpointCell.endpoint_gateSlots_le divide base (base 2400) (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1

theorem replay_gateSlots_le (divide : Bool) : gateSlots (replay divide)≤13941000 := by
  have first := firstPacket_gateSlots_le divide
  have rest := groups_gateSlots_le divide 1 101
  have last := endPacket_gateSlots_le divide
  cases divide <;> simp only [replay,rename_gateSlots,logicalReplay,Bool.false_eq_true,if_false,if_true,gateSlots_append]
    at first rest last ⊢ <;> omega

end Slots

end ECDSAAdd.Entrant.Q6EndpointReplay

end

-- ENDPOINT COMPONENT SWE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointSW
open ECDSAAdd.Arithmetic MappedCompressed CompressedFieldSupport Secp256k1 DirectSkywalk SW
attribute [local irreducible] wires

/-! ### Definitions -/

def cellS (divide : Bool) (g sw : Wire) : Program :=
  selW g (base 2409) (selW sw (base 2410) (Q6EndpointCell.body divide base (base 2409) (base 2410)))

def rawReplayS (divide : Bool) : List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => if divide then cellS true l.1.1 l.1.2++rawReplayS true ls
    else rawReplayS false ls++cellS false l.1.1 l.1.2

def basePacketS (divide : Bool) (j : Nat) : Program :=
  History5.decode base (5*j)++rawReplayS divide (Replay5.letters j)++History5.encode base (5*j)

def packetS (divide : Bool) (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (basePacketS divide j)

def groupsS (divide : Bool) (j n : Nat) : Program :=
  PacketSequence.program divide (packetS divide) j n

def swapBody : Program :=
  swapRegisters (base 2410) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def firstSwapS : Program := selW (base 1028) (base 2410) swapBody

def swapBodyM : Program :=
  UncompSwap.mswap (base 2410) (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y

def firstSwapMS : Program := selW (base 1028) (base 2410) swapBodyM

def firstBodyS (divide : Bool) : Program :=
  if divide then firstSwapS++rawReplayS true Replay5.restLetters
  else rawReplayS false Replay5.restLetters++firstSwapMS

def baseFirstPacketS (divide : Bool) : Program :=
  History5.decode base 0++firstBodyS divide++History5.encode base 0

def firstPacketS (divide : Bool) : Program :=
  renameProgram (shifted (Placement5.pi 0)) (baseFirstPacketS divide)

def rawEndS (divide : Bool) : Program :=
  selW (base 510) (base 2409) (Q6EndpointCell.halfE divide base (base 2409))

def endPacketS (divide : Bool) : Program := renameProgram (shifted Placement5.pi0) (rawEndS divide)

def logicalReplayS (divide : Bool) : Program :=
  if divide then firstPacketS true++groupsS true 1 101++endPacketS true
  else endPacketS false++groupsS false 1 101++firstPacketS false

def replayS (divide : Bool) : Program := renameProgram (OB5.sig 511) (logicalReplayS divide)

def segmentS (divide : Bool) : Program :=
  if divide then OwnQ5Endpoint.centerT++(replayS true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT))
  else OwnQ5Endpoint.centerT++(HalfFieldOB5.copyN++(replayS false++OwnQ5Endpoint.canonT))

/-- The selector-hosted segment (`KernelOB5.segH`) around the selector-free segment. -/
def segHS (divide : Bool) : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap (segmentS divide) ++ [.X (base 511)])

def kernelS (divide : Bool) : Program :=
  NativeFirstDirect.forward base++stackForwardT++skywalkArithmeticClear base++
    segHS divide++skywalkArithmeticClear base++stackReverseT++
      NativeFirstKnown.inverse base

/-! ### Frames -/

theorem Sel.castb {b b' : Wire} {k : Nat} {P' P : Program} (h : Sel b k P' P) (e : b=b') :
    Sel b' k P' P := e ▸ h

theorem selNotZero5 : ¬Placement5.zeroRegion 2400 := by
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega

theorem selShift_fix (j : Nat) (hj : j < 102) : shifted (Placement5.pi j) (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi_outside j 2400 hj selNotZero5]

theorem selShift0_fix : shifted Placement5.pi0 (base 2400)=base 2400 := by
  rw [shifted_base,Placement5.pi0_outside 2400 selNotZero5]

theorem selSig_2400 : OB5.sig 511 (base 2400)=base 2400 := by
  rw [OB5.sig_base 511 2400 (le_refl _),if_neg (by omega)]

theorem selEndpoint_fix : HalfFieldOB5.endpointMap (base 2400)=base 2400 := by
  have hb : HalfFieldOB5.bank 2400=2400 := by decide
  have hp : Placement5.pi 51 2400=2400 := Placement5.pi_outside 51 2400 (by omega) selNotZero5
  have h1 : base 2400≠base 1796 := by decide
  have h2 : base 2400≠base 1285 := by decide
  show OB5.sig 511 ((Equiv.swap (base 1796) (base 1285))
    ((shifted (Placement5.pi 51)) ((shifted HalfFieldOB5.bank) (base 2400))))=base 2400
  rw [shifted_base,hb,shifted_base,hp,Equiv.swap_apply_of_ne_of_ne h1 h2,selSig_2400]

theorem selHost_fix : HostOB5.hostSwap (base 2400)=base 2400 := by
  have a1 : base 2400≠base 2409 := by decide
  have a2 : base 2400≠base 511 := by decide
  have a3 : base 2400≠base 2410 := by decide
  have a4 : base 2400≠base 1542 := by decide
  unfold HostOB5.hostSwap
  rw [if_neg a1,if_neg a2,if_neg a3,if_neg a4]

/-! ### Label 2400 is never used outside the windows -/

theorem selX511_away : base 2400∉wires [Instr.X (base 511)] := by
  intro h
  have e : base 2400=base 511 := by simpa [wires,Instr.wires] using h
  have := base_injective e
  omega

def selW0 : Finset Wire := (base 2409::Q6EndpointCell.ids.map base).toFinset ∪ {base 2410}

theorem selW0_away : base 2400∉selW0 := by
  intro h
  simp only [selW0,Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_map,
    Finset.mem_singleton] at h
  rcases h with (e|⟨j,hj,e⟩)|e
  · have := base_injective e; omega
  · have := base_injective e; have := Q6EndpointCell.ids_bound j hj; omega
  · have := base_injective e; omega

theorem selBody_away (divide : Bool) :
    base 2400∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := fun h =>
  selW0_away (Q6EndpointCell.body_support divide base (base 2409) (base 2410) selW0
    Finset.subset_union_left (Finset.mem_union_right _ (Finset.mem_singleton_self _)) h)

theorem selHalf_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.half divide base (base 2409)) :=
  fun h => selW0_away (Q6EndpointCell.half_support divide base (base 2409) selW0
    Finset.subset_union_left h)

theorem selHalfE_away (divide : Bool) : base 2400∉wires (Q6EndpointCell.halfE divide base (base 2409)) :=
  fun h => selHalf_away divide (Q6EndpointCell.halfE_wires divide _ _ h)

theorem selSwap_away : base 2400∉wires swapBody := by
  have sub : wires swapBody⊆wires (Q6EndpointCell.body true base (base 2409) (base 2410)) := by
    simp only [swapBody,Q6EndpointCell.body,if_true,wires_append,Q6EndpointCell.ports_r,
      Q6EndpointCell.ports_y]
    exact Finset.subset_union_right
  exact fun h => selBody_away true (sub h)

theorem selSwapM_away : base 2400∉wires swapBodyM := by
  rw [swapBodyM,UncompSwap.mswap_wires]
  exact selSwap_away

theorem selHist_away (start : Nat) (hs : start+5 ≤ 512) :
    base 2400∉wires (History5.encode base start) ∧ base 2400∉wires (History5.decode base start) := by
  have lift (P : Program) (he : P=History5.encode base start ∨ P=History5.decode base start) :
      base 2400∉wires P := by
    intro hq
    obtain ⟨u,hu⟩ := History5.history_gate_mem base start P he _ hq
    have bound := History5.historyId_bound start hs u
    have hu' : base 2400=base (History5.historyId start u) := hu
    have := base_injective hu'
    omega
  exact ⟨lift _ (Or.inl rfl),lift _ (Or.inr rfl)⟩

theorem selCenter_away : base 2400∉wires HalfFieldOB5.centerT ∧
    base 2400∉wires HalfFieldOB5.canonT ∧ base 2400∉wires HalfFieldOB5.copyN := by
  have ids (q : Wire) (hq : q∈(HalfField.ids.map base).toFinset) : q≠base 2400 := by
    intro e
    subst e
    obtain ⟨i,hi,e⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have := base_injective e
    simp only [HalfField.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,
      or_false] at hi
    omega
  have ren (P : Program) (hP : wires P⊆(HalfField.ids.map base).toFinset) :
      base 2400∉wires (renameProgram HalfFieldOB5.endpointMap P) := by
    rw [renameProgram_support]
    intro h
    obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
    rw [← selEndpoint_fix] at e
    exact ids q (hP hq) (HalfFieldOB5.endpointMap.injective e)
  exact ⟨ren _ HalfField.centerT_sites,ren _ HalfField.canonT_sites,
    fun h => ids _ (HalfField.copyN_sites h) rfl⟩

theorem selInt_away : base 2400∉wires (stackForwardT) ∧ base 2400∉wires (stackReverseT) := by
  have bad : base 2400∉OB5.integerSites := by
    intro h
    obtain ⟨l,e,hl⟩ := (OB5.integerSites_mem _).mp h
    have := base_injective e
    omega
  exact ⟨fun h => bad (StackOB5.forward_support (stackForwardT_subset h)),fun h => bad (StackOB5.reverse_support (stackReverseT_subset h))⟩

theorem selPrefix_away : base 2400∉(NativeFirstDirect.prefixSites base).toFinset := by
  intro h
  simp only [NativeFirstDirect.prefixSites,wireBlock,List.mem_toFinset,List.mem_append,
    List.mem_cons,List.mem_map,List.mem_range'_1,List.not_mem_nil,or_false,
    base_injective.eq_iff] at h
  omega

theorem selClear_away : base 2400∉wires (skywalkArithmeticClear base) := by
  rw [skywalkArithmeticClear,skywalkTerminalClear_wires]
  simp [base]

/-! ### Letters -/

theorem selLetter_nodup (i : Nat) (hi : i < 510) :
    [base 2400,(tapeLetter i).1.1,base 2409].Nodup ∧ [base 2400,(tapeLetter i).1.2,base 2410].Nodup := by
  simp only [tapeLetter]
  rw [mixedTape_base_getD i (by omega)]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,and_true,
    not_or,not_false_eq_true,base_injective.eq_iff]
  omega

theorem selLetters_nodup (j : Nat) (hj : j < 102) (l : MixedTranscriptLetter)
    (hl : l∈Replay5.letters j) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2410].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range.mp hk
  exact selLetter_nodup (5*j+k) (by omega)

theorem selRest_nodup (l : MixedTranscriptLetter) (hl : l∈Replay5.restLetters) :
    [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2410].Nodup := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
  have := List.mem_range'_1.mp hk
  exact selLetter_nodup k (by omega)

/-! ### Cells and packets -/

theorem selCell_sel (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : [base 2400,g,base 2409].Nodup) (hs : [base 2400,sw,base 2410].Nodup) :
    Sel (base 2400) 2 (cellS divide g sw)
      (Q6EndpointCell.cell divide base (base 2400) g sw (base 2409) (base 2410) ig is) :=
  (((Sel.refl _ _ (selBody_away divide)).window sw (base 2410) is hs).window g (base 2409) ig
    hg).cast (by norm_num) rfl rfl

theorem selRaw_sel (divide : Bool) (ls : List MixedTranscriptLetter)
    (hl : ∀ l∈ls, [base 2400,l.1.1,base 2409].Nodup ∧ [base 2400,l.1.2,base 2410].Nodup) :
    Sel (base 2400) (2*ls.length) (rawReplayS divide ls) (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | cons l ls ih =>
    have hh := hl l (List.mem_cons_self ..)
    have rest := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    cases divide
    · exact (rest.append (selCell_sel false l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2)).cast
        (by simp only [List.length_cons]; omega) rfl rfl
    · exact ((selCell_sel true l.1.1 l.1.2 l.2.1 l.2.2 hh.1 hh.2).append rest).cast
        (by simp only [List.length_cons]; omega) rfl rfl

theorem selPacket_sel (divide : Bool) (j : Nat) (hj : j < 102) :
    Sel (base 2400) 10 (packetS divide j) (Q6EndpointReplay.packet divide j) := by
  have codec := selHist_away (5*j) (by omega)
  have r := selRaw_sel divide (Replay5.letters j) (selLetters_nodup j hj)
  have len : (Replay5.letters j).length=5 := by simp [Replay5.letters]
  rw [len] at r
  have b : Sel (base 2400) 10 (basePacketS divide j) (Q6EndpointReplay.basePacket divide j) :=
    (((Sel.refl _ _ codec.2).append r).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi j)) (selShift_fix j hj)

theorem selGroups_sel (divide : Bool) (j n : Nat) (bound : j+n ≤ 102) :
    Sel (base 2400) (10*n) (groupsS divide j n) (Q6EndpointReplay.groups divide j n) := by
  unfold groupsS Q6EndpointReplay.groups
  induction n generalizing j with
  | zero => exact (Sel.refl _ [] (by simp [wires])).cast (by simp) rfl rfl
  | succ n ih =>
    have head := selPacket_sel divide j (by omega)
    have rest := ih (j+1) (by omega)
    cases divide
    · simp only [PacketSequence.program,Bool.false_eq_true,if_false]
      exact (rest.append head).cast (by ring) rfl rfl
    · simp only [PacketSequence.program,if_true]
      exact (head.append rest).cast (by ring) rfl rfl

theorem selFirstSwap_sel : Sel (base 2400) 1 firstSwapS Replay5.firstSwap := by
  have n : [base 2400,base 1028,base 2410].Nodup := by decide
  exact ((Sel.refl _ _ selSwap_away).window (base 1028) (base 2410)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstSwapM_sel : Sel (base 2400) 1 firstSwapMS UncompSwap.firstSwapM := by
  have n : [base 2400,base 1028,base 2410].Nodup := by decide
  exact ((Sel.refl _ _ selSwapM_away).window (base 1028) (base 2410)
    (mixedTranscriptUnitTrace.getD 0 (false,false)).2 n).cast (by norm_num) rfl rfl

theorem selFirstPacket_sel (divide : Bool) :
    Sel (base 2400) 9 (firstPacketS divide) (Q6EndpointReplay.firstPacket divide) := by
  have codec := selHist_away 0 (by omega)
  have r := selRaw_sel divide Replay5.restLetters selRest_nodup
  have len : Replay5.restLetters.length=4 := by simp [Replay5.restLetters]
  rw [len] at r
  have body : Sel (base 2400) 9 (firstBodyS divide) (Q6EndpointReplay.firstBody divide) := by
    cases divide
    · exact (r.append selFirstSwapM_sel).cast (by norm_num) rfl rfl
    · exact (selFirstSwap_sel.append r).cast (by norm_num) rfl rfl
  have b : Sel (base 2400) 9 (baseFirstPacketS divide) (Q6EndpointReplay.baseFirstPacket divide) :=
    (((Sel.refl _ _ codec.2).append body).append (Sel.refl _ _ codec.1)).cast (by norm_num) rfl rfl
  exact b.rename (shifted (Placement5.pi 0)) (selShift_fix 0 (by omega))

theorem selEnd_sel (divide : Bool) :
    Sel (base 2400) 1 (endPacketS divide) (Q6EndpointReplay.endPacket divide) := by
  have n : [base 2400,base 510,base 2409].Nodup := by decide
  have b : Sel (base 2400) 1 (rawEndS divide) (Q6EndpointReplay.rawEnd divide) :=
    ((Sel.refl _ _ (selHalfE_away divide)).window (base 510) (base 2409)
      (mixedTranscriptUnitTrace.getD 510 (false,false)).1 n).cast (by norm_num) rfl rfl
  exact b.rename (shifted Placement5.pi0) selShift0_fix

/-! ### Replay, segment, kernel -/

theorem selLogical_sel (divide : Bool) :
    Sel (base 2400) 1020 (logicalReplayS divide) (Q6EndpointReplay.logicalReplay divide) := by
  have g := selGroups_sel divide 1 101 (by omega)
  have e := selEnd_sel divide
  have f := selFirstPacket_sel divide
  cases divide
  · exact ((e.append g).append f).cast (by norm_num) rfl rfl
  · exact ((f.append g).append e).cast (by norm_num) rfl rfl

theorem selReplay_sel (divide : Bool) :
    Sel (base 2400) 1020 (replayS divide) (Q6EndpointReplay.replay divide) :=
  ((selLogical_sel divide).rename_inj (OB5.sig 511) (OB5.sig_injective 511 (by decide))).castb
    selSig_2400

end ECDSAAdd.Entrant.Q6EndpointSW


-- ENDPOINT COMPONENT SegmentE.lean
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointSegment
open Arithmetic Secp256k1 BalancedField MappedCompressed OffsetBorrowedCanonical History5 HalfFieldOB5
attribute [local irreducible] run wires HalfFieldOB5.centerT HalfFieldOB5.canonT Q6EndpointReplay.replay

def program (divide : Bool) : Program :=
  if divide then OwnQ5Endpoint.centerT++(Q6EndpointReplay.replay true++(copyN++OwnQ5Endpoint.canonT))
  else OwnQ5Endpoint.centerT++(copyN++(Q6EndpointReplay.replay false++OwnQ5Endpoint.canonT))

private theorem run_four_states (a b c d : Program) (P : State → State → Prop)
    (h : ∀ (s s1 s2 s3 s4 : State) (m1 m2 m3 m4 : List Bool),
      run a m1 s=s1 → run b m2 s1=s2 → run c m3 s2=s3 → run d m4 s3=s4 → P s s4)
    (s : State) (m : List Bool) : P s (run (a++(b++(c++d))) m s) := by
  simp only [run_append]
  exact h _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl

private theorem double_half (Y W : Fp) : 2*(Y/2*W)=Y*W := by
  have two : (2:Fp) ≠ 0 := by decide
  field_simp

private theorem double_half_div (Y W : Fp) : 2*(Y/2/W)=Y/W := by
  have two : (2:Fp) ≠ 0 := by decide
  rw [div_div,mul_comm (2:Fp) W,←div_div,mul_div_cancel₀ _ two]

private theorem double_half_one (Y : Fp) : 2*(Y/2)=Y := by
  have two : (2:Fp) ≠ 0 := by decide
  exact mul_div_cancel₀ Y two

/-- Same hypotheses and conclusion as the protected selected field segment. -/
theorem program_spec (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    let out := run (program divide) m s
    out.phase=s.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult divide origin x Y) 0 out := by
  let ctx : Q6EndpointReplay.Context origin := ⟨hn,ho,hp,hf,hg0,hs0,env,legal,hr⟩
  cases divide
  · let P : State → State → Prop := fun initial out => FieldFrameOB5.EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult false origin x Y) 0 out
    have all := run_four_states OwnQ5Endpoint.centerT copyN (Q6EndpointReplay.replay false) OwnQ5Endpoint.canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := OwnQ5Endpoint.center_frame hn (hp _ (by simp)) origin env legal hr ha Y initial m1 hin
      rw [h1] at c1
      have c2 := copy_fill hn origin (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := Q6EndpointReplay.inverse_frame origin ctx
        x hx0 hx trace (Y/2) s2 m3 c2.2
      rw [h3] at c3
      have c4 := OwnQ5Endpoint.canon_frame hn (hp _ (by simp)) origin env legal hr ha _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2*(x:Fp) else Y/2)=fieldResult false origin x Y := by
        unfold fieldResult
        split
        · simp only [Bool.false_eq_true,if_false]; exact double_half Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [program,Bool.false_eq_true,if_false] using all input
  · let P : State → State → Prop := fun initial out => FieldFrameOB5.EncodedCanonicalFrame origin Y 0 initial →
      out.phase=initial.phase ∧ FieldFrameOB5.EncodedCanonicalFrame origin (fieldResult true origin x Y) 0 out
    have all := run_four_states OwnQ5Endpoint.centerT (Q6EndpointReplay.replay true) copyN OwnQ5Endpoint.canonT P (by
      intro initial s1 s2 s3 s4 m1 m2 m3 m4 h1 h2 h3 h4 hin
      have c1 := OwnQ5Endpoint.center_frame hn (hp _ (by simp)) origin env legal hr ha Y initial m1 hin
      rw [h1] at c1
      have c2 := Q6EndpointReplay.forward_frame origin ctx x hx0 hx trace
        (Y/2) s1 m2 c1.2
      rw [h2] at c2
      have c3 := copy_clear hn origin _ s2 m3 c2.2
      rw [h3] at c3
      have c4 := OwnQ5Endpoint.canon_frame hn (hp _ (by simp)) origin env legal hr ha _ s3 m4 c3.2
      rw [h4] at c4
      refine ⟨c4.1.trans (c3.1.trans (c2.1.trans c1.1)),?_⟩
      have eq : 2*(if origin (base 2400) then Y/2/(x:Fp) else Y/2)=fieldResult true origin x Y := by
        unfold fieldResult
        split
        · simp only [if_true]; exact double_half_div Y _
        · exact double_half_one Y
      rw [←eq]
      exact c4.2) s m
    simpa only [program,if_true] using all input

attribute [local irreducible] toffoliCount measurementCount

theorem program_counts (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (ho : base 2410∉skywalkSharedWires base) :
    toffoliCount (program divide)=(if divide then 654074 else 654072) ∧
      measurementCount (program divide)=(if divide then 522850 else 523106) := by
  have ce := OwnQ5Endpoint.endpoint_counts
  have r := Q6EndpointReplay.replay_counts divide hn ho
  have len : (balancedSharedPorts base (base 2409)).r.length=
      (balancedSharedPorts base (base 2409)).y.length := by
    rw [balancedSharedPorts_r,balancedSharedPorts_y]; simp [wireBlock_length]
  have k := copyRegister_counts none (balancedSharedPorts base (base 2409)).r
    (balancedSharedPorts base (base 2409)).y len
  have cp : toffoliCount copyN=0 ∧ measurementCount copyN=0 := by
    simpa only [copyN,HalfField5.copyN,HalfField.copyN,HalfField.ports,
      Option.isSome_none,Bool.false_eq_true,if_false] using k
  cases divide <;> simp only [program,Bool.false_eq_true,if_false,if_true,toffoliCount_append,
    measurementCount_append,ce.1,ce.2.1,ce.2.2.1,ce.2.2.2,cp.1,cp.2] at r ⊢
  all_goals constructor <;> omega


theorem program_physical (divide : Bool) (hn : (skywalkSharedWires base).Nodup)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) :
    GatePhysical (program divide) := by
  have c := OwnQ5Endpoint.endpoint_physical hn
  have r := Q6EndpointReplay.replay_physical divide hn ho hf
  cases divide <;> simp only [program,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨c.1,c.2.2,r,c.2.1⟩
  · exact ⟨c.1,r,c.2.2,c.2.1⟩

theorem program_gateSlots_le (divide : Bool) : Challenge.gateSlots (program divide)≤14100000 := by
  have c := OwnQ5Endpoint.endpoint_gateSlots_le
  have r := Q6EndpointReplay.replay_gateSlots_le divide
  cases divide <;> simp only [program,Bool.false_eq_true,if_false,if_true,Challenge.gateSlots_append] <;> omega

theorem program_state_eq (divide : Bool)
    (hn : (skywalkSharedWires base).Nodup) (ho : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkSharedWires base)
    (hp : ∀ q ∈ [base 2400,base 2409,base 2410],q ∉ skywalkPoolWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (origin : BasisState) (hg0 : origin (base 2409)=false) (hs0 : origin (base 2410)=false)
    (env : Env base origin) (legal : History5.RawLegal base 102 origin)
    (hr : origin (base 2312)=false) (ha : regValue (skywalkSharedField base).a origin=0)
    (x : Nat) (hx0 : 0 < x) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x:Int) (p:Int)))
    (Y : Fp) (s : State) (m : List Bool) (input : FieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    run (program divide) m s=run (SegmentOB5.program divide) m s := by
  have new:=program_spec divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  have old:=SegmentOB5.program_spec divide hn ho hp hf origin hg0 hs0 env legal hr ha x hx0 hx trace Y s m input
  have eq:=encoded_canonical_unique origin (fieldResult divide origin x Y) 0
    (pullState (OB5.sig 511) (run (program divide) m s))
    (pullState (OB5.sig 511) (run (SegmentOB5.program divide) m s)) new.2 old.2 (new.1.trans old.1.symm)
  have pulled:=congrArg (pullState (OB5.sig 511)) eq
  simpa only [OB5.pull_invol 511 (by decide)] using pulled

end ECDSAAdd.Entrant.Q6EndpointSegment

-- ENDPOINT COMPONENT SupportE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointReplaySupport
open Arithmetic MappedCompressed Q6EndpointReplay
attribute [local irreducible] wires

private def preFrame (i : Nat) : Prop :=
  (i<1542 ∧ i≠769 ∧ i≠511 ∧ i≠1539) ∨ i=1797 ∨ (2056 ≤ i ∧ i ≤ 2312) ∨ i=2400 ∨ i=2409 ∨ i=2410

private theorem sigma_mem (i : Nat) (hi : preFrame i) (safe : ¬Placement5.omitted i) :
    OB5.sig 511 (base i)∈OB5Support.segSites := by
  rw [OB5.sig_base 511 i (by decide)]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨_,?_,rfl⟩
  simp only [OB5Support.segIndices,List.mem_append,List.mem_range'_1,List.mem_cons,
    List.not_mem_nil,or_false]
  unfold preFrame Placement5.omitted at *
  split_ifs <;> omega

private theorem perm_frame (e : Equiv.Perm Nat)
    (fix : ∀i,¬Placement5.zeroRegion i → e i=i) (i : Nat) (hi : preFrame i) : preFrame (e i) := by
  have bounded (i : Nat) (hi : i<1542) : e i<1542 := by
    by_contra hn
    have outside : ¬Placement5.zeroRegion (e i) := by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega
    have same := e.injective (fix (e i) outside)
    omega
  have no769 (i : Nat) (hi : i≠769) : e i≠769 := by
    intro eq
    have same := e.injective (eq.trans (fix 769 (by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega)).symm)
    exact hi same
  rcases hi with h|h|h|h|h|h
  · have noC (c : Nat) (hc : ¬Placement5.zeroRegion c) (k : Nat) (hk : k≠c) : e k≠c := by
      intro eq
      exact hk (e.injective (eq.trans (fix c hc).symm))
    exact Or.inl ⟨bounded i h.1,no769 i h.2.1,
      noC 511 (by unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega) i h.2.2.1,
      noC 1539 (by unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion; omega) i h.2.2.2⟩
  all_goals
    have outside : ¬Placement5.zeroRegion i := by
      unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
      omega
    rw [fix i outside]
    unfold preFrame
    omega

private theorem pi_mem (j i : Nat) (hj : j<102) (hi : preFrame i)
    (hole : ¬Placement5.holeRegion i) :
    OB5.sig 511 (base (Placement5.pi j i))∈OB5Support.segSites :=
  sigma_mem _ (perm_frame (Placement5.pi j) (fun q hq => Placement5.pi_outside j q hj hq) i hi)
    (Placement5.nonhole_pi_safe j i hj hole)

private theorem pi0_mem (i : Nat) (hi : preFrame i) (hole : ¬Placement5.holeRegion i) :
    OB5.sig 511 (base (Placement5.pi0 i))∈OB5Support.segSites :=
  sigma_mem _ (perm_frame Placement5.pi0 Placement5.pi0_outside i hi)
    (Placement5.nonhole_pi0_safe i hole)

private theorem field_index (i : Nat) (hi : i∈Q6EndpointCell.ids) :
    preFrame i ∧ ¬Placement5.holeRegion i := by
  simp only [Q6EndpointCell.ids,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_range'_1,or_false] at hi
  unfold preFrame Placement5.holeRegion
  omega

private theorem history_pi_mem (j : Nat) (hj : j<102) (r : Fin 10) :
    OB5.sig 511 (base (Placement5.pi j (History5.historyId (5*j) r)))∈OB5Support.segSites := by
  have bounds := History5.historyId_region (5*j) (by omega) r
  have low : preFrame (History5.historyId (5*j) r) := by
    have hr := r.isLt
    unfold preFrame History5.historyId
    split <;> omega
  by_cases hole : Placement5.holeRegion (History5.historyId (5*j) r)
  · have h : History5.historyId (5*j) r=Placement5.H (2*j) ∨
        History5.historyId (5*j) r=Placement5.H (2*j+1) := by
      have hr := r.isLt
      have he : Placement5.H (2*j)=1030+5*j := by unfold Placement5.H; omega
      have ho : Placement5.H (2*j+1)=1032+5*j := by unfold Placement5.H; omega
      rw [he,ho]
      unfold History5.historyId at hole ⊢
      split_ifs at hole ⊢ <;> unfold Placement5.holeRegion at hole <;> omega
    rcases h with h|h
    · rw [h,Placement5.pi_current_even j hj]
      apply sigma_mem
      · have b := Placement5.H_bound (2*j) (by omega)
        unfold preFrame
        omega
      · have b := Placement5.H_bound (2*j) (by omega)
        unfold Placement5.omitted
        omega
    · rw [h,Placement5.pi_current_odd j hj]
      apply sigma_mem
      · have b := Placement5.H_bound (2*j+1) (by omega)
        unfold preFrame
        omega
      · have b := Placement5.H_bound (2*j+1) (by omega)
        unfold Placement5.omitted
        omega
  · exact pi_mem j _ hj low hole

private theorem read_placed (j : Nat) (hj : j<102) (q : Wire) (hq : q∈readSites (5*j)) :
    OB5.sig 511 (shifted (Placement5.pi j) q)∈OB5Support.segSites := by
  simp only [readSites,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · rcases List.mem_cons.mp (List.mem_toFinset.mp h) with rfl|h
    · rw [shifted_base]
      exact pi_mem j 2409 hj (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      rw [shifted_base]
      exact pi_mem j i hj (field_index i hi).1 (field_index i hi).2
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl
    · rw [shifted_base]
      exact pi_mem j 2400 hj (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · rw [shifted_base]
      exact pi_mem j 2410 hj (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
  · obtain ⟨r,rfl⟩ := History5.history_gate_mem base (5*j) _ (Or.inl rfl) q h
    rw [History5.historyMap,shifted_base]
    exact history_pi_mem j hj r

private theorem stage_placed_support (j : Nat) (hj : j<102) (P : Program)
    (hP : wires P⊆readSites (5*j)) :
    wires (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi j)) P))⊆OB5Support.segSites := by
  rw [renameProgram_support (OB5.sig 511) (renameProgram (shifted (Placement5.pi j)) P)]
  intro q hq
  obtain ⟨middle,hmid,eqSig⟩ := Finset.mem_image.mp hq
  rw [renameProgram_support (shifted (Placement5.pi j)) P] at hmid
  obtain ⟨old,hold,eqPi⟩ := Finset.mem_image.mp hmid
  rw [←eqSig,←eqPi]
  exact read_placed j hj old (hP hold)

private theorem codec_read (start : Nat) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : wires P⊆readSites start := by
  intro q hq
  obtain ⟨r,rfl⟩ := History5.history_gate_mem base start P hp q hq
  exact Finset.mem_union_right _ (History5.history_site_mem base start r)

theorem packet_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (renameProgram (OB5.sig 511) (packet divide j))⊆OB5Support.segSites := by
  apply stage_placed_support j hj
  simp only [basePacket,wires_append,Finset.union_subset_iff]
  exact ⟨⟨codec_read _ _ (Or.inr rfl),body_support divide j hj⟩,codec_read _ _ (Or.inl rfl)⟩

theorem firstPacket_support (divide : Bool) :
    wires (renameProgram (OB5.sig 511) (firstPacket divide))⊆OB5Support.segSites := by
  apply stage_placed_support 0 (by decide)
  simp only [baseFirstPacket,wires_append,Finset.union_subset_iff]
  exact ⟨⟨codec_read _ _ (Or.inr rfl),firstBody_support divide⟩,codec_read _ _ (Or.inl rfl)⟩

theorem endPacket_support (divide : Bool) :
    wires (renameProgram (OB5.sig 511) (endPacket divide))⊆OB5Support.segSites := by
  rw [renameProgram_support (OB5.sig 511) (endPacket divide)]
  intro q hq
  obtain ⟨middle,hmid,eqSig⟩ := Finset.mem_image.mp hq
  rw [endPacket,renameProgram_support (shifted Placement5.pi0) (rawEnd divide)] at hmid
  obtain ⟨old,hold,eqPi⟩ := Finset.mem_image.mp hmid
  rw [←eqSig,←eqPi]
  rcases Finset.mem_union.mp (rawEnd_support divide hold) with h|h
  · rcases List.mem_cons.mp (List.mem_toFinset.mp h) with rfl|h
    · rw [shifted_base]
      exact pi0_mem 2409 (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      rw [shifted_base]
      exact pi0_mem i (field_index i hi).1 (field_index i hi).2
  · simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl
    · rw [shifted_base]
      exact pi0_mem 2400 (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)
    · rw [shifted_base]
      exact pi0_mem 510 (by unfold preFrame; omega) (by unfold Placement5.holeRegion; omega)

theorem groups_support (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    wires (renameProgram (OB5.sig 511) (groups divide j n))⊆OB5Support.segSites := by
  induction n generalizing j with
  | zero => simp [groups,PacketSequence.program,renameProgram,wires]
  | succ n ih =>
    have head := packet_support divide j (by omega)
    have rest := ih (j+1) (by omega)
    simp only [groups] at rest
    cases divide <;> simp only [groups,PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      FieldRename.rename_append,wires_append,Finset.union_subset_iff] at rest ⊢
    · exact ⟨rest,head⟩
    · exact ⟨head,rest⟩

theorem replay_support (divide : Bool) : wires (replay divide)⊆OB5Support.segSites := by
  have first := firstPacket_support divide
  have middle := groups_support divide 1 101 (by decide)
  have last := endPacket_support divide
  cases divide <;> simp only [replay,logicalReplay,Bool.false_eq_true,if_false,if_true,
    FieldRename.rename_append,wires_append,Finset.union_subset_iff] at first middle last ⊢
  · exact ⟨⟨last,middle⟩,first⟩
  · exact ⟨⟨first,middle⟩,last⟩

end ECDSAAdd.Entrant.Q6EndpointReplaySupport

-- ENDPOINT COMPONENT EntryE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointEntryRaw
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI EntryFuse
attribute [local irreducible] run wires

def field5 : Program := Q6EndpointReplay.replay true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5 : Program := [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5 ++ [.X (base 511)])
def kernel5 : Program := NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
  hostField5 ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

theorem field_support : wires field5⊆OB5Support.segSites := by
  simp only [field5,wires_append,Finset.union_subset_iff]
  exact ⟨Q6EndpointReplaySupport.replay_support true,HalfFieldOB5Support.copy_support,OwnQ5Endpoint.support.2⟩

theorem field_free : base 511∉wires field5 ∧ base 1542∉wires field5 :=
  ⟨fun h=>OB5Support.seg_host_free.1 (field_support h),fun h=>OB5Support.seg_host_free.2 (field_support h)⟩

theorem field5_unhosted_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base)) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run field5 m4 v3=v4) :
    let a1 := run (NativeFirstDirect.forward base) m1 s
    let a2 := run (stackForwardT) m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    run (SegmentOB5.program true)
      (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) a3=v4 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  have paired := pool_three (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) first_pool5 forward_pool5 clear_pool5 s t m1 m2 m3
    phase.symm (fun q hq => (same q hq).symm) v1 v2 v3 h1 h2 h3
  change a3.phase=v3.phase ∧
    (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
    (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) at paired
  have target : regValue (wireBlock base 2056 256) v3.basis=centerWord (Y/2) := by
    exact (regValue_congr _ _ _ paired.2.2).trans value
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
  let t2 := run (compactForward5 base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ a1.basis).mpr first
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp hpGap hx cop a1 m2 m2 first
  have e2 : a2=pullState (OB5.sig 511) t2 := by
    change run stackForwardT m2 a1 = _
    rw [stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx a1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,_,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin a1 t2 t3 rfl rfl rfl first
  have hpPool : base 2409∉skywalkPoolWires base := by
    intro bad
    exact ho _ (by simp) (arith_block_subset_shared base 0 1798 (by omega) bad)
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have centerEq := center5_compare hn hpPool origin.basis facts.env legal facts.targetHigh
    facts.sourceHigh facts.sourceZero Y a3 v3 placedInput paired.1 paired.2.1 target
    ((List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4).take
      (measurementCount OwnQ5Endpoint.centerT))
  let dummy := List.replicate (measurementCount OwnQ5Endpoint.centerT) false
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have replacement:=Q6EndpointSegment.program_state_eq true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 (dummy++m4) placedInput
  change run (SegmentOB5.program true) (dummy++m4) a3=v4
  rw [←replacement]
  have shape : Q6EndpointSegment.program true=OwnQ5Endpoint.centerT++field5 := by
    simp only [Q6EndpointSegment.program,field5,if_true]
  change run (Q6EndpointSegment.program true) (dummy++m4) a3=v4
  rw [shape,run_append]
  have drop : (dummy++m4).drop (measurementCount OwnQ5Endpoint.centerT)=m4 := by simp [dummy]
  rw [drop,centerEq]
  exact h4

theorem kernel5_field_state
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostField5 m4 v3=v4) :
    let a1 := run (NativeFirstDirect.forward base) m1 s
    let a2 := run (stackForwardT) m2 a1
    let a3 := run (skywalkArithmeticClear base) m3 a2
    run (KernelOB5.segH true)
      (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) a3=v4 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  let dummy := List.replicate (measurementCount OwnQ5Endpoint.centerT) false
  let oldRecords := dummy++m4
  let v4' := run field5 m4 v3
  have unEq := field5_unhosted_state hn hlo ho x Y hx0 hx s t m1 m2 m3 m4 hg0 hs0 hf hin
    phase same value v1 v2 v3 v4' h1 h2 h3 rfl
  change run (SegmentOB5.program true) oldRecords a3=v4' at unEq
  have paired := pool_three (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) first_pool5 forward_pool5 clear_pool5 s t m1 m2 m3
    phase.symm (fun q hq => (same q hq).symm) v1 v2 v3 h1 h2 h3
  change a3.phase=v3.phase ∧
    (∀q,q∉wireBlock base 2056 256 → a3.basis q=v3.basis q) ∧
    (∀q,q∈wireBlock base 2056 256 → v3.basis q=t.basis q) at paired
  have first := NativeFirstDirect.caller_first_stage base hn x Y.val hx0 hx s m1 hin
  change CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 a1.basis at first
  let t2 := run (compactForward5 base 1 511) m2 a1
  let t3 := run (skywalkArithmeticClear base) m3 t2
  obtain ⟨hp0,hpo,hpp,cop⟩ := OB5.prime_facts x hx0 hx
  have pool := skywalkShared_integer_nodup base hn
  have firstW := (W.compactSkywalkStage_one base _ a1.basis).mpr first
  have hpGap : p+2^32 ≤ 2^256 := by norm_num [p]
  have wEq : run (Stack5.forward5 base 1 511) m2 a1=t2 :=
    Stack5.forward_old_eq base pool hlo x p hp0 hx0 hpo hpp hpGap hx cop a1 m2 m2 first
  have e2 : a2=pullState (OB5.sig 511) t2 := by
    change run stackForwardT m2 a1 = _
    rw [stackForwardT_run hn hlo x hx0 hx a1 m2 firstW]
    have fwd := StackOB5.forward_run x hx0 hx a1 m2 firstW
    rw [wEq] at fwd
    exact fwd
  have e3 : a3=pullState (OB5.sig 511) t3 := by
    change run (skywalkArithmeticClear base) m3 a2=_
    rw [e2,KernelOB5.clear_placed]
  obtain ⟨origin,facts,legal,_,encEq,entry⟩ := Kernel5.preparation_facts5 hn hlo ho x Y hx0 hx s
    m1 m2 m3 hin a1 t2 t3 rfl rfl rfl first
  have hp : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkPoolWires base := by
    intro q hq bad
    exact ho q hq (arith_block_subset_shared base 0 1798 (by omega) bad)
  have hg : origin.basis (base 2409)=false := (facts.controls _ (by simp)).trans hg0
  have hs : origin.basis (base 2410)=false := (facts.controls _ (by simp)).trans hs0
  have placedInput : FieldFrameOB5.EncodedCanonicalFrame origin.basis Y 0 a3 := by
    change EncodedCanonicalFrame5 origin.basis Y 0 (pullState (OB5.sig 511) a3)
    rw [e3,OB5.pull_invol 511 (by decide)]
    exact entry
  have fresh := SegmentOB5.program_spec true hn ho hp hf origin.basis hg hs facts.env legal
    facts.targetHigh facts.sourceZero x hx0 hx facts.trace Y a3 oldRecords placedInput
  have inS := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero Y a3 placedInput
  have outS := encoded_selectors5 hn hp origin.basis hg hs facts.sourceZero _ _ fresh.2
  have hostBits := encoded_host_bits5 x hx0 hx origin t3 a3 facts.trace encEq e3
  have in2409 : a3.basis (base 2409)=false := inS.1
  have in2410 : a3.basis (base 2410)=false := inS.2
  have in511 : a3.basis (base 511)=true := hostBits.1
  have in1542 : a3.basis (base 1542)=false := hostBits.2
  have out2409 : (run (SegmentOB5.program true) oldRecords a3).basis (base 2409)=false := outS.1
  have out2410 : (run (SegmentOB5.program true) oldRecords a3).basis (base 2410)=false := outS.2
  have away (i : Nat) (hi : i < 2056 ∨ 2312 ≤ i) : base i∉wireBlock base 2056 256 := by
    intro mem
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp mem
    simp only [List.mem_range'_1] at hj
    have e := base_injective eq
    omega
  have inT (i : Nat) (hi : i < 2056 ∨ 2312 ≤ i) : v3.basis (base i)=a3.basis (base i) :=
    (paired.2.1 _ (away i hi)).symm
  have freeP := KernelOB5.seg_free true
  have freeQ511 : base 511∉wires field5 := field_free.1
  have freeQ1542 : base 1542∉wires field5 := field_free.2
  have hosted := hosted_pair5 (SegmentOB5.program true) field5 a3 v3 oldRecords m4
    freeP.1 freeP.2 freeQ511 freeQ1542 in2409 in511 in2410 in1542
    ((inT 2409 (by omega)).trans in2409) ((inT 511 (by omega)).trans in511)
    ((inT 2410 (by omega)).trans in2410) ((inT 1542 (by omega)).trans in1542)
    out2409 out2410 unEq
  change run (KernelOB5.segH true) oldRecords a3=v4
  rw [show KernelOB5.segH true=[.X (base 511)]++
    (renameProgram HostOB5.hostSwap (SegmentOB5.program true)++[.X (base 511)]) from rfl,hosted]
  simpa only [hostField5] using h4

theorem kernel5_states
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (v1 v2 v3 v4 v5 v6 v7 : State)
    (h1 : run (NativeFirstDirect.forward base) m1 t=v1)
    (h2 : run (stackForwardT) m2 v1=v2)
    (h3 : run (skywalkArithmeticClear base) m3 v2=v3)
    (h4 : run hostField5 m4 v3=v4)
    (h5 : run (skywalkArithmeticClear base) m5 v4=v5)
    (h6 : run (stackReverseT) m6 v5=v6)
    (h7 : run (NativeFirstKnown.inverse base) m7 v6=v7) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s v7 := by
  let a1 := run (NativeFirstDirect.forward base) m1 s
  let a2 := run (stackForwardT) m2 a1
  let a3 := run (skywalkArithmeticClear base) m3 a2
  have old4 := kernel5_field_state hn hlo ho hf x Y hx0 hx s t m1 m2 m3 m4 hin hg0 hs0
    phase same value v1 v2 v3 v4 h1 h2 h3 h4
  exact KernelOB5.program_states true hn hlo ho hf x Y hx0 hx s
    m1 m2 m3 (List.replicate (measurementCount OwnQ5Endpoint.centerT) false++m4) m5 m6 m7
    hin hg0 hs0 a1 a2 a3 v4 v5 v6 v7 rfl rfl rfl old4 h5 h6 h7

theorem kernel5_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  let P : State → State → Prop := fun initial out =>
    initial.phase=s.phase →
    (∀q,q∉wireBlock base 2056 256 → initial.basis q=s.basis q) →
    regValue (wireBlock base 2056 256) initial.basis=centerWord (Y/2) →
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s out
  have all := skywalkRunSeven (NativeFirstDirect.forward base) (stackForwardT)
    (skywalkArithmeticClear base) hostField5 (skywalkArithmeticClear base)
    (stackReverseT) (NativeFirstKnown.inverse base) P (by
      intro initial v1 v2 v3 v4 v5 v6 v7 m1 m2 m3 m4 m5 m6 m7 h1 h2 h3 h4 h5 h6 h7 hp hs hv
      exact kernel5_states hn hlo ho hf x Y hx0 hx s initial m1 m2 m3 m4 m5 m6 m7
        hin hg0 hs0 hp hs hv v1 v2 v3 v4 v5 v6 v7 h1 h2 h3 h4 h5 h6 h7) t m
  simpa only [kernel5,List.append_assoc] using all phase same value

end ECDSAAdd.Entrant.Q6EndpointEntryRaw


-- ENDPOINT COMPONENT RetiredE.lean
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant.Q6EndpointRetired
open ECDSAAdd Arithmetic MappedCompressed OwnMinusHost
attribute [local irreducible] wires OwnQ6Core5.kernel OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT
variable (hKernel : ∀divide,base 1541∉wires (OwnQ6Core5.kernel divide (Q6EndpointCell.ports base (base 2409))))
include hKernel

theorem half_avoid (divide : Bool) :
    base 1541∉wires (Q6EndpointCell.half divide base (base 2409)) := by
  have k:=hKernel divide
  simpa only [Q6EndpointCell.half,OwnQ6Core5.half,wires_append,wires,Instr.wires,
    Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false,
    Q6EndpointCell.ports,not_or] using
    And.intro (And.intro (by decide : base 1541≠base 2409) k) (by decide : base 1541≠base 2409)

theorem swap_avoid : base 1541∉wires (swapRegisters (base 2410)
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y) := by
  have len:(Q6EndpointCell.ports base (base 2409)).r.length=
      (Q6EndpointCell.ports base (base 2409)).y.length := by
    rw [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
    simp [wireBlock_length]
  have h:=swapRegisters_wires (base 2410) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y len
  intro used
  have mem:=h used
  rw [List.mem_toFinset,List.mem_cons,List.mem_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with eq|r|y
  · exact (by decide : base 1541≠base 2410) eq
  · exact not_block 1541 2056 256 (by omega) r
  · exact not_block 1541 770 256 (by omega) y

theorem body_avoid (divide : Bool) :
    base 1541∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := by
  cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨swap_avoid hKernel,half_avoid hKernel false⟩
  · exact ⟨half_avoid hKernel true,swap_avoid hKernel⟩

theorem select_avoid (b source flag : Wire) (v : Bool) (P : Program)
    (hb : base 1541≠b) (hs : base 1541≠source) (hf : base 1541≠flag)
    (hp : base 1541∉wires P) : base 1541∉wires (transcriptSelectWindow b source flag v P) := by
  intro used
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at used <;> tauto

theorem cell_avoid (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : base 1541≠g) (hs : base 1541≠sw) :
    base 1541∉wires (Q6EndpointCell.cell divide base (base 2400) g sw (base 2409) (base 2410) ig is) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide)
    (select_avoid hKernel _ _ _ _ _ (by decide) hs (by decide) (body_avoid hKernel divide))

theorem endpoint_avoid (divide : Bool) (g : Wire) (ig : Bool) (hg : base 1541≠g) :
    base 1541∉wires (Q6EndpointCell.endpoint divide base (base 2400) g (base 2409) ig) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide) (fun used => half_avoid hKernel divide (Q6EndpointCell.halfE_wires divide base (base 2409) used))

attribute [local irreducible] Q6EndpointCell.cell Q6EndpointCell.endpoint

theorem codec_avoid (start : Nat) (hs : start+5≤512) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : base 1541∉wires P := by
  intro used
  obtain ⟨r,eq⟩:=History5.history_gate_mem base start P hp (base 1541) used
  have bounds:=History5.historyId_region start hs r
  change base 1541=base (History5.historyId start r) at eq
  have same:=base_injective eq
  omega

theorem raw_avoid (divide : Bool) (ls : List MixedTranscriptLetter)
    (controls : ∀l∈ls,base 1541≠l.1.1 ∧ base 1541≠l.1.2) :
    base 1541∉wires (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => simp [Q6EndpointReplay.rawReplay,wires]
  | cons l ls ih =>
    have c:=cell_avoid hKernel divide l.1.1 l.1.2 l.2.1 l.2.2 (controls l (by simp)).1 (controls l (by simp)).2
    have rest:=ih (fun k hk=>controls k (List.mem_cons_of_mem _ hk))
    cases divide <;> simp only [Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_replay_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 1541∉wires (Q6EndpointReplay.body divide j) := by
  apply raw_avoid hKernel
  intro l hl
  have c:=Replay5.letters_controls j hj l hl
  have no:=codec_avoid hKernel (5*j) (by omega) _ (Or.inl rfl)
  exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩

theorem firstSwap_avoid : base 1541∉wires Replay5.firstSwap := by
  apply select_avoid hKernel _ _ _ _ _ (by decide) (by decide) (by decide)
  exact swap_avoid hKernel

theorem firstBody_avoid (divide : Bool) : base 1541∉wires (Q6EndpointReplay.firstBody divide) := by
  have ctrl : ∀l∈Replay5.restLetters,base 1541≠l.1.1 ∧ base 1541≠l.1.2 := by
    intro l hl
    have mem:l∈Replay5.letters 0:=by rw [Replay5.letters_zero];simp [hl]
    have c:=Replay5.letters_controls 0 (by omega) l mem
    have no:=codec_avoid hKernel 0 (by omega) _ (Or.inl rfl)
    exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩
  cases divide <;> simp only [Q6EndpointReplay.firstBody,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨raw_avoid hKernel false _ ctrl,by rw [UncompSwap.firstSwapM_wires]; exact firstSwap_avoid hKernel⟩
  · exact ⟨firstSwap_avoid hKernel,raw_avoid hKernel true _ ctrl⟩

theorem pi_fix (j : Nat) (hj : j<102) : shifted (Placement5.pi j) (base 1541)=base 1541 := by
  rw [shifted_base,Placement5.pi_outside j 1541 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

theorem packet_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 1541∉wires (Q6EndpointReplay.packet divide j) := by
  apply rename_avoid _ _ _ (pi_fix hKernel j hj)
  simp only [Q6EndpointReplay.basePacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),body_replay_avoid hKernel divide j hj⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem firstPacket_avoid (divide : Bool) : base 1541∉wires (Q6EndpointReplay.firstPacket divide) := by
  apply rename_avoid _ _ _ (pi_fix hKernel 0 (by omega))
  simp only [Q6EndpointReplay.baseFirstPacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),firstBody_avoid hKernel divide⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem endPacket_avoid (divide : Bool) : base 1541∉wires (Q6EndpointReplay.endPacket divide) := by
  have fix:shifted Placement5.pi0 (base 1541)=base 1541:=by
    rw [shifted_base,Placement5.pi0_outside 1541]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply rename_avoid _ _ _ fix
  apply endpoint_avoid hKernel
  decide

theorem groups_avoid (divide : Bool) (j n : Nat) (hb : j+n≤102) :
    base 1541∉wires (Q6EndpointReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [Q6EndpointReplay.groups,PacketSequence.program,wires]
  | succ n ih =>
    have head:=packet_avoid hKernel divide j (by omega)
    have tail:=ih (j+1) (by omega)
    cases divide <;> simp only [Q6EndpointReplay.groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,wires_append,Finset.mem_union,not_or] at head tail ⊢
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem replay_avoid (divide : Bool) : base 1541∉wires (Q6EndpointReplay.replay divide) := by
  let e:Equiv.Perm Wire:=⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by omega),OB5.sig_invol 511 (by omega)⟩
  have fix:e (base 1541)=base 1541:=by decide +kernel
  apply rename_avoid e _ _ fix
  cases divide <;> simp only [Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨⟨endPacket_avoid hKernel false,groups_avoid hKernel false 1 101 (by omega)⟩,firstPacket_avoid hKernel false⟩
  · exact ⟨⟨firstPacket_avoid hKernel true,groups_avoid hKernel true 1 101 (by omega)⟩,endPacket_avoid hKernel true⟩

end ECDSAAdd.Entrant.Q6EndpointRetired


-- ENDPOINT COMPONENT OmissionsE.lean
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant.Q6EndpointFree1026
open ECDSAAdd Arithmetic MappedCompressed OwnMinusHost
attribute [local irreducible] wires OwnQ6Core5.kernel OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT
variable (hKernel : ∀divide,base 1026∉wires (OwnQ6Core5.kernel divide (Q6EndpointCell.ports base (base 2409))))
include hKernel

theorem half_avoid (divide : Bool) :
    base 1026∉wires (Q6EndpointCell.half divide base (base 2409)) := by
  have k:=hKernel divide
  simpa only [Q6EndpointCell.half,OwnQ6Core5.half,wires_append,wires,Instr.wires,
    Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false,
    Q6EndpointCell.ports,not_or] using
    And.intro (And.intro (by decide : base 1026≠base 2409) k) (by decide : base 1026≠base 2409)

theorem swap_avoid : base 1026∉wires (swapRegisters (base 2410)
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y) := by
  have len:(Q6EndpointCell.ports base (base 2409)).r.length=
      (Q6EndpointCell.ports base (base 2409)).y.length := by
    rw [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
    simp [wireBlock_length]
  have h:=swapRegisters_wires (base 2410) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y len
  intro used
  have mem:=h used
  rw [List.mem_toFinset,List.mem_cons,List.mem_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with eq|r|y
  · exact (by decide : base 1026≠base 2410) eq
  · exact not_block 1026 2056 256 (by omega) r
  · exact not_block 1026 770 256 (by omega) y

theorem body_avoid (divide : Bool) :
    base 1026∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := by
  cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨swap_avoid hKernel,half_avoid hKernel false⟩
  · exact ⟨half_avoid hKernel true,swap_avoid hKernel⟩

theorem select_avoid (b source flag : Wire) (v : Bool) (P : Program)
    (hb : base 1026≠b) (hs : base 1026≠source) (hf : base 1026≠flag)
    (hp : base 1026∉wires P) : base 1026∉wires (transcriptSelectWindow b source flag v P) := by
  intro used
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at used <;> tauto

theorem cell_avoid (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : base 1026≠g) (hs : base 1026≠sw) :
    base 1026∉wires (Q6EndpointCell.cell divide base (base 2400) g sw (base 2409) (base 2410) ig is) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide)
    (select_avoid hKernel _ _ _ _ _ (by decide) hs (by decide) (body_avoid hKernel divide))

theorem endpoint_avoid (divide : Bool) (g : Wire) (ig : Bool) (hg : base 1026≠g) :
    base 1026∉wires (Q6EndpointCell.endpoint divide base (base 2400) g (base 2409) ig) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide) (fun used => half_avoid hKernel divide (Q6EndpointCell.halfE_wires divide base (base 2409) used))

attribute [local irreducible] Q6EndpointCell.cell Q6EndpointCell.endpoint

theorem codec_avoid (start : Nat) (hs : start+5≤512) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : base 1026∉wires P := by
  intro used
  obtain ⟨r,eq⟩:=History5.history_gate_mem base start P hp (base 1026) used
  have bounds:=History5.historyId_region start hs r
  change base 1026=base (History5.historyId start r) at eq
  have same:=base_injective eq
  omega

theorem raw_avoid (divide : Bool) (ls : List MixedTranscriptLetter)
    (controls : ∀l∈ls,base 1026≠l.1.1 ∧ base 1026≠l.1.2) :
    base 1026∉wires (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => simp [Q6EndpointReplay.rawReplay,wires]
  | cons l ls ih =>
    have c:=cell_avoid hKernel divide l.1.1 l.1.2 l.2.1 l.2.2 (controls l (by simp)).1 (controls l (by simp)).2
    have rest:=ih (fun k hk=>controls k (List.mem_cons_of_mem _ hk))
    cases divide <;> simp only [Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_replay_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 1026∉wires (Q6EndpointReplay.body divide j) := by
  apply raw_avoid hKernel
  intro l hl
  have c:=Replay5.letters_controls j hj l hl
  have no:=codec_avoid hKernel (5*j) (by omega) _ (Or.inl rfl)
  exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩

theorem firstSwap_avoid : base 1026∉wires Replay5.firstSwap := by
  apply select_avoid hKernel _ _ _ _ _ (by decide) (by decide) (by decide)
  exact swap_avoid hKernel

theorem firstBody_avoid (divide : Bool) : base 1026∉wires (Q6EndpointReplay.firstBody divide) := by
  have ctrl : ∀l∈Replay5.restLetters,base 1026≠l.1.1 ∧ base 1026≠l.1.2 := by
    intro l hl
    have mem:l∈Replay5.letters 0:=by rw [Replay5.letters_zero];simp [hl]
    have c:=Replay5.letters_controls 0 (by omega) l mem
    have no:=codec_avoid hKernel 0 (by omega) _ (Or.inl rfl)
    exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩
  cases divide <;> simp only [Q6EndpointReplay.firstBody,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨raw_avoid hKernel false _ ctrl,by rw [UncompSwap.firstSwapM_wires]; exact firstSwap_avoid hKernel⟩
  · exact ⟨firstSwap_avoid hKernel,raw_avoid hKernel true _ ctrl⟩

theorem pi_fix (j : Nat) (hj : j<102) : shifted (Placement5.pi j) (base 1026)=base 1026 := by
  rw [shifted_base,Placement5.pi_outside j 1026 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

theorem packet_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 1026∉wires (Q6EndpointReplay.packet divide j) := by
  apply rename_avoid _ _ _ (pi_fix hKernel j hj)
  simp only [Q6EndpointReplay.basePacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),body_replay_avoid hKernel divide j hj⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem firstPacket_avoid (divide : Bool) : base 1026∉wires (Q6EndpointReplay.firstPacket divide) := by
  apply rename_avoid _ _ _ (pi_fix hKernel 0 (by omega))
  simp only [Q6EndpointReplay.baseFirstPacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),firstBody_avoid hKernel divide⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem endPacket_avoid (divide : Bool) : base 1026∉wires (Q6EndpointReplay.endPacket divide) := by
  have fix:shifted Placement5.pi0 (base 1026)=base 1026:=by
    rw [shifted_base,Placement5.pi0_outside 1026]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply rename_avoid _ _ _ fix
  apply endpoint_avoid hKernel
  decide

theorem groups_avoid (divide : Bool) (j n : Nat) (hb : j+n≤102) :
    base 1026∉wires (Q6EndpointReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [Q6EndpointReplay.groups,PacketSequence.program,wires]
  | succ n ih =>
    have head:=packet_avoid hKernel divide j (by omega)
    have tail:=ih (j+1) (by omega)
    cases divide <;> simp only [Q6EndpointReplay.groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,wires_append,Finset.mem_union,not_or] at head tail ⊢
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem replay_avoid (divide : Bool) : base 1026∉wires (Q6EndpointReplay.replay divide) := by
  let e:Equiv.Perm Wire:=⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by omega),OB5.sig_invol 511 (by omega)⟩
  have fix:e (base 1026)=base 1026:=by decide +kernel
  apply rename_avoid e _ _ fix
  cases divide <;> simp only [Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨⟨endPacket_avoid hKernel false,groups_avoid hKernel false 1 101 (by omega)⟩,firstPacket_avoid hKernel false⟩
  · exact ⟨⟨firstPacket_avoid hKernel true,groups_avoid hKernel true 1 101 (by omega)⟩,endPacket_avoid hKernel true⟩

end ECDSAAdd.Entrant.Q6EndpointFree1026

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant.Q6EndpointFree2312
open ECDSAAdd Arithmetic MappedCompressed OwnMinusHost
attribute [local irreducible] wires OwnQ6Core5.kernel OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT
variable (hKernel : ∀divide,base 2312∉wires (OwnQ6Core5.kernel divide (Q6EndpointCell.ports base (base 2409))))
include hKernel

theorem half_avoid (divide : Bool) :
    base 2312∉wires (Q6EndpointCell.half divide base (base 2409)) := by
  have k:=hKernel divide
  simpa only [Q6EndpointCell.half,OwnQ6Core5.half,wires_append,wires,Instr.wires,
    Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false,
    Q6EndpointCell.ports,not_or] using
    And.intro (And.intro (by decide : base 2312≠base 2409) k) (by decide : base 2312≠base 2409)

theorem swap_avoid : base 2312∉wires (swapRegisters (base 2410)
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y) := by
  have len:(Q6EndpointCell.ports base (base 2409)).r.length=
      (Q6EndpointCell.ports base (base 2409)).y.length := by
    rw [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
    simp [wireBlock_length]
  have h:=swapRegisters_wires (base 2410) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y len
  intro used
  have mem:=h used
  rw [List.mem_toFinset,List.mem_cons,List.mem_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with eq|r|y
  · exact (by decide : base 2312≠base 2410) eq
  · exact not_block 2312 2056 256 (by omega) r
  · exact not_block 2312 770 256 (by omega) y

theorem body_avoid (divide : Bool) :
    base 2312∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := by
  cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨swap_avoid hKernel,half_avoid hKernel false⟩
  · exact ⟨half_avoid hKernel true,swap_avoid hKernel⟩

theorem select_avoid (b source flag : Wire) (v : Bool) (P : Program)
    (hb : base 2312≠b) (hs : base 2312≠source) (hf : base 2312≠flag)
    (hp : base 2312∉wires P) : base 2312∉wires (transcriptSelectWindow b source flag v P) := by
  intro used
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at used <;> tauto

theorem cell_avoid (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : base 2312≠g) (hs : base 2312≠sw) :
    base 2312∉wires (Q6EndpointCell.cell divide base (base 2400) g sw (base 2409) (base 2410) ig is) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide)
    (select_avoid hKernel _ _ _ _ _ (by decide) hs (by decide) (body_avoid hKernel divide))

theorem endpoint_avoid (divide : Bool) (g : Wire) (ig : Bool) (hg : base 2312≠g) :
    base 2312∉wires (Q6EndpointCell.endpoint divide base (base 2400) g (base 2409) ig) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide) (fun used => half_avoid hKernel divide (Q6EndpointCell.halfE_wires divide base (base 2409) used))

attribute [local irreducible] Q6EndpointCell.cell Q6EndpointCell.endpoint

theorem codec_avoid (start : Nat) (hs : start+5≤512) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : base 2312∉wires P := by
  intro used
  obtain ⟨r,eq⟩:=History5.history_gate_mem base start P hp (base 2312) used
  have bounds:=History5.historyId_region start hs r
  change base 2312=base (History5.historyId start r) at eq
  have same:=base_injective eq
  omega

theorem raw_avoid (divide : Bool) (ls : List MixedTranscriptLetter)
    (controls : ∀l∈ls,base 2312≠l.1.1 ∧ base 2312≠l.1.2) :
    base 2312∉wires (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => simp [Q6EndpointReplay.rawReplay,wires]
  | cons l ls ih =>
    have c:=cell_avoid hKernel divide l.1.1 l.1.2 l.2.1 l.2.2 (controls l (by simp)).1 (controls l (by simp)).2
    have rest:=ih (fun k hk=>controls k (List.mem_cons_of_mem _ hk))
    cases divide <;> simp only [Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_replay_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 2312∉wires (Q6EndpointReplay.body divide j) := by
  apply raw_avoid hKernel
  intro l hl
  have c:=Replay5.letters_controls j hj l hl
  have no:=codec_avoid hKernel (5*j) (by omega) _ (Or.inl rfl)
  exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩

theorem firstSwap_avoid : base 2312∉wires Replay5.firstSwap := by
  apply select_avoid hKernel _ _ _ _ _ (by decide) (by decide) (by decide)
  exact swap_avoid hKernel

theorem firstBody_avoid (divide : Bool) : base 2312∉wires (Q6EndpointReplay.firstBody divide) := by
  have ctrl : ∀l∈Replay5.restLetters,base 2312≠l.1.1 ∧ base 2312≠l.1.2 := by
    intro l hl
    have mem:l∈Replay5.letters 0:=by rw [Replay5.letters_zero];simp [hl]
    have c:=Replay5.letters_controls 0 (by omega) l mem
    have no:=codec_avoid hKernel 0 (by omega) _ (Or.inl rfl)
    exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩
  cases divide <;> simp only [Q6EndpointReplay.firstBody,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨raw_avoid hKernel false _ ctrl,by rw [UncompSwap.firstSwapM_wires]; exact firstSwap_avoid hKernel⟩
  · exact ⟨firstSwap_avoid hKernel,raw_avoid hKernel true _ ctrl⟩

theorem pi_fix (j : Nat) (hj : j<102) : shifted (Placement5.pi j) (base 2312)=base 2312 := by
  rw [shifted_base,Placement5.pi_outside j 2312 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

theorem packet_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 2312∉wires (Q6EndpointReplay.packet divide j) := by
  apply rename_avoid _ _ _ (pi_fix hKernel j hj)
  simp only [Q6EndpointReplay.basePacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),body_replay_avoid hKernel divide j hj⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem firstPacket_avoid (divide : Bool) : base 2312∉wires (Q6EndpointReplay.firstPacket divide) := by
  apply rename_avoid _ _ _ (pi_fix hKernel 0 (by omega))
  simp only [Q6EndpointReplay.baseFirstPacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),firstBody_avoid hKernel divide⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem endPacket_avoid (divide : Bool) : base 2312∉wires (Q6EndpointReplay.endPacket divide) := by
  have fix:shifted Placement5.pi0 (base 2312)=base 2312:=by
    rw [shifted_base,Placement5.pi0_outside 2312]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply rename_avoid _ _ _ fix
  apply endpoint_avoid hKernel
  decide

theorem groups_avoid (divide : Bool) (j n : Nat) (hb : j+n≤102) :
    base 2312∉wires (Q6EndpointReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [Q6EndpointReplay.groups,PacketSequence.program,wires]
  | succ n ih =>
    have head:=packet_avoid hKernel divide j (by omega)
    have tail:=ih (j+1) (by omega)
    cases divide <;> simp only [Q6EndpointReplay.groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,wires_append,Finset.mem_union,not_or] at head tail ⊢
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem replay_avoid (divide : Bool) : base 2312∉wires (Q6EndpointReplay.replay divide) := by
  let e:Equiv.Perm Wire:=⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by omega),OB5.sig_invol 511 (by omega)⟩
  have fix:e (base 2312)=base 2312:=by decide +kernel
  apply rename_avoid e _ _ fix
  cases divide <;> simp only [Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨⟨endPacket_avoid hKernel false,groups_avoid hKernel false 1 101 (by omega)⟩,firstPacket_avoid hKernel false⟩
  · exact ⟨⟨firstPacket_avoid hKernel true,groups_avoid hKernel true 1 101 (by omega)⟩,endPacket_avoid hKernel true⟩

end ECDSAAdd.Entrant.Q6EndpointFree2312

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant.Q6EndpointFree766
open ECDSAAdd Arithmetic MappedCompressed OwnMinusHost
attribute [local irreducible] wires OwnQ6Core5.kernel OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT
variable (hKernel : ∀divide,base 766∉wires (OwnQ6Core5.kernel divide (Q6EndpointCell.ports base (base 2409))))
include hKernel

theorem half_avoid (divide : Bool) :
    base 766∉wires (Q6EndpointCell.half divide base (base 2409)) := by
  have k:=hKernel divide
  simpa only [Q6EndpointCell.half,OwnQ6Core5.half,wires_append,wires,Instr.wires,
    Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false,
    Q6EndpointCell.ports,not_or] using
    And.intro (And.intro (by decide : base 766≠base 2409) k) (by decide : base 766≠base 2409)

theorem swap_avoid : base 766∉wires (swapRegisters (base 2410)
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y) := by
  have len:(Q6EndpointCell.ports base (base 2409)).r.length=
      (Q6EndpointCell.ports base (base 2409)).y.length := by
    rw [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
    simp [wireBlock_length]
  have h:=swapRegisters_wires (base 2410) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y len
  intro used
  have mem:=h used
  rw [List.mem_toFinset,List.mem_cons,List.mem_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with eq|r|y
  · exact (by decide : base 766≠base 2410) eq
  · exact not_block 766 2056 256 (by omega) r
  · exact not_block 766 770 256 (by omega) y

theorem body_avoid (divide : Bool) :
    base 766∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := by
  cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨swap_avoid hKernel,half_avoid hKernel false⟩
  · exact ⟨half_avoid hKernel true,swap_avoid hKernel⟩

theorem select_avoid (b source flag : Wire) (v : Bool) (P : Program)
    (hb : base 766≠b) (hs : base 766≠source) (hf : base 766≠flag)
    (hp : base 766∉wires P) : base 766∉wires (transcriptSelectWindow b source flag v P) := by
  intro used
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at used <;> tauto

theorem cell_avoid (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : base 766≠g) (hs : base 766≠sw) :
    base 766∉wires (Q6EndpointCell.cell divide base (base 2400) g sw (base 2409) (base 2410) ig is) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide)
    (select_avoid hKernel _ _ _ _ _ (by decide) hs (by decide) (body_avoid hKernel divide))

theorem endpoint_avoid (divide : Bool) (g : Wire) (ig : Bool) (hg : base 766≠g) :
    base 766∉wires (Q6EndpointCell.endpoint divide base (base 2400) g (base 2409) ig) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide) (fun used => half_avoid hKernel divide (Q6EndpointCell.halfE_wires divide base (base 2409) used))

attribute [local irreducible] Q6EndpointCell.cell Q6EndpointCell.endpoint

theorem codec_avoid (start : Nat) (hs : start+5≤512) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : base 766∉wires P := by
  intro used
  obtain ⟨r,eq⟩:=History5.history_gate_mem base start P hp (base 766) used
  have bounds:=History5.historyId_region start hs r
  change base 766=base (History5.historyId start r) at eq
  have same:=base_injective eq
  omega

theorem raw_avoid (divide : Bool) (ls : List MixedTranscriptLetter)
    (controls : ∀l∈ls,base 766≠l.1.1 ∧ base 766≠l.1.2) :
    base 766∉wires (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => simp [Q6EndpointReplay.rawReplay,wires]
  | cons l ls ih =>
    have c:=cell_avoid hKernel divide l.1.1 l.1.2 l.2.1 l.2.2 (controls l (by simp)).1 (controls l (by simp)).2
    have rest:=ih (fun k hk=>controls k (List.mem_cons_of_mem _ hk))
    cases divide <;> simp only [Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_replay_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 766∉wires (Q6EndpointReplay.body divide j) := by
  apply raw_avoid hKernel
  intro l hl
  have c:=Replay5.letters_controls j hj l hl
  have no:=codec_avoid hKernel (5*j) (by omega) _ (Or.inl rfl)
  exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩

theorem firstSwap_avoid : base 766∉wires Replay5.firstSwap := by
  apply select_avoid hKernel _ _ _ _ _ (by decide) (by decide) (by decide)
  exact swap_avoid hKernel

theorem firstBody_avoid (divide : Bool) : base 766∉wires (Q6EndpointReplay.firstBody divide) := by
  have ctrl : ∀l∈Replay5.restLetters,base 766≠l.1.1 ∧ base 766≠l.1.2 := by
    intro l hl
    have mem:l∈Replay5.letters 0:=by rw [Replay5.letters_zero];simp [hl]
    have c:=Replay5.letters_controls 0 (by omega) l mem
    have no:=codec_avoid hKernel 0 (by omega) _ (Or.inl rfl)
    exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩
  cases divide <;> simp only [Q6EndpointReplay.firstBody,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨raw_avoid hKernel false _ ctrl,by rw [UncompSwap.firstSwapM_wires]; exact firstSwap_avoid hKernel⟩
  · exact ⟨firstSwap_avoid hKernel,raw_avoid hKernel true _ ctrl⟩

theorem pi_fix (j : Nat) (hj : j<102) : shifted (Placement5.pi j) (base 766)=base 766 := by
  rw [shifted_base,Placement5.pi_outside j 766 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

theorem packet_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 766∉wires (Q6EndpointReplay.packet divide j) := by
  apply rename_avoid _ _ _ (pi_fix hKernel j hj)
  simp only [Q6EndpointReplay.basePacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),body_replay_avoid hKernel divide j hj⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem firstPacket_avoid (divide : Bool) : base 766∉wires (Q6EndpointReplay.firstPacket divide) := by
  apply rename_avoid _ _ _ (pi_fix hKernel 0 (by omega))
  simp only [Q6EndpointReplay.baseFirstPacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),firstBody_avoid hKernel divide⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem endPacket_avoid (divide : Bool) : base 766∉wires (Q6EndpointReplay.endPacket divide) := by
  have fix:shifted Placement5.pi0 (base 766)=base 766:=by
    rw [shifted_base,Placement5.pi0_outside 766]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply rename_avoid _ _ _ fix
  apply endpoint_avoid hKernel
  decide

theorem groups_avoid (divide : Bool) (j n : Nat) (hb : j+n≤102) :
    base 766∉wires (Q6EndpointReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [Q6EndpointReplay.groups,PacketSequence.program,wires]
  | succ n ih =>
    have head:=packet_avoid hKernel divide j (by omega)
    have tail:=ih (j+1) (by omega)
    cases divide <;> simp only [Q6EndpointReplay.groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,wires_append,Finset.mem_union,not_or] at head tail ⊢
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem replay_avoid (divide : Bool) : base 766∉wires (Q6EndpointReplay.replay divide) := by
  let e:Equiv.Perm Wire:=⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by omega),OB5.sig_invol 511 (by omega)⟩
  have fix:e (base 766)=base 766:=by decide +kernel
  apply rename_avoid e _ _ fix
  cases divide <;> simp only [Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨⟨endPacket_avoid hKernel false,groups_avoid hKernel false 1 101 (by omega)⟩,firstPacket_avoid hKernel false⟩
  · exact ⟨⟨firstPacket_avoid hKernel true,groups_avoid hKernel true 1 101 (by omega)⟩,endPacket_avoid hKernel true⟩

end ECDSAAdd.Entrant.Q6EndpointFree766

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant.Q6EndpointFree765
open ECDSAAdd Arithmetic MappedCompressed OwnMinusHost
attribute [local irreducible] wires OwnQ6Core5.kernel OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT
variable (hKernel : ∀divide,base 765∉wires (OwnQ6Core5.kernel divide (Q6EndpointCell.ports base (base 2409))))
include hKernel

theorem half_avoid (divide : Bool) :
    base 765∉wires (Q6EndpointCell.half divide base (base 2409)) := by
  have k:=hKernel divide
  simpa only [Q6EndpointCell.half,OwnQ6Core5.half,wires_append,wires,Instr.wires,
    Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false,
    Q6EndpointCell.ports,not_or] using
    And.intro (And.intro (by decide : base 765≠base 2409) k) (by decide : base 765≠base 2409)

theorem swap_avoid : base 765∉wires (swapRegisters (base 2410)
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y) := by
  have len:(Q6EndpointCell.ports base (base 2409)).r.length=
      (Q6EndpointCell.ports base (base 2409)).y.length := by
    rw [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
    simp [wireBlock_length]
  have h:=swapRegisters_wires (base 2410) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y len
  intro used
  have mem:=h used
  rw [List.mem_toFinset,List.mem_cons,List.mem_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with eq|r|y
  · exact (by decide : base 765≠base 2410) eq
  · exact not_block 765 2056 256 (by omega) r
  · exact not_block 765 770 256 (by omega) y

theorem body_avoid (divide : Bool) :
    base 765∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := by
  cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨swap_avoid hKernel,half_avoid hKernel false⟩
  · exact ⟨half_avoid hKernel true,swap_avoid hKernel⟩

theorem select_avoid (b source flag : Wire) (v : Bool) (P : Program)
    (hb : base 765≠b) (hs : base 765≠source) (hf : base 765≠flag)
    (hp : base 765∉wires P) : base 765∉wires (transcriptSelectWindow b source flag v P) := by
  intro used
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at used <;> tauto

theorem cell_avoid (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : base 765≠g) (hs : base 765≠sw) :
    base 765∉wires (Q6EndpointCell.cell divide base (base 2400) g sw (base 2409) (base 2410) ig is) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide)
    (select_avoid hKernel _ _ _ _ _ (by decide) hs (by decide) (body_avoid hKernel divide))

theorem endpoint_avoid (divide : Bool) (g : Wire) (ig : Bool) (hg : base 765≠g) :
    base 765∉wires (Q6EndpointCell.endpoint divide base (base 2400) g (base 2409) ig) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide) (fun used => half_avoid hKernel divide (Q6EndpointCell.halfE_wires divide base (base 2409) used))

attribute [local irreducible] Q6EndpointCell.cell Q6EndpointCell.endpoint

theorem codec_avoid (start : Nat) (hs : start+5≤512) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : base 765∉wires P := by
  intro used
  obtain ⟨r,eq⟩:=History5.history_gate_mem base start P hp (base 765) used
  have bounds:=History5.historyId_region start hs r
  change base 765=base (History5.historyId start r) at eq
  have same:=base_injective eq
  omega

theorem raw_avoid (divide : Bool) (ls : List MixedTranscriptLetter)
    (controls : ∀l∈ls,base 765≠l.1.1 ∧ base 765≠l.1.2) :
    base 765∉wires (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => simp [Q6EndpointReplay.rawReplay,wires]
  | cons l ls ih =>
    have c:=cell_avoid hKernel divide l.1.1 l.1.2 l.2.1 l.2.2 (controls l (by simp)).1 (controls l (by simp)).2
    have rest:=ih (fun k hk=>controls k (List.mem_cons_of_mem _ hk))
    cases divide <;> simp only [Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_replay_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 765∉wires (Q6EndpointReplay.body divide j) := by
  apply raw_avoid hKernel
  intro l hl
  have c:=Replay5.letters_controls j hj l hl
  have no:=codec_avoid hKernel (5*j) (by omega) _ (Or.inl rfl)
  exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩

theorem firstSwap_avoid : base 765∉wires Replay5.firstSwap := by
  apply select_avoid hKernel _ _ _ _ _ (by decide) (by decide) (by decide)
  exact swap_avoid hKernel

theorem firstBody_avoid (divide : Bool) : base 765∉wires (Q6EndpointReplay.firstBody divide) := by
  have ctrl : ∀l∈Replay5.restLetters,base 765≠l.1.1 ∧ base 765≠l.1.2 := by
    intro l hl
    have mem:l∈Replay5.letters 0:=by rw [Replay5.letters_zero];simp [hl]
    have c:=Replay5.letters_controls 0 (by omega) l mem
    have no:=codec_avoid hKernel 0 (by omega) _ (Or.inl rfl)
    exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩
  cases divide <;> simp only [Q6EndpointReplay.firstBody,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨raw_avoid hKernel false _ ctrl,by rw [UncompSwap.firstSwapM_wires]; exact firstSwap_avoid hKernel⟩
  · exact ⟨firstSwap_avoid hKernel,raw_avoid hKernel true _ ctrl⟩

theorem pi_fix (j : Nat) (hj : j<102) : shifted (Placement5.pi j) (base 765)=base 765 := by
  rw [shifted_base,Placement5.pi_outside j 765 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

theorem packet_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 765∉wires (Q6EndpointReplay.packet divide j) := by
  apply rename_avoid _ _ _ (pi_fix hKernel j hj)
  simp only [Q6EndpointReplay.basePacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),body_replay_avoid hKernel divide j hj⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem firstPacket_avoid (divide : Bool) : base 765∉wires (Q6EndpointReplay.firstPacket divide) := by
  apply rename_avoid _ _ _ (pi_fix hKernel 0 (by omega))
  simp only [Q6EndpointReplay.baseFirstPacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),firstBody_avoid hKernel divide⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem endPacket_avoid (divide : Bool) : base 765∉wires (Q6EndpointReplay.endPacket divide) := by
  have fix:shifted Placement5.pi0 (base 765)=base 765:=by
    rw [shifted_base,Placement5.pi0_outside 765]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply rename_avoid _ _ _ fix
  apply endpoint_avoid hKernel
  decide

theorem groups_avoid (divide : Bool) (j n : Nat) (hb : j+n≤102) :
    base 765∉wires (Q6EndpointReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [Q6EndpointReplay.groups,PacketSequence.program,wires]
  | succ n ih =>
    have head:=packet_avoid hKernel divide j (by omega)
    have tail:=ih (j+1) (by omega)
    cases divide <;> simp only [Q6EndpointReplay.groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,wires_append,Finset.mem_union,not_or] at head tail ⊢
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem replay_avoid (divide : Bool) : base 765∉wires (Q6EndpointReplay.replay divide) := by
  let e:Equiv.Perm Wire:=⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by omega),OB5.sig_invol 511 (by omega)⟩
  have fix:e (base 765)=base 765:=by decide +kernel
  apply rename_avoid e _ _ fix
  cases divide <;> simp only [Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨⟨endPacket_avoid hKernel false,groups_avoid hKernel false 1 101 (by omega)⟩,firstPacket_avoid hKernel false⟩
  · exact ⟨⟨firstPacket_avoid hKernel true,groups_avoid hKernel true 1 101 (by omega)⟩,endPacket_avoid hKernel true⟩

end ECDSAAdd.Entrant.Q6EndpointFree765

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant.Q6EndpointFree767
open ECDSAAdd Arithmetic MappedCompressed OwnMinusHost
attribute [local irreducible] wires OwnQ6Core5.kernel OwnQ5Endpoint.centerT OwnQ5Endpoint.canonT
variable (hKernel : ∀divide,base 767∉wires (OwnQ6Core5.kernel divide (Q6EndpointCell.ports base (base 2409))))
include hKernel

theorem half_avoid (divide : Bool) :
    base 767∉wires (Q6EndpointCell.half divide base (base 2409)) := by
  have k:=hKernel divide
  simpa only [Q6EndpointCell.half,OwnQ6Core5.half,wires_append,wires,Instr.wires,
    Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false,
    Q6EndpointCell.ports,not_or] using
    And.intro (And.intro (by decide : base 767≠base 2409) k) (by decide : base 767≠base 2409)

theorem swap_avoid : base 767∉wires (swapRegisters (base 2410)
    (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y) := by
  have len:(Q6EndpointCell.ports base (base 2409)).r.length=
      (Q6EndpointCell.ports base (base 2409)).y.length := by
    rw [Q6EndpointCell.ports_r,Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y]
    simp [wireBlock_length]
  have h:=swapRegisters_wires (base 2410) (Q6EndpointCell.ports base (base 2409)).r
    (Q6EndpointCell.ports base (base 2409)).y len
  intro used
  have mem:=h used
  rw [List.mem_toFinset,List.mem_cons,List.mem_append,Q6EndpointCell.ports_r,
    Q6EndpointCell.ports_y,balancedSharedPorts_r,balancedSharedPorts_y] at mem
  rcases mem with eq|r|y
  · exact (by decide : base 767≠base 2410) eq
  · exact not_block 767 2056 256 (by omega) r
  · exact not_block 767 770 256 (by omega) y

theorem body_avoid (divide : Bool) :
    base 767∉wires (Q6EndpointCell.body divide base (base 2409) (base 2410)) := by
  cases divide <;> simp only [Q6EndpointCell.body,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨swap_avoid hKernel,half_avoid hKernel false⟩
  · exact ⟨half_avoid hKernel true,swap_avoid hKernel⟩

theorem select_avoid (b source flag : Wire) (v : Bool) (P : Program)
    (hb : base 767≠b) (hs : base 767≠source) (hf : base 767≠flag)
    (hp : base 767∉wires P) : base 767∉wires (transcriptSelectWindow b source flag v P) := by
  intro used
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at used <;> tauto

theorem cell_avoid (divide : Bool) (g sw : Wire) (ig is : Bool)
    (hg : base 767≠g) (hs : base 767≠sw) :
    base 767∉wires (Q6EndpointCell.cell divide base (base 2400) g sw (base 2409) (base 2410) ig is) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide)
    (select_avoid hKernel _ _ _ _ _ (by decide) hs (by decide) (body_avoid hKernel divide))

theorem endpoint_avoid (divide : Bool) (g : Wire) (ig : Bool) (hg : base 767≠g) :
    base 767∉wires (Q6EndpointCell.endpoint divide base (base 2400) g (base 2409) ig) := by
  exact select_avoid hKernel _ _ _ _ _ (by decide) hg (by decide) (fun used => half_avoid hKernel divide (Q6EndpointCell.halfE_wires divide base (base 2409) used))

attribute [local irreducible] Q6EndpointCell.cell Q6EndpointCell.endpoint

theorem codec_avoid (start : Nat) (hs : start+5≤512) (P : Program)
    (hp : P=History5.encode base start ∨ P=History5.decode base start) : base 767∉wires P := by
  intro used
  obtain ⟨r,eq⟩:=History5.history_gate_mem base start P hp (base 767) used
  have bounds:=History5.historyId_region start hs r
  change base 767=base (History5.historyId start r) at eq
  have same:=base_injective eq
  omega

theorem raw_avoid (divide : Bool) (ls : List MixedTranscriptLetter)
    (controls : ∀l∈ls,base 767≠l.1.1 ∧ base 767≠l.1.2) :
    base 767∉wires (Q6EndpointReplay.rawReplay divide ls) := by
  induction ls with
  | nil => simp [Q6EndpointReplay.rawReplay,wires]
  | cons l ls ih =>
    have c:=cell_avoid hKernel divide l.1.1 l.1.2 l.2.1 l.2.2 (controls l (by simp)).1 (controls l (by simp)).2
    have rest:=ih (fun k hk=>controls k (List.mem_cons_of_mem _ hk))
    cases divide <;> simp only [Q6EndpointReplay.rawReplay,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union,not_or] at c rest ⊢
    · exact ⟨rest,c⟩
    · exact ⟨c,rest⟩

theorem body_replay_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 767∉wires (Q6EndpointReplay.body divide j) := by
  apply raw_avoid hKernel
  intro l hl
  have c:=Replay5.letters_controls j hj l hl
  have no:=codec_avoid hKernel (5*j) (by omega) _ (Or.inl rfl)
  exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩

theorem firstSwap_avoid : base 767∉wires Replay5.firstSwap := by
  apply select_avoid hKernel _ _ _ _ _ (by decide) (by decide) (by decide)
  exact swap_avoid hKernel

theorem firstBody_avoid (divide : Bool) : base 767∉wires (Q6EndpointReplay.firstBody divide) := by
  have ctrl : ∀l∈Replay5.restLetters,base 767≠l.1.1 ∧ base 767≠l.1.2 := by
    intro l hl
    have mem:l∈Replay5.letters 0:=by rw [Replay5.letters_zero];simp [hl]
    have c:=Replay5.letters_controls 0 (by omega) l mem
    have no:=codec_avoid hKernel 0 (by omega) _ (Or.inl rfl)
    exact ⟨fun e=>no (e ▸ c.1),fun e=>no (e ▸ c.2)⟩
  cases divide <;> simp only [Q6EndpointReplay.firstBody,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨raw_avoid hKernel false _ ctrl,by rw [UncompSwap.firstSwapM_wires]; exact firstSwap_avoid hKernel⟩
  · exact ⟨firstSwap_avoid hKernel,raw_avoid hKernel true _ ctrl⟩

theorem pi_fix (j : Nat) (hj : j<102) : shifted (Placement5.pi j) (base 767)=base 767 := by
  rw [shifted_base,Placement5.pi_outside j 767 hj]
  unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
  omega

theorem packet_avoid (divide : Bool) (j : Nat) (hj : j<102) :
    base 767∉wires (Q6EndpointReplay.packet divide j) := by
  apply rename_avoid _ _ _ (pi_fix hKernel j hj)
  simp only [Q6EndpointReplay.basePacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),body_replay_avoid hKernel divide j hj⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem firstPacket_avoid (divide : Bool) : base 767∉wires (Q6EndpointReplay.firstPacket divide) := by
  apply rename_avoid _ _ _ (pi_fix hKernel 0 (by omega))
  simp only [Q6EndpointReplay.baseFirstPacket,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨codec_avoid hKernel _ (by omega) _ (Or.inr rfl),firstBody_avoid hKernel divide⟩,
    codec_avoid hKernel _ (by omega) _ (Or.inl rfl)⟩

theorem endPacket_avoid (divide : Bool) : base 767∉wires (Q6EndpointReplay.endPacket divide) := by
  have fix:shifted Placement5.pi0 (base 767)=base 767:=by
    rw [shifted_base,Placement5.pi0_outside 767]
    unfold Placement5.zeroRegion Placement5.workRegion Placement5.holeRegion
    omega
  apply rename_avoid _ _ _ fix
  apply endpoint_avoid hKernel
  decide

theorem groups_avoid (divide : Bool) (j n : Nat) (hb : j+n≤102) :
    base 767∉wires (Q6EndpointReplay.groups divide j n) := by
  induction n generalizing j with
  | zero => simp [Q6EndpointReplay.groups,PacketSequence.program,wires]
  | succ n ih =>
    have head:=packet_avoid hKernel divide j (by omega)
    have tail:=ih (j+1) (by omega)
    cases divide <;> simp only [Q6EndpointReplay.groups,PacketSequence.program,Bool.false_eq_true,
      if_false,if_true,wires_append,Finset.mem_union,not_or] at head tail ⊢
    · exact ⟨tail,head⟩
    · exact ⟨head,tail⟩

theorem replay_avoid (divide : Bool) : base 767∉wires (Q6EndpointReplay.replay divide) := by
  let e:Equiv.Perm Wire:=⟨OB5.sig 511,OB5.sig 511,OB5.sig_invol 511 (by omega),OB5.sig_invol 511 (by omega)⟩
  have fix:e (base 767)=base 767:=by decide +kernel
  apply rename_avoid e _ _ fix
  cases divide <;> simp only [Q6EndpointReplay.logicalReplay,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.mem_union,not_or]
  · exact ⟨⟨endPacket_avoid hKernel false,groups_avoid hKernel false 1 101 (by omega)⟩,firstPacket_avoid hKernel false⟩
  · exact ⟨⟨firstPacket_avoid hKernel true,groups_avoid hKernel true 1 101 (by omega)⟩,endPacket_avoid hKernel true⟩

end ECDSAAdd.Entrant.Q6EndpointFree767



-- ENDPOINT COMPONENT ConcreteOmissionsE.lean
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Entrant.Q6EndpointOmissions
open Arithmetic MappedCompressed
attribute [local irreducible] wires OwnQ6Core5.kernel
private theorem ports_nodup : (Q6EndpointCell.ports base (base 2409)).wires.Nodup := by
  apply Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective
  decide +kernel

theorem kernel_free (divide : Bool) (k : Nat) (hk : k∈[1541,1026,2312,766,765,767]) :
    base k∉wires (OwnQ6Core5.kernel divide (Q6EndpointCell.ports base (base 2409))) := by
  have hw:=Q6EndpointCell.ports_widths base (base 2409)
  have hn:=ports_nodup
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [show (Q6EndpointCell.ports base (base 2409)).carry.getD 254 0=base 1541 by decide +kernel] using
      OwnQ6Core5.kernel_retired_free divide _ hw hn
  · simpa only [show (Q6EndpointCell.ports base (base 2409)).carry.getD 255 0=base 1026 by decide +kernel] using
      OwnQ6Core5.kernel_last_free divide _ hw hn
  all_goals
    apply OwnQ6Core5.kernel_unused_free divide _ hw hn
    decide +kernel

theorem replay_free (divide : Bool) (k : Nat) (hk : k∈[1541,1026,2312,766,765,767]) :
    base k∉wires (Q6EndpointReplay.replay divide) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Q6EndpointRetired.replay_avoid (fun d => kernel_free d 1541 (by decide)) divide
  · exact Q6EndpointFree1026.replay_avoid (fun d => kernel_free d 1026 (by decide)) divide
  · exact Q6EndpointFree2312.replay_avoid (fun d => kernel_free d 2312 (by decide)) divide
  · exact Q6EndpointFree766.replay_avoid (fun d => kernel_free d 766 (by decide)) divide
  · exact Q6EndpointFree765.replay_avoid (fun d => kernel_free d 765 (by decide)) divide
  · exact Q6EndpointFree767.replay_avoid (fun d => kernel_free d 767 (by decide)) divide
end ECDSAAdd.Entrant.Q6EndpointOmissions


-- ENDPOINT COMPONENT ConverterOmissionsE.lean
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointConverterFree
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 BalancedField
attribute [local irreducible] wires

theorem raw_free : base 513 ∉ wires HalfField5.centerT ∧
    base 513 ∉ wires HalfField5.canonT := by
  have sup := HalfConvert.support HalfField.tgt (balancedSharedTargetConvert_widths base)
  have out : base 513 ∉ HalfField.tgt.wires.toFinset := by decide +kernel
  exact ⟨fun h => out (sup.1 h),fun h => out (sup.2 h)⟩

theorem relocated_free : base 1541 ∉ wires HalfFieldOB5.centerT ∧
    base 1541 ∉ wires HalfFieldOB5.canonT := by
  have image : HalfFieldOB5.endpointMap (base 513)=base 1541 := by decide +kernel
  have lift (P : Program) (hp : base 513∉wires P) :
      base 1541∉wires (renameProgram HalfFieldOB5.endpointMap P) := by
    intro h
    rw [renameProgram_support] at h
    obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp h
    have same : q=base 513 := HalfFieldOB5.endpointMap.injective (eq.trans image.symm)
    subst q
    exact hp hq
  exact ⟨lift _ raw_free.1,lift _ raw_free.2⟩

theorem plus_free : base 1541 ∉ wires OwnPlusEndpoint.centerT ∧
    base 1541 ∉ wires OwnPlusEndpoint.canonT := by
  have fix : OwnPlusEndpoint.swap (base 1541)=base 1541 := by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix relocated_free.1,
    OwnPlusHost.rename_avoid _ _ _ fix relocated_free.2⟩

theorem guard_free : base 1541 ∉ wires OwnGuardEndpoint.centerT ∧
    base 1541 ∉ wires OwnGuardEndpoint.canonT := by
  have fix : OwnGuardEndpoint.swap (base 1541)=base 1541 := by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix plus_free.1,
    OwnPlusHost.rename_avoid _ _ _ fix plus_free.2⟩

theorem q4_free : base 1541 ∉ wires OwnQ4Endpoint.centerT ∧
    base 1541 ∉ wires OwnQ4Endpoint.canonT := by
  have fix : OwnQ4Endpoint.swap (base 1541)=base 1541 := by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix guard_free.1,
    OwnPlusHost.rename_avoid _ _ _ fix guard_free.2⟩

theorem endpoint_free : base 1541 ∉ wires OwnQ5Endpoint.centerT ∧
    base 1541 ∉ wires OwnQ5Endpoint.canonT := by
  have fix : OwnQ5Endpoint.swap (base 1541)=base 1541 := by decide +kernel
  exact ⟨OwnPlusHost.rename_avoid _ _ _ fix q4_free.1,
    OwnPlusHost.rename_avoid _ _ _ fix q4_free.2⟩
end ECDSAAdd.Entrant.Q6EndpointConverterFree

namespace ECDSAAdd.Entrant.Q6EndpointOmissions
open Arithmetic MappedCompressed
attribute [local irreducible] wires

theorem converter_free (k : Nat) (hk : k∈[1541,1026,2312,766,765,767]) :
 base k∉wires OwnQ5Endpoint.centerT ∧ base k∉wires OwnQ5Endpoint.canonT := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
 · exact Q6EndpointConverterFree.endpoint_free
 · exact OwnQ5Endpoint.plus_free
 · exact OwnQ5Endpoint.parity_free
 · exact OwnQ5Endpoint.prior_free766
 · exact OwnQ5Endpoint.prior_free765
 · exact OwnQ5Endpoint.prior_free767

theorem copy_free (k : Nat) (hk : k∈[1541,1026,2312,766,765,767]) :
 base k∉wires HalfFieldOB5.copyN := by
 intro used
 have mem:=copyRegister_wires_subset none
    (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y used
 simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,
    balancedSharedPorts_r,balancedSharedPorts_y] at mem
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases mem with a|a
 · exact OwnMinusHost.not_block k 2056 256 (by rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega) a
 · exact OwnMinusHost.not_block k 770 256 (by rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega) a
end ECDSAAdd.Entrant.Q6EndpointOmissions


-- ENDPOINT COMPONENT FieldOmissionsE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6EndpointOmissions
open Arithmetic MappedCompressed
attribute [local irreducible] wires Q6EndpointReplay.replay Q6EndpointSW.replayS

theorem field_free (k : Nat) (hk : k∈[1541,1026,2312,766,765,767]) :
 base k∉wires (Q6EndpointReplay.replay true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT)) := by
 simp only [wires_append,Finset.mem_union,not_or]
 exact ⟨replay_free true k hk,copy_free k hk,(converter_free k hk).2⟩

theorem selected_replay_free (divide : Bool) (k : Nat) (hk : k∈[1541,1026,2312,766,765,767]) :
 base k∉wires (Q6EndpointSW.replayS divide) := by
 intro used
 exact replay_free divide k hk
   ((@SW.InstrSub2.wires_sub (Q6EndpointSW.replayS divide) (Q6EndpointReplay.replay divide)
     (Q6EndpointSW.selReplay_sel divide).sub) used)

theorem fieldS_free (k : Nat) (hk : k∈[1541,1026,2312,766,765,767]) :
 base k∉wires (Q6EndpointSW.replayS true++(HalfFieldOB5.copyN++OwnQ5Endpoint.canonT)) := by
 simp only [wires_append,Finset.mem_union,not_or]
 exact ⟨selected_replay_free true k hk,copy_free k hk,(converter_free k hk).2⟩

theorem host_free (P : Program) (k : Nat) (hk : k∈[1541,1026,2312,766,765,767])
 (hP : base k∉wires P) :
 base k∉wires ([.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)])) := by
 have fix : HostOB5.hostSwap (base k)=base k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
 have no : base k≠base 511 := by
  intro h
  have e:=base_injective h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
 let e : Equiv.Perm Wire:=⟨HostOB5.hostSwap,HostOB5.hostSwap,HostOB5.hostSwap_invol,HostOB5.hostSwap_invol⟩
 have mid:=OwnPlusHost.rename_avoid e (base k) P fix hP
 simpa only [wires_append,wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,
   Finset.notMem_empty,or_false,not_or] using And.intro no (And.intro mid no)

end ECDSAAdd.Entrant.Q6EndpointOmissions


-- ENDPOINT SUCCESSOR SelectedE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6EndpointEntryRaw
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI
attribute [local irreducible] run wires kernel5
def field5S : Program := Q6EndpointSW.replayS true ++ (HalfFieldOB5.copyN ++ OwnQ5Endpoint.canonT)
def hostField5S : Program :=
  [.X (base 511)] ++ (renameProgram HostOB5.hostSwap field5S ++ [.X (base 511)])
def kernel5S : Program :=
  NativeFirstDirect.forward base ++ stackForwardT ++ skywalkArithmeticClear base ++
    hostField5S ++ skywalkArithmeticClear base ++ stackReverseT ++ NativeFirstKnown.inverse base

theorem selField5 : SW.Sel (base 2400) 1020 field5S field5 := by
  have r:=Q6EndpointSW.selReplay_sel true
  have old:=Q5FusionFields.selField5
  have canonAway : base 2400∉wires OwnQ5Endpoint.canonT := by
    intro h
    exact old.away (by simp only [Q5FusionFields.field5S,wires_append,Finset.mem_union];exact Or.inr (Or.inr h))
  have cp:=SW.Sel.refl (base 2400) HalfFieldOB5.copyN SW.selCenter_away.2.2
  have cn:=SW.Sel.refl (base 2400) OwnQ5Endpoint.canonT canonAway
  simpa only [field5S,field5,Nat.add_zero] using r.append (cp.append cn)

theorem selHostField5 : SW.Sel (base 2400) 1020 hostField5S hostField5 := by
  have r := (selField5.rename_inj HostOB5.hostSwap HostOB5.hostSwap_injective).castb SW.selHost_fix
  have h := (SW.Sel.refl _ _ SW.selX511_away).append
    (r.append (SW.Sel.refl _ _ SW.selX511_away))
  simpa only [hostField5S,hostField5,Nat.zero_add,Nat.add_zero] using h

theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 := by
  have native := NativeFirstDirect.prefix_support base
  have known := NativeFirstKnown.inverse_support base
  have fw : base 2400∉wires (NativeFirstDirect.forward base) := fun h => SW.selPrefix_away (native.1 h)
  have iv : base 2400∉wires (NativeFirstKnown.inverse base) := fun h => SW.selPrefix_away (known h)
  have ints := SW.selInt_away
  have h := ((((((SW.Sel.refl _ _ fw).append (SW.Sel.refl _ _ ints.1)).append
    (SW.Sel.refl _ _ SW.selClear_away)).append selHostField5).append
    (SW.Sel.refl _ _ SW.selClear_away)).append (SW.Sel.refl _ _ ints.2)).append (SW.Sel.refl _ _ iv)
  simpa only [kernel5S,kernel5,Nat.zero_add,Nat.add_zero] using h


attribute [local irreducible] kernel5S
def forceControl5 (s : State) : State := ⟨s.phase,writeBit s.basis (base 2400) true⟩

theorem forceControl5_keep (s : State) (q : Wire) (hq : q≠base 2400) :
    (forceControl5 s).basis q=s.basis q := by simp [forceControl5,writeBit,Function.update_of_ne hq]

theorem forceControl5_true (s : State) : (forceControl5 s).basis (base 2400)=true := by
  simp [forceControl5,writeBit]

/-- The shortened selector-free division receives a half-centered numerator. -/
theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  let a := forceControl5 s
  let b := forceControl5 t
  have shared : base 2400∉skywalkSharedWires base := ho _ (by simp)
  have divAway : base 2400∉wireBlock base 770 256 := fun h =>
    shared (arith_block_subset_shared base 770 256 (by omega) h)
  have numAway : base 2400∉wireBlock base 2056 256 := fun h =>
    shared (arith_block_subset_shared base 2056 256 (by omega) h)
  have input : SkywalkArithmeticInput base x Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=x
      apply (regValue_congr _ _ _ ?_).trans hin.1
      intro q hq
      exact forceControl5_keep s q (fun e => divAway (e ▸ hq))
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      apply (regValue_congr _ _ _ ?_).trans hin.2.1
      intro q hq
      exact forceControl5_keep s q (fun e => numAway (e ▸ hq))
    · intro q hq hdx hdy
      rw [forceControl5_keep s q (fun e => shared (e ▸ hq))]
      exact hin.2.2 q hq hdx hdy
  have hg : a.basis (base 2409)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hg0
  have hs : a.basis (base 2410)=false :=
    (forceControl5_keep s _ (by simp [base])).trans hs0
  have ab : a.basis (base 2400)=true := forceControl5_true s
  have bb : b.basis (base 2400)=true := forceControl5_true t
  have phases : b.phase=a.phase := phase
  have paired (q : Wire) (hq : q∉wireBlock base 2056 256) : b.basis q=a.basis q := by
    by_cases e : q=base 2400
    · subst q; rw [forceControl5_true,forceControl5_true]
    · rw [forceControl5_keep t q e,forceControl5_keep s q e]
      exact same q hq
  have half : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    exact forceControl5_keep t q (fun e => numAway (e ▸ hq))
  have strong := kernel5_correct hn hlo ho hf x Y hx0 hx a b m input hg hs phases paired half
  obtain ⟨equiv,_⟩ := selKernel5.eq m b bb
  unfold DirectSkywalkArithmeticStrong at strong
  rw [ab,←equiv] at strong
  simp only [directSkywalkResult,if_true] at strong
  have agree := pool_run_agrees kernel5S (wires kernel5S) (Finset.Subset.refl _) m t b rfl
    (fun q hq => (forceControl5_keep t q (fun e => selKernel5.away (e ▸ hq))).symm)
  have sameRun (q : Wire) (hq : q≠base 2400) :
      (run kernel5S m t).basis q=(run kernel5S m b).basis q := by
    by_cases used : q∈wires kernel5S
    · exact agree.2 q used
    · rw [run_preserves_outside _ m t q used,run_preserves_outside _ m b q used]
      exact (forceControl5_keep t q hq).symm
  refine ⟨agree.1.trans strong.1,?_,?_⟩
  · apply (regValue_congr _ _ _ ?_).trans strong.2.1
    intro q hq
    exact sameRun q (fun e => numAway (e ▸ hq))
  · intro q hq
    by_cases e : q=base 2400
    · subst q
      exact (run_preserves_outside _ m t _ selKernel5.away).trans (same _ numAway)
    · exact (sameRun q e).trans ((strong.2.2 q hq).trans (forceControl5_keep s q e))


end ECDSAAdd.Entrant.Q6EndpointEntryRaw


-- ENDPOINT SUCCESSOR PhaseKernelsE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EndpointEntryQ5
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5
  Q6EndpointEntryRaw Q5Global718
attribute [local irreducible] run wires Q6EndpointEntryRaw.kernel5 Q6EndpointEntryRaw.kernel5S

def kernel5 : Program:=Q5FusionPhase.relocated hostField5
def kernel5S : Program:=Q5FusionPhase.relocated hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free : base 1026∉wires hostField5 := by
 exact Q6EndpointOmissions.host_free field5 1026 (by simp) (Q6EndpointOmissions.field_free 1026 (by simp))
theorem hostField5S_free : base 1026∉wires hostField5S := by
 exact Q6EndpointOmissions.host_free field5S 1026 (by simp) (Q6EndpointOmissions.fieldS_free 1026 (by simp))
theorem old_shape : Q5FusionPhase.kernel hostField5=Q6EndpointEntryRaw.kernel5 := by
 simp only [Q5FusionPhase.kernel,firstPhase,lastPhase,Q6EndpointEntryRaw.kernel5,List.append_assoc]
theorem old_shapeS : Q5FusionPhase.kernel hostField5S=Q6EndpointEntryRaw.kernel5S := by
 simp only [Q5FusionPhase.kernel,firstPhase,lastPhase,Q6EndpointEntryRaw.kernel5S,List.append_assoc]
theorem kernel5_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old := Q6EndpointEntryRaw.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have contract : DirectSkywalkArithmeticStrong true base (base 2400) x Y s
      (run (Q5FusionPhase.kernel hostField5) m t) := by
    simpa only [old_shape] using old
  have eq := Q5FusionPhase.state_eq_of_contract hn x Y hx0 hx s t m hostField5 true
    hin same hostField5_free contract
  rw [kernel5,eq]
  exact contract

theorem kernel5S_correct
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old := Q6EndpointEntryRaw.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q5FusionPhase.kernel hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shapeS] using old.2.2
  have eq := Q5FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m hostField5S
    hin same hostField5S_free frame
  simp only [kernel5S,eq,old_shapeS]
  exact old


end ECDSAAdd.Entrant.EndpointEntryQ5


-- ENDPOINT SUCCESSOR KernelsE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnEndpointEntryQ6
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed BalancedField History5 Q6EndpointEntryRaw
attribute [local irreducible] run wires

def kernel5 : Program:=Q6FusionPhase.relocated Q6EndpointEntryRaw.hostField5
def kernel5S : Program:=Q6FusionPhase.relocated Q6EndpointEntryRaw.hostField5S
attribute [local irreducible] kernel5 kernel5S

theorem hostField5_free1541 : base 1541∉wires Q6EndpointEntryRaw.hostField5 := by
 exact Q6EndpointOmissions.host_free field5 1541 (by simp) (Q6EndpointOmissions.field_free 1541 (by simp))
theorem hostField5S_free1541 : base 1541∉wires Q6EndpointEntryRaw.hostField5S := by
 exact Q6EndpointOmissions.host_free field5S 1541 (by simp) (Q6EndpointOmissions.fieldS_free 1541 (by simp))

theorem outer_shape (F : Program) : Q6FusionPhase.kernel F=Q5FusionPhase.relocated F := by
 simp only [Q6FusionPhase.kernel,Q5FusionPhase.relocated,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
   Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase]
theorem old_shape_kernel5 : Q6FusionPhase.kernel Q6EndpointEntryRaw.hostField5=EndpointEntryQ5.kernel5 := by
 simpa only [EndpointEntryQ5.kernel5] using outer_shape Q6EndpointEntryRaw.hostField5
theorem old_shape_kernel5S : Q6FusionPhase.kernel Q6EndpointEntryRaw.hostField5S=EndpointEntryQ5.kernel5S := by
 simpa only [EndpointEntryQ5.kernel5S] using outer_shape Q6EndpointEntryRaw.hostField5S
theorem kernel5_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    DirectSkywalkArithmeticStrong true base (base 2400) x Y s (run kernel5 m t) := by
  have old:=EndpointEntryQ5.kernel5_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel Q6EndpointEntryRaw.hostField5) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m Q6EndpointEntryRaw.hostField5 hin same hostField5_free1541 frame
  simpa only [kernel5,eq,old_shape_kernel5] using old
theorem kernel5S_correct     (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) (s t : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409)=false) (hs0 : s.basis (base 2410)=false)
    (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2)) :
    let out := run kernel5S m t
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(skywalkArithmeticResult true x Y).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have old:=EndpointEntryQ5.kernel5S_correct hn hlo ho hf x Y hx0 hx s t m hin hg0 hs0 phase same value
  have frame : ∀q,q∉wireBlock base 2056 256 →
      (run (Q6FusionPhase.kernel Q6EndpointEntryRaw.hostField5S) m t).basis q=s.basis q := by
    simpa only [old_shape_kernel5S] using old.2.2
  have eq:=Q6FusionPhase.state_eq_of_frame hn x Y hx0 hx s t m Q6EndpointEntryRaw.hostField5S hin same hostField5S_free1541 frame
  simpa only [kernel5S,eq,old_shape_kernel5S] using old

end ECDSAAdd.Entrant.OwnEndpointEntryQ6


-- ENDPOINT SUCCESSOR GeometryE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EndpointEntryGeometry
open Arithmetic MappedCompressed Q6IntegerHost
attribute [local irreducible] wires run
set_option maxHeartbeats 1000000 in
theorem host_support (P : Program) (hp:wires P⊆OB5Support.segSites) : wires ([.X (base 511)]++(renameProgram HostOB5.hostSwap P++[.X (base 511)]))⊆OB5Support.logicalSites := by
  have mem (i : Nat) (hi : i ∈ OB5Support.logicalIndices) : base i ∈ OB5Support.logicalSites :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hi, rfl⟩)
  have m511 : base 511 ∈ OB5Support.logicalSites := mem 511 (by
    simp only [OB5Support.logicalIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false]; omega)
  have m1542 : base 1542 ∈ OB5Support.logicalSites := mem 1542 (by
    simp only [OB5Support.logicalIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
      List.not_mem_nil, or_false]; omega)
  have x (r : Wire) (hr : r ∈ wires [Instr.X (base 511)]) : r = base 511 := by
    simpa [wires, Instr.wires] using hr
  intro q hq
  simp only [wires_append, Finset.mem_union] at hq
  rcases hq with h|h|h
  · rw [x q h]; exact m511
  · rw [renameProgram_support] at h
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp h
    have hs := hp hold
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
    unfold HostOB5.hostSwap
    split_ifs with c d e f
    · exact m511
    · exfalso
      have := base_injective d
      subst this
      simp only [OB5Support.segIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      omega
    · exact m1542
    · exfalso
      have := base_injective f
      subst this
      simp only [OB5Support.segIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      omega
    · apply mem
      have c' : i ≠ 2409 := fun h => c (by rw [h])
      have e' : i ≠ 2410 := fun h => e (by rw [h])
      simp only [OB5Support.segIndices, OB5Support.logicalIndices, List.mem_append, List.mem_range'_1,
        List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
  · rw [x q h]; exact m511

theorem raw_support : wires Q6EndpointEntryRaw.kernel5⊆OB5Support.logicalSites := by
 have first:=(NativeFirstDirect.prefix_support base).1.trans OB5Support.prefixSites_sub_logical
 have f:=stackForwardT_subset.trans (StackOB5.forward_support.trans OB5Support.integer_sub_logical)
 have c:=OB5Support.clear_support_logical
 have b:=host_support Q6EndpointEntryRaw.field5 Q6EndpointEntryRaw.field_support
 have r:=stackReverseT_subset.trans (StackOB5.reverse_support.trans OB5Support.integer_sub_logical)
 have last:=(NativeFirstKnown.inverse_support base).trans OB5Support.prefixSites_sub_logical
 simp only [Q6EndpointEntryRaw.kernel5,wires_append,Finset.union_subset_iff,and_assoc]
 exact ⟨first,f,c,b,c,r,last⟩

theorem q5support (F : Program) (old:wires (Q5FusionPhase.kernel F)⊆OB5Support.logicalSites) :
 wires (Q5FusionPhase.relocated F)⊆OB5Support.logicalSites := by
 simp only [Q5FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
 simp only [Q5FusionPhase.relocated,wires_append,Finset.union_subset_iff]
 exact ⟨OwnQ5Integer.rename_support _ old.1,old.2.1,OwnQ5Integer.rename_support _ old.2.2⟩
theorem swap_logical (q : Wire) (hq : q∈OB5Support.logicalSites) : swap q∈OB5Support.logicalSites := by
  have member (i : Nat) (hi : i=719∨i=1541) : base i∈OB5Support.logicalSites := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    rcases hi with rfl|rfl <;> omega
  by_cases a:q=base 1541
  · subst q;simpa only [swap,Equiv.swap_apply_left] using member 719 (Or.inl rfl)
  · by_cases b:q=base 719
    · subst q;simpa only [swap,Equiv.swap_apply_right] using member 1541 (Or.inr rfl)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem rename_support (P : Program) (old : wires P⊆OB5Support.logicalSites) :
    wires (renameProgram swap P)⊆OB5Support.logicalSites := by
  rw [renameProgram_support]
  intro q h
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp h
  exact swap_logical w (old hw)

theorem q6support (F : Program) (old : wires (Q5FusionPhase.relocated F)⊆OB5Support.logicalSites) :
    wires (Q6FusionPhase.relocated F)⊆OB5Support.logicalSites := by
  rw [←OwnEndpointEntryQ6.outer_shape] at old
  simp only [Q6FusionPhase.kernel,wires_append,Finset.union_subset_iff] at old
  simp only [Q6FusionPhase.relocated,wires_append,Finset.union_subset_iff]
  exact ⟨rename_support _ old.1,old.2.1,rename_support _ old.2.2⟩

theorem sel (F G : Program) (h : SW.Sel (base 2400) 1020 G F) :
    SW.Sel (base 2400) 1020 (Q6FusionPhase.relocated G) (Q6FusionPhase.relocated F) := by
  have fp : base 2400∉wires q5First := by
    simpa only [q5First,Q6IntegerHost.firstPhase,Q5Global718.firstPhase] using OwnQ5SW.renamed_first_away
  have lp : base 2400∉wires q5Last := by
    simpa only [q5Last,Q6IntegerHost.lastPhase,Q5Global718.lastPhase] using OwnQ5SW.renamed_last_away
  have fix : swap (base 2400)=base 2400 := by decide +kernel
  have hh:=(SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix fp)).append
    (h.append (SW.Sel.refl _ _ (OwnPlusHost.rename_avoid _ _ _ fix lp)))
  simpa only [Q6FusionPhase.relocated,Nat.zero_add,Nat.add_zero] using hh

end ECDSAAdd.Entrant.EndpointEntryGeometry
namespace ECDSAAdd.Entrant.OwnEndpointEntryQ6
open Arithmetic MappedCompressed Q6IntegerHost
attribute [local irreducible] wires

theorem kernel5_support : wires kernel5⊆OB5Support.logicalSites := by
 apply EndpointEntryGeometry.q6support
 apply EndpointEntryGeometry.q5support
 simpa only [EndpointEntryQ5.old_shape] using EndpointEntryGeometry.raw_support

theorem selKernel5 : SW.Sel (base 2400) 1020 kernel5S kernel5 :=
 EndpointEntryGeometry.sel _ _ Q6EndpointEntryRaw.selHostField5

theorem kernel5S_support : wires kernel5S⊆OB5Support.logicalSites :=
 selKernel5.sub.wires_sub.trans kernel5_support
end ECDSAAdd.Entrant.OwnEndpointEntryQ6


-- ENDPOINT SUCCESSOR CallersE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section
namespace ECDSAAdd.Entrant.OwnEndpointEntryQ6
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires

private theorem mapped_regS (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀q∈r,logical q=physical (f q)) :
    regValue r logical=regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0)+2*regValue rs logical=
      (if physical (f a) then 1 else 0)+2*regValue (rs.map f) physical
    rw [h a (by simp),ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

/-- A renamed replay receives the same pool as a canonical virtual state,
while its actual numerator has already been half-centered. -/
theorem kernelTransferS (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀a∈domain,∀b∈domain,f a=f b → a=b)
    (divisorMap : (wireBlock base 770 256).map f=L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f=L.point.y)
    (controlMap : f (base 2400)=L.core.generic)
    (sharedWork : ∀q∈skywalkSharedWires base,q∈domain → q∉wireBlock base 770 256 →
      q∉wireBlock base 2056 256 → f q∈L.dialogPool)
    (selectorG : f (base 2409)∈L.dialogPool) (selectorS : f (base 2410)∈L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset⊆domain)
    (dySites : (wireBlock base 2056 256).toFinset⊆domain) (bSite : base 2400∈domain)
    (sites : wires OwnEndpointEntryQ6.kernel5S⊆domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0)
    (phase : t.phase=s.phase) (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (renameProgram f OwnEndpointEntryQ6.kernel5S) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q∈domain) : a.basis q=s.basis (f q) := by
    simp only [a,laneLogicalInput,if_pos hq]
  have bBits (q : Wire) (hq : q∈domain) : b.basis q=t.basis (f q) := by
    simp only [b,laneLogicalInput,if_pos hq]
  have zero (q : Wire) (hq : f q∈L.dialogPool) : a.basis q=false := by
    change (if q∈domain then s.basis (f q) else false)=false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_,?_,?_⟩
    · change regValue (wireBlock base 770 256) a.basis=X
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))),divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis=Y.val
      rw [mapped_regS f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q∈domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a,laneLogicalInput,if_neg used]
  have outside (q : Wire) (hq : q∈domain) (haway : q∉wireBlock base 2056 256) : f q∉L.point.y := by
    rw [←numeratorMap]
    intro bad
    obtain ⟨r,hr,he⟩ := List.mem_map.mp bad
    have eq : q=r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀q,q∉wireBlock base 2056 256 → b.basis q=a.basis q := by
    intro q hq
    by_cases used : q∈domain
    · rw [bBits q used,aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a,b,laneLogicalInput,if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis=centerWord (Y/2) := by
    rw [mapped_regS f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))),numeratorMap]
    exact half
  have phases : b.phase=a.phase := by change t.phase=s.phase; exact phase
  have strong := OwnEndpointEntryQ6.kernel5S_correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective OwnEndpointEntryQ6.kernel5S sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1,?_,?_⟩
  · rw [←numeratorMap]
    exact (mapped_regS f _ (run OwnEndpointEntryQ6.kernel5S m b).basis
      (run (renameProgram f OwnEndpointEntryQ6.kernel5S) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q∈domain.image f
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp image
      have away : r∉skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [←numeratorMap]
        exact List.mem_map.mpr ⟨r,mem,rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain OwnEndpointEntryQ6.kernel5S sites m t q image).trans (same q hq)


end ECDSAAdd.Entrant.OwnEndpointEntryQ6
end
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnEndpointEntryQ6
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5
attribute [local irreducible] run wires toffoliCount measurementCount
def arithEntryS (L : ControlledPointLayout) : Program := renameProgram (wireFn2 L) OwnEndpointEntryQ6.kernel5S

theorem arithEntryS_support (L : ControlledPointLayout) (hw : L.Widths) :
    wires (arithEntryS L)⊆(OB5Support.sites L).toFinset :=
  OB5Support.placed_support_logical L hw _ kernel5S_support

private theorem divisor_sitesS : (wireBlock base 770 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inl (List.mem_toFinset.mp hq))

private theorem numerator_sitesS : (wireBlock base 2056 256).toFinset⊆slots.toFinset := by
  intro q hq
  apply resident_support
  simp only [resident,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (List.mem_toFinset.mp hq))

private theorem control_siteS : base 2400∈slots.toFinset := by
  apply slot_mem
  · unfold live; omega
  · unfold CompressedAllocation.omitted; omega

theorem arithEntryS_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    let out := run (arithEntryS L) m t
    out.phase=s.phase ∧ regValue L.point.y out.basis=(skywalkArithmeticResult true X Y).val ∧
      ∀q,q∉L.point.y → out.basis q=s.basis q := by
  rcases placement2 L hw hn with ⟨inj,divisor,numerator,control,shared,selG,selS,_⟩
  exact kernelTransferS L (wireFn2 L) slots.toFinset inj divisor numerator control shared selG selS
    divisor_sitesS numerator_sitesS control_siteS (OwnEndpointEntryQ6.kernel5S_support.trans ArithmeticOB5.logical_sub_old)
    logicalND hlo logicalAway logicalReplay X Y B hX0 hX s t m hb hx hy clean phase same half

attribute [local irreducible] arithEntryS arithS

theorem arithEntryS_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (B : Bool) (hX0 : 0<X) (hX : X<p)
    (s t : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y.val)
    (clean : regValue L.dialogPool s.basis=0) (phase : t.phase=s.phase)
    (same : ∀q,q∉L.point.y → t.basis q=s.basis q)
    (half : regValue L.point.y t.basis=centerWord (Y/2)) :
    run (arithEntryS L) m t=run (arithS L false) [] s := by
  have newer := arithEntryS_correct L hw hn logicalND hlo logicalAway logicalReplay X Y B hX0 hX
    s t m hb hx hy clean phase same half
  have older := arithS_correct L hw hn false X Y.val hX hX0 (ZMod.val_lt Y) s [] hx hy clean
  have sameValue : regValue L.point.y (run (arithEntryS L) m t).basis =
      regValue L.point.y (run (arithS L false) [] s).basis := by
    rw [newer.2.1,older.2.1]
    simp [skywalkArithmeticResult,ZMod.natCast_zmod_val]
  apply State.extensionality
  · exact newer.1.trans older.1.symm
  · funext q
    by_cases hq : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp sameValue q hq
    · exact (newer.2.2 q hq).trans (older.2.2 q hq).symm

end ECDSAAdd.Entrant.OwnEndpointEntryQ6
end


namespace ECDSAAdd.Entrant.OwnEndpointEntryQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse
open Challenge Baselines
def fusedDivisionF (L : ControlledPointLayout) (k : Fp) : Program :=
  fusedY L k ++ arithEntryS L

section EntryStep
attribute [local irreducible] run arithEntryS arithS fusedY fastConstAdd

theorem fusedDivisionF_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X≠0) :
    Triple (PointDialogValues L X Y G origin) (fusedDivisionF L k)
      (PointDialogValues L X ((Y+(if G then k else 0))/X) G origin) := by
  intro s m v
  let Z : Fp := Y+(if G then k else 0)
  let n := measurementCount (fusedY L k)
  let a := run (fusedY L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := fusedY_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase=s.phase ∧ regValue L.point.y a.basis=
    centerWord ((Y+(if s.basis L.core.generic then k else 0))/2) ∧
    ∀q,q∉L.point.y → a.basis q=s.basis q at fused
  change c.phase=s.phase ∧ regValue L.point.y c.basis=(Y.val+(if G then k.val else 0))%p ∧
    ∀q,q∉L.point.y → c.basis q=s.basis q at oldAdd
  have phase : a.phase=c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q∉L.point.y) : a.basis q=c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis=centerWord (Z/2) := by
    simpa only [v.generic,Z] using fused.2.1
  have hp : 0<X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have equal := arithEntryS_eq L hw hn logicalND hlo logicalAway logicalReplay X.val Z G hp X.isLt
    c a (m.drop n) canonical.generic canonical.x canonical.y canonical.clean phase same half
  have eqProgram : run (fusedDivisionF L k) m s=run (arithS L false) [] c := by
    simp only [fusedDivisionF,run_append]
    change run (arithEntryS L) (m.drop n) a=run (arithS L false) [] c
    exact equal
  have old := arith3F_step L hw hn X Z G origin false hX c [] canonical
  rw [eqProgram]
  refine ⟨old.1.trans oldStep.1,?_⟩
  simpa only [Z,Bool.false_eq_true,if_false] using old.2

end EntryStep
end ECDSAAdd.Entrant.OwnEndpointEntryQ6


-- ENDPOINT SUCCESSOR ResourcesE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EndpointEntryResources
open Arithmetic Secp256k1 DirectSkywalk MappedCompressed MappedCompressed.LaneA
  CompressedAllocation CompressedFieldSupport OffsetBorrowedCanonical BalancedField History5 LaneI
attribute [local irreducible] wires run toffoliCount measurementCount

theorem field_sub : InstrSub Q6EndpointEntryRaw.field5 (Q6EndpointSegment.program true) := by
 constructor
 · intro i hi
   left
   change i∈OwnQ5Endpoint.centerT++Q6EndpointEntryRaw.field5
   exact List.mem_append_right _ hi
 · change Challenge.gateSlots Q6EndpointEntryRaw.field5≤
     Challenge.gateSlots (OwnQ5Endpoint.centerT++Q6EndpointEntryRaw.field5)
   rw [Challenge.gateSlots_append]
   omega

theorem raw_physical : GatePhysical Q6EndpointEntryRaw.kernel5 := by
 have cfg:=MappedCompressed.LaneA.laneLogical_config
 have f:=field_sub.physical (Q6EndpointSegment.program_physical true cfg.1 cfg.2.1 cfg.2.2)
 have hosted:=Q5FusionFields.host_physical Q6EndpointEntryRaw.field5 f
 have first:=(NativeFirstDirect.programs_physical base base_pool_nodup).1
 have last:=NativeFirstKnown.inverse_physical base base_pool_nodup
 simp only [Q6EndpointEntryRaw.kernel5,gatePhysical_append]
 exact ⟨⟨⟨⟨⟨⟨first,stackForwardT_physical⟩,mappedClear_physical⟩,hosted⟩,
   mappedClear_physical⟩,stackReverseT_physical⟩,last⟩

theorem raw_slots : Challenge.gateSlots Q6EndpointEntryRaw.kernel5≤20500006 := by
 have native:=Baselines.nativeFirst_gateSlots_le base
 have integer:=Stack5.slots_le base base_pool_nodup 1 511 (by omega)
 have f:=StackOB5.forward_counts.2.2
 have r:=StackOB5.reverse_counts.2.2
 have ft:=stackForwardT_metrics.2.2
 have rt:=stackReverseT_metrics.2.2
 have field:=field_sub.slots.trans (Q6EndpointSegment.program_gateSlots_le true)
 have clear:Challenge.gateSlots (skywalkArithmeticClear base)=3:=by
   simp [skywalkArithmeticClear,skywalkTerminalClear,Challenge.gateSlots,Challenge.instructionSlots]
 have x:Challenge.gateSlots [.X (base 511)]=1:=rfl
 simp only [Q6EndpointEntryRaw.kernel5,Q6EndpointEntryRaw.hostField5,
   Challenge.gateSlots_append,Baselines.rename_gateSlots,clear,x]
 omega

/-- Exact counts use the new field body and protected integer budget, not a mutable old parent. -/
theorem raw_counts : toffoliCount Q6EndpointEntryRaw.kernel5=1048904 ∧
 measurementCount Q6EndpointEntryRaw.kernel5=720767 := by
 have cfg:=MappedCompressed.LaneA.laneLogical_config
 have narrow:=W.compactPasses5_old_counts base base_pool_nodup
 have repair:=Stack5.counts_511 base base_pool_nodup
 have old:=Kernel5.actualKernel5_counts true
 have oldField:=HalfField5.segment5_counts true cfg.1 cfg.2.2 cfg.2.1
 have fresh:=Q6EndpointSegment.program_counts true cfg.1 (cfg.2.1 _ (by simp))
 have f:=StackOB5.forward_counts
 have r:=StackOB5.reverse_counts
 have ft:=stackForwardT_metrics
 have rt:=stackReverseT_metrics
 have cv:=OwnQ5Endpoint.endpoint_counts
 simp only [Kernel5.actualKernel5,toffoliCount_append,measurementCount_append] at old
 simp only [Q6EndpointSegment.program,if_true,toffoliCount_append,measurementCount_append] at fresh
 have ren:=renameProgram_counts HostOB5.hostSwap Q6EndpointEntryRaw.field5
 simp only [Q6EndpointEntryRaw.kernel5,Q6EndpointEntryRaw.hostField5,
   toffoliCount_append,measurementCount_append,ren.1,ren.2,toffoliCount,measurementCount]
 simp only [Q6EndpointEntryRaw.field5,toffoliCount_append,measurementCount_append]
 simp only [Bool.false_eq_true,if_false,if_true] at old oldField fresh
 constructor <;> omega

theorem q5_physical (F : Program) (h:GatePhysical (Q5FusionPhase.kernel F)) :
 GatePhysical (Q5FusionPhase.relocated F) := by
 simp only [Q5FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q5FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q5Global718.swap Q5Global718.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q5Global718.swap Q5Global718.swap.injective _ h.2.2⟩

theorem q6_physical (F : Program) (h:GatePhysical (Q5FusionPhase.relocated F)) :
 GatePhysical (Q6FusionPhase.relocated F) := by
 rw [←OwnEndpointEntryQ6.outer_shape] at h
 simp only [Q6FusionPhase.kernel,gatePhysical_append] at h
 simp only [Q6FusionPhase.relocated,gatePhysical_append]
 exact ⟨gatePhysical_rename Q6IntegerHost.swap Q6IntegerHost.swap.injective _ h.1,
   h.2.1,gatePhysical_rename Q6IntegerHost.swap Q6IntegerHost.swap.injective _ h.2.2⟩

theorem outer_slots (F : Program) :
 Challenge.gateSlots (Q6FusionPhase.relocated F)=Challenge.gateSlots (Q5FusionPhase.kernel F) := by
 simp only [Q6FusionPhase.relocated,Q5FusionPhase.kernel,Q6IntegerHost.q5First,Q6IntegerHost.q5Last,
   Q6IntegerHost.firstPhase,Q6IntegerHost.lastPhase,Q5Global718.firstPhase,Q5Global718.lastPhase,
   Challenge.gateSlots_append,Baselines.rename_gateSlots]

theorem outer_counts (F : Program) :
 toffoliCount (Q6FusionPhase.relocated F)=toffoliCount (Q5FusionPhase.kernel F) ∧
 measurementCount (Q6FusionPhase.relocated F)=measurementCount (Q5FusionPhase.kernel F) := by
 have a:=Q6FusionPhase.relocated_counts F
 rw [OwnEndpointEntryQ6.outer_shape] at a
 have b:=Q5FusionPhase.relocated_counts F
 exact ⟨a.1.trans b.1,a.2.trans b.2⟩
end ECDSAAdd.Entrant.EndpointEntryResources

namespace ECDSAAdd.Entrant.OwnEndpointEntryQ6
open Arithmetic Secp256k1 MappedCompressed DirectSkywalk Q6EndpointEntryRaw
attribute [local irreducible] run wires toffoliCount measurementCount

theorem kernel5_physical : GatePhysical kernel5 := by
 apply EndpointEntryResources.q6_physical
 apply EndpointEntryResources.q5_physical
 simpa only [EndpointEntryQ5.old_shape] using EndpointEntryResources.raw_physical

theorem kernel5S_physical : GatePhysical kernel5S := selKernel5.sub.physical kernel5_physical

theorem kernel5_slots_le : Challenge.gateSlots kernel5≤20500006 := by
 rw [kernel5,EndpointEntryResources.outer_slots,EndpointEntryQ5.old_shape]
 exact EndpointEntryResources.raw_slots

theorem kernel5S_slots_le : Challenge.gateSlots kernel5S≤20500006 :=
 selKernel5.sub.slots.trans kernel5_slots_le

theorem kernel5_counts : toffoliCount kernel5=1048904 ∧ measurementCount kernel5=720767 := by
 have h:=EndpointEntryResources.outer_counts Q6EndpointEntryRaw.hostField5
 rw [EndpointEntryQ5.old_shape] at h
 simpa only [kernel5,h.1,h.2] using EndpointEntryResources.raw_counts

theorem kernel5S_counts : toffoliCount kernel5S=1047884 ∧ measurementCount kernel5S=720767 := by
 have c:=kernel5_counts
 have t:=selKernel5.tc
 have m:=selKernel5.mc
 constructor <;> omega

theorem arithEntryS_physical (L : ControlledPointLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 GatePhysical (arithEntryS L) := by
 apply gatePhysical_rename_support (wireFn2 L) kernel5S
 · intro a ha b hb eq
   exact (placement2 L hw hn).injectiveOnSlots a (ArithmeticOB5.logical_sub_old (kernel5S_support ha))
     b (ArithmeticOB5.logical_sub_old (kernel5S_support hb)) eq
 · exact kernel5S_physical

theorem arithEntryS_counts (L : ControlledPointLayout) :
 toffoliCount (arithEntryS L)=1047884 ∧ measurementCount (arithEntryS L)=720767 := by
 simpa only [arithEntryS,(renameProgram_counts (wireFn2 L) kernel5S).1,
   (renameProgram_counts (wireFn2 L) kernel5S).2] using kernel5S_counts

theorem arithEntryS_gateSlots_le (L : ControlledPointLayout) :
 Challenge.gateSlots (arithEntryS L)≤20500006 := by
 simpa only [arithEntryS,Baselines.rename_gateSlots] using kernel5S_slots_le

theorem fusedDivisionF_counts (L : ControlledPointLayout) (hw:L.Widths) (k:Fp) :
 toffoliCount (fusedDivisionF L k)=1048650 ∧ measurementCount (fusedDivisionF L k)=721534 := by
 have a:=EntryFuse.fusedY_counts L hw k
 have b:=arithEntryS_counts L
 simp only [fusedDivisionF,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
 constructor <;> trivial
end ECDSAAdd.Entrant.OwnEndpointEntryQ6


-- ENDPOINT SUCCESSOR OmissionsPlacedE.lean
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EndpointEntryOmissions
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 CompressedPointDialog
attribute [local irreducible] wires
private theorem placed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (P : Program) (hp : wires P⊆OB5Support.logicalSites) (i k : Nat)
 (hi : base i∈OB5Support.logicalSites) (hm : wireFn2 L (base i)=L.core.poolWire k)
 (free : base i∉wires P) : L.core.poolWire k∉wires (renameProgram (wireFn2 L) P) := by
 rw [renameProgram_support]
 intro h
 obtain ⟨old,used,eq⟩ := Finset.mem_image.mp h
 have mapped : wireFn2 L old=wireFn2 L (base i) := by simpa only [hm] using eq
 have back := (placement2 L hw hn).injectiveOnSlots old
   (ArithmeticOB5.logical_sub_old (hp used)) (base i) (ArithmeticOB5.logical_sub_old hi) mapped
 exact free (back ▸ used)
private theorem logical (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∈OB5Support.logicalSites := by
 simp only [OB5Support.logicalSites,List.mem_toFinset,List.mem_map]
 refine ⟨i,?_,rfl⟩
 simp only [OB5Support.logicalIndices,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 omega
private theorem entry_old (i : Nat) (hi : i∈[2312,766,765,767,1026]) : base i∉wires OwnEntryFuseQ5.kernel5S := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnParityHost.kernel_parity_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnPlusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnGuardFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact fun used => OwnQ5Integer.preserve_avoid true _ (by decide +kernel) (by decide +kernel)
     (OwnMinusFinal.kernel_free true) (OwnEntryFuseQ5.kernel5_sub.wires_sub (OwnEntryFuseQ5.selKernel5.sub.wires_sub used))
 · exact OwnEntryFuseQ5.kernel5S_1026_free

private theorem q5_free (i : Nat) (hi : i∈[2312,766,765,767,1026]) :
 base i∉wires (Q5FusionPhase.relocated Q6EndpointEntryRaw.hostField5S) := by
 have h:=entry_old i hi
 have newField : base i∉wires Q6EndpointEntryRaw.hostField5S := by
  apply Q6EndpointOmissions.host_free _ i
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
  · apply Q6EndpointOmissions.fieldS_free
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    omega
 simp only [OwnEntryFuseQ5.kernel5S,Q5FusionPhase.relocated,wires_append,Finset.mem_union,not_or] at h ⊢
 exact ⟨h.1,newField,h.2.2⟩

private theorem kernel_free (i : Nat) (hi : i∈[2312,766,765,767,1026,1541]) :
 base i∉wires OwnEndpointEntryQ6.kernel5S := by
 by_cases last : i=1541
 · subst i
   simpa only [OwnEndpointEntryQ6.kernel5S] using
    Q6FusionPhase.relocated_1541_free _ OwnEndpointEntryQ6.hostField5S_free1541
 · have prior : i∈[2312,766,765,767,1026] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
   have old:=q5_free i prior
   rw [←OwnEndpointEntryQ6.outer_shape] at old
   simp only [Q6FusionPhase.kernel,wires_append,Finset.mem_union,not_or] at old
   have fix : Q6IntegerHost.swap (base i)=base i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro eq; exact last (base_injective eq)
    · intro eq
      have same:=base_injective eq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at prior
      omega
   have first:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.1
   have final:=OwnPlusHost.rename_avoid Q6IntegerHost.swap (base i) _ fix old.2.2
   simpa only [OwnEndpointEntryQ6.kernel5S,Q6FusionPhase.relocated,wires_append,Finset.mem_union,not_or] using
     And.intro first (And.intro old.2.1 final)

theorem entry_avoids (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) :
 L.core.poolWire k∉wires (OwnEndpointEntryQ6.arithEntryS L) := by
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
 · exact placed L hw hn OwnEndpointEntryQ6.kernel5S OwnEndpointEntryQ6.kernel5S_support 2312 1800
     (logical 2312 (by simp)) (by rfl) (kernel_free 2312 (by simp))
 · exact placed L hw hn OwnEndpointEntryQ6.kernel5S OwnEndpointEntryQ6.kernel5S_support 766 766
     (logical 766 (by simp)) (by rfl) (kernel_free 766 (by simp))
 · exact placed L hw hn OwnEndpointEntryQ6.kernel5S OwnEndpointEntryQ6.kernel5S_support 765 765
     (logical 765 (by simp)) (by rfl) (kernel_free 765 (by simp))
 · exact placed L hw hn OwnEndpointEntryQ6.kernel5S OwnEndpointEntryQ6.kernel5S_support 767 767
     (logical 767 (by simp)) (by rfl) (kernel_free 767 (by simp))
 · exact placed L hw hn OwnEndpointEntryQ6.kernel5S OwnEndpointEntryQ6.kernel5S_support 1026 770
     (logical 1026 (by simp)) (by rfl) (kernel_free 1026 (by simp))
 · exact placed L hw hn OwnEndpointEntryQ6.kernel5S OwnEndpointEntryQ6.kernel5S_support 1541 1285
     (logical 1541 (by simp)) (by rfl) (kernel_free 1541 (by simp))
end ECDSAAdd.Entrant.EndpointEntryOmissions


-- ENDPOINT SUCCESSOR CountsE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.EndpointAll12Counts
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
attribute [local irreducible] toffoliCount measurementCount

theorem generic_diff (L : ControlledPointLayout) (D Dold : Fp→Program) (S P : Program)
 (delta : Nat) (hD : ∀k,toffoliCount (D k)+delta=toffoliCount (Dold k) ∧
   measurementCount (D k)=measurementCount (Dold k)) (cx cy : Fp) :
 toffoliCount (All12Generic.generic L D S P cx cy)+delta=
   toffoliCount (All12Generic.generic L Dold S P cx cy) ∧
 measurementCount (All12Generic.generic L D S P cx cy)=
   measurementCount (All12Generic.generic L Dold S P cx cy) := by
 have h:=hD (-cy)
 simp only [All12Generic.generic,toffoliCount_append,measurementCount_append]
 constructor <;> omega

theorem gen_diff (L : ControlledPointLayout) (D Dold : Fp→Program) (S P : Program)
 (delta : Nat) (hD : ∀k,toffoliCount (D k)+delta=toffoliCount (Dold k) ∧
   measurementCount (D k)=measurementCount (Dold k)) (cx cy : Fp) :
 toffoliCount (All12Generic.gen L D S P cx cy)+delta=
   toffoliCount (All12Generic.gen L Dold S P cx cy) ∧
 measurementCount (All12Generic.gen L D S P cx cy)=
   measurementCount (All12Generic.gen L Dold S P cx cy) := by
 have h:=generic_diff L D Dold S P delta hD cx cy
 simp only [All12Generic.gen,All12Generic.mid,toffoliCount_append,measurementCount_append,
   renameProgram_counts]
 constructor <;> omega
end ECDSAAdd.Entrant.EndpointAll12Counts


-- ENDPOINT SUCCESSOR NormalParentCounts.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.EndpointNormalParent
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
attribute [local irreducible] toffoliCount measurementCount
-- The isolated endpoint foundation already has the optimization; make the
-- normal-half count premise explicit, and close it in the final MainBasis.
theorem division_counts (oldNormal : toffoliCount OwnEntryFuseQ5.kernel5=1049158 ∧
 measurementCount OwnEntryFuseQ5.kernel5=720767)
 (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 toffoliCount (OwnEntryFuseQ6.fusedDivisionF L k)=1048904 ∧
 measurementCount (OwnEntryFuseQ6.fusedDivisionF L k)=721534 := by
 have eq:=OwnEntryFuseQ6.kernel5_counts_eq
 have tc:=OwnEntryFuseQ6.selKernel5.tc
 have mc:=OwnEntryFuseQ6.selKernel5.mc
 have fy:=EntryFuse.fusedY_counts L hw k
 have renameCounts:=renameProgram_counts (wireFn2 L) OwnEntryFuseQ6.kernel5S
 simp only [OwnEntryFuseQ6.fusedDivisionF,OwnEntryFuseQ6.arithEntryS,
   toffoliCount_append,measurementCount_append,renameCounts.1,renameCounts.2]
 constructor <;> omega
end ECDSAAdd.Entrant.EndpointNormalParent


-- ENDPOINT SUCCESSOR EntryPropertiesE.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
namespace ECDSAAdd.Entrant.EndpointEntryProperties
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
 CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run toffoliCount measurementCount
theorem division_support (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
    wires (OwnEndpointEntryQ6.fusedDivisionF L k)⊆(OB5Support.sites L).toFinset := by
  simp only [OwnEndpointEntryQ6.fusedDivisionF,wires_append,Finset.union_subset_iff]
  exact ⟨(fusedY_support L hw k).trans (finConst_sites L hw L.point.y (Or.inr rfl)),
    OwnEndpointEntryQ6.arithEntryS_support L hw⟩

theorem division_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (k : Fp) :
    GatePhysical (OwnEndpointEntryQ6.fusedDivisionF L k) := by
  simp only [OwnEndpointEntryQ6.fusedDivisionF,gatePhysical_append]
  exact ⟨fusedY_physical L hw hn k,OwnEndpointEntryQ6.arithEntryS_physical L hw hn⟩

theorem division_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat)
    (hk : k∈[1800,766,765,767,770,1285]) (c : Fp) :
    L.core.poolWire k∉wires (OwnEndpointEntryQ6.fusedDivisionF L c) := by
  have bounds : 515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have old := ExitGenericQ5.constant_ports_avoid_large L hw hn k bounds L.point.y (Or.inr rfl)
  simp only [OwnEndpointEntryQ6.fusedDivisionF,wires_append,Finset.mem_union,not_or]
  exact ⟨fun h=>old (fusedY_support L hw c h),EndpointEntryOmissions.entry_avoids L hw hn k hk⟩


theorem division_slots (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 gateSlots (OwnEndpointEntryQ6.fusedDivisionF L k)≤20525006 := by
 have d:=OwnEndpointEntryQ6.arithEntryS_gateSlots_le L
 have y:=entry_gateSlots_le (L.recoveryConstant L.point.y) L.core.generic
    EntryFuseArithmetic.complement k.val (L.recoveryConstant_widths hw L.point.y hw.inputY)
 simp only [OwnEndpointEntryQ6.fusedDivisionF,EntryFuse.fusedY,gateSlots_append]
 omega

theorem division_counts_diff (Dold : Program)
 (oldCounts : toffoliCount Dold=1048904 ∧ measurementCount Dold=721534)
 (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 toffoliCount (OwnEndpointEntryQ6.fusedDivisionF L k)+254=toffoliCount Dold ∧
 measurementCount (OwnEndpointEntryQ6.fusedDivisionF L k)=measurementCount Dold := by
 have a:=OwnEndpointEntryQ6.fusedDivisionF_counts L hw k
 constructor <;> omega
end ECDSAAdd.Entrant.EndpointEntryProperties


-- ENDPOINT SUCCESSOR ActualE.lean
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OwnEndpointActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run fastConstAdd fastConstNeg fastConstRefl ExitFusionResearch.exitY

def genericE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.generic L (OwnEndpointEntryQ6.fusedDivisionF L) (OwnAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy

def genE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.gen L (OwnEndpointEntryQ6.fusedDivisionF L) (OwnAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy



theorem square_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (OwnAll12PlacedQ6.program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1 : Nat) else 0)) Y G origin) := by
  have h:=OwnAll12PlacedQ6.correct L hw hn X Y G origin
  cases G <;> simpa only [OwnAll12Square.cFlipK,Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h

private theorem actual_division_diff (L : ControlledPointLayout) (hw : L.Widths) (k : Fp) :
 toffoliCount (OwnEndpointEntryQ6.fusedDivisionF L k)+254=
   toffoliCount (OwnEntryFuseQ6.fusedDivisionF L k) ∧
 measurementCount (OwnEndpointEntryQ6.fusedDivisionF L k)=
   measurementCount (OwnEntryFuseQ6.fusedDivisionF L k) :=
 EndpointEntryProperties.division_counts_diff _
   (EndpointNormalParent.division_counts OwnEntryFuseQ5.kernel5_counts L hw k) L hw k

theorem genericE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
 toffoliCount (genericE L cx cy)+510=toffoliCount (OwnQ6Producer.genericE L cx cy) ∧
 measurementCount (genericE L cx cy)+255=measurementCount (OwnQ6Producer.genericE L cx cy) := by
 have a:=EndpointAll12Counts.generic_diff L (OwnEndpointEntryQ6.fusedDivisionF L)
   (OwnEntryFuseQ6.fusedDivisionF L) (OwnAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L)
   254 (actual_division_diff L hw) cx cy
 have b:=OwnAll12Producer.genericE_counts_diff L hw cx cy
 change toffoliCount (genericE L cx cy)+254=toffoliCount (OwnAll12Producer.genericE L cx cy) ∧
   measurementCount (genericE L cx cy)=measurementCount (OwnAll12Producer.genericE L cx cy) at a
 constructor <;> omega

theorem genE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
 toffoliCount (genE L cx cy)+510=toffoliCount (OwnQ6Producer.genE L cx cy) ∧
 measurementCount (genE L cx cy)+255=measurementCount (OwnQ6Producer.genE L cx cy) := by
 have a:=EndpointAll12Counts.gen_diff L (OwnEndpointEntryQ6.fusedDivisionF L)
   (OwnEntryFuseQ6.fusedDivisionF L) (OwnAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L)
   254 (actual_division_diff L hw) cx cy
 have b:=OwnAll12Producer.genE_counts_diff L hw cx cy
 change toffoliCount (genE L cx cy)+254=toffoliCount (OwnAll12Producer.genE L cx cy) ∧
   measurementCount (genE L cx cy)=measurementCount (OwnAll12Producer.genE L cx cy) at a
 constructor <;> omega

theorem genE_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (genE L cx cy)≤49200000 :=
  All12Generic.gen_slots_le L hw _ _ _ (EndpointEntryProperties.division_slots L hw)
    (OwnAll12PlacedQ6.slots L hw) ((OwnExitFuseQ6.arithExit_slots_le L).trans (by decide)) cx cy


theorem genericE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genericE L cx cy)⊆(OB5Support.sites L).toFinset :=
  All12Generic.generic_sites L hw _ _ _ (EndpointEntryProperties.division_support L hw)
    (OwnAll12PlacedQ6.support L hw hn) (OwnExitFuseQ6.arithExit_support L hw) cx cy

theorem genE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genE L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [genE,All12Generic.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (genericE_sites L hw hn cx cy)

theorem genE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (genE L cx cy) :=
  All12Generic.gen_physical L hw hn _ _ _ (EndpointEntryProperties.division_physical L hw hn)
    (OwnAll12PlacedQ6.physical L hw hn) (OwnExitFuseQ6.arithExit_physical L hw hn) cx cy


theorem genericE_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) (cx cy : Fp) :
    L.core.poolWire k∉wires (genericE L cx cy) := by
  have bounds:515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  exact All12Generic.generic_free L hw hn _ _ _ k bounds
    (EndpointEntryProperties.division_free L hw hn k hk)
    (OwnAll12PlacedQ6.square_free L hw hn k hk)
    (Q6FusionOmissions.exit_avoids L hw hn exitFree k hk) cx cy

theorem genE_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base)) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (genE L cx cy) :=
  All12Generic.genFFused_ok L hw hn _ _ _
    (OwnExitFuseQ6.arithExit_correct exitFree L hw hn)
    (OwnEndpointEntryQ6.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
    (square_step L hw hn) hc
end ECDSAAdd.Entrant.OwnEndpointActual


-- ENDPOINT SUCCESSOR ActualInventoryE.lean
namespace ECDSAAdd.Entrant.OwnEndpointActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

theorem genE_qubits1593
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS) (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (genE layout cx cy))≤1593 := by
  rw [genE,All12Generic.gen_shape]
  apply GenericQ6Geometry.edges_wrapG_qubits _ (genericE_sites layout layout_widths layout_nodup cx cy)
  · intro k hk
    exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with h|h|h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) cx cy
  · exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree 1285 (by simp) cx cy
end ECDSAAdd.Entrant.OwnEndpointActual
