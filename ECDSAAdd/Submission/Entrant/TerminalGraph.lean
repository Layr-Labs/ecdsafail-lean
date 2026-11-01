import ECDSAAdd.Submission.Entrant.MainA

/-! Terminal graph decoder for the divide endpoint, from ArthurOstapenko's submission baaabf50
(`TerminalGraph.lean` of commit ab9dd95), sections GraphCell … EndpointCaller, TerminalSupportOnly,
TerminalFootprint and TerminalPhysicalOnly copied unchanged. -/

-- TERMINAL GRAPH COMPONENT GraphCell
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def xorSum (a b cin out : Wire) : Program := [.CX a out,.CX b out,.CX cin out]

theorem xorSum_run (a b cin out : Wire) (ha : a≠out) (hb : b≠out) (hc : cin≠out)
    (s : State) (m : List Bool) :
    run (xorSum a b cin out) m s =
      ⟨s.phase,writeBit s.basis out (s.basis out ^^ sumBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
  simp only [xorSum,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq:q=out
  · subst q
    simp [writeBit,Function.update,ha,hb,hc,sumBit,Bool.xor_assoc]
  · simp [writeBit,Function.update,hq]

/-- Decode a supplied sum bit into a clean carry wire using only CNOTs. -/
theorem extractCarry_run (a b out carry : Wire)
    (ha : a≠carry) (hb : b≠carry) (ho : out≠carry)
    (s : State) (m : List Bool) (clean : s.basis carry=false) (C : Bool)
    (sum : s.basis out=sumBit (s.basis a) (s.basis b) C) :
    run (xorSum a b out carry) m s=⟨s.phase,writeBit s.basis carry C⟩ := by
  rw [xorSum_run a b out carry ha hb ho,clean,sum]
  congr 2
  cases s.basis a <;> cases s.basis b <;> cases C <;> rfl

def eraseGraphCell (a b cin out carry : Wire) : Program :=
  xorSum a b cin out ++ eraseCarry a b cin carry

/-- A supplied sum/majority graph is erased with zero T, for every measurement tape. -/
theorem eraseGraphCell_run (a b cin out carry : Wire)
    (ha : a≠out) (hb : b≠out) (hc : cin≠out)
    (hak : a≠carry) (hbk : b≠carry) (hck : cin≠carry)
    (hok : out≠carry) (s : State) (m : List Bool)
    (sum : s.basis out=sumBit (s.basis a) (s.basis b) (s.basis cin))
    (maj : s.basis carry=carryBit (s.basis a) (s.basis b) (s.basis cin)) :
    run (eraseGraphCell a b cin out carry) m s=
      ⟨s.phase,writeBit (writeBit s.basis out false) carry false⟩ := by
  have x : run (xorSum a b cin out) m s=⟨s.phase,writeBit s.basis out false⟩ := by
    rw [xorSum_run a b cin out ha hb hc,sum]
    simp
  let t : State:=⟨s.phase,writeBit s.basis out false⟩
  have tm : t.basis carry=carryBit (t.basis a) (t.basis b) (t.basis cin) := by
    simpa only [t,writeBit,Function.update_of_ne ha,Function.update_of_ne hb,
      Function.update_of_ne hc,Function.update_of_ne hok.symm] using maj
  rw [eraseGraphCell,run_append,run_take,x]
  simpa only [t] using eraseCarry_correct a b cin carry hak hbk hck t tm
    (m.drop (measurementCount (xorSum a b cin out)))

theorem graphCell_resources (a b cin out carry : Wire) :
    toffoliCount (eraseGraphCell a b cin out carry)=0 ∧
    measurementCount (eraseGraphCell a b cin out carry)=1 := by
  simp [eraseGraphCell,xorSum,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,eraseCarry]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AffineStream
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def parity (xs : List Wire) (b : BasisState) : Bool:=xs.foldr (fun x t=>b x ^^ t) false
def xorList (xs : List Wire) (target : Wire) : Program:=xs.map (fun x=>.CX x target)

theorem parity_congr (xs : List Wire) (b b' : BasisState) (h : ∀q∈xs,b q=b' q) :
    parity xs b=parity xs b' := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change (b x ^^ parity xs b)=(b' x ^^ parity xs b')
    rw [h x (by simp),ih (fun q hq=>h q (by simp [hq]))]

theorem xorList_run (xs : List Wire) (target : Wire) (away : target∉xs)
    (s : State) (m : List Bool) :
    run (xorList xs target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^ parity xs s.basis)⟩ := by
  induction xs generalizing s with
  | nil=>
    simp only [xorList,List.map_nil,run,parity,List.foldr_nil,Bool.xor_false]
    cases s with
    | mk phase basis =>
      apply congrArg (State.mk phase)
      funext q
      by_cases hq:q=target <;> simp [writeBit,hq]
  | cons x xs ih=>
    have xt:x≠target:=fun e=>away (by simp [e])
    have tail:target∉xs:=fun h=>away (by simp [h])
    let t : State:=⟨s.phase,writeBit s.basis target (s.basis target ^^ s.basis x)⟩
    have pa:parity xs t.basis=parity xs s.basis:=parity_congr _ _ _ (by
      intro q hq
      have nq:q≠target:=fun e=>tail (e ▸ hq)
      simp [t,writeBit,nq])
    simp only [xorList,List.map_cons,run]
    change run (xorList xs target) m t=_
    rw [ih tail t,pa]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq:q=target
    · subst q
      simp [t,writeBit,parity,Bool.xor_assoc]
    · simp [t,writeBit,hq]

/-- Move a supplied output into a consumed clean target slot, removing its affine sum.
The full state map is Clifford and holds without any arithmetic-graph premise. -/
def streamStage (xs : List Wire) (prev out : Wire) : Program:=
  [.CX out prev]++xorList xs prev++xorList xs out++[.CX prev out]

theorem streamStage_run (xs : List Wire) (prev out : Wire)
    (ne : prev≠out) (ap : prev∉xs) (ao : out∉xs)
    (s : State) (m : List Bool) (clean : s.basis prev=false) :
    run (streamStage xs prev out) m s=
      ⟨s.phase,writeBit (writeBit s.basis prev (s.basis out ^^ parity xs s.basis)) out false⟩ := by
  let t : State:=⟨s.phase,writeBit s.basis prev (s.basis out)⟩
  have first (r : List Bool) : run [.CX out prev] r s=t:=by simp [run,t,writeBit,clean]
  have par1:parity xs t.basis=parity xs s.basis:=parity_congr _ _ _ (by
    intro q hq;have nq:q≠prev:=fun e=>ap (e ▸ hq);simp [t,writeBit,nq])
  let u : State:=⟨s.phase,writeBit t.basis prev (s.basis out ^^ parity xs s.basis)⟩
  have second (r : List Bool) : run (xorList xs prev) r t=u:=by
    rw [xorList_run xs prev ap,par1]
    simp [u,t,writeBit]
  have par2:parity xs u.basis=parity xs s.basis:=parity_congr _ _ _ (by
    intro q hq;have nq:q≠prev:=fun e=>ap (e ▸ hq);simp [u,t,writeBit,nq])
  let v : State:=⟨s.phase,writeBit u.basis out (s.basis out ^^ parity xs s.basis)⟩
  have third (r : List Bool) : run (xorList xs out) r u=v:=by
    rw [xorList_run xs out ao,par2]
    simp [v,u,t,writeBit,Ne.symm ne]
  have final:run [.CX prev out] m v=
      ⟨s.phase,writeBit (writeBit s.basis prev (s.basis out ^^ parity xs s.basis)) out false⟩ := by
    simp only [run]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hp:q=prev
    · subst q;simp [v,u,t,writeBit,ne]
    · by_cases ho:q=out
      · subst q;simp [v,u,t,writeBit,ne,Ne.symm ne]
      · simp [v,u,t,writeBit,hp,ho]
  have zero (xs : List Wire) (target : Wire) : measurementCount (xorList xs target)=0:=by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simpa only [xorList,List.map_cons,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih
  rw [streamStage]
  simp only [List.append_assoc,run_append,run_take,measurementCount,List.sum_cons,
    List.sum_nil,Nat.zero_add,List.take_zero,List.drop_zero,zero]
  rw [first,second,third]
  exact final
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT ControlledCompare
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def selectedBorrow (bit : Bool) (x cin carry control target : Wire) : Program :=
  constantBorrow bit x cin carry ++ [.CCX control carry target] ++ constantBorrowErase bit x cin carry

theorem selectedBorrow_counts (bit : Bool) (x cin carry control target : Wire) :
    toffoliCount (selectedBorrow bit x cin carry control target)=2 ∧
    measurementCount (selectedBorrow bit x cin carry control target)=1 := by
  have c:=constantBorrow_counts bit x cin carry
  simp only [selectedBorrow,toffoliCount_append,measurementCount_append,c.1,c.2.1,c.2.2.1,c.2.2.2]
  simp [toffoliCount,measurementCount]

def compareSelected : List Wire → List Wire → Wire → Wire → Wire → Nat → Program
  | x::x'::xs,c::cs,cin,control,target,k =>
      constantBorrow (decide (k%2=1)) x cin c ++
        compareSelected (x'::xs) cs c control target (k/2) ++
          constantBorrowErase (decide (k%2=1)) x cin c
  | [x],c::_,cin,control,target,k => selectedBorrow (decide (k%2=1)) x cin c control target
  | _,_,_,_,_,_ => []

theorem compareSelected_counts (xs carry : List Wire) (cin control target : Wire) (k : Nat)
    (hn : 0<xs.length) (hc : carry.length=xs.length) :
    toffoliCount (compareSelected xs carry cin control target k)=xs.length+1 ∧
    measurementCount (compareSelected xs carry cin control target k)=xs.length := by
  induction xs generalizing carry cin k with
  | nil => simp at hn
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases carry with
      | nil => simp at hc
      | cons c cs => simpa only [compareSelected,List.length_cons,List.length_nil] using selectedBorrow_counts (decide (k%2=1)) x cin c control target
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have r:=ih cs c (k/2) (by simp) (by simpa using hc)
        have b:=constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareSelected]
        constructor
        · simp only [toffoliCount_append,b.1,b.2.2.1,r.1,List.length_cons];omega
        · simp only [measurementCount_append,b.2.1,b.2.2.2,r.2,List.length_cons];omega

theorem selectedBorrow_correct (bit : Bool) (x cin carry control target : Wire)
    (hn : [x,cin,carry,control,target].Nodup) (s : State) (m : List Bool)
    (zero : s.basis carry=false) :
    run (selectedBorrow bit x cin carry control target) m s=
      ⟨s.phase,writeBit (writeBit s.basis target
        (s.basis target ^^ (s.basis control && carryBit (!s.basis x) bit (s.basis cin)))) carry false⟩ := by
  have nd : [x,cin,carry].Nodup:=hn.sublist (by simp)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at hn
  obtain ⟨⟨hxi,hxc,hxb,hxt⟩,⟨hic,hib,hit⟩,⟨hcb,hct⟩,hbt⟩:=hn
  let K:=carryBit (!s.basis x) bit (s.basis cin)
  let s1 : State:=⟨s.phase,writeBit s.basis carry K⟩
  have first (r : List Bool) : run (constantBorrow bit x cin carry) r s=s1 := by
    rw [constantBorrow_correct bit x cin carry nd,zero]
    simp [s1,K]
  let s2 : State:=⟨s.phase,writeBit s1.basis target (s.basis target ^^ (s.basis control && K))⟩
  have second (r : List Bool) : run [.CCX control carry target] r s1=s2 := by
    simp [s1,s2,run,writeBit,(Ne.symm hct),(Ne.symm hcb)]
  have final (r : List Bool) : run (constantBorrowErase bit x cin carry) r s2=
      ⟨s.phase,writeBit s2.basis carry false⟩ := by
    have km : s2.basis carry=carryBit (!s2.basis x) bit (s2.basis cin) := by
      simp [s2,s1,writeBit,hct,hxt,hit,hxc,hic,K]
    exact constantBorrowErase_correct bit x cin carry nd s2 r km
  have counts:=constantBorrow_counts bit x cin carry
  rw [selectedBorrow]
  simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
  rw [first,second,final]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq:q=carry
  · subst q;simp [s1,s2,writeBit]
  · by_cases ht:q=target
    · subst q;simp [s1,s2,writeBit,(Ne.symm hct),K]
    · simp [s1,s2,writeBit,hq,ht]

theorem compareSelected_correct (xs carry : List Wire) (cin control target : Wire) (k : Nat)
    (hn : (control::target::cin::(xs++carry)).Nodup) (hpos : 0<xs.length)
    (hc : carry.length=xs.length) (hk : k<2^xs.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    (run (compareSelected xs carry cin control target k) m s).phase=s.phase ∧
    (∀q,q≠target → (run (compareSelected xs carry cin control target k) m s).basis q=s.basis q) ∧
    (run (compareSelected xs carry cin control target k) m s).basis target=
      (s.basis target ^^ (s.basis control && decide (regValue xs s.basis<k+(s.basis cin).toNat))) := by
  induction xs generalizing carry cin k s m with
  | nil => simp at hpos
  | cons x xs ih =>
    have cnt:=List.nodup_iff_count.mp hn
    have htx : target≠x := by
      intro bad;have h:=cnt target;subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have htci : target≠cin := by
      intro bad;have h:=cnt target;subst cin
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    have hxc : x≠cin := by
      intro bad;have h:=cnt cin;subst x
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
    cases xs with
    | nil =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have nd : [x,cin,c,control,target].Nodup := by
          apply List.nodup_iff_count.mpr;intro q;have h:=cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have htc : target≠c := by
          intro bad;have h:=cnt target;subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have zero:=hclean c (by simp)
        rw [compareSelected,selectedBorrow_correct _ _ _ _ _ _ nd s m zero]
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          by_cases hqc:q=c
          · subst q;simp [writeBit,zero]
          · simp [writeBit,hqc,hq]
        · have small : k<2 := by simpa using hk
          by_cases h0:k=0
          · subst k
            cases hx:s.basis x <;> cases hi:s.basis cin <;> cases hb:s.basis control <;>
              simp [writeBit,htc,regValue,carryBit,hx,hi,hb]
          · have h1:k=1:=by omega
            subst k
            cases hx:s.basis x <;> cases hi:s.basis cin <;> cases hb:s.basis control <;>
              simp [writeBit,htc,regValue,carryBit,hx,hi,hb]
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have htc : target≠c := by
          intro bad; have h := cnt target; subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hbc : control≠c := by
          intro bad; have h:=cnt control;subst c
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hxc' : x≠c := by
          intro bad; have h := cnt c; subst x
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hcic : cin≠c := by
          intro bad; have h := cnt c; subst cin
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have hctail : c∉x'::xs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h pos
          omega
        have hccs : c∉cs := by
          intro bad; have h := cnt c; have pos := List.count_pos_iff.mpr bad
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have nd' : (control::target::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr; intro q; have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        let bit := decide (k%2=1)
        let K := carryBit (!s.basis x) bit (s.basis cin)
        let s1 : State := ⟨s.phase,writeBit s.basis c K⟩
        have keep (q : Wire) (hq : q≠c) : s1.basis q=s.basis q := by simp [s1,writeBit,hq]
        have zero := hclean c (by simp)
        have first (record : List Bool) : run (constantBorrow bit x cin c) record s=s1 := by
          rw [constantBorrow_correct _ _ _ _ nd]
          simp [s1,K,zero]
        have clean' : ∀q∈cs,s1.basis q=false := by
          intro q hq
          rw [keep q (fun bad => hccs (bad ▸ hq))]
          exact hclean q (by simp [hq])
        have high : k/2<2^(x'::xs).length := by
          simp only [List.length_cons,Nat.pow_succ] at hk ⊢
          omega
        obtain ⟨hp,he,hv⟩ := ih cs c (k/2) nd' (by simp) (by simpa using hc) high s1 m clean'
        let t := run (compareSelected (x'::xs) cs c control target (k/2)) m s1
        have tx : t.basis x=s.basis x := (he x htx.symm).trans (keep x hxc')
        have ti : t.basis cin=s.basis cin := (he cin htci.symm).trans (keep cin hcic)
        have tk : t.basis c=K := by rw [he c htc.symm]; simp [s1,writeBit]
        have clear (record : List Bool) : run (constantBorrowErase bit x cin c) record t=
            ⟨t.phase,writeBit t.basis c false⟩ := by
          apply constantBorrowErase_correct _ _ _ _ nd t record
          rw [tx,ti,tk]
        have counts := constantBorrow_counts (decide (k%2=1)) x cin c
        rw [compareSelected]
        simp only [List.append_assoc,run_append,run_take,counts.2.1,List.take_zero,List.drop_zero]
        rw [first]
        change (run (constantBorrowErase bit x cin c) _ t).phase=_ ∧ _
        rw [clear]
        refine ⟨hp,?_,?_⟩
        · intro q hq
          by_cases hqc : q=c
          · subst q; simp [writeBit,zero]
          · simp only [writeBit,Function.update_of_ne hqc]
            exact (he q hq).trans (keep q hqc)
        · simp only [writeBit,Function.update_of_ne htc]
          rw [hv,keep target htc,keep control hbc]
          have v : regValue (x'::xs) s1.basis=regValue (x'::xs) s.basis :=
            regValue_congr _ _ _ (fun q hq => keep q (fun bad => hctail (bad ▸ hq)))
          have carryVal : s1.basis c=K := by simp [s1,writeBit]
          rw [v,carryVal]
          have split : bit.toNat+2*(k/2)=k := by
            have e := Nat.mod_add_div k 2
            have b := Nat.mod_lt k (by decide : 0<2)
            by_cases odd : k%2=1 <;> simp [bit,odd] <;> omega
          have thr := borrow_threshold (s.basis x) bit (s.basis cin)
            (regValue (x'::xs) s.basis) (k/2)
          rw [split] at thr
          have pred : decide (regValue (x::x'::xs) s.basis<k+(s.basis cin).toNat)=
              decide (regValue (x'::xs) s.basis<k/2+K.toNat) := by
            apply decide_eq_decide.mpr
            simpa only [regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,K] using thr
          rw [pred]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Emitter
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

structure DecoderLayout where
  y : List Wire
  r : List Wire
  carry : List Wire
  sigma : Wire
  h : Wire
  bias : Wire

def DecoderLayout.Widths (L : DecoderLayout) : Prop:=L.y.length=256 ∧ L.r.length=256 ∧ L.carry.length=255

def DecoderLayout.Y (L : DecoderLayout) (i : Nat):Wire:=L.y.getD i 0
def DecoderLayout.R (L : DecoderLayout) (i : Nat):Wire:=L.r.getD i 0
def DecoderLayout.A (L : DecoderLayout) (i : Nat):Wire:=L.carry.getD i 0

def rawSources (L : DecoderLayout) (i : Nat) : List Wire:=
 if i=0 then [L.Y 0]
 else if i<255 then [L.Y (i-1),L.Y i,L.sigma,L.A (i-1)]
 else [L.Y 254,L.sigma,L.A 254]

def correction (L : DecoderLayout) (i : Nat) : MappedBit:=
 if i=1 then ⟨some L.bias,false⟩
 else if Nat.testBit (2^32+977) i then ⟨some L.h,false⟩ else ⟨none,false⟩

def correctionSources (L : DecoderLayout) (i : Nat) : List Wire:=
 (correction L i).wire.toList

def addCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=0 then [.CX L.sigma (L.Y 0),.CCX L.sigma (L.Y 0) (L.A 0),.CX L.sigma (L.Y 0)]
 else [.CX L.sigma (L.Y i)]++majority (L.Y (i-1)) (L.Y i) (L.A (i-1)) (L.A i)++[.CX L.sigma (L.Y i)]

def eraseAddCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=0 then [.CX L.sigma (L.Y 0),.measureX (L.A 0) [] [.CZ L.sigma (L.Y 0)],.CX L.sigma (L.Y 0)]
 else [.CX L.sigma (L.Y i)]++eraseCarry (L.Y (i-1)) (L.Y i) (L.A (i-1)) (L.A i)++[.CX L.sigma (L.Y i)]

def streamCarry (L : DecoderLayout) (i : Nat) : Program:=
 streamStage (rawSources L i++correctionSources L i) (L.R (i-1)) (L.R i)

def eraseCorrectionCarry (L : DecoderLayout) (i : Nat) : Program:=
 if i=1 then [.measureX (L.R 0) [] [.CZ (L.Y 0) L.h]]
 else xorList (rawSources L (i-1)) (L.R 255)++
   mappedEraseCarry (correction L (i-1)) (L.R 255) (L.R (i-2)) (L.R (i-1))++
     xorList (rawSources L (i-1)) (L.R 255)

def biasCompute (L : DecoderLayout) : Program:=
 [.X L.sigma,.CCX (L.Y 255) L.sigma L.bias,.X L.sigma]
def biasErase (L : DecoderLayout) : Program:=
 [.X L.sigma,.measureX L.bias [] [.CZ (L.Y 255) L.sigma],.X L.sigma]

def normalize (L : DecoderLayout) : Program:=
 (L.y.take 255).map (fun q=>.CX (L.Y 255) q)++L.r.map (fun q=>.CX (L.Y 255) q)
def restoreSource (L : DecoderLayout) : Program:=(L.y.take 255).map (fun q=>.CX (L.Y 255) q)
def copySource (L : DecoderLayout) : Program:=(L.y.zip L.r).map (fun q=>.CX q.1 q.2)

def clearQuotient (L : DecoderLayout) : Program:=
 [.X (L.Y 255),.X L.sigma]++
   compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h (((ECDSAAdd.p-1)/2)/3)++
     [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)]

def decoder (L : DecoderLayout) : Program:=
 normalize L++[.CX (L.R 0) L.h,.CX (L.Y 0) L.h]++biasCompute L++
 (List.range 255).flatMap (addCarry L)++
 xorList (rawSources L 0++correctionSources L 0) (L.R 0)++
 (List.range' 1 255).flatMap (streamCarry L)++
 (List.range' 1 255).reverse.flatMap (eraseCorrectionCarry L)++
 (List.range 255).reverse.flatMap (eraseAddCarry L)++
 biasErase L++clearQuotient L++restoreSource L++copySource L

theorem xorList_counts (xs : List Wire) (target : Wire) :
 toffoliCount (xorList xs target)=0 ∧ measurementCount (xorList xs target)=0 := by
 induction xs with
 | nil=>exact ⟨rfl,rfl⟩
 | cons x xs ih=>simpa only [xorList,List.map_cons,toffoliCount,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih

theorem streamStage_counts (xs : List Wire) (prev out : Wire) :
 toffoliCount (streamStage xs prev out)=0 ∧ measurementCount (streamStage xs prev out)=0 := by
 have p:=xorList_counts xs prev;have q:=xorList_counts xs out
 simp [streamStage,toffoliCount_append,measurementCount_append,p.1,p.2,q.1,q.2,toffoliCount,measurementCount]

theorem local_counts (L : DecoderLayout) (i : Nat) :
 (toffoliCount (addCarry L i)=1 ∧ measurementCount (addCarry L i)=0) ∧
 (toffoliCount (eraseAddCarry L i)=0 ∧ measurementCount (eraseAddCarry L i)=1) ∧
 (toffoliCount (streamCarry L i)=0 ∧ measurementCount (streamCarry L i)=0) ∧
 (toffoliCount (eraseCorrectionCarry L i)=0 ∧ measurementCount (eraseCorrectionCarry L i)=1) := by
 have st:=streamStage_counts (rawSources L i++correctionSources L i) (L.R (i-1)) (L.R i)
 have x:=xorList_counts (rawSources L (i-1)) (L.R 255)
 have m:=mappedBit_counts (correction L (i-1)) (L.R 255) (L.R (i-2)) (L.R (i-1))
 constructor
 · by_cases h:i=0 <;> simp [addCarry,h,majority,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
 constructor
 · by_cases h:i=0 <;> simp [eraseAddCarry,h,eraseCarry,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
 constructor
 · exact st
 · by_cases h:i=1
   · simp [eraseCorrectionCarry,h,toffoliCount,measurementCount]
   · simp only [eraseCorrectionCarry,h,ite_false,toffoliCount_append,measurementCount_append,x.1,x.2,m.2.2.1,m.2.2.2.1]
     simp
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Counts
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem flat_counts {α : Type} (xs : List α) (f : α→Program) (T M : Nat)
    (h : ∀i∈xs,toffoliCount (f i)=T ∧ measurementCount (f i)=M) :
    toffoliCount (xs.flatMap f)=T*xs.length ∧ measurementCount (xs.flatMap f)=M*xs.length := by
 induction xs with
 | nil=>simp [toffoliCount,measurementCount]
 | cons x xs ih=>
   have a:=h x (by simp)
   have b:=ih (fun i hi=>h i (by simp [hi]))
   simp only [List.flatMap_cons,toffoliCount_append,measurementCount_append,List.length_cons,a.1,a.2,b.1,b.2,Nat.mul_succ]
   constructor <;> omega

theorem cxMap_counts {α : Type} (xs : List α) (f g : α→Wire) :
    toffoliCount (xs.map (fun x=>Instr.CX (f x) (g x)))=0 ∧
    measurementCount (xs.map (fun x=>Instr.CX (f x) (g x)))=0 := by
 induction xs with
 | nil=>exact ⟨rfl,rfl⟩
 | cons x xs ih=>simpa only [List.map_cons,toffoliCount,measurementCount,List.map_cons,List.sum_cons,Nat.zero_add] using ih

theorem simple_counts (L : DecoderLayout) :
 (toffoliCount (normalize L)=0 ∧ measurementCount (normalize L)=0) ∧
 (toffoliCount (restoreSource L)=0 ∧ measurementCount (restoreSource L)=0) ∧
 (toffoliCount (copySource L)=0 ∧ measurementCount (copySource L)=0) ∧
 (toffoliCount (biasCompute L)=1 ∧ measurementCount (biasCompute L)=0) ∧
 (toffoliCount (biasErase L)=0 ∧ measurementCount (biasErase L)=1) := by
 have a:=cxMap_counts (L.y.take 255) (fun _=>L.Y 255) id
 have b:=cxMap_counts L.r (fun _=>L.Y 255) id
 have c:=cxMap_counts (L.y.zip L.r) Prod.fst Prod.snd
 simp only [id_eq] at a b
 refine ⟨?_,?_,?_,?_,?_⟩
 · simp only [normalize,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,Nat.zero_add,and_self]
 · exact a
 · exact c
 · simp [biasCompute,toffoliCount,measurementCount]
 · simp [biasErase,toffoliCount,measurementCount]


theorem clearQuotient_counts (L : DecoderLayout) (hw : L.Widths) :
 toffoliCount (clearQuotient L)=256 ∧ measurementCount (clearQuotient L)=255 := by
 have yl : (L.y.take 255).length=255:=by simp [hw.1]
 have c:=compareSelected_counts (L.y.take 255) L.carry (L.Y 255) L.sigma L.h (((ECDSAAdd.p-1)/2)/3)
   (by omega) (by rw [hw.2.2,yl])
 simp only [clearQuotient,toffoliCount_append,measurementCount_append,c.1,c.2,yl]
 simp [toffoliCount,measurementCount]

theorem decoder_counts (L : DecoderLayout) (hw : L.Widths) :
 toffoliCount (decoder L)=512 ∧ measurementCount (decoder L)=766 := by
 have a:=flat_counts (List.range 255) (addCarry L) 1 0 (fun i _=>(local_counts L i).1)
 have b:=flat_counts (List.range' 1 255) (streamCarry L) 0 0 (fun i _=>(local_counts L i).2.2.1)
 have c:=flat_counts (List.range' 1 255).reverse (eraseCorrectionCarry L) 0 1 (fun i _=>(local_counts L i).2.2.2)
 have d:=flat_counts (List.range 255).reverse (eraseAddCarry L) 0 1 (fun i _=>(local_counts L i).2.1)
 have z:=xorList_counts (rawSources L 0++correctionSources L 0) (L.R 0)
 have e:=simple_counts L
 have q:=clearQuotient_counts L hw
 simp only [List.length_range,List.length_range',List.length_reverse,Nat.one_mul,Nat.zero_mul] at a b c d
 simp only [decoder,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,d.1,d.2,z.1,z.2,
   e.1.1,e.1.2,e.2.1.1,e.2.1.2,e.2.2.1.1,e.2.2.1.2,e.2.2.2.1.1,e.2.2.2.1.2,e.2.2.2.2.1,e.2.2.2.2.2,q.1,q.2]
 simp [toffoliCount,measurementCount]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CarryWindow
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def cxWindow (sigma x : Wire) (P : Program) : Program := [.CX sigma x]++P++[.CX sigma x]
def cxBasis (sigma x : Wire) (b : BasisState) : BasisState :=writeBit b x (b x ^^ b sigma)

theorem cxWindow_write (sigma x target : Wire) (P : Program)
    (hsx : sigma≠x) (hst : sigma≠target) (hxt : x≠target)
    (s : State) (m : List Bool) (value : Bool)
    (middle : ∀r,run P r ⟨s.phase,cxBasis sigma x s.basis⟩=
      ⟨s.phase,writeBit (cxBasis sigma x s.basis) target value⟩) :
    run (cxWindow sigma x P) m s=⟨s.phase,writeBit s.basis target value⟩ := by
  have first (r : List Bool):run [.CX sigma x] r s=⟨s.phase,cxBasis sigma x s.basis⟩:=rfl
  rw [cxWindow]
  simp only [List.append_assoc,run_append,run_take,measurementCount,List.map_cons,List.sum_cons,List.sum_nil,Nat.zero_add,List.take_zero,List.drop_zero]
  rw [first,middle]
  simp only [run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hx:q=x
  · subst q;simp [cxBasis,writeBit,hsx,hst,hxt]
  · by_cases ht:q=target
    · subst q;simp [cxBasis,writeBit,hxt,Ne.symm hxt]
    · simp [cxBasis,writeBit,hx,ht]

theorem cxBasis_mapped (b : MappedBit) (sigma x : Wire) (basis : BasisState)
    (ha : ∀q∈b.wire,q≠x) : b.value (cxBasis sigma x basis)=b.value basis := by
 apply mappedBit_value_congr
 intro q hq
 simp [cxBasis,writeBit,ha q hq]

theorem windowMajority_run (b : MappedBit) (sigma x cin cout : Wire)
    (nd : [x,cin,cout].Nodup) (ha : ∀q∈b.wire,q∉[x,cin,cout])
    (hsx : sigma≠x) (hsc : sigma≠cout)
    (s : State) (m : List Bool) :
    run (cxWindow sigma x (mappedMajority b x cin cout)) m s=
      ⟨s.phase,writeBit s.basis cout (s.basis cout ^^
        carryBit (b.value s.basis) (s.basis x ^^ s.basis sigma) (s.basis cin))⟩ := by
 have xc:x≠cout:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 have ic:cin≠x:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 apply cxWindow_write sigma x cout _ hsx hsc xc
 intro r
 rw [mappedMajority_correct b x cin cout nd ha]
 have bm:=cxBasis_mapped b sigma x s.basis (by
   intro q hq hqx;exact ha q hq (by simp [hqx]))
 rw [bm]
 simp [cxBasis,writeBit,Ne.symm xc,ic]

theorem windowErase_run (b : MappedBit) (sigma x cin cout : Wire)
    (nd : [x,cin,cout].Nodup) (ha : ∀q∈b.wire,q∉[x,cin,cout])
    (hsx : sigma≠x) (hsc : sigma≠cout)
    (s : State) (m : List Bool)
    (known : s.basis cout=carryBit (b.value s.basis) (s.basis x ^^ s.basis sigma) (s.basis cin)) :
    run (cxWindow sigma x (mappedEraseCarry b x cin cout)) m s=
      ⟨s.phase,writeBit s.basis cout false⟩ := by
 have xc:x≠cout:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 have ic:cin≠x:=fun e=>(List.nodup_cons.mp nd).1 (by simp [e])
 apply cxWindow_write sigma x cout _ hsx hsc xc
 intro r
 apply mappedEraseCarry_correct b x cin cout nd ha
 have bm:=cxBasis_mapped b sigma x s.basis (by
   intro q hq hqx;exact ha q hq (by simp [hqx]))
 rw [bm]
 simpa [cxBasis,writeBit,Ne.symm xc,ic] using known
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT LayoutFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def DecoderLayout.wires (L : DecoderLayout) : List Wire:=
 [L.sigma,L.h,L.bias]++L.y++L.r++L.carry

def ofBalanced (L : BalancedCircuit.Layout) : DecoderLayout:=
 ⟨L.y,L.r,L.carry.take 254++[L.lower],L.sign,L.one,L.parity⟩

theorem ofBalanced_widths (L : BalancedCircuit.Layout) (hw : L.Widths) :
 (ofBalanced L).Widths := by
 have w:=BalancedCleanup.widths L.toLayout hw
 simp [ofBalanced,DecoderLayout.Widths,w.2.1,w.2.2.1,List.length_take,hw.2.2]

theorem ofBalanced_nodup (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
 (ofBalanced L).wires.Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 have take: (L.carry.take 254).count q≤L.carry.count q:=(List.take_sublist 254 L.carry).count_le q
 simp only [ofBalanced,DecoderLayout.wires,BalancedCircuit.Layout.wires,
  BalancedCleanup.Layout.wires,BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,
  BalancedCleanup.Layout.low,List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem getD_mem (xs : List Wire) (i : Nat) (hi : i<xs.length) : xs.getD i 0∈xs := by
 rw [List.getD_eq_getElem _ _ hi]
 exact List.getElem_mem hi

theorem getD_inj (xs : List Wire) (hn : xs.Nodup) (i j : Nat)
    (hi : i<xs.length) (hj : j<xs.length) (eq : xs.getD i 0=xs.getD j 0) : i=j := by
 apply List.getElem?_inj hi hn
 have x:=congrArg some eq
 simpa only [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj,
   List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using x

theorem register_nodup (L : DecoderLayout) (hn : L.wires.Nodup) :
 L.y.Nodup ∧ L.r.Nodup ∧ L.carry.Nodup := by
 unfold DecoderLayout.wires at hn
 have a:=List.nodup_append'.mp hn
 have b:=List.nodup_append'.mp a.1
 have c:=List.nodup_append'.mp b.1
 exact ⟨c.2.1,b.2.1,a.2.1⟩

theorem carry_source_away (L : DecoderLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.carry := by
 intro hc
 have h:=List.nodup_iff_count.mp hn q
 have pos:0<L.carry.count q:=List.count_pos_iff.mpr hc
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
 rcases hq with hy|rfl|rfl|rfl
 · have yy:=List.count_pos_iff.mpr hy;omega
 all_goals simp only [beq_self_eq_true,if_true] at h;omega

theorem carry_ne_carry (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i j : Nat) (hi : i<255) (hj : j<255) (ne : i≠j) : L.A i≠L.A j := by
 intro eq
 have len:=hw.2.2
 exact ne (getD_inj L.carry (register_nodup L hn).2.2 i j (by omega) (by omega) eq)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Geometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem y_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.Y i∈L.y :=
 getD_mem L.y i (by have h:=hw.1;omega)
theorem a_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<255) : L.A i∈L.carry :=
 getD_mem L.carry i (by have h:=hw.2.2;omega)
theorem r_mem (L : DecoderLayout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.R i∈L.r :=
 getD_mem L.r i (by have h:=hw.2.1;omega)

theorem y_ne_a (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<255) : L.Y i≠L.A j := by
 intro e
 exact carry_source_away L hn _ (Or.inl (y_mem L hw i hi)) (e ▸ a_mem L hw j hj)

theorem sigma_ne_a (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<255) : L.sigma≠L.A i := by
 intro e
 exact carry_source_away L hn _ (Or.inr (Or.inl rfl)) (e ▸ a_mem L hw i hi)

theorem sigma_ne_y (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) : L.sigma≠L.Y i := by
 intro eq
 have h:=List.nodup_iff_count.mp hn L.sigma
 have mem:=y_mem L hw i hi
 rw [←eq] at mem
 have pos:=List.count_pos_iff.mpr mem
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil,
  beq_self_eq_true,if_true] at h
 omega

theorem y_ne_y (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<256) (ne : i≠j) : L.Y i≠L.Y j := by
 intro eq
 have len:=hw.1
 exact ne (getD_inj L.y (register_nodup L hn).1 i j (by omega) (by omega) eq)

theorem source_r_away (L : DecoderLayout) (hn : L.wires.Nodup)
 (q : Wire) (hq : q∈L.y ∨ q∈L.carry ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.r := by
 intro hr
 have h:=List.nodup_iff_count.mp hn q
 have pos:=List.count_pos_iff.mpr hr
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
 rcases hq with hy|hc|rfl|rfl|rfl
 · have yy:=List.count_pos_iff.mpr hy;omega
 · have cc:=List.count_pos_iff.mpr hc;omega
 all_goals simp only [beq_self_eq_true,if_true] at h;omega

theorem raw_source_r_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (q : Wire) (hq : q∈rawSources L i) : q∉L.r := by
 apply source_r_away L hn q
 unfold rawSources at hq
 split_ifs at hq with h0 h255
 · have eq:q=L.Y 0:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hq
   subst q
   exact Or.inl (y_mem L hw 0 (by omega))
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl
   · exact Or.inl (y_mem L hw (i-1) (by omega))
   · exact Or.inl (y_mem L hw i hi)
   · exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inl (a_mem L hw (i-1) (by omega)))
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl
   · exact Or.inl (y_mem L hw 254 (by omega))
   · exact Or.inr (Or.inr (Or.inl rfl))
   · exact Or.inr (Or.inl (a_mem L hw 254 (by omega)))
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT QuotientClear
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run compareSelected

theorem state_ext (s t : State) (hp : s.phase=t.phase) (hb : ∀q,s.basis q=t.basis q) : s=t := by
 cases s
 cases t
 exact congrArg₂ State.mk hp (funext hb)

theorem y_split (L : DecoderLayout) (hw : L.Widths) :
 L.y=L.y.take 255++[L.Y 255] := by
 have len:=hw.1
 have split : L.y.take 255++[L.y.getD 255 0]=L.y.take 256 := by
   conv_rhs=>rw [show 256=255+1 from rfl,List.take_add_one]
   simp only [List.getD_eq_getElem _ _ (by omega : 255<L.y.length)]
   simp [List.getElem?_eq_getElem (by omega : 255<L.y.length)]
 simpa only [DecoderLayout.Y,List.take_of_length_le (by omega : L.y.length≤256)] using split.symm

theorem compare_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (L.sigma::L.h::L.Y 255::(L.y.take 255++L.carry)).Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 unfold DecoderLayout.wires at h
 rw [y_split L hw] at h
 simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem clearQuotient_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) (clean : ∀q∈L.carry,s.basis q=false)
 (quotient : s.basis L.h = (!s.basis L.sigma &&
   !(decide (regValue (L.y.take 255) s.basis < ((p-1)/2)/3+(!s.basis (L.Y 255)).toNat)))) :
 run (clearQuotient L) m s=⟨s.phase,writeBit s.basis L.h false⟩ := by
 have nd:=compare_nd L hw hn
 have yz:=sigma_ne_y L hw hn 255 (by omega)
 have hs : L.h≠L.sigma := by
   intro e
   have h:=List.nodup_iff_count.mp nd L.h
   simp only [List.count_cons,List.count_append,List.count_nil] at h
   simp only [e,beq_self_eq_true,if_true] at h
   omega
 have hy : L.h≠L.Y 255 := by
   intro e
   have h:=List.nodup_iff_count.mp nd L.h
   simp only [List.count_cons,List.count_append,List.count_nil] at h
   simp only [e,beq_self_eq_true,if_true] at h
   omega
 let t : State:=⟨s.phase,writeBit (writeBit s.basis (L.Y 255) (!s.basis (L.Y 255))) L.sigma (!s.basis L.sigma)⟩
 have pre (r : List Bool) : run [.X (L.Y 255),.X L.sigma] r s=t := by
   simp [run,t,writeBit,yz]
 have tclean : ∀q∈L.carry,t.basis q=false := by
   intro q hq
   have qy:q≠L.Y 255:=fun e=>carry_source_away L hn _ (Or.inl (y_mem L hw 255 (by omega))) (e ▸ hq)
   have qs:q≠L.sigma:=fun e=>carry_source_away L hn _ (Or.inr (Or.inl rfl)) (e ▸ hq)
   simpa only [t,writeBit,Function.update_of_ne qs,Function.update_of_ne qy] using clean q hq
 have tv : regValue (L.y.take 255) t.basis=regValue (L.y.take 255) s.basis := by
   apply regValue_congr
   intro q hq
   have qs:q≠L.sigma := fun e => (List.nodup_cons.mp nd).1 (by simp [←e,hq])
   have qy:q≠L.Y 255 := fun e =>
     (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp nd).2).2).1 (by simp [←e,hq])
   simp [t,writeBit,qs,qy]
 let k:=((p-1)/2)/3
 let v : State:=⟨s.phase,writeBit t.basis L.h
   (s.basis L.h ^^ (!s.basis L.sigma && decide (regValue (L.y.take 255) s.basis < k+(!s.basis (L.Y 255)).toNat)))⟩
 have mid (r : List Bool) :
   run (compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k) r t=v := by
   have c:=compareSelected_correct (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k nd
     (by simp [hw.1]) (by simp [hw.1,hw.2.2]) (by norm_num [k,p,hw.1]) t r tclean
   rw [tv] at c
   apply state_ext
   · exact c.1
   · intro q
     by_cases eq:q=L.h
     · subst q
       simpa [v,t,writeBit,hs,hy,Ne.symm yz,tv] using c.2.2
     · simpa [v,writeBit,eq] using c.2.1 q eq
 have post (r : List Bool) : run [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)] r v=
   ⟨s.phase,writeBit s.basis L.h false⟩ := by
   apply state_ext
   · simp [run,v,t]
   · intro q
     by_cases qh:q=L.h
     · subst q
       simp only [run,v,t,writeBit,Function.update_apply]
       simp only [hs,hy,Ne.symm hs,Ne.symm hy,yz,Ne.symm yz,if_false,if_true]
       rw [quotient]
       cases s.basis L.sigma <;>
         cases decide (regValue (L.y.take 255) s.basis < k+(!s.basis (L.Y 255)).toNat) <;>
         simp_all [k]
     · by_cases qs:q=L.sigma
       · subst q;simp [run,v,t,writeBit,hs,Ne.symm hs,yz,Ne.symm yz]
       · by_cases qy:q=L.Y 255
         · subst q;simp [run,v,t,writeBit,hy,Ne.symm hy,yz,Ne.symm yz]
         · simp [run,v,t,writeBit,qh,qs,qy]
 have result:=run_three_states [.X (L.Y 255),.X L.sigma]
   (compareSelected (L.y.take 255) L.carry (L.Y 255) L.sigma L.h k)
   [.CX L.sigma L.h,.X L.sigma,.X (L.Y 255)]
   (fun a d => a=s → d=⟨s.phase,writeBit s.basis L.h false⟩) (by
     intro a b c d m1 m2 m3 hab hbc hcd eq
     subst a
     rw [pre] at hab
     subst b
     rw [mid] at hbc
     subst c
     exact hcd.symm.trans (post m3)) s m
 simpa only [clearQuotient,List.append_assoc,k] using result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT BiasSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

theorem bias_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 [L.Y 255,L.sigma,L.bias].Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 have mem:=y_mem L hw 255 (by omega)
 have take : (if L.Y 255==q then 1 else 0) ≤ L.y.count q := by
   by_cases eq:L.Y 255=q
   · subst q;simpa using (List.count_pos_iff.mpr mem)
   · simp [eq]
 simp only [DecoderLayout.wires,List.count_cons,List.count_append,List.count_nil] at h ⊢
 omega

theorem biasCompute_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (biasCompute L) m s=
   ⟨s.phase,writeBit s.basis L.bias
      (s.basis L.bias ^^ (s.basis (L.Y 255) && !s.basis L.sigma))⟩ := by
 have nd:=bias_nd L hw hn
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
   not_false_eq_true,and_true] at nd
 obtain ⟨⟨yx,yb⟩,xb⟩:=nd
 simp only [biasCompute,run]
 apply congrArg (State.mk s.phase)
 funext q
 by_cases eq:q=L.sigma
 · subst q;simp [writeBit,yx,xb]
 · by_cases eb:q=L.bias
   · subst q;simp [writeBit,yx,Ne.symm xb]
   · simp [writeBit,eq,eb,yx]

theorem biasErase_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool)
 (known : s.basis L.bias=(s.basis (L.Y 255) && !s.basis L.sigma)) :
 run (biasErase L) m s=⟨s.phase,writeBit s.basis L.bias false⟩ := by
 have nd:=bias_nd L hw hn
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
   not_false_eq_true,and_true] at nd
 obtain ⟨⟨yx,yb⟩,xb⟩:=nd
 simp only [biasErase,run]
 cases hm:m.headD false <;>
   simp [measureAndCorrect,correct,writeBit,yx,xb,Ne.symm xb,yb,known]
 all_goals
   funext q
   by_cases eq:q=L.sigma
   · subst q;simp [xb]
   · simp [Function.update_apply,eq]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT NormalizeSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

def complementBasis (control : Wire) (xs : List Wire) (b : BasisState) : BasisState :=
 fun q=>if q∈xs then b q ^^ b control else b q

theorem conditional_complement_run (control : Wire) (xs : List Wire)
 (hn : xs.Nodup) (away : control∉xs) (s : State) (m : List Bool) :
 run (xs.map (fun q=>Instr.CX control q)) m s=⟨s.phase,complementBasis control xs s.basis⟩ := by
 induction xs generalizing s with
 | nil =>
   apply state_ext
   · simp [run]
   · intro q;simp [run,complementBasis]
 | cons x xs ih =>
   obtain ⟨xaway,tailnd⟩:=List.nodup_cons.mp hn
   have cx:control≠x:=fun e=>away (by simp [e])
   have ct:control∉xs:=fun h=>away (by simp [h])
   let t : State:=⟨s.phase,writeBit s.basis x (s.basis x ^^ s.basis control)⟩
   simp only [List.map_cons,run]
   change run (xs.map (fun q=>Instr.CX control q)) m t=_
   rw [ih tailnd ct]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases eq:q=x
   · subst q;simp [complementBasis,t,writeBit,xaway]
   · simp [complementBasis,t,writeBit,eq,cx]

theorem normalize_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
 (L.y.take 255++L.r).Nodup ∧ L.Y 255∉L.y.take 255++L.r := by
 have full:(L.y++L.r).Nodup := by
   apply List.nodup_iff_count.mpr
   intro q
   have h:=List.nodup_iff_count.mp hn q
   simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
   omega
 have sub:(L.y.take 255++L.r).Sublist (L.y++L.r) := (List.take_sublist 255 L.y).append (List.Sublist.refl _)
 constructor
 · exact full.sublist sub
 · have shape:=y_split L hw
   have hn':(L.y.take 255++[L.Y 255]++L.r).Nodup := by simpa only [←shape] using full
   intro mem
   have c:=List.nodup_iff_count.mp hn' (L.Y 255)
   have pos:=List.count_pos_iff.mpr mem
   simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at c pos
   omega

theorem normalize_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (normalize L) m s=
 ⟨s.phase,complementBasis (L.Y 255) (L.y.take 255++L.r) s.basis⟩ := by
 have nd:=normalize_nd L hw hn
 simpa only [normalize,List.map_append] using conditional_complement_run (L.Y 255) (L.y.take 255++L.r) nd.1 nd.2 s m

theorem restoreSource_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (restoreSource L) m s=
 ⟨s.phase,complementBasis (L.Y 255) (L.y.take 255) s.basis⟩ := by
 have nd:=normalize_nd L hw hn
 exact conditional_complement_run (L.Y 255) (L.y.take 255)
   (List.nodup_append'.mp nd.1).1 (fun h=>nd.2 (List.mem_append_left _ h)) s m
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamGeometry
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def bSources (L : DecoderLayout) (i : Nat) : List Wire:=rawSources L i++correctionSources L i

theorem r_ne_r (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i j : Nat) (hi : i<256) (hj : j<256) (ne : i≠j) : L.R i≠L.R j := by
 intro eq
 have len:=hw.2.1
 exact ne (getD_inj L.r (register_nodup L hn).2.1 i j (by omega) (by omega) eq)

theorem correction_r_away (L : DecoderLayout) (hn : L.wires.Nodup)
 (i : Nat) (q : Wire) (hq : q∈correctionSources L i) : q∉L.r := by
 apply source_r_away L hn q
 unfold correctionSources correction at hq
 split_ifs at hq with h1 hc
 · have eq:q=L.bias:=by simpa using hq
   subst q;exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
 · have eq:q=L.h:=by simpa using hq
   subst q;exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
 · simp at hq

theorem bSources_r_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (q : Wire) (hq : q∈bSources L i) : q∉L.r := by
 rcases List.mem_append.mp hq with h|h
 · exact raw_source_r_away L hw hn i hi q h
 · exact correction_r_away L hn i q h

theorem bSources_parity (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (s t : BasisState)
 (agree : ∀q,q∉L.r→s q=t q) : parity (bSources L i) s=parity (bSources L i) t := by
 apply parity_congr
 intro q hq
 exact agree q (bSources_r_away L hw hn i hi q hq)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamForward
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def bExpected (L : DecoderLayout) (origin : BasisState) (i : Nat) : Bool:=
 origin (L.R i) ^^ parity (bSources L i) origin

structure StreamFrame (L : DecoderLayout) (origin : State) (nDone : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 outside : ∀q,q∉L.r→s.basis q=origin.basis q
 stored : ∀j,j<nDone→s.basis (L.R j)=bExpected L origin.basis (j+1)
 current : s.basis (L.R nDone)=false
 pending : ∀j,nDone<j→j<256→s.basis (L.R j)=origin.basis (L.R j)

theorem stream_initial (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (m : List Bool)
 (low : origin.basis (L.R 0)=parity (bSources L 0) origin.basis) :
 StreamFrame L origin 0 (run (xorList (bSources L 0) (L.R 0)) m origin) := by
 have away:L.R 0∉bSources L 0:=by
   intro h;exact bSources_r_away L hw hn 0 (by omega) _ h (r_mem L hw 0 (by omega))
 rw [xorList_run _ _ away,low]
 simp only [Bool.xor_self]
 refine ⟨rfl,?_,?_,?_,?_⟩
 · intro q hq
   have ne:q≠L.R 0:=fun e=>hq (e ▸ r_mem L hw 0 (by omega))
   simp [writeBit,ne]
 · intro j hj;omega
 · simp [writeBit]
 · intro j hj hbound
   simp [writeBit,r_ne_r L hw hn j 0 hbound (by omega) (by omega)]

theorem stream_frame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (n : Nat) (bound : n<255) (f : StreamFrame L origin n s) (m : List Bool) :
 StreamFrame L origin (n+1) (run (streamCarry L (n+1)) m s) := by
 have ne:=r_ne_r L hw hn n (n+1) (by omega) (by omega) (by omega)
 have ap:L.R n∉bSources L (n+1):=by
   intro h;exact bSources_r_away L hw hn (n+1) (by omega) _ h (r_mem L hw n (by omega))
 have ao:L.R (n+1)∉bSources L (n+1):=by
   intro h;exact bSources_r_away L hw hn (n+1) (by omega) _ h (r_mem L hw (n+1) (by omega))
 have par:=bSources_parity L hw hn (n+1) (by omega) s.basis origin.basis f.outside
 have pending:=f.pending (n+1) (by omega) (by omega)
 simp only [streamCarry,Nat.add_sub_cancel]
 change StreamFrame L origin (n+1) (run (streamStage (bSources L (n+1)) (L.R n) (L.R (n+1))) m s)
 rw [streamStage_run _ _ _ ne ap ao s m f.current,pending,par]
 change StreamFrame L origin (n+1)
   ⟨s.phase,writeBit (writeBit s.basis (L.R n) (bExpected L origin.basis (n+1))) (L.R (n+1)) false⟩
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · intro q hq
   have n0:q≠L.R n:=fun e=>hq (e ▸ r_mem L hw n (by omega))
   have n1:q≠L.R (n+1):=fun e=>hq (e ▸ r_mem L hw (n+1) (by omega))
   simpa only [writeBit,Function.update_of_ne n0,Function.update_of_ne n1] using f.outside q hq
 · intro j hj
   have nj1:=r_ne_r L hw hn j (n+1) (by omega) (by omega) (by omega)
   simp only [writeBit,Function.update_of_ne nj1]
   by_cases eq:j=n
   · subst j;simp
   · have nj0:=r_ne_r L hw hn j n (by omega) (by omega) eq
     simpa only [Function.update_of_ne nj0] using f.stored j (by omega)
 · simp [writeBit]
 · intro j hj hbound
   have nj1:=r_ne_r L hw hn j (n+1) hbound (by omega) (by omega)
   have nj0:=r_ne_r L hw hn j n hbound (by omega) (by omega)
   simpa only [writeBit,Function.update_of_ne nj0,Function.update_of_ne nj1] using f.pending j (by omega) hbound

theorem stream_forward_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : StreamFrame L origin 0 s) (n : Nat) (bound : n≤255) (m : List Bool) :
 StreamFrame L origin n (run ((List.range' 1 n).flatMap (streamCarry L)) m s) := by
 induction n generalizing m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range'_1_concat,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   rw [Nat.add_comm 1 n]
   apply stream_frame_step L hw hn origin _ n (by omega)
   exact ih (by omega) _

end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT XorWindow
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def xorWindow (xs : List Wire) (temp : Wire) (P : Program) : Program:=xorList xs temp++P++xorList xs temp

theorem xorWindow_write (xs : List Wire) (temp target : Wire) (P : Program)
 (awayT : temp∉xs) (awayQ : target∉xs) (ne : temp≠target)
 (s : State) (m : List Bool) (value : Bool)
 (middle : ∀r,run P r ⟨s.phase,writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)⟩=
   ⟨s.phase,writeBit (writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)) target value⟩) :
 run (xorWindow xs temp P) m s=⟨s.phase,writeBit s.basis target value⟩ := by
 let t : State:=⟨s.phase,writeBit s.basis temp (s.basis temp ^^ parity xs s.basis)⟩
 let u : State:=⟨s.phase,writeBit t.basis target value⟩
 have first (r : List Bool):run (xorList xs temp) r s=t:=xorList_run _ _ awayT _ _
 have par:parity xs u.basis=parity xs s.basis:=by
   apply parity_congr
   intro q hq
   have qt:q≠temp:=fun e=>awayT (e ▸ hq)
   have qq:q≠target:=fun e=>awayQ (e ▸ hq)
   simp [u,t,writeBit,qt,qq]
 have last (r : List Bool):run (xorList xs temp) r u=⟨s.phase,writeBit s.basis target value⟩:=by
   rw [xorList_run _ _ awayT,par]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases qt:q=temp
   · subst q;simp [u,t,writeBit,ne]
   · by_cases qq:q=target
     · subst q;simp [u,t,writeBit,ne,Ne.symm ne]
     · simp [u,t,writeBit,qt,qq]
 rw [xorWindow]
 simp only [List.append_assoc,run_append,run_take,(xorList_counts xs temp).2,List.take_zero,List.drop_zero]
 rw [first,middle]
 exact last _
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamEraseSteps
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def BGraph (L : DecoderLayout) (origin : BasisState) : Prop:=
 ∀ i, 1 ≤ i → i ≤ 255 → bExpected L origin i=
   carryBit ((correction L (i-1)).value origin) (parity (rawSources L (i-1)) origin)
     (if i=1 then false else bExpected L origin (i-1))

structure EraseBFrame (L : DecoderLayout) (origin : State) (nLive : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 outside : ∀ q, q∉L.r → s.basis q=origin.basis q
 live : ∀j,j<nLive → s.basis (L.R j)=bExpected L origin.basis (j+1)
 clean : ∀j,nLive ≤ j → j<256 → s.basis (L.R j)=false

theorem flag_y_away (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire)
 (hq : q∈[L.sigma,L.h,L.bias]) : q∉L.y := by
 intro hy
 have p:=List.count_pos_iff.mpr hq
 have y:=List.count_pos_iff.mpr hy
 have h:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append] at h
 omega

theorem correction_option_r_away (L : DecoderLayout) (hn : L.wires.Nodup) (i : Nat)
 (q : Wire) (hq : q∈(correction L i).wire) : q∉L.r := by
 apply correction_r_away L hn i q
 simpa only [correctionSources,Option.mem_toList] using hq

theorem correction_value_same (L : DecoderLayout) (hn : L.wires.Nodup) (i : Nat)
 (s t : BasisState) (same : ∀ q, q∉L.r → s q=t q) :
 (correction L i).value s=(correction L i).value t := by
 apply mappedBit_value_congr
 intro q hq
 exact same q (correction_option_r_away L hn i q hq)

theorem raw_parity_same (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (i : Nat) (hi : i<256) (s t : BasisState) (same : ∀ q, q∉L.r → s q=t q) :
 parity (rawSources L i) s=parity (rawSources L i) t := by
 apply parity_congr
 intro q hq
 exact same q (raw_source_r_away L hw hn i hi q hq)

theorem eraseCorrectionCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hlo : 1 ≤ i) (hi : i ≤ 255)
 (graph : BGraph L origin.basis) (f : EraseBFrame L origin i s) (m : List Bool) :
 run (eraseCorrectionCarry L i) m s=⟨s.phase,writeBit s.basis (L.R (i-1)) false⟩ := by
 by_cases h1:i=1
 · subst i
   have ym:=y_mem L hw 0 (by omega)
   have rm:=r_mem L hw 0 (by omega)
   have hy:L.h∉L.y:=flag_y_away L hn _ (by simp)
   have yr:L.Y 0≠L.R 0:=fun e=>source_r_away L hn _ (Or.inl ym) (e ▸ rm)
   have hr:L.h≠L.R 0:=fun e=>source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (e ▸ rm)
   have yh:L.Y 0≠L.h:=fun e=>hy (e ▸ ym)
   have nd:[L.Y 0,L.h,L.R 0].Nodup:=by simp [yh,yr,hr]
   have ySame:=f.outside (L.Y 0) (source_r_away L hn _ (Or.inl ym))
   have hSame:=f.outside L.h (source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
   have g:=graph 1 (by omega) (by omega)
   have k:=f.live 0 (by omega)
   have corr:correction L 0=⟨some L.h,false⟩:=by rfl
   rw [show 1-1=0 by omega] at g
   rw [corr] at g
   simp only [rawSources,ite_true,parity,List.foldr_cons,List.foldr_nil,Bool.xor_false,
     MappedBit.value,Option.map_some,Option.getD_some,Bool.false_xor,ite_true] at g
   have known:s.basis (L.R 0)=carryBit false (s.basis (L.Y 0)) (s.basis L.h) := by
     rw [k,g,ySame,hSame]
     cases origin.basis (L.Y 0) <;> cases origin.basis L.h <;> rfl
   change run (mappedEraseCarry ⟨none,false⟩ (L.Y 0) L.h (L.R 0)) m s=_
   apply mappedEraseCarry_correct ⟨none,false⟩ (L.Y 0) L.h (L.R 0) nd (by simp)
   simpa [MappedBit.value] using known
 · have h2:2 ≤ i:=by omega
   let tmp:=L.R 255
   let cin:=L.R (i-2)
   let target:=L.R (i-1)
   have tc:tmp≠cin:=r_ne_r L hw hn 255 (i-2) (by omega) (by omega) (by omega)
   have tt:tmp≠target:=r_ne_r L hw hn 255 (i-1) (by omega) (by omega) (by omega)
   have ct:cin≠target:=r_ne_r L hw hn (i-2) (i-1) (by omega) (by omega) (by omega)
   have nd:[tmp,cin,target].Nodup:=by simp [tc,tt,ct]
   have optAway:∀q∈(correction L (i-1)).wire,q∉[tmp,cin,target]:=by
     intro q hq bad
     have away:=correction_option_r_away L hn (i-1) q hq
     simp only [List.mem_cons,List.not_mem_nil,or_false] at bad
     rcases bad with rfl|rfl|rfl
     · exact away (r_mem L hw 255 (by omega))
     · exact away (r_mem L hw (i-2) (by omega))
     · exact away (r_mem L hw (i-1) (by omega))
   have awayTemp:tmp∉rawSources L (i-1):=by
     intro q;exact raw_source_r_away L hw hn (i-1) (by omega) tmp q (r_mem L hw 255 (by omega))
   have aq:target∉rawSources L (i-1):=by
     intro q;exact raw_source_r_away L hw hn (i-1) (by omega) target q (r_mem L hw (i-1) (by omega))
   have tempZero:s.basis tmp=false:=f.clean 255 hi (by omega)
   have rawSame:=raw_parity_same L hw hn (i-1) (by omega) s.basis origin.basis f.outside
   have corSame:=correction_value_same L hn (i-1) s.basis origin.basis f.outside
   have cinValue:s.basis cin=bExpected L origin.basis (i-1):=by
     have a:=f.live (i-2) (by omega)
     simpa only [show i-2+1=i-1 by omega] using a
   have targetValue:s.basis target=bExpected L origin.basis i:=by
     have a:=f.live (i-1) (by omega)
     simpa only [show i-1+1=i by omega] using a
   rw [eraseCorrectionCarry,if_neg h1]
   change run (xorWindow (rawSources L (i-1)) tmp
     (mappedEraseCarry (correction L (i-1)) tmp cin target)) m s=_
   apply xorWindow_write _ tmp target _ awayTemp aq tt
   intro r
   apply mappedEraseCarry_correct (correction L (i-1)) tmp cin target nd optAway
   have bm:(correction L (i-1)).value
       (writeBit s.basis tmp (s.basis tmp ^^ parity (rawSources L (i-1)) s.basis))=
       (correction L (i-1)).value origin.basis := by
     apply correction_value_same L hn (i-1)
     intro q hq
     have nq:q≠tmp:=fun e=>hq (e ▸ r_mem L hw 255 (by omega))
     simpa [writeBit,nq] using f.outside q hq
   rw [bm]
   simp only [writeBit,Function.update_of_ne (Ne.symm tt),Function.update_of_ne (Ne.symm tc),
     Function.update_self,tempZero,Bool.false_xor,targetValue,cinValue,rawSame]
   simpa only [h1,ite_false] using graph i hlo hi
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Front
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run normalize biasCompute

def front (L : DecoderLayout) : Program :=
 normalize L ++ ([.CX (L.R 0) L.h,.CX (L.Y 0) L.h] ++ biasCompute L)

def frontBasis (L : DecoderLayout) (b : BasisState) : BasisState :=
 let n:=complementBasis (L.Y 255) (L.y.take 255++L.r) b
 writeBit (writeBit n L.h (n L.h ^^ n (L.R 0) ^^ n (L.Y 0))) L.bias
   (n L.bias ^^ (n (L.Y 255) && !n L.sigma))

theorem front_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) : run (front L) m s=⟨s.phase,frontBasis L s.basis⟩ := by
 have hy:L.h≠L.Y 0:=fun e=>flag_y_away L hn _ (by simp) (e ▸ y_mem L hw 0 (by omega))
 have hr:L.h≠L.R 0:=fun e=>source_r_away L hn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (e ▸ r_mem L hw 0 (by omega))
 have hh : [L.sigma,L.h,L.bias].Nodup := by
   apply List.nodup_iff_count.mpr
   intro q
   have c:=List.nodup_iff_count.mp hn q
   simp only [DecoderLayout.wires,List.count_append] at c
   omega
 have hs:L.sigma≠L.h := fun e=>(List.nodup_cons.mp hh).1 (by simp[e])
 have hb:L.bias≠L.h := fun e=>(List.nodup_cons.mp (List.nodup_cons.mp hh).2).1 (by simp[e])
 have htop:L.Y 255≠L.h:=fun e=>flag_y_away L hn _ (by simp) (e.symm ▸ y_mem L hw 255 (by omega))
 let n : State:=⟨s.phase,complementBasis (L.Y 255) (L.y.take 255++L.r) s.basis⟩
 let u : State:=⟨s.phase,writeBit n.basis L.h (n.basis L.h ^^ n.basis (L.R 0) ^^ n.basis (L.Y 0))⟩
 have middle (r : List Bool) : run [.CX (L.R 0) L.h,.CX (L.Y 0) L.h] r n=u := by
   simp only [run]
   apply congrArg (State.mk s.phase)
   funext q
   by_cases eq:q=L.h
   · subst q;simp [u,n,writeBit,Ne.symm hy]
   · simp [u,n,writeBit,eq]
 have last (r : List Bool) : run (biasCompute L) r u=⟨s.phase,frontBasis L s.basis⟩ := by
   rw [biasCompute_run L hw hn]
   simp only [u,n,frontBasis,writeBit,Function.update_of_ne hb,Function.update_of_ne htop,Function.update_of_ne hs]
 have result:=run_three_states (normalize L) [.CX (L.R 0) L.h,.CX (L.Y 0) L.h] (biasCompute L)
   (fun a d=>a=s → d=⟨s.phase,frontBasis L s.basis⟩) (by
     intro a b c d m1 m2 m3 hab hbc hcd eq
     subst a
     rw [normalize_run L hw hn] at hab
     change n=b at hab
     subst b
     rw [middle] at hbc
     subst c
     exact hcd.symm.trans (last m3)) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CopySteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run

theorem zip_copy (ys rs : List Wire) :
 (ys.zip rs).map (fun q=>Instr.CX q.1 q.2)=copyRegister none ys rs := by
 induction ys generalizing rs with
 |nil=>cases rs <;>rfl
 |cons y ys ih=>cases rs with
   |nil=>rfl
   |cons r rs=>simp only [List.zip_cons_cons,List.map_cons,copyRegister,copyGate,List.singleton_append];rw[ih]

theorem yr_nodup (L : DecoderLayout) (hn : L.wires.Nodup) : (L.y++L.r).Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have h:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
 omega

theorem copySource_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (m : List Bool) :
 (run (copySource L) m s).phase=s.phase ∧
 (∀q,q∉L.r → (run (copySource L) m s).basis q=s.basis q) ∧
 regValue L.r (run (copySource L) m s).basis=regValue L.r s.basis ^^^ regValue L.y s.basis := by
 rw [copySource,zip_copy]
 simpa only [copyValue] using copyRegister_correct none L.y L.r (hw.1.trans hw.2.1.symm)
   (yr_nodup L hn) (by simp) s m

theorem complementBasis_value (control : Wire) (xs : List Wire) (b : BasisState) :
 regValue xs (complementBasis control xs b)=
 if b control then 2^xs.length-1-regValue xs b else regValue xs b := by
 cases hb:b control
 · apply regValue_congr
   intro q hq
   simp [complementBasis,hb,hq]
 · rw [regValue_congr xs _ (fun q=>!b q) (by intro q hq;simp[complementBasis,hb,hq])]
   exact regValue_complement xs b
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FrontFacts
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem flags_nd (L : DecoderLayout) (hn : L.wires.Nodup) : [L.sigma,L.h,L.bias].Nodup := by
 apply List.nodup_iff_count.mpr
 intro q
 have c:=List.nodup_iff_count.mp hn q
 simp only [DecoderLayout.wires,List.count_append] at c
 omega

theorem flags_bank_away (L : DecoderLayout) (hn : L.wires.Nodup) (f : Wire)
 (hf : f=L.h ∨ f=L.bias) (q : Wire) (hq:q∈L.y ∨ q∈L.r ∨ q∈L.carry) : q≠f := by
 intro eq
 subst q
 rcases hq with hy|hr|hc
 · exact flag_y_away L hn f (by rcases hf with rfl|rfl <;>simp) hy
 · exact source_r_away L hn f (by rcases hf with rfl|rfl <;>tauto) hr
 · exact carry_source_away L hn f (by rcases hf with rfl|rfl <;>tauto) hc

theorem front_on_banks (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState)
 (q : Wire) (hq:q∈L.y ∨ q∈L.r ∨ q∈L.carry) :
 frontBasis L b q=complementBasis (L.Y 255) (L.y.take 255++L.r) b q := by
 have qh:=flags_bank_away L hn L.h (Or.inl rfl) q hq
 have qb:=flags_bank_away L hn L.bias (Or.inr rfl) q hq
 simp [frontBasis,writeBit,qh,qb]

theorem normalized_flag (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState)
 (f : Wire) (hf:f∈[L.sigma,L.h,L.bias]) :
 complementBasis (L.Y 255) (L.y.take 255++L.r) b f=b f := by
 have ya:=flag_y_away L hn f hf
 have ra:f∉L.r:=by
   simp only[List.mem_cons,List.not_mem_nil,or_false] at hf
   apply source_r_away L hn f
   rcases hf with rfl|rfl|rfl <;>tauto
 simp [complementBasis,show f∉L.y.take 255 from fun h=>ya (List.mem_of_mem_take h),ra]

theorem front_source_sigma (L : DecoderLayout) (hn : L.wires.Nodup) (b : BasisState) :
 frontBasis L b L.sigma=b L.sigma := by
 have nd:=flags_nd L hn
 have sh:L.sigma≠L.h:=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
 have sb:L.sigma≠L.bias:=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
 simp only[frontBasis,writeBit,Function.update_of_ne sh,Function.update_of_ne sb]
 exact normalized_flag L hn b L.sigma (by simp)

theorem front_bias (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (clean : b L.bias=false) :
 frontBasis L b L.bias=(b (L.Y 255) && !b L.sigma) := by
 have norm:=normalize_nd L hw hn
 simp only[frontBasis,writeBit,Function.update_self]
 rw[normalized_flag L hn b L.bias (by simp),normalized_flag L hn b L.sigma (by simp)]
 simp [complementBasis,norm.2,clean]

theorem front_h (L : DecoderLayout) (hn : L.wires.Nodup)
 (b : BasisState) (clean : b L.h=false) :
 frontBasis L b L.h=
  (complementBasis (L.Y 255) (L.y.take 255++L.r) b (L.R 0) ^^
   complementBasis (L.Y 255) (L.y.take 255++L.r) b (L.Y 0)) := by
 have nd:=flags_nd L hn
 have hb:L.h≠L.bias:=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
 simp only[frontBasis,writeBit,Function.update_of_ne hb,Function.update_self]
 rw[normalized_flag L hn b L.h (by simp),clean,Bool.false_xor]

theorem front_carry_clean (L : DecoderLayout) (hn : L.wires.Nodup)
 (b : BasisState) (clean : ∀q∈L.carry,b q=false) : ∀q∈L.carry,frontBasis L b q=false := by
 intro q hq
 rw[front_on_banks L hn b q (Or.inr (Or.inr hq))]
 have qy:q∉L.y := by
   intro hy
   exact carry_source_away L hn q (Or.inl hy) hq
 have qr:q∉L.r:=source_r_away L hn q (Or.inr (Or.inl hq))
 simp [complementBasis,show q∉L.y.take 255 from fun h=>qy (List.mem_of_mem_take h),qr,clean q hq]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FrontValues
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

theorem complement_subset_value (control : Wire) (xs region : List Wire)
 (sub : ∀q∈xs,q∈region) (b : BasisState) :
 regValue xs (complementBasis control region b)=
 if b control then 2^xs.length-1-regValue xs b else regValue xs b := by
 rw[regValue_congr xs _ (complementBasis control xs b) (by intro q hq;simp[complementBasis,hq,sub q hq])]
 exact complementBasis_value control xs b

theorem getD_testBit (xs : List Wire) (i : Nat) (b : BasisState) (hi:i<xs.length) :
 b (xs.getD i 0)=Nat.testBit (regValue xs b) i := by
 have h:=regValue_bit xs i 0 b hi
 rw[Nat.testBit_eq_decide_div_mod_eq]
 cases eq:b (xs.getD i 0) <;> simp only[eq,Bool.toNat_false,Bool.toNat_true] at h ⊢ <;>
   simp[←h]

theorem front_low_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) (b : BasisState) :
 regValue (L.y.take 255) (frontBasis L b)=
 if b (L.Y 255) then 2^255-1-regValue L.y b%2^255 else regValue L.y b%2^255 := by
 rw[regValue_congr (L.y.take 255) _ (complementBasis (L.Y 255) (L.y.take 255++L.r) b)
   (by intro q hq;exact front_on_banks L hn b q (Or.inl (List.mem_of_mem_take hq)))]
 rw[complement_subset_value _ _ _ (by intro q hq;exact List.mem_append_left _ hq)]
 have len:=hw.1
 rw[CuccaroStreamedSquareWideLayout.regValue_take_mod L.y 255 (by omega) b]
 simp only[List.length_take,len,Nat.min_eq_left (by omega : 255≤256)]

theorem front_r_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup) (b : BasisState) :
 regValue L.r (frontBasis L b)=
 if b (L.Y 255) then 2^256-1-regValue L.r b else regValue L.r b := by
 rw[regValue_congr L.r _ (complementBasis (L.Y 255) (L.y.take 255++L.r) b)
   (by intro q hq;exact front_on_banks L hn b q (Or.inr (Or.inl hq)))]
 rw[complement_subset_value _ _ _ (by intro q hq;exact List.mem_append_right _ hq)]
 rw[hw.2.1]

theorem front_h_value (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (clean:b L.h=false) :
 frontBasis L b L.h=
   (Nat.testBit (regValue L.r (frontBasis L b)) 0 ^^
    Nat.testBit (regValue (L.y.take 255) (frontBasis L b)) 0) := by
 rw[front_h L hn b clean]
 have r:=getD_testBit L.r 0 (frontBasis L b) (by have len:=hw.2.1;omega)
 have y:=getD_testBit (L.y.take 255) 0 (frontBasis L b) (by simp[hw.1])
 have yget:(L.y.take 255).getD 0 0=L.Y 0 :=by
   cases eq:L.y with
   |nil=>have len:=hw.1;simp[eq] at len
   |cons a as=>simp[DecoderLayout.Y,eq]
 rw[yget] at y
 change frontBasis L b (L.R 0)=_ at r
 rw[front_on_banks L hn b (L.R 0) (Or.inr (Or.inl (r_mem L hw 0 (by omega))))] at r
 rw[front_on_banks L hn b (L.Y 0) (Or.inl (y_mem L hw 0 (by omega)))] at y
 rw[r,y]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT QuotientMath
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.TerminalGraph
open Secp256k1

def M : Int:=2^256
def C : Int:=2^32+977
def Q : Int:=((p:Int)-1)/2

theorem constants : (p:Int)=M-C ∧ M%2=0 ∧ C%2=1 ∧ C%4=1 ∧ C%4<2 ∧ Q%3=0 := by
  norm_num [M,C,Q,p]

/-- One's-complement normalization leaves only a nonnegative single-bit modular correction. -/
theorem normalized_equation (z r j sigma sy : Int)
    (eq : r=(3-2*sigma)*z-j*(p:Int))
    (sg : z=(1-2*sy)*((if sy=0 then z else -z-1)+sy))
    (hs : sy=0 ∨ sy=1) :
    let y:=if sy=0 then z else -z-1
    let t:=if sy=0 then r else -r-1
    let h:=(1-2*sy)*j
    t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int) := by
  rcases hs with rfl|rfl <;> dsimp <;> simp [eq] <;> ring


theorem positive_correction (y t h sigma sy : Int)
    (eq : t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int)) :
    (3-2*sigma)*y+2*(1-sigma)*sy+h*C=t+h*M := by
  rw [constants.1] at eq
  linear_combination -eq

/-- The quotient flag can be copied from the low parity, without a wide comparator. -/
theorem quotient_low (y t h sigma sy : Int)
    (hs : sigma=0 ∨ sigma=1) (hh : h=0 ∨ h=1)
    (eq : t=(3-2*sigma)*y+2*(1-sigma)*sy-h*(p:Int)) :
    (t-y)%2=h := by
  rcases hs with rfl|rfl <;> rcases hh with rfl|rfl <;>
    norm_num [p] at eq ⊢ <;> omega

/-- A paid comparator can clear the quotient after the graph carries are erased. -/
theorem quotient_threshold (y t h sy : Int)
    (hy : 0≤y) (hs : sy=0 ∨ sy=1) (hh : h=0 ∨ h=1)
    (eq : t=3*y+2*sy-h*(p:Int)) (bounds : -Q-sy≤t ∧ t≤Q) :
    h=1 ↔ Q/3<y ∨ (sy=1 ∧ y=Q/3) := by
  rcases hs with rfl|rfl <;> rcases hh with rfl|rfl <;>
    norm_num [Q,p] at eq bounds ⊢ <;> omega
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT FpQuotient
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem center_triple (z : Int) (hz : Centered z) :
    centerFp (3*(z:Fp)) =
      if q<3*z then 3*z-(p:Int) else if 3*z< -q then 3*z+(p:Int) else 3*z := by
  have hp := BalancedField.constants
  have pc : ((p:Int):Fp)=0 := by simp
  unfold Centered at hz
  split_ifs with hi hlo
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp [Int.cast_sub,Int.cast_mul,pc]
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp [Int.cast_add,Int.cast_mul,pc]
  · apply centered_cast_unique _ _ (centerFp_bounds _)
    · unfold Centered; constructor <;> omega
    · rw [centerFp_cast]; simp

/-- The signed modular quotient has one bit of magnitude and follows the source sign. -/
theorem quotient_exists (Y : Fp) (sigma : Bool) :
    let z:=centerFp Y
    let r:=centerFp ((if sigma then 1 else 3)*Y)
    ∃ j : Int, r=(if sigma then 1 else 3)*z-j*(p:Int) ∧
      -1≤j ∧ j≤1 ∧ (0≤z → 0≤j) ∧ (z<0 → j≤0) ∧ (sigma=true → j=0) := by
  have hz:=centerFp_bounds Y
  have hp:=BalancedField.constants
  cases sigma
  · dsimp
    have eq:=center_triple (centerFp Y) hz
    rw [centerFp_cast] at eq
    unfold Centered at hz
    by_cases hi : q<3*centerFp Y
    · refine ⟨1,?_,by omega,by omega,?_,?_,by simp⟩
      · simpa [hi] using eq
      · intro _; omega
      · intro hn; omega
    · by_cases hlo : 3*centerFp Y< -q
      · refine ⟨-1,?_,by omega,by omega,?_,?_,by simp⟩
        · simpa [hi,hlo] using eq
        · intro hn; omega
        · intro _; omega
      · refine ⟨0,?_,by omega,by omega,?_,?_,by simp⟩
        · simpa [hi,hlo] using eq
        · intro _; omega
        · intro _; omega
  · dsimp; refine ⟨0,?_,by omega,by omega,?_,?_,by simp⟩
    · simp
    · intro _; omega
    · intro _; omega

/-- Actual Fp inputs supply every signed/range premise of the checked decoder algebra. -/
theorem normalized_bridge (Y : Fp) (sigma : Bool) :
    let z:=centerFp Y
    let r:=centerFp ((if sigma then 1 else 3)*Y)
    let sy:Int:=if z<0 then 1 else 0
    let y:=if sy=0 then z else -z-1
    let t:=if sy=0 then r else -r-1
    ∃ h : Int, (h=0 ∨ h=1) ∧ 0≤y ∧ -TerminalGraph.Q-sy≤t ∧ t≤TerminalGraph.Q ∧
      t=(3-2*(if sigma then 1 else 0))*y+
        2*(1-(if sigma then 1 else 0))*sy-h*(p:Int) ∧ (sigma=true → h=0) := by
  dsimp
  obtain ⟨j,he,hlo,hhi,hpos,hneg,hzero⟩:=quotient_exists Y sigma
  have hz:=centerFp_bounds Y
  have hr:=centerFp_bounds ((if sigma then 1 else 3)*Y)
  have he' : centerFp ((if sigma then 1 else 3)*Y)=
      (3-2*(if sigma then 1 else 0 : Int))*centerFp Y-j*(p:Int) := by
    cases sigma <;> simpa using he
  by_cases hs : centerFp Y<0
  · have sg : centerFp Y=(1-2*(1:Int))*(-centerFp Y-1+1) := by ring
    have hn:=TerminalGraph.normalized_equation _ _ _ (if sigma then 1 else 0) 1 he' sg (Or.inr rfl)
    simp only [show ¬(1:Int)=0 by omega,if_false] at hn
    unfold Centered at hz hr
    refine ⟨-j,?_,?_,?_,?_,?_,?_⟩
    · have hj:=hneg hs; omega
    · simp [hs]; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simpa [hs] using hn
    · intro ht; rw [hzero ht]; omega
  · have sg : centerFp Y=(1-2*(0:Int))*(centerFp Y+0) := by ring
    have hn:=TerminalGraph.normalized_equation _ _ _ (if sigma then 1 else 0) 0 he' sg (Or.inl rfl)
    simp only [mul_zero,sub_zero,if_pos rfl,zero_add,one_mul] at hn
    unfold Centered at hz hr
    refine ⟨j,?_,?_,?_,?_,?_,?_⟩
    · have hj:=hpos (by omega); omega
    · simp [hs]; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simp [hs,TerminalGraph.Q,q] at *; omega
    · simpa [hs] using hn
    · exact hzero
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT WordBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem normalized_source_bounds (Y : Fp) :
    0≤(if centerFp Y<0 then -centerFp Y-1 else centerFp Y) ∧
    (if centerFp Y<0 then -centerFp Y-1 else centerFp Y)≤TerminalGraph.Q := by
  have h:=centerFp_bounds Y
  unfold Centered at h
  have eq : q=TerminalGraph.Q := rfl
  split_ifs <;> omega

theorem centerWord_msb (Y : Fp) :
    (centerWord Y).testBit 255=decide (centerFp Y<0) := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hs:=centerWord_sign Y
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hd : centerWord Y / 2^255 < 2 := by
    norm_num only [Nat.reducePow] at hb ⊢
    omega
  rw [Nat.mod_eq_of_lt hd]
  have eq : centerWord Y / 2^255 = 1 ↔ centerFp Y<0 := by
    norm_num only [Nat.reducePow] at hb hs ⊢
    omega
  simp only [eq]

/-- Complementing a complete canonical256-bit word is exact one's complement. -/
theorem full_complement_word (Y : Fp) :
    2^256-1-centerWord Y=encodeWord 256 (-centerFp Y-1) := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hd:=centerWord_decode Y
  have hc : 2^256-1-centerWord Y<2^256 := by omega
  have dec : signedDecode 256 (2^256-1-centerWord Y)= -centerFp Y-1 := by
    unfold signedDecode at hd ⊢
    norm_num only [Nat.reduceSub,Nat.reducePow] at hd hb ⊢
    split_ifs at hd ⊢ <;> omega
  rw [←dec,encode_decodeWord 256 _ hc]

def lowNormalize (w : Nat) (sign : Bool) : Nat :=
  if sign then 2^255+(2^255-1-w%2^255) else w

/-- Low255 complement retains the original source MSB and exposes the nonnegative magnitude. -/
theorem low_complement_word (Y : Fp) :
    lowNormalize (centerWord Y) (decide (centerFp Y<0))=
      (if centerFp Y<0 then -centerFp Y-1 else centerFp Y).toNat+
        (decide (centerFp Y<0)).toNat*2^255 := by
  have hb : centerWord Y<2^256:=encodeWord_bound _ _
  have hd:=centerWord_decode Y
  have hs:=centerWord_sign Y
  have hz:=centerFp_bounds Y
  unfold Centered at hz
  have hq:=BalancedField.constants
  unfold lowNormalize signedDecode at *
  norm_num only [Nat.reduceSub,Nat.reducePow] at *
  by_cases hn : centerFp Y<0
  · have ge : 2^255≤centerWord Y := hs.mpr hn
    norm_num only [Nat.reducePow] at ge
    have hdec : ¬centerWord Y<57896044618658097711785492504343953926634992332820282019728792003956564819968 := by omega
    simp only [if_neg hdec] at hd
    have pos : 0≤ -centerFp Y-1 := by omega
    have tn:=Int.toNat_of_nonneg pos
    simp [hn]
    omega
  · have lt : centerWord Y<2^255 := by have :=hs.not.mpr hn;omega
    norm_num only [Nat.reducePow] at lt
    simp only [if_pos lt] at hd
    have pos : 0≤centerFp Y := by omega
    have tn:=Int.toNat_of_nonneg pos
    simp [hn]
    omega
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT FrontMath
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraphFp
open Arithmetic Secp256k1 Arithmetic.BalancedField

theorem encoded_positive (y : Nat) (sigma sy h : Bool) (t : Int)
 (eq : t=(3-2*(sigma.toNat:Int))*(y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(h.toNat:Int)*(p:Int)) :
 encodeWord 256 t=
 ((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256 := by
 have corr:=TerminalGraph.positive_correction (y:Int) t (h.toNat:Int) (sigma.toNat:Int) (sy.toNat:Int) eq
 apply Int.ofNat_injective
 change (encodeWord 256 t:Int)=((((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256 : Nat):Int)
 rw [encodeWord_cast,Int.natCast_emod]
 cases sigma <;> cases sy <;> cases h <;>
   norm_num [TerminalGraph.C,TerminalGraph.M] at corr ⊢ <;> omega

theorem encoded_parity (y : Nat) (sigma sy h : Bool) (t : Int)
 (eq : t=(3-2*(sigma.toNat:Int))*(y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(h.toNat:Int)*(p:Int)) :
 (Nat.testBit (encodeWord 256 t) 0 ^^ Nat.testBit y 0)=h := by
 have e:=encoded_positive y sigma sy h t eq
 rw [e,Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq]
 simp only [Nat.pow_zero,Nat.div_one]
 have parityEq : (((if sigma then y else 3*y)+2*(sy && !sigma).toNat+h.toNat*(2^32+977))%2^256)%2=(y+h.toNat)%2 := by
   cases sigma <;> cases sy <;> cases h <;> norm_num at * <;> omega
 rw [parityEq]
 cases h <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero]
 · simp
 · have bound : y%2<2:=Nat.mod_lt _ (by omega)
   by_cases h0:y%2=0
   · have h1 : (y+1)%2=1:=by omega
     simp [h0,h1]
   · have h1 : y%2=1:=by omega
     have h2 : (y+1)%2=0:=by omega
     simp [h1,h2]
def frontY (Y : Fp) : Nat := (if centerFp Y<0 then -centerFp Y-1 else centerFp Y).toNat

def frontR (Y : Fp) (sigma : Bool) : Nat :=
 if centerFp Y<0 then 2^256-1-centerWord ((if sigma then 1 else 3)*Y)
 else centerWord ((if sigma then 1 else 3)*Y)

def frontH (Y : Fp) (sigma : Bool) : Bool := Nat.testBit (frontR Y sigma) 0 ^^ Nat.testBit (frontY Y) 0

theorem actual_front_equations (Y : Fp) (sigma : Bool) :
 frontR Y sigma=((if sigma then frontY Y else 3*frontY Y)+
  2*(decide (centerFp Y<0) && !sigma).toNat+(frontH Y sigma).toNat*(2^32+977))%2^256 ∧
 frontH Y sigma=(!sigma && !decide (frontY Y<((p-1)/2)/3+(!decide (centerFp Y<0)).toNat)) := by
 let sy:=decide (centerFp Y<0)
 let yi:=if centerFp Y<0 then -centerFp Y-1 else centerFp Y
 let ti:=if centerFp Y<0 then -centerFp ((if sigma then 1 else 3)*Y)-1 else centerFp ((if sigma then 1 else 3)*Y)
 have norm : ∃h:Int,(h=0 ∨ h=1) ∧ 0≤yi ∧ -TerminalGraph.Q-(sy.toNat:Int)≤ti ∧ ti≤TerminalGraph.Q ∧
   ti=(3-2*(sigma.toNat:Int))*yi+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-h*(p:Int) ∧ (sigma=true→h=0) := by
   have nn:=normalized_bridge Y sigma
   cases sigma <;> by_cases hs:centerFp Y<0 <;> simpa [sy,yi,ti,hs] using nn
 obtain ⟨h,hh,hy,hlo,hhi,he,hzero⟩:=norm
 let hb:=decide (h=1)
 have hc : (hb.toNat:Int)=h := by
   rcases hh with h0|h1
   · simp [hb,h0]
   · simp [hb,h1]
 have yc : (frontY Y:Int)=yi := Int.toNat_of_nonneg hy
 have he' : ti=(3-2*(sigma.toNat:Int))*(frontY Y:Int)+2*(1-(sigma.toNat:Int))*(sy.toNat:Int)-(hb.toNat:Int)*(p:Int) := by rw [yc,hc];exact he
 have rwrd : frontR Y sigma=encodeWord 256 ti := by
   by_cases hs:centerFp Y<0
   · simpa [frontR,ti,hs] using full_complement_word ((if sigma then 1 else 3)*Y)
   · simp [frontR,ti,hs,centerWord]
 have par : frontH Y sigma=hb := by
   unfold frontH
   rw [rwrd]
   exact encoded_parity _ _ _ _ _ he'
 constructor
 · rw [par,rwrd]
   exact encoded_positive _ _ _ _ _ he'
 · rw [par]
   have threshold : hb=(!sigma && !decide (frontY Y<((p-1)/2)/3+(!sy).toNat)) := by
     cases eqs:sigma with
     | true =>
       have hz:=hzero eqs
       simp [hb,hz]
     | false =>
       have hef : ti=3*yi+2*(sy.toNat:Int)-h*(p:Int) := by simpa [eqs] using he
       have hs : (sy.toNat:Int)=0 ∨ (sy.toNat:Int)=1 := by cases sy <;> simp
       have ht:=TerminalGraph.quotient_threshold yi ti h (sy.toNat:Int) hy hs hh hef ⟨hlo,hhi⟩
       have yn : 0≤(frontY Y:Int):=by omega
       norm_num [TerminalGraph.Q,p] at ht ⊢
       dsimp [hb]
       by_cases sign:sy=true
       · simp [sign] at ht ⊢
         rw [←yc] at ht
         by_cases hp:h=1 <;> simp [hp] at ht ⊢ <;> omega
       · have sf:sy=false:=Bool.eq_false_iff.mpr sign
         simp [sf] at ht ⊢
         rw [←yc] at ht
         by_cases hp:h=1 <;> simp [hp] at ht ⊢ <;> omega
   simpa [sy] using threshold
end ECDSAAdd.Entrant.TerminalGraphFp


-- TERMINAL GRAPH COMPONENT ActualFront
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField TerminalGraphFp

theorem normalized_low_word (Y : Fp) :
 (if decide (centerFp Y<0) then 2^255-1-centerWord Y%2^255 else centerWord Y%2^255)=frontY Y := by
 have h:=low_complement_word Y
 have hs:=centerWord_sign Y
 by_cases neg:centerFp Y<0
 · simp [lowNormalize,frontY,neg] at h ⊢
   omega
 · have lt:centerWord Y<2^255:=by have nn:=hs.not.mpr neg;omega
   simp [lowNormalize,frontY,neg] at h ⊢
   simpa only[Nat.reducePow] using (Nat.mod_eq_of_lt lt).trans h

theorem actual_front_values (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (Y : Fp) (sigma : Bool)
 (ys : regValue L.y b=centerWord Y)
 (rs : regValue L.r b=centerWord ((if sigma then 1 else 3)*Y))
 (sig : b L.sigma=sigma) (hc:b L.h=false) (bc:b L.bias=false) :
 let f:=frontBasis L b
 regValue (L.y.take 255) f=frontY Y ∧ regValue L.r f=frontR Y sigma ∧
 f L.h=frontH Y sigma ∧ f L.bias=(decide (centerFp Y<0) && !sigma) ∧
 f L.sigma=sigma ∧ f (L.Y 255)=decide (centerFp Y<0) := by
 have msb:b (L.Y 255)=decide (centerFp Y<0) := by
   have g:=getD_testBit L.y 255 b (by have len:=hw.1;omega)
   rw[ys,centerWord_msb] at g
   exact g
 have fy:regValue (L.y.take 255) (frontBasis L b)=frontY Y := by
   rw[front_low_value L hw hn,ys,msb]
   exact normalized_low_word Y
 have fr:regValue L.r (frontBasis L b)=frontR Y sigma := by
   rw[front_r_value L hw hn,rs,msb]
   simp only[frontR]
   split_ifs <;>simp_all
 have fh:frontBasis L b L.h=frontH Y sigma := by
   rw[front_h_value L hw hn b hc,fy,fr]
   rfl
 refine ⟨fy,fr,fh,?_,?_,?_⟩
 · rw[front_bias L hw hn b bc,msb,sig]
 · rw[front_source_sigma L hn b,sig]
 · rw[front_on_banks L hn b (L.Y 255) (Or.inl (y_mem L hw 255 (by omega)))]
   simp only[complementBasis,if_neg (normalize_nd L hw hn).2,msb]

theorem actual_front_scalar (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (Y : Fp) (sigma : Bool)
 (ys : regValue L.y b=centerWord Y)
 (rs : regValue L.r b=centerWord ((if sigma then 1 else 3)*Y))
 (sig : b L.sigma=sigma) (hc:b L.h=false) (bc:b L.bias=false) :
 let f:=frontBasis L b
 regValue L.r f=((if f L.sigma then regValue (L.y.take 255) f else 3*regValue (L.y.take 255) f)+
   2*(f L.bias).toNat+(f L.h).toNat*(2^32+977))%2^256 ∧
 f L.h=(!f L.sigma && !(decide (regValue (L.y.take 255) f<((p-1)/2)/3+(!f (L.Y 255)).toNat))) := by
 have v:=actual_front_values L hw hn b Y sigma ys rs sig hc bc
 dsimp only
 rw[v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2]
 exact actual_front_equations Y sigma
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddCarrySteps
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def aStepValue (L : DecoderLayout) (s : BasisState) (i : Nat) : Bool:=
 if i=0 then carryBit false (s L.sigma) (s (L.Y 0) ^^ s L.sigma)
 else carryBit (s (L.Y (i-1))) (s (L.Y i) ^^ s L.sigma) (s (L.A (i-1)))

theorem step_nd (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (h0 : i≠0) :
    [L.Y i,L.A (i-1),L.A i].Nodup := by
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
  not_or,not_false_eq_true,and_true]
 exact ⟨⟨y_ne_a L hw hn i (i-1) (by omega) (by omega),
   y_ne_a L hw hn i i (by omega) hi⟩,
   carry_ne_carry L hw hn (i-1) i (by omega) hi (by omega)⟩

theorem step_source_away (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (h0 : i≠0) :
    ∀q∈(some (L.Y (i-1))),q∉[L.Y i,L.A (i-1),L.A i] := by
 intro q hq
 have eq:L.Y (i-1)=q:=by simpa using hq
 subst q
 simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
 exact ⟨y_ne_y L hw hn (i-1) i (by omega) (by omega) (by omega),
   y_ne_a L hw hn (i-1) (i-1) (by omega) (by omega),
   y_ne_a L hw hn (i-1) i (by omega) hi⟩

theorem addCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (s : State) (m : List Bool) :
    run (addCarry L i) m s=
      ⟨s.phase,writeBit s.basis (L.A i) (s.basis (L.A i) ^^ aStepValue L s.basis i)⟩ := by
 by_cases h0:i=0
 · subst i
   have sy:=sigma_ne_y L hw hn 0 (by omega)
   have sa:=sigma_ne_a L hw hn 0 (by omega)
   have ya:=y_ne_a L hw hn 0 0 (by omega) (by omega)
   change run (cxWindow L.sigma (L.Y 0) [.CCX L.sigma (L.Y 0) (L.A 0)]) m s=_
   apply cxWindow_write L.sigma (L.Y 0) (L.A 0) _ sy sa ya
   intro r
   simp [run,cxBasis,writeBit,sy,Ne.symm sy,Ne.symm sa,Ne.symm ya,aStepValue,carryBit]
 · have h:=windowMajority_run (⟨some (L.Y (i-1)),false⟩ : MappedBit)
     L.sigma (L.Y i) (L.A (i-1)) (L.A i) (step_nd L hw hn i hi h0)
     (step_source_away L hw hn i hi h0) (sigma_ne_y L hw hn i (by omega))
     (sigma_ne_a L hw hn i hi) s m
   simpa only [addCarry,h0,ite_false,cxWindow,mappedMajority,Bool.false_eq_true,
     aStepValue,MappedBit.value,Bool.xor_false,Bool.false_xor,Option.map_some,Option.getD_some] using h

theorem eraseAddCarry_run (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i<255) (s : State) (m : List Bool)
    (known : s.basis (L.A i)=aStepValue L s.basis i) :
    run (eraseAddCarry L i) m s=⟨s.phase,writeBit s.basis (L.A i) false⟩ := by
 by_cases h0:i=0
 · subst i
   have sy:=sigma_ne_y L hw hn 0 (by omega)
   have sa:=sigma_ne_a L hw hn 0 (by omega)
   have ya:=y_ne_a L hw hn 0 0 (by omega) (by omega)
   have nd:[L.sigma,L.Y 0,L.A 0].Nodup:=by simp [sy,sa,ya]
   change run (cxWindow L.sigma (L.Y 0)
     (mappedEraseCarry ⟨none,false⟩ L.sigma (L.Y 0) (L.A 0))) m s=_
   apply cxWindow_write L.sigma (L.Y 0) (L.A 0) _ sy sa ya
   intro r
   apply mappedEraseCarry_correct ⟨none,false⟩ L.sigma (L.Y 0) (L.A 0) nd (by simp)
   simpa [cxBasis,writeBit,sy,Ne.symm sy,Ne.symm ya,MappedBit.value,aStepValue] using known
 · have h:=windowErase_run (⟨some (L.Y (i-1)),false⟩ : MappedBit)
     L.sigma (L.Y i) (L.A (i-1)) (L.A i) (step_nd L hw hn i hi h0)
     (step_source_away L hw hn i hi h0) (sigma_ne_y L hw hn i (by omega))
     (sigma_ne_a L hw hn i hi) s m (by simpa [aStepValue,h0,MappedBit.value] using known)
   simpa only [eraseAddCarry,h0,ite_false,cxWindow,mappedEraseCarry,Bool.false_eq_true] using h
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddChain
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic

def aExpected (L : DecoderLayout) (origin : BasisState) : Nat→Bool
 | 0 => carryBit false (origin L.sigma) (origin (L.Y 0) ^^ origin L.sigma)
 | j+1 => carryBit (origin (L.Y j)) (origin (L.Y (j+1)) ^^ origin L.sigma) (aExpected L origin j)

structure AddFrame (L : DecoderLayout) (origin : State) (nDone : Nat) (s : State) : Prop where
 phase : s.phase=origin.phase
 sigma : s.basis L.sigma=origin.basis L.sigma
 source : ∀ i, i<256 → s.basis (L.Y i)=origin.basis (L.Y i)
 computed : ∀ i, i< nDone → s.basis (L.A i)=aExpected L origin.basis i
 clean : ∀ i, nDone≤ i → i<255 → s.basis (L.A i)=false

theorem addFrame_initial (L : DecoderLayout) (s : State)
 (clean : ∀ i, i<255 → s.basis (L.A i)=false) : AddFrame L s 0 s := by
 refine ⟨rfl,rfl,fun _ _=>rfl,?_,?_⟩
 · intro i hi;omega
 · intro i _ hi;exact clean i hi

theorem value_expected (L : DecoderLayout) (origin s : State) (nDone i : Nat)
 (f : AddFrame L origin nDone s) (hi : i<255) (hd : i≤nDone) :
 aStepValue L s.basis i=aExpected L origin.basis i := by
 by_cases h0:i=0
 · subst i
   simp only [aStepValue,ite_true,aExpected]
   rw [f.sigma,f.source 0 (by omega)]
 · obtain ⟨j,rfl⟩:∃j,i=j+1:=⟨i-1,by omega⟩
   simp only [aStepValue,Nat.add_sub_cancel,show ¬j+1=0 by omega,ite_false,aExpected]
   rw [f.source j (by omega),f.source (j+1) (by omega),f.sigma,f.computed j (by omega)]

theorem addFrame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hi : i<255) (f : AddFrame L origin i s) (m : List Bool) :
 AddFrame L origin (i+1) (run (addCarry L i) m s) := by
 have val:=value_expected L origin s i i f hi (le_refl _)
 have zero:=f.clean i (le_refl _) hi
 rw [addCarry_run L hw hn i hi s m,zero,val,Bool.false_xor]
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · simpa only [writeBit,Function.update_of_ne (sigma_ne_a L hw hn i hi)] using f.sigma
 · intro j hj
   simpa only [writeBit,Function.update_of_ne (y_ne_a L hw hn j i hj hi)] using f.source j hj
 · intro j hj
   by_cases eq:j=i
   · subst j;simp [writeBit]
   · have ne:=carry_ne_carry L hw hn j i (by omega) hi eq
     simpa only [writeBit,Function.update_of_ne ne] using f.computed j (by omega)
 · intro j hji hj
   have ne:=carry_ne_carry L hw hn j i hj hi (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem addFrame_erase_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hi : i<255) (f : AddFrame L origin (i+1) s) (m : List Bool) :
 AddFrame L origin i (run (eraseAddCarry L i) m s) := by
 have val:=value_expected L origin s (i+1) i f hi (by omega)
 have known:s.basis (L.A i)=aStepValue L s.basis i:=(f.computed i (by omega)).trans val.symm
 rw [eraseAddCarry_run L hw hn i hi s m known]
 refine ⟨f.phase,?_,?_,?_,?_⟩
 · simpa only [writeBit,Function.update_of_ne (sigma_ne_a L hw hn i hi)] using f.sigma
 · intro j hj
   simpa only [writeBit,Function.update_of_ne (y_ne_a L hw hn j i hj hi)] using f.source j hj
 · intro j hj
   have ne:=carry_ne_carry L hw hn j i (by omega) hi (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.computed j (by omega)
 · intro j hji hj
   by_cases eq:j=i
   · subst j;simp [writeBit]
   · have ne:=carry_ne_carry L hw hn j i hj hi eq
     simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem add_forward_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : AddFrame L origin 0 s) (n : Nat) (bound : n≤255) (m : List Bool) :
 AddFrame L origin n (run ((List.range n).flatMap (addCarry L)) m s) := by
 induction n generalizing m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   apply addFrame_step L hw hn origin _ n (by omega)
   exact ih (by omega) _

theorem add_reverse_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (n : Nat) (bound : n≤255) (s : State) (f : AddFrame L origin n s) (m : List Bool) :
 AddFrame L origin 0 (run ((List.range n).reverse.flatMap (eraseAddCarry L)) m s) := by
 induction n generalizing s m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   apply ih (by omega)
   exact addFrame_erase_step L hw hn origin s n (by omega) f _
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT AddOutside
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry

theorem add_forward_outside (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (n : Nat) (bound : n ≤ 255) (s : State) (m : List Bool) (q : Wire)
 (away : q ∉ L.carry) :
 (run ((List.range n).flatMap (addCarry L)) m s).basis q=s.basis q := by
 induction n generalizing m with
 | zero => simp [run]
 | succ n ih =>
   rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   rw [addCarry_run L hw hn n (by omega)]
   have ne:q ≠ L.A n := fun e => away (e ▸ a_mem L hw n (by omega))
   simp only [writeBit,Function.update_of_ne ne]
   exact ih (by omega) _

theorem add_reverse_outside (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (n : Nat) (bound : n ≤ 255) (s : State)
 (f : AddFrame L origin n s) (m : List Bool) (q : Wire) (away : q ∉ L.carry) :
 (run ((List.range n).reverse.flatMap (eraseAddCarry L)) m s).basis q=s.basis q := by
 induction n generalizing s m with
 | zero => simp [run]
 | succ n ih =>
   rw [List.range_succ,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take]
   have f' := addFrame_erase_step L hw hn origin s n (by omega) f m
   rw [ih (by omega) _ f' _]
   have val:=value_expected L origin s (n+1) n f (by omega) (by omega)
   have known:s.basis (L.A n)=aStepValue L s.basis n := (f.computed n (by omega)).trans val.symm
   rw [eraseAddCarry_run L hw hn n (by omega) s m known]
   have ne:q ≠ L.A n := fun e => away (e ▸ a_mem L hw n (by omega))
   simp only [writeBit,Function.update_of_ne ne]
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT StreamReverse
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run xorList streamCarry eraseCorrectionCarry

theorem stream_to_erase (L : DecoderLayout) (origin s : State)
 (f : StreamFrame L origin 255 s) : EraseBFrame L origin 255 s := by
 refine ⟨f.phase,f.outside,f.stored,?_⟩
 intro j hj hbound
 have eq:j=255:=by omega
 subst j
 exact f.current

theorem eraseBFrame_step (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (i : Nat) (hlo : 1 ≤ i) (hi : i ≤ 255)
 (graph : BGraph L origin.basis) (f : EraseBFrame L origin i s) (m : List Bool) :
 EraseBFrame L origin (i-1) (run (eraseCorrectionCarry L i) m s) := by
 rw [eraseCorrectionCarry_run L hw hn origin s i hlo hi graph f m]
 refine ⟨f.phase,?_,?_,?_⟩
 · intro q hq
   have ne:q≠L.R (i-1):=fun e=>hq (e ▸ r_mem L hw (i-1) (by omega))
   simpa only [writeBit,Function.update_of_ne ne] using f.outside q hq
 · intro j hj
   have ne:=r_ne_r L hw hn j (i-1) (by omega) (by omega) (by omega)
   simpa only [writeBit,Function.update_of_ne ne] using f.live j (by omega)
 · intro j hji hj
   by_cases eq:j=i-1
   · subst j;simp [writeBit]
   · have ne:=r_ne_r L hw hn j (i-1) hj (by omega) eq
     simpa only [writeBit,Function.update_of_ne ne] using f.clean j (by omega) hj

theorem eraseB_reverse_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (graph : BGraph L origin.basis) (n : Nat) (bound : n ≤ 255)
 (s : State) (f : EraseBFrame L origin n s) (m : List Bool) :
 EraseBFrame L origin 0 (run ((List.range' 1 n).reverse.flatMap (eraseCorrectionCarry L)) m s) := by
 induction n generalizing s m with
 |zero=>simpa [run] using f
 |succ n ih=>
   rw [List.range'_1_concat,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,run_append,run_take,Nat.add_comm 1 n]
   apply ih (by omega)
   have a:=eraseBFrame_step L hw hn origin s (n+1) (by omega) bound graph f
     m
   simpa only [Nat.add_sub_cancel] using a

def bBlock (L : DecoderLayout) : Program:=
 xorList (bSources L 0) (L.R 0)++(List.range' 1 255).flatMap (streamCarry L)++
   (List.range' 1 255).reverse.flatMap (eraseCorrectionCarry L)

theorem bBlock_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : State) (graph : BGraph L origin.basis)
 (low : origin.basis (L.R 0)=parity (bSources L 0) origin.basis) (m : List Bool) :
 (run (bBlock L) m origin).phase=origin.phase ∧
 (∀q,q∉L.r → (run (bBlock L) m origin).basis q=origin.basis q) ∧
 ∀i,i<256 → (run (bBlock L) m origin).basis (L.R i)=false := by
 have f : EraseBFrame L origin 0 (run (bBlock L) m origin) := by
   rw [bBlock,List.append_assoc,run_append,run_take]
   rw [run_append,run_take]
   apply eraseB_reverse_frame L hw hn origin graph 255 (le_refl _)
   apply stream_to_erase
   apply stream_forward_frame L hw hn origin _ _ 255 (le_refl _)
   exact stream_initial L hw hn origin _ low
 exact ⟨f.phase,f.outside,fun i hi=>f.clean i (by omega) hi⟩
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CoreStages
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry bBlock

def aProgram (L : DecoderLayout) : Program := (List.range 255).flatMap (addCarry L)
def eraseAProgram (L : DecoderLayout) : Program := (List.range 255).reverse.flatMap (eraseAddCarry L)

theorem aProgram_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false) (m : List Bool) :
 AddFrame L s 255 (run (aProgram L) m s) :=
 add_forward_frame L hw hn s s (addFrame_initial L s clean) 255 (le_refl _) m

theorem eraseAProgram_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin s : State) (f : AddFrame L origin 255 s) (m : List Bool) :
 AddFrame L origin 0 (run (eraseAProgram L) m s) :=
 add_reverse_frame L hw hn origin 255 (le_refl _) s f m

attribute [local irreducible] aProgram eraseAProgram

theorem bBlock_addFrame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin a : State) (af : AddFrame L origin 255 a)
 (graph : BGraph L a.basis) (low : a.basis (L.R 0)=parity (bSources L 0) a.basis)
 (m : List Bool) : AddFrame L origin 255 (run (bBlock L) m a) := by
 have bc:=bBlock_correct L hw hn a graph low m
 refine ⟨bc.1.trans af.phase,?_,?_,?_,?_⟩
 · exact (bc.2.1 L.sigma (source_r_away L hn _ (by tauto))).trans af.sigma
 · intro i hi
   exact (bc.2.1 (L.Y i) (source_r_away L hn _ (Or.inl (y_mem L hw i hi)))).trans (af.source i hi)
 · intro i hi
   exact (bc.2.1 (L.A i) (source_r_away L hn _ (Or.inr (Or.inl (a_mem L hw i hi))))).trans (af.computed i hi)
 · intro i hi hb;omega
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CarryMath
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalCarryMath
open Arithmetic

def value : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def sums : List Bool → List Bool → Bool → List Bool
  | a::as,b::bs,c => sumBit a b c::sums as bs (carryBit a b c)
  | _,_,_ => []

def carryAt : List Bool → List Bool → Bool → Nat → Bool
  | _,_,c,0 => c
  | a::as,b::bs,c,n+1 => carryAt as bs (carryBit a b c) n
  | _,_,_,_ => false

theorem sums_length (A B : List Bool) (c : Bool) (hlen : A.length=B.length) :
    (sums A B c).length=A.length := by
  induction A generalizing B c with
  | nil => cases B <;> simp_all [sums]
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs => simp only [sums,List.length_cons];rw [ih bs _ (by simpa using hlen)]

theorem sums_value (A B : List Bool) (c : Bool) (hlen : A.length=B.length) :
    value (sums A B c)=(value A+value B+c.toNat)%2^A.length := by
  induction A generalizing B c with
  | nil => cases B with
    | nil => cases c <;> decide
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      simp only [sums,value,List.length_cons]
      rw [ih bs _ (by simpa using hlen)]
      exact sum_value_step a b c (value as) (value bs) as.length

theorem value_injective (A B : List Bool) (hlen : A.length=B.length)
    (hv : value A=value B) : A=B := by
  induction A generalizing B with
  | nil => cases B <;> simp_all
  | cons a as ih =>
    cases B with
    | nil => simp at hlen
    | cons b bs =>
      have head : a=b := by
        cases a <;> cases b <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> omega
      subst b
      have tail : value as=value bs := by simp only [value] at hv;omega
      rw [ih bs (by simpa using hlen) tail]

theorem graph_eq_sums (A B R : List Bool) (c : Bool)
    (hlen : A.length=B.length) (hr : R.length=A.length)
    (hv : value R=(value A+value B+c.toNat)%2^A.length) : R=sums A B c :=
  value_injective R _ (hr.trans (sums_length A B c hlen).symm)
    (hv.trans (sums_value A B c hlen).symm)

theorem sums_at (A B : List Bool) (c : Bool) (i : Nat)
    (hlen : A.length=B.length) (hi : i<A.length) :
    (sums A B c).getD i false=
      sumBit (A.getD i false) (B.getD i false) (carryAt A B c i) := by
  induction i generalizing A B c with
  | zero =>
    cases A with
    | nil => simp at hi
    | cons a as => cases B with
      | nil => simp at hlen
      | cons b bs => rfl
  | succ i ih =>
    cases A with
    | nil => simp at hi
    | cons a as => cases B with
      | nil => simp at hlen
      | cons b bs =>
        simpa only [sums,carryAt,List.getD_cons_succ] using
          ih as bs (carryBit a b c) (by simpa using hlen) (by simpa using hi)

theorem graph_carry_extract (A B R : List Bool) (c : Bool) (i : Nat)
    (hlen : A.length=B.length) (hr : R.length=A.length)
    (hv : value R=(value A+value B+c.toNat)%2^A.length) (hi : i<A.length) :
    carryAt A B c i=R.getD i false ^^ A.getD i false ^^ B.getD i false := by
  rw [graph_eq_sums A B R c hlen hr hv,sums_at A B c i hlen hi]
  cases A.getD i false <;> cases B.getD i false <;> cases carryAt A B c i <;> decide
end ECDSAAdd.Entrant.TerminalCarryMath


-- TERMINAL GRAPH COMPONENT GraphValues
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic TerminalCarryMath

def bitVector (n : Nat) (f : Nat → Bool) : List Bool := (List.range n).map f
@[simp] theorem bitVector_length (n : Nat) (f : Nat → Bool) : (bitVector n f).length=n := by simp [bitVector]
theorem bitVector_get (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i<n) :
 (bitVector n f).getD i false=f i := by
 rw [List.getD_eq_getElem _ _ (by simpa using hi)]
 simp [bitVector]

theorem carryAt_next (A B : List Bool) (c : Bool) (i : Nat)
 (ha : i<A.length) (hb : i<B.length) :
 carryAt A B c (i+1)=carryBit (A.getD i false) (B.getD i false) (carryAt A B c i) := by
 induction i generalizing A B c with
 | zero => cases A with
   | nil => simp at ha
   | cons a as => cases B with
     | nil => simp at hb
     | cons b bs => simp [carryAt]
 | succ i ih => cases A with
   | nil => simp at ha
   | cons a as => cases B with
     | nil => simp at hb
     | cons b bs => simpa only [carryAt,List.getD_cons_succ] using ih as bs (carryBit a b c) (by simpa using ha) (by simpa using hb)

theorem correctionSources_parity (L : DecoderLayout) (i : Nat) (s : BasisState) :
 parity (correctionSources L i) s=(correction L i).value s := by
 unfold correctionSources correction
 split_ifs <;> simp [MappedBit.value,parity]

theorem parity_cat (xs ys : List Wire) (s : BasisState) :
 parity (xs++ys) s=(parity xs s ^^ parity ys s) := by
 induction xs with
 | nil => simp [parity]
 | cons x xs ih =>
   change (s x ^^ parity (xs++ys) s)=((s x ^^ parity xs s) ^^ parity ys s)
   rw [ih,Bool.xor_assoc]

def rawBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>parity (rawSources L i) s)
def correctionBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>(correction L i).value s)
def resultBits (L : DecoderLayout) (s : BasisState) : List Bool := bitVector 256 (fun i=>s (L.R i))

theorem graph_of_bit_values (L : DecoderLayout) (s : BasisState)
 (hv : value (resultBits L s)=(value (rawBits L s)+value (correctionBits L s))%2^256) :
 BGraph L s ∧ s (L.R 0)=parity (bSources L 0) s := by
 let A:=rawBits L s
 let B:=correctionBits L s
 let R:=resultBits L s
 have la:A.length=256:=bitVector_length _ _
 have lb:B.length=256:=bitVector_length _ _
 have lr:R.length=256:=bitVector_length _ _
 have av (i : Nat) (hi : i<256) : A.getD i false=parity (rawSources L i) s:=bitVector_get _ _ _ hi
 have bv (i : Nat) (hi : i<256) : B.getD i false=(correction L i).value s:=bitVector_get _ _ _ hi
 have rv (i : Nat) (hi : i<256) : R.getD i false=s (L.R i):=bitVector_get _ _ _ hi
 have val : value R=(value A+value B+false.toNat)%2^A.length := by simpa [la] using hv
 have extract (i : Nat) (hi : i<256) : carryAt A B false i=bExpected L s i := by
   have old:=graph_carry_extract A B R false i (la.trans lb.symm) (lr.trans la.symm) val (by omega)
   have e : carryAt A B false i=(R.getD i false ^^ A.getD i false ^^ B.getD i false) := by
     cases hc:carryAt A B false i <;> cases hr:R.getD i false <;> cases ha:A.getD i false <;> cases hb:B.getD i false <;> simp_all
   rw [rv i hi,av i hi,bv i hi] at e
   rw [e]
   simp only [bExpected,bSources,parity_cat,correctionSources_parity,Bool.xor_assoc]
 constructor
 · intro i hl hi
   rw [←extract i (by omega)]
   have eq : i-1+1=i:=by omega
   have step:=carryAt_next A B false (i-1) (by omega) (by omega)
   rw [eq] at step
   rw [step]
   have prev : carryAt A B false (i-1)=(if i=1 then false else bExpected L s (i-1)) := by
     split_ifs with e
     · subst i;rfl
     · exact extract _ (by omega)
   rw [prev,av (i-1) (by omega),bv (i-1) (by omega)]
   cases (correction L (i-1)).value s <;> cases parity (rawSources L (i-1)) s <;> cases (if i=1 then false else bExpected L s (i-1)) <;> decide
 · have e:=sums_at A B false 0 (la.trans lb.symm) (by rw [la];omega)
   have eq:=graph_eq_sums A B R false (la.trans lb.symm) (lr.trans la.symm) val
   rw [←eq] at e
   rw [rv 0 (by omega),av 0 (by omega),bv 0 (by omega)] at e
   simpa [bSources,parity_cat,correctionSources_parity,sumBit,carryAt] using e
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT GraphRaw
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic TerminalCarryMath

theorem value_append_bits (xs ys : List Bool) :
 value (xs++ys)=value xs+2^xs.length*value ys := by
 induction xs with
 | nil => simp [value]
 | cons x xs ih => simp only [List.cons_append,value,List.length_cons,ih,Nat.pow_succ];ring

theorem value_map_register (xs : List Wire) (s : BasisState) : value (xs.map s)=regValue xs s := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
   change (s x).toNat+2*value (xs.map s)=(if s x then 1 else 0)+2*regValue xs s
   rw [ih];cases s x <;> rfl

theorem getD_map_valid {α β : Type} (xs : List α) (f : α→β) (d : α) (e : β) (i : Nat) (hi : i<xs.length) :
 (xs.map f).getD i e=f (xs.getD i d) := by
 rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
 simp

theorem bitVector_register (xs : List Wire) (s : BasisState) :
 bitVector xs.length (fun i=>s (xs.getD i 0))=xs.map s := by
 apply List.ext_getElem (by simp)
 intro i hi hj
 have bound:i<xs.length:=by simpa using hi
 rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj]
 rw [bitVector_get _ _ _ bound,getD_map_valid xs s 0 false i bound]

theorem resultBits_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 value (resultBits L s)=regValue L.r s := by
 change value (bitVector 256 (fun i=>s (L.r.getD i 0)))=_
 rw [←hw.2.1,bitVector_register,value_map_register]

theorem complement_value (xs : List Bool) : value (xs.map not)=2^xs.length-1-value xs := by
 have hs : value (xs.map not)+value xs+1=2^xs.length := by
   induction xs with
   | nil => rfl
   | cons x xs ih => simp only [List.map_cons,value,List.length_cons,Nat.pow_succ];cases x <;> simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false] <;> omega
 omega

def lowBits (L : DecoderLayout) (s : BasisState) : List Bool := (L.y.take 255).map s

theorem lowBits_length (L : DecoderLayout) (hw : L.Widths) (s : BasisState) : (lowBits L s).length=255 := by simp [lowBits,hw.1]

theorem lowBits_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<255) :
 (lowBits L s).getD i false=s (L.Y i) := by
 unfold lowBits DecoderLayout.Y
 rw [getD_map_valid _ s 0 false i (by simp [hw.1];omega)]
 rw [List.getD_eq_getElem _ _ (by simp [hw.1];omega),List.getD_eq_getElem _ _ (by rw [hw.1];omega)]
 simp [lowBits,DecoderLayout.Y]

def sourceA (L : DecoderLayout) (s : BasisState) : List Bool := false::lowBits L s
def sourceB (L : DecoderLayout) (s : BasisState) : List Bool := (lowBits L s++[false]).map (fun b=>b^^s L.sigma)

theorem sources_length (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 (sourceA L s).length=256 ∧ (sourceB L s).length=256 := by simp [sourceA,sourceB,lowBits_length L hw s]

theorem sources_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState) :
 (value (sourceA L s)+value (sourceB L s)+(s L.sigma).toNat)%2^256=
 (if s L.sigma then regValue (L.y.take 255) s else 3*regValue (L.y.take 255) s)%2^256 := by
 have vy : value (lowBits L s)=regValue (L.y.take 255) s:=value_map_register _ _
 have ly:=lowBits_length L hw s
 have h:=regValue_lt (L.y.take 255) s
 have ln : (L.y.take 255).length=255:=by simp [hw.1]
 rw [ln] at h
 cases eq:s L.sigma with
 | false => simp [sourceA,sourceB,eq,value_append_bits,value,vy];congr 1;omega
 | true =>
   have bb : sourceB L s=(lowBits L s++[false]).map not := by
     simp only [sourceB,eq];congr 1;funext b;cases b <;> rfl
   rw [bb,complement_value]
   simp only [sourceA,value,List.length_append,List.length_singleton,ly,value_append_bits,vy,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,eq,Bool.toNat_true,ite_true]
   norm_num only [Nat.reducePow] at h ⊢
   omega
theorem sourceA_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<256) :
 (sourceA L s).getD i false=(if i=0 then false else s (L.Y (i-1))) := by
 cases i with
 | zero => rfl
 | succ i => simpa only [sourceA,List.getD_cons_succ,Nat.add_sub_cancel,show ¬i+1=0 by omega,ite_false] using lowBits_get L hw s i (by omega)

theorem sourceB_get (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<256) :
 (sourceB L s).getD i false=(if i<255 then s (L.Y i) ^^ s L.sigma else s L.sigma) := by
 unfold sourceB
 rw [getD_map_valid _ _ false false i (by simp [lowBits_length L hw s];omega)]
 by_cases h:i<255
 · rw [if_pos h,List.getD_append _ _ _ _ (by rw [lowBits_length L hw s];omega),lowBits_get L hw s i h]
 · have e:i=255:=by omega
   subst i
   rw [List.getD_eq_getElem _ _ (by simp [lowBits_length L hw s])]
   simp [List.getElem_append,lowBits_length L hw s]

theorem source_carry (L : DecoderLayout) (hw : L.Widths) (s : BasisState) (i : Nat) (hi : i<255) :
 carryAt (sourceA L s) (sourceB L s) (s L.sigma) (i+1)=aExpected L s i := by
 induction i with
 | zero =>
   rw [carryAt_next _ _ _ 0 (by rw [(sources_length L hw s).1];omega) (by rw [(sources_length L hw s).2];omega),sourceA_get L hw s 0 (by omega),sourceB_get L hw s 0 (by omega)]
   simp only [ite_true,show 0<255 by omega,aExpected,carryAt]
   cases s L.sigma <;> cases s (L.Y 0) <;> decide
 | succ i ih =>
   rw [carryAt_next _ _ _ (i+1) (by rw [(sources_length L hw s).1];omega) (by rw [(sources_length L hw s).2];omega),sourceA_get L hw s (i+1) (by omega),sourceB_get L hw s (i+1) (by omega),ih (by omega)]
   simp [aExpected,show ¬i+1=0 by omega,show i+1<255 by omega]

theorem raw_bit_sum (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) (i : Nat) (hi : i<256) :
 parity (rawSources L i) s=sumBit ((sourceA L s).getD i false) ((sourceB L s).getD i false)
   (carryAt (sourceA L s) (sourceB L s) (s L.sigma) i) := by
 rw [sourceA_get L hw s i hi,sourceB_get L hw s i hi]
 by_cases z:i=0
 · subst i
   simp only [rawSources,ite_true,show 0<255 by omega,parity,List.foldr_cons,List.foldr_nil,carryAt,sumBit]
   cases s (L.Y 0) <;> cases s L.sigma <;> decide
 · obtain ⟨j,rfl⟩:∃j,i=j+1:=⟨i-1,by omega⟩
   rw [source_carry L hw s j (by omega)]
   simp only [rawSources,show ¬j+1=0 by omega,ite_false,Nat.add_sub_cancel]
   by_cases h:j+1<255
   · simp only [h,ite_true,parity,List.foldr_cons,List.foldr_nil,sumBit]
     rw [carries j (by omega)]
     cases s (L.Y j) <;> cases s (L.Y (j+1)) <;> cases s L.sigma <;> cases aExpected L s j <;> decide
   · have e:j=254:=by omega
     subst j
     simp only [show ¬254+1<255 by omega,ite_false,parity,List.foldr_cons,List.foldr_nil,sumBit]
     rw [carries 254 (by omega)]
     cases s (L.Y 254) <;> cases s L.sigma <;> cases aExpected L s 254 <;> decide

theorem rawBits_eq_sums (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) :
 rawBits L s=sums (sourceA L s) (sourceB L s) (s L.sigma) := by
 have lens: (sourceA L s).length=(sourceB L s).length:=(sources_length L hw s).1.trans (sources_length L hw s).2.symm
 apply List.ext_getElem (by rw [sums_length _ _ _ lens];simp [rawBits,(sources_length L hw s).1])
 intro i hi hj
 have h:i<256:=by simpa [rawBits] using hi
 rw [←List.getD_eq_getElem _ false hi,←List.getD_eq_getElem _ false hj]
 rw [rawBits,bitVector_get _ _ _ h,sums_at _ _ _ _ lens (by rw [(sources_length L hw s).1];omega)]
 exact raw_bit_sum L hw s carries i h

theorem rawBits_value (L : DecoderLayout) (hw : L.Widths) (s : BasisState)
 (carries : ∀i,i<255→s (L.A i)=aExpected L s i) :
 value (rawBits L s)=(if s L.sigma then regValue (L.y.take 255) s else 3*regValue (L.y.take 255) s)%2^256 := by
 rw [rawBits_eq_sums L hw s carries,sums_value _ _ _ ((sources_length L hw s).1.trans (sources_length L hw s).2.symm),(sources_length L hw s).1]
 exact sources_value L hw s
theorem correction_literal (h b : Bool) :
 value (bitVector 256 (fun i=>if i=1 then b else if Nat.testBit (2^32+977) i then h else false))=
 h.toNat*(2^32+977)+2*b.toNat := by
 cases h <;> cases b <;> decide +kernel

theorem correctionBits_value (L : DecoderLayout) (s : BasisState) :
 value (correctionBits L s)=(s L.h).toNat*(2^32+977)+2*(s L.bias).toNat := by
 have eq : correctionBits L s=bitVector 256 (fun i=>if i=1 then s L.bias else if Nat.testBit (2^32+977) i then s L.h else false) := by
   unfold correctionBits
   congr 1
   funext i
   unfold correction
   split_ifs <;> simp [MappedBit.value]
 rw [eq,correction_literal]

theorem graph_of_register_values (L : DecoderLayout)
 (hw : L.Widths) (hn : L.wires.Nodup) (basis : BasisState)
 (carries : ∀i,i<255→basis (L.A i)=aExpected L basis i)
 (hv : regValue L.r basis=
 ((if basis L.sigma then regValue (L.y.take 255) basis else 3*regValue (L.y.take 255) basis)+
  2*(basis L.bias).toNat+(basis L.h).toNat*(2^32+977))%2^256) :
 BGraph L basis ∧ basis (L.R 0)=parity (bSources L 0) basis := by
 apply graph_of_bit_values
 rw [resultBits_value L hw,rawBits_value L hw basis carries,correctionBits_value]
 rw [hv,Nat.mod_add_mod]
 congr 1
 ring
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT GraphCore
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run addCarry eraseAddCarry bBlock aProgram eraseAProgram

def graphCore (L : DecoderLayout) : Program := aProgram L ++ (bBlock L ++ eraseAProgram L)

theorem graphCore_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false)
 (graph : ∀m, BGraph L (run (aProgram L) m s).basis)
 (low : ∀m, let t:=run (aProgram L) m s
   t.basis (L.R 0)=parity (bSources L 0) t.basis) (m : List Bool) :
 (run (graphCore L) m s).phase=s.phase ∧
 (∀q,q∉L.carry → q∉L.r → (run (graphCore L) m s).basis q=s.basis q) ∧
 (∀i,i<255 → (run (graphCore L) m s).basis (L.A i)=false) ∧
 (∀i,i<256 → (run (graphCore L) m s).basis (L.R i)=false) := by
 have result:=run_three_states (aProgram L) (bBlock L) (eraseAProgram L)
   (fun a d => a=s → d.phase=s.phase ∧
    (∀q,q∉L.carry → q∉L.r → d.basis q=s.basis q) ∧
    (∀i,i<255 → d.basis (L.A i)=false) ∧
    (∀i,i<256 → d.basis (L.R i)=false)) (by
   intro a b c d m1 m2 m3 hab hbc hcd eq
   subst a
   have af:=aProgram_frame L hw hn s clean m1
   have g:=graph m1
   have l:=low m1
   rw [hab] at af g l
   have bc:=bBlock_correct L hw hn b g l m2
   have bf:=bBlock_addFrame L hw hn s b af g l m2
   rw [hbc] at bc bf
   have final:=eraseAProgram_frame L hw hn s c bf m3
   rw [hcd] at final
   have out (q : Wire) (hq:q∉L.carry) : d.basis q=c.basis q := by
     rw [←hcd]
     simpa only [eraseAProgram] using add_reverse_outside L hw hn s 255 (le_refl _) c bf m3 q hq
   refine ⟨final.phase,?_,fun i hi=>final.clean i (by omega) hi,?_⟩
   · intro q hc hr
     have first : b.basis q=s.basis q := by
       rw [←hab]
       simpa only [aProgram] using add_forward_outside L hw hn 255 (le_refl _) s m1 q hc
     exact (out q hc).trans ((bc.2.1 q hr).trans first)
   · intro i hi
     have away : L.R i∉L.carry := by
       intro ha
       exact source_r_away L hn _ (Or.inr (Or.inl ha)) (r_mem L hw i hi)
     exact (out (L.R i) away).trans (bc.2.2 i hi)) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT CleanedCore
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run graphCore biasErase clearQuotient

def CoreResult (L : DecoderLayout) (s t : State) : Prop :=
 t.phase=s.phase ∧ (∀q,q∉L.carry → q∉L.r → t.basis q=s.basis q) ∧
 (∀i,i<255 → t.basis (L.A i)=false) ∧ (∀i,i<256 → t.basis (L.R i)=false)

def cleanedCore (L : DecoderLayout) : Program :=graphCore L++(biasErase L++clearQuotient L)

theorem source_outside (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire)
 (hq : q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : q∉L.carry ∧ q∉L.r := by
 refine ⟨carry_source_away L hn q hq,?_⟩
 apply source_r_away L hn q
 rcases hq with h|h|h|h
 · exact Or.inl h
 · exact Or.inr (Or.inr (Or.inl h))
 · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
 · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem cleanedCore_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean : ∀i,i<255 → s.basis (L.A i)=false)
 (graph : ∀m, BGraph L (run (aProgram L) m s).basis)
 (low : ∀m, let t:=run (aProgram L) m s
   t.basis (L.R 0)=parity (bSources L 0) t.basis)
 (bias : s.basis L.bias=(s.basis (L.Y 255) && !s.basis L.sigma))
 (quotient : s.basis L.h=(!s.basis L.sigma &&
   !(decide (regValue (L.y.take 255) s.basis < ((p-1)/2)/3+(!s.basis (L.Y 255)).toNat))))
 (m : List Bool) :
 ∃t,CoreResult L s t ∧ run (cleanedCore L) m s=
   ⟨s.phase,writeBit (writeBit t.basis L.bias false) L.h false⟩ := by
 have result:=run_three_states (graphCore L) (biasErase L) (clearQuotient L)
   (fun a d=>a=s → ∃t,CoreResult L s t ∧ d=
     ⟨s.phase,writeBit (writeBit t.basis L.bias false) L.h false⟩) (by
   intro a t u v m1 m2 m3 hat htu huv eq
   subst a
   have tc:=graphCore_correct L hw hn s clean graph low m1
   rw [hat] at tc
   have stable (q : Wire) (hq:q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : t.basis q=s.basis q :=
     tc.2.1 q (source_outside L hn q hq).1 (source_outside L hn q hq).2
   have tsy:=stable (L.Y 255) (Or.inl (y_mem L hw 255 (by omega)))
   have ts:=stable L.sigma (by tauto)
   have th:=stable L.h (by tauto)
   have tb:=stable L.bias (by tauto)
   have bknown:t.basis L.bias=(t.basis (L.Y 255) && !t.basis L.sigma) := by rw[tb,tsy,ts];exact bias
   have ub:=biasErase_run L hw hn t m2 bknown
   rw[htu] at ub
   have baway:L.bias∉L.y:=flag_y_away L hn _ (by simp)
   have nd: [L.sigma,L.h,L.bias].Nodup := by
     apply List.nodup_iff_count.mpr
     intro q
     have h:=List.nodup_iff_count.mp hn q
     simp only[DecoderLayout.wires,List.count_append] at h
     omega
   have sh:L.sigma≠L.bias :=fun e=>(List.nodup_cons.mp nd).1 (by simp[e])
   have hb:L.h≠L.bias :=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
   have yb:L.Y 255≠L.bias :=fun e=>baway (e ▸ y_mem L hw 255 (by omega))
   have uy:u.basis (L.Y 255)=s.basis (L.Y 255) :=by rw[ub];simpa[writeBit,yb] using tsy
   have us:u.basis L.sigma=s.basis L.sigma :=by rw[ub];simpa[writeBit,sh] using ts
   have uh:u.basis L.h=s.basis L.h :=by rw[ub];simpa[writeBit,hb] using th
   have uv:regValue (L.y.take 255) u.basis=regValue (L.y.take 255) s.basis := by
     apply regValue_congr
     intro q hq
     have qb:q≠L.bias:=fun e=>baway (e ▸ List.mem_of_mem_take hq)
     rw[ub]
     simpa[writeBit,qb] using stable q (Or.inl (List.mem_of_mem_take hq))
   have uq:u.basis L.h=(!u.basis L.sigma && !(decide (regValue (L.y.take 255) u.basis<((p-1)/2)/3+(!u.basis (L.Y 255)).toNat))) := by
     rw[uy,us,uh,uv];exact quotient
   have uc:∀q∈L.carry,u.basis q=false := by
     intro q hq
     obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
     have i255:i<255:=by have len:=hw.2.2;omega
     have aeq:L.A i=q:=by
       change L.carry.getD i 0=q
       rw[List.getD_eq_getElem _ _ hi]
       exact eq
     have qb:q≠L.bias:=fun e=>carry_source_away L hn _ (by tauto) (e ▸ hq)
     rw[ub]
     simpa only[writeBit,Function.update_of_ne qb,←aeq] using tc.2.2.1 i i255
   have vc:=clearQuotient_correct L hw hn u m3 uc uq
   rw[huv] at vc
   refine ⟨t,tc,?_⟩
   rw[vc,ub]
   simp only[tc.1]) s m
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT PostAGraph
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run aProgram

theorem aExpected_congr (L : DecoderLayout) (a b : BasisState)
 (sigma : a L.sigma=b L.sigma) (ys : ∀i,i<256→a (L.Y i)=b (L.Y i))
 (i : Nat) (hi:i<255) : aExpected L a i=aExpected L b i := by
 induction i with
 |zero=>simp only[aExpected];rw[sigma,ys 0 (by omega)]
 |succ i ih=>simp only[aExpected];rw[ys i (by omega),ys (i+1) (by omega),sigma,ih (by omega)]

theorem aProgram_graph (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (s : State) (clean:∀i,i<255→s.basis (L.A i)=false)
 (hv : regValue L.r s.basis=
 ((if s.basis L.sigma then regValue (L.y.take 255) s.basis else 3*regValue (L.y.take 255) s.basis)+
  2*(s.basis L.bias).toNat+(s.basis L.h).toNat*(2^32+977))%2^256) (m : List Bool) :
 BGraph L (run (aProgram L) m s).basis ∧
 (run (aProgram L) m s).basis (L.R 0)=parity (bSources L 0) (run (aProgram L) m s).basis := by
 let t:=run (aProgram L) m s
 have af:=aProgram_frame L hw hn s clean m
 have out (q : Wire) (hq:q∉L.carry) : t.basis q=s.basis q :=by
   simpa only[t,aProgram] using add_forward_outside L hw hn 255 (le_refl _) s m q hq
 have stable (q : Wire) (hq:q∈L.y ∨ q=L.sigma ∨ q=L.h ∨ q=L.bias) : t.basis q=s.basis q :=
   out q (carry_source_away L hn q hq)
 apply graph_of_register_values L hw hn t.basis
 · intro i hi
   exact (af.computed i hi).trans (aExpected_congr L s.basis t.basis af.sigma.symm
     (fun j hj=>(af.source j hj).symm) i hi)
 · have rv:regValue L.r t.basis=regValue L.r s.basis :=by
     apply regValue_congr
     intro q hq
     apply out
     intro hc
     exact source_r_away L hn q (Or.inr (Or.inl hc)) hq
   have yv:regValue (L.y.take 255) t.basis=regValue (L.y.take 255) s.basis :=by
     apply regValue_congr
     intro q hq
     exact stable q (Or.inl (List.mem_of_mem_take hq))
   rw[rv,yv,stable L.sigma (by tauto),stable L.h (by tauto),stable L.bias (by tauto)]
   exact hv
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Back
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic
attribute [local irreducible] run restoreSource copySource

theorem index_zero_mem (xs : List Wire) (b : BasisState)
 (zero:∀i,i<xs.length→b (xs.getD i 0)=false) (q : Wire) (hq:q∈xs) : b q=false := by
 obtain ⟨i,hi,eq⟩:=List.mem_iff_getElem.mp hq
 have get:xs.getD i 0=q := by rw[List.getD_eq_getElem _ _ hi];exact eq
 rw[←get]
 exact zero i hi

def zeroR (L : DecoderLayout) (b : BasisState) : BasisState :=
 fun q=>if q∈L.r then false else complementBasis (L.Y 255) (L.y.take 255) b q

theorem cleaned_front_basis (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (t : State)
 (f : CoreResult L ⟨phase,frontBasis L b⟩ t)
 (ch:b L.h=false) (cb:b L.bias=false) (cc:∀q∈L.carry,b q=false) :
 writeBit (writeBit t.basis L.bias false) L.h false=zeroR L b := by
 have nd:=flags_nd L hn
 have hb:L.h≠L.bias:=fun e=>(List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp[e])
 have hy:=flag_y_away L hn L.h (by simp)
 have byy:=flag_y_away L hn L.bias (by simp)
 have hr:=source_r_away L hn L.h (by tauto)
 have br:=source_r_away L hn L.bias (by tauto)
 have tr:∀q∈L.r,t.basis q=false := index_zero_mem L.r t.basis (by intro i hi;exact f.2.2.2 i (by have len:=hw.2.1;omega))
 have tc:∀q∈L.carry,t.basis q=false :=index_zero_mem L.carry t.basis (by intro i hi;exact f.2.2.1 i (by have len:=hw.2.2;omega))
 funext q
 by_cases qh:q=L.h
 · subst q
   simp[writeBit,zeroR,hr,complementBasis,show L.h∉L.y.take 255 from fun h=>hy (List.mem_of_mem_take h),ch]
 · by_cases qb:q=L.bias
   · subst q
     simp[writeBit,Ne.symm hb,zeroR,br,complementBasis,show L.bias∉L.y.take 255 from fun h=>byy (List.mem_of_mem_take h),cb]
   · simp only[writeBit,Function.update_of_ne qh,Function.update_of_ne qb]
     by_cases qr:q∈L.r
     · simp[zeroR,qr,tr q qr]
     · by_cases qc:q∈L.carry
       · have qy:q∉L.y:=fun h=>carry_source_away L hn q (Or.inl h) qc
         simp[zeroR,qr,tc q qc,complementBasis,show q∉L.y.take 255 from fun h=>qy (List.mem_of_mem_take h),cc q qc]
       · rw[f.2.1 q qc qr]
         simp[frontBasis,writeBit,qh,qb,zeroR,qr,complementBasis]

theorem restore_zeroR (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (m : List Bool) :
 run (restoreSource L) m ⟨phase,zeroR L b⟩=
  ⟨phase,fun q=>if q∈L.r then false else b q⟩ := by
 rw[restoreSource_run L hw hn]
 have nd:=normalize_nd L hw hn
 have sig:zeroR L b (L.Y 255)=b (L.Y 255):=by
   simp[zeroR,complementBasis,show L.Y 255∉L.y.take 255 from fun h=>nd.2 (List.mem_append_left _ h),
     show L.Y 255∉L.r from fun h=>nd.2 (List.mem_append_right _ h)]
 apply congrArg (State.mk phase)
 funext q
 simp only[complementBasis,sig]
 by_cases qr:q∈L.r
 · have qt:q∉L.y.take 255 := by
     intro h
     exact source_r_away L hn q (Or.inl (List.mem_of_mem_take h)) qr
   simp[qr,qt,zeroR]
 · by_cases qt:q∈L.y.take 255
   · simp[zeroR,complementBasis,qr,qt,Bool.xor_assoc]
   · simp[zeroR,complementBasis,qr,qt]

def back (L : DecoderLayout) : Program :=restoreSource L++copySource L

theorem back_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (b : BasisState) (phase : Bool) (m : List Bool) :
 (run (back L) m ⟨phase,zeroR L b⟩).phase=phase ∧
 (∀q,q∉L.r → (run (back L) m ⟨phase,zeroR L b⟩).basis q=b q) ∧
 regValue L.r (run (back L) m ⟨phase,zeroR L b⟩).basis=regValue L.y b := by
 rw[back,run_append,run_take,restore_zeroR L hw hn]
 let v : State:=⟨phase,fun q=>if q∈L.r then false else b q⟩
 have c:=copySource_correct L hw hn v (m.drop (measurementCount (restoreSource L)))
 refine ⟨c.1,?_,?_⟩
 · intro q hq
   simpa only[v,if_neg hq] using c.2.1 q hq
 · rw[c.2.2]
   have rz:regValue L.r v.basis=0 :=(regValue_zero _ _).mpr (by intro q hq;simp[v,hq])
   have yv:regValue L.y v.basis=regValue L.y b :=by
     apply regValue_congr
     intro q hq
     have qr:q∉L.r:=source_r_away L hn q (Or.inl hq)
     simp[v,qr]
   rw[rz,yv,Nat.zero_xor]
end ECDSAAdd.Entrant.TerminalGraph



-- TERMINAL GRAPH COMPONENT DecoderCorrect
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField
attribute [local irreducible] run front cleanedCore back aProgram

theorem decoder_parts (L : DecoderLayout) : decoder L=front L++(cleanedCore L++back L) := by
 simp only[decoder,front,cleanedCore,graphCore,aProgram,eraseAProgram,bBlock,bSources,back,List.append_assoc]

theorem decoder_correct (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (Y : Fp) (sigma : Bool) (s : State) (m : List Bool)
 (ys:regValue L.y s.basis=centerWord Y)
 (rs:regValue L.r s.basis=centerWord ((if sigma then 1 else 3)*Y))
 (sig:s.basis L.sigma=sigma) (hc:s.basis L.h=false) (bc:s.basis L.bias=false)
 (cc:∀q∈L.carry,s.basis q=false) :
 (run (decoder L) m s).phase=s.phase ∧
 (∀q,q∉L.r → (run (decoder L) m s).basis q=s.basis q) ∧
 regValue L.r (run (decoder L) m s).basis=centerWord Y := by
 have result:=run_three_states (front L) (cleanedCore L) (back L)
   (fun a d=>a=s → d.phase=s.phase ∧ (∀q,q∉L.r → d.basis q=s.basis q) ∧
     regValue L.r d.basis=centerWord Y) (by
   intro a n u d m1 m2 m3 han hnu hud eq
   subst a
   have nf:=front_run L hw hn s m1
   rw[han] at nf
   let f : State:=⟨s.phase,frontBasis L s.basis⟩
   have neq:n=f:=nf
   subst n
   rw[nf] at hnu
   have scalar:=actual_front_scalar L hw hn s.basis Y sigma ys rs sig hc bc
   have nc:∀i,i<255→f.basis (L.A i)=false :=by
     intro i hi
     exact front_carry_clean L hn s.basis cc (L.A i) (a_mem L hw i hi)
   have bb:f.basis L.bias=(f.basis (L.Y 255) && !f.basis L.sigma) :=by
     have facts:=actual_front_values L hw hn s.basis Y sigma ys rs sig hc bc
     change frontBasis L s.basis L.bias=(frontBasis L s.basis (L.Y 255) && !frontBasis L s.basis L.sigma)
     rw[facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2]
   have cg:=cleanedCore_correct L hw hn f nc
     (fun r=>(aProgram_graph L hw hn f nc scalar.1 r).1)
     (fun r=>(aProgram_graph L hw hn f nc scalar.1 r).2) bb scalar.2 m2
   obtain ⟨t,tf,ut⟩:=cg
   rw[hnu] at ut
   have cleanbasis:=cleaned_front_basis L hw hn s.basis s.phase t tf hc bc cc
   have uz:u=⟨s.phase,zeroR L s.basis⟩ :=by
     rw[ut,cleanbasis]
   have done:=back_correct L hw hn s.basis s.phase m3
   rw[uz] at hud
   rw[hud] at done
   exact ⟨done.1,done.2.1,done.2.2.trans ys⟩) s m
 rw[decoder_parts]
 exact result rfl
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT Caller
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic Secp256k1 Arithmetic.BalancedField
attribute [local irreducible] run decoder

def work (L : DecoderLayout) : List Wire:=L.carry++[L.h,L.bias]

theorem work_away (L : DecoderLayout) (hn : L.wires.Nodup) (q : Wire) (hq:q∈work L) :
 q∉L.r ∧ q∉L.y := by
 simp only[work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with hc|rfl|rfl
 · refine ⟨source_r_away L hn q (Or.inr (Or.inl hc)),?_⟩
   intro hy
   exact carry_source_away L hn q (Or.inl hy) hc
 · exact ⟨source_r_away L hn _ (by tauto),flag_y_away L hn _ (by simp)⟩
 · exact ⟨source_r_away L hn _ (by tauto),flag_y_away L hn _ (by simp)⟩

theorem terminal_relation (X Y : Fp) (sigma : Bool)
 (h:(X+(if sigma then Y else -Y))/2=Y) : X=(if sigma then 1 else 3)*Y := by
 have two:(2:Fp)≠0:=by decide
 have e: X+(if sigma then Y else -Y)=Y*2 := (div_eq_iff two).mp h
 cases sigma <;> simp only[Bool.false_eq_true,if_false,if_true] at e ⊢ <;> linear_combination e

theorem decoder_frame (L : DecoderLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (origin : BasisState) (clean : ∀q∈work L,origin q=false) (X Y : Fp)
 (hend:(X+(if origin L.sigma then Y else -Y))/2=Y) :
 Triple (PairFrame L.r L.y origin (centerWord X) (centerWord Y)) (decoder L)
   (PairFrame L.r L.y origin (centerWord Y) (centerWord Y)) := by
 intro s m input
 have cleanS (q : Wire) (hq:q∈work L) : s.basis q=false :=
   (input.2.2 q (work_away L hn q hq).1 (work_away L hn q hq).2).trans (clean q hq)
 have sig:s.basis L.sigma=origin L.sigma:=input.2.2 L.sigma
   (source_r_away L hn _ (by tauto)) (flag_y_away L hn _ (by simp))
 have rel:=terminal_relation X Y (origin L.sigma) hend
 have rword:regValue L.r s.basis=centerWord ((if origin L.sigma then 1 else 3)*Y) := by
   rw[input.1,rel]
 have c:=decoder_correct L hw hn Y (origin L.sigma) s m input.2.1 rword sig
   (cleanS L.h (by simp[work])) (cleanS L.bias (by simp[work]))
   (fun q hq=>cleanS q (by simp[work,hq]))
 refine ⟨c.1,c.2.2,?_,?_⟩
 · exact (regValue_congr L.y _ _ (fun q hq=>c.2.1 q (source_r_away L hn q (Or.inl hq)))).trans input.2.1
 · intro q qr qy
   exact (c.2.1 q qr).trans (input.2.2 q qr qy)
end ECDSAAdd.Entrant.TerminalGraph


-- TERMINAL GRAPH COMPONENT EndpointCaller
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphEndpoint
open Arithmetic Secp256k1 BalancedField TerminalGraph
attribute [local irreducible] run TerminalGraph.decoder

def half (divide : Bool) (w : Nat→Wire) (sign : Wire) : Program :=
 if divide then decoder (ofBalanced (Q6EndpointCell.ports w sign)) else Q6EndpointCell.half false w sign

def endpoint (divide : Bool) (w : Nat→Wire) (b g sign : Wire) (ig : Bool) : Program :=
 transcriptSelectWindow b g sign ig (half divide w sign)

theorem clean_decoder (w : Nat→Wire) (sign : Wire) (origin : BasisState)
 (hc:Q6EndpointCell.Clean w origin) :
 ∀q∈work (ofBalanced (Q6EndpointCell.ports w sign)),origin q=false := by
 have cl:=Q6EndpointCell.clean_work w sign origin hc
 intro q hq
 apply cl
 simp only[work,ofBalanced,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
 simp only[BalancedCircuit.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
 rcases hq with (h|rfl)|rfl|rfl
 · exact Or.inr (List.mem_of_mem_take h)
 all_goals tauto

theorem half_frame (divide : Bool) (w : Nat→Wire) (sign : Wire)
 (hn:(Q6EndpointCell.ports w sign).wires.Nodup) (origin : BasisState)
 (hc:Q6EndpointCell.Clean w origin) (X Y : Fp)
 (hend:divide=true→(X+(if origin sign then Y else -Y))/2=Y) :
 Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin (centerWord X) (centerWord Y))
   (half divide w sign)
   (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
     (centerWord (if divide then (X+(if origin sign then Y else -Y))/2 else 2*X+(if origin sign then -Y else Y)))
     (centerWord Y)) := by
 cases divide
 · exact Q6EndpointCell.half_frame false w sign hn origin hc X Y
 · have c:=decoder_frame (ofBalanced (Q6EndpointCell.ports w sign))
     (ofBalanced_widths _ (Q6EndpointCell.ports_widths w sign)) (ofBalanced_nodup _ hn)
     origin (clean_decoder w sign origin hc) X Y (by simpa only[ofBalanced,Q6EndpointCell.ports_sign] using hend rfl)
   simpa only[half,ofBalanced,if_true,hend rfl] using c

theorem endpoint_frame (divide : Bool) (w : Nat → Wire) (b g sign : Wire) (ig : Bool)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup) (nd : [b,g,sign].Nodup)
    (hb : b∉(Q6EndpointCell.ports w sign).r ∧ b∉(Q6EndpointCell.ports w sign).y)
    (hg : g∉(Q6EndpointCell.ports w sign).r ∧ g∉(Q6EndpointCell.ports w sign).y)
    (hs : sign∉(Q6EndpointCell.ports w sign).r ∧ sign∉(Q6EndpointCell.ports w sign).y)
    (origin : BasisState) (hz : origin sign=false) (hc : Q6EndpointCell.Clean w origin) (X Y : Fp)
    (hend : divide=true → (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2=Y) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
      (centerWord X) (centerWord Y)) (endpoint divide w b g sign ig)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (centerWord (if divide then (X+(if mixedTranscriptBit origin b g ig then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit origin b g ig then -Y else Y))) (centerWord Y)) := by
 have ns:=OwnQ6Core5.sign_work (Q6EndpointCell.ports w sign) hn
 have cl:Q6EndpointCell.Clean w (mixedTranscriptBase origin b g sign ig) :=by
   intro q hq
   have nq:q≠sign:=fun e=>ns (by simpa only[Q6EndpointCell.ports_work] using e ▸ hq)
   simpa only[mixedTranscriptBase,writeBit,Function.update_of_ne nq] using hc q hq
 have body:=half_frame divide w sign hn (mixedTranscriptBase origin b g sign ig) cl X Y
   (by simpa only[mixedTranscriptBase,writeBit,Function.update_self] using hend)
 simp only[mixedTranscriptBase,writeBit,Function.update_self] at body
 exact transcriptSelectWindow_pairFrame b g sign ig _ _ nd hb hg hs origin hz _ _ _ _ _ body

theorem half_counts (divide : Bool) (w : Nat→Wire) (sign : Wire) :
 toffoliCount (half divide w sign)=(if divide then 512 else 1020) ∧
 measurementCount (half divide w sign)=(if divide then 766 else 1021) := by
 cases divide
 · exact Q6EndpointCell.half_counts false w sign
 · exact decoder_counts _ (ofBalanced_widths _ (Q6EndpointCell.ports_widths w sign))
end ECDSAAdd.Entrant.TerminalGraphEndpoint


-- TERMINAL GRAPH COMPONENT TerminalSupportOnly
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraphSupportOnly
open Arithmetic MappedCompressed TerminalGraph

def actualLayout (sign : Nat) : DecoderLayout :=
  ofBalanced (Q6EndpointCell.ports base (base sign))
def actualDecoder (sign : Nat) : Program := decoder (actualLayout sign)

private abbrev footprint (s q : Nat) : Prop :=
 q=base s ∨ q=base 1027 ∨ q=base 768 ∨ q=base 1797 ∨ q=base 1540 ∨
 (base 770≤q ∧ q<base 1026) ∨ (base 2056≤q ∧ q<base 2312) ∨
 (base 512≤q ∧ q<base 765)

private theorem block_mem (q start n : Nat) :
 q∈wireBlock base start n ↔ base start≤q ∧ q<base (start+n) := by
 simp only [wireBlock,List.mem_map,List.mem_range'_1]
 constructor
 · rintro ⟨a,⟨ha,hb⟩,he⟩
   change a+16=q at he
   constructor
   · change start+16≤q
     rw [←he]
     exact Nat.add_le_add_right ha 16
   · change q<start+n+16
     rw [←he]
     exact Nat.add_lt_add_right hb 16
 · rintro ⟨hlo,hhi⟩
   change start+16≤q at hlo
   change q<start+n+16 at hhi
   have hq : 16≤q := le_trans (Nat.le_add_left 16 start) hlo
   have eq : q-16+16=q := Nat.sub_add_cancel hq
   refine ⟨q-16,⟨?_,?_⟩,?_⟩
   · have hh : start+16≤q-16+16 := by rw [eq]; exact hlo
     exact (show start+16≤q-16+16 ↔ start≤q-16 from Nat.add_le_add_iff_right).mp hh
   · have hh : q-16+16<start+n+16 := by rw [eq]; exact hhi
     exact (show q-16+16<start+n+16 ↔ q-16<start+n from Nat.add_lt_add_iff_right).mp hh
   · exact eq

private theorem actual_carry (s : Nat) :
 (actualLayout s).carry=wireBlock base 512 253++[base 1540,base 1797] := by
 simp only [actualLayout,ofBalanced,Q6EndpointCell.ports,List.take_append,
   show (wireBlock base 512 253).length=253 from by simp [wireBlock],
   show (wireBlock base 512 253).take 254=wireBlock base 512 253 from
     List.take_of_length_le (by simp [wireBlock]),Nat.reduceSub,List.take_succ_cons,
   List.take_zero,List.nil_append,List.append_assoc,List.singleton_append]

private theorem actual_y (s : Nat) :
 (actualLayout s).y=wireBlock base 770 256 := by rfl
private theorem actual_r (s : Nat) :
 (actualLayout s).r=wireBlock base 2056 256 := by rfl

private theorem actual_sites (s q : Nat) :
 q∈(actualLayout s).wires.toFinset ↔ footprint s q := by
 simp only [List.mem_toFinset,DecoderLayout.wires,List.mem_append,
   List.mem_cons,List.not_mem_nil,or_false,actual_carry,actual_y,actual_r,block_mem]
 simp only [actualLayout,ofBalanced,Q6EndpointCell.ports,footprint]
 tauto

private def correctionCheck (s : Nat) : List Correction→Bool
 | []=>true
 | .Z t::cs=>decide (footprint s t) && correctionCheck s cs
 | .CZ a b::cs=>decide (footprint s a) && decide (footprint s b) && correctionCheck s cs

private theorem correctionCheck_iff (s : Nat) (cs : List Correction) :
 correctionCheck s cs=true ↔ correctionWires cs⊆(actualLayout s).wires.toFinset := by
 induction cs with
 | nil=>simp [correctionCheck,correctionWires]
 | cons c cs ih=>
   cases c <;>
     simp only [correctionCheck,correctionWires,Bool.and_eq_true,decide_eq_true_eq,
       Finset.union_subset_iff,Finset.singleton_subset_iff,Finset.insert_subset_iff,
       Finset.empty_subset,and_true,ih,actual_sites]

private def instructionCheck (s : Nat) : Instr→Bool
 | .X t=>decide (footprint s t)
 | .CX a t=>decide (footprint s a) && decide (footprint s t)
 | .CCX a b t=>decide (footprint s a) && decide (footprint s b) && decide (footprint s t)
 | .measureX t c d=>decide (footprint s t) && correctionCheck s c && correctionCheck s d

private theorem instructionCheck_iff (s : Nat) (i : Instr) :
 instructionCheck s i=true ↔ i.wires⊆(actualLayout s).wires.toFinset := by
 cases i <;>
   simp only [instructionCheck,Instr.wires,Bool.and_eq_true,decide_eq_true_eq,
     Finset.union_subset_iff,Finset.singleton_subset_iff,Finset.insert_subset_iff,
     Finset.empty_subset,and_true,actual_sites,correctionCheck_iff,and_assoc]

private def supportCheck (s : Nat) (P : Program) : Bool := P.all (instructionCheck s)
private theorem supportCheck_correct (s : Nat) (P : Program)
 (h : supportCheck s P=true) : wires P⊆(actualLayout s).wires.toFinset := by
 induction P with
 | nil=>simp [wires]
 | cons i P ih=>
   have hh : instructionCheck s i=true ∧ supportCheck s P=true := by
     simpa only [supportCheck,List.all_cons,Bool.and_eq_true] using h
   simp only [wires,Finset.union_subset_iff]
   exact ⟨(instructionCheck_iff s i).mp hh.1,ih hh.2⟩

theorem actual_decoder_support :
    wires (actualDecoder 2409)⊆(ofBalanced (Q6EndpointCell.ports base (base 2409))).wires.toFinset ∧
    wires (actualDecoder 2410)⊆(ofBalanced (Q6EndpointCell.ports base (base 2410))).wires.toFinset := by
  constructor <;> apply supportCheck_correct <;> decide +kernel

end ECDSAAdd.Entrant.TerminalGraphSupportOnly


-- TERMINAL GRAPH COMPONENT TerminalFootprint
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TerminalGraph
open Arithmetic MappedCompressed
attribute [local irreducible] wires CoherentTail.addPrefix Q6Structural.rawAdd Q6EndpointStructural.forwardE Q6EndpointCell.halfE
theorem prefix_sites (x y c : List Wire) (a t z cin : Wire)
 (hy:y.length=x.length) (hc:c.length=x.length) :
 wires (CoherentTail.addPrefix x y c a t z cin)=(x++y++c++[a,t,z,cin]).toFinset := by
 induction x generalizing y c cin with
 | nil=>
   have ey:y=[]:=List.eq_nil_of_length_eq_zero hy
   have ec:c=[]:=List.eq_nil_of_length_eq_zero hc
   subst y; subst c
   ext q
   simp [CoherentTail.addPrefix,CoherentTail.program,wires,Instr.wires]
   tauto
 | cons b xs ih=>
   cases y with
   | nil=>simp at hy
   | cons d ys=>
     cases c with
     | nil=>simp at hc
     | cons k ks=>
       have hy':ys.length=xs.length:=by simpa using hy
       have hc':ks.length=xs.length:=by simpa using hc
       rw [CoherentTail.addPrefix,wires_append,wires_append,wires_append,ih _ _ _ hy' hc']
       ext q
       simp [majority,eraseCarry,wires,Instr.wires,correctionWires]
       tauto

theorem layout_subset_forwardE (L : BalancedCircuit.Layout) (hw : L.Widths) :
 (ofBalanced L).wires.toFinset⊆wires (Q6EndpointStructural.forwardE L) := by
 have len:=hw.2.2
 have yw:=hw.2.1
 have rw:=hw.1
 have ct:(Q6Structural.carryLayout L).carry.take 255=L.carry.take 254++[L.lower] := by
   simp [Q6Structural.carryLayout,Q6Structural.q6Carry,List.take_append,List.length_take,len]
 have plen:((Q6Structural.carryLayout L).carry.take 255).length=L.ylow.length :=by
   rw[ct]
   simp[yw,len]
 have ylen:L.low.length=L.ylow.length:=by simp[BalancedCleanup.Layout.low,rw,yw]
 have pref:=prefix_sites L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign ylen plen
 have rawsub:wires (CoherentTail.addPrefix L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
   L.ymsb L.rmsb L.one L.sign)⊆wires (Q6Structural.rawAdd L) :=by
   simp only[Q6Structural.rawAdd,FifthCarry.rawAdd,Q6Structural.carryLayout,FieldRename.mapCircuit] at *
   intro q hq
   simp only[wires_append]
   exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)
 have allsub:wires (GuardCompression.seed L)∪wires (Q6Structural.rawAdd L)⊆wires (Q6EndpointStructural.forwardE L) :=by
   intro q hq
   simp only[Q6EndpointStructural.forwardE,Q6StructuralCell.forwardPrefix,wires_append,Finset.mem_union] at hq ⊢
   tauto
 intro q hq
 apply allsub
 by_cases parity:q=L.parity
 · subst q
   exact Finset.mem_union_left _ (by simp[GuardCompression.seed,wires,Instr.wires])
 · apply Finset.mem_union_right
   apply rawsub
   rw[pref,ct]
   simp only[DecoderLayout.wires,ofBalanced,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
     BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low] at hq ⊢
   tauto

theorem actual_layout_subset_halfE :
 (ofBalanced (Q6EndpointCell.ports base (base 2409))).wires.toFinset⊆
 wires (Q6EndpointCell.halfE true base (base 2409)) := by
 have core:=layout_subset_forwardE (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths _ _)
 intro q hq
 have h:=core hq
 rw[Q6EndpointCell.halfE_true,wires_append,wires_append]
 exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
end ECDSAAdd.Entrant.TerminalGraph



-- TERMINAL GRAPH COMPONENT TerminalPhysicalOnly
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.TerminalGraphPhysicalOnly
open Arithmetic MappedCompressed

def actualDecoder (sign : Nat) : Program :=
 TerminalGraph.decoder (TerminalGraph.ofBalanced (Q6EndpointCell.ports base (base sign)))
attribute [local irreducible] GatePhysical actualDecoder TerminalGraph.decoder

theorem physical : GatePhysical (actualDecoder 2409) :=
 physicalGateCheck_correct _ (by decide +kernel)

theorem slots : Challenge.gateSlots (actualDecoder 2409)≤23900 := by
 decide +kernel
end ECDSAAdd.Entrant.TerminalGraphPhysicalOnly


