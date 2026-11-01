import ECDSAAdd.Submission.Entrant.MainA
import ECDSAAdd.Arithmetic.BalancedFieldCircuitProof
import ECDSAAdd.Arithmetic.BalancedInverseComposeProof
import ECDSAAdd.Framework.GateInverse
import ECDSAAdd.Arithmetic.MeasuredGateSupport
set_option Elab.async false

/-! Measured joint inverse of the S2 (multiplication) first packet, placed in the 1,588-qubit
Rolling layout.

Ported from submission f2dcda16 (ArthurOstapenko): `CleanInverse5` and `FirstInverse5` below are
that submission's generic measured inverse of the forward joint entry `EntryRetained5.program`
(which is already in the record).  The record's layout has two fewer clean wires than f2's at this
point (virtual carries `516` and `1541` have no host: `516` was hosted on G1 by the record's
`loanWindow`, but the joint inverse needs G1 as a control and the flag `2409` as its `sign`
scalar), so `JointInverse1588` hosts them inside the kernel:
* during `clearParity` on the still-clean scalars `one` and `sign`;
* during the inner adder (source bits 4..255) of the subtraction on `lowY` (u = J∧G) and
  `sign` (e = lower∧u), which are measured away before and recomputed after (+2 Toffolis). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CleanInverse5
open Arithmetic
attribute [local irreducible] run

def undo : Instr → Program
  | .CCX a b t => [.measureX t [] [.CZ a b]]
  | .X t => [.X t]
  | .CX a t => [.CX a t]
  | .measureX _ _ _ => []

def inverse : Program → Program
  | [] => []
  | i::p => inverse p ++ undo i

def CleanTarget (i : Instr) (s : State) : Prop :=
  match i with | .CCX _ _ t => s.basis t=false | _ => True

def Ready : Program → State → Prop
  | [],_ => True
  | i::p,s => ProperGate i ∧
      CleanTarget i s ∧
      Ready p (run [i] [] s)

theorem ready_proper (p : Program) (s : State) (h : Ready p s) : ProperProgram p := by
  induction p generalizing s with
  | nil => simp [ProperProgram]
  | cons i p ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl|hj
    · exact h.1
    · exact ih _ h.2.2 _ hj

theorem ready_append (p q : Program) (s : State) :
    Ready (p++q) s ↔ Ready p s ∧ Ready q (run p [] s) := by
  induction p generalizing s with
  | nil => simp [Ready,run]
  | cons i p ih =>
    cases i <;> simp only [List.cons_append,Ready,CleanTarget] <;>
      simp only [ih,run] <;> tauto

theorem undo_gate (i : Instr) (s : State) (m : List Bool)
    (hp : ProperGate i)
    (hc : CleanTarget i s) :
    run (undo i) m (run [i] [] s)=s := by
  cases i with
  | X t => exact properGate_involution (.X t) hp s [] m
  | CX a t => exact properGate_involution (.CX a t) hp s [] m
  | measureX t c0 c1 => contradiction
  | CCX a b t =>
    have ha : a≠t := hp.1
    have hb : b≠t := hp.2
    have erase := EntryHalf5.eraseAnd a b t ha hb (run [.CCX a b t] [] s) m (by
      simp [run,writeBit,CleanTarget] at hc ⊢
      simp [hc,ha,hb])
    change run [.measureX t [] [.CZ a b]] m (run [.CCX a b t] [] s)=s
    rw [erase]
    apply State.extensionality
    · simp only [run]
    · funext q
      by_cases hq : q=t
      · subst q;simp [writeBit,CleanTarget] at hc ⊢
        exact hc
      · simp [run,writeBit,hq]

theorem inverse_run (p : Program) (s : State) (h : Ready p s) (m : List Bool) :
    run (inverse p) m (run p [] s)=s := by
  induction p generalizing s m with
  | nil => simp [inverse,run]
  | cons i p ih =>
    have hp : ProperProgram p := ready_proper p _ h.2.2
    have pm := properProgram_measurementCount p hp
    have first : run (i::p) [] s=run p [] (run [i] [] s) := by
      cases i <;> simp_all [run,ProperGate,CleanTarget]
    rw [inverse,first,run_append,run_take,ih _ h.2.2]
    exact undo_gate i s _ h.1 h.2.1

theorem counts (p : Program) (hp : ProperProgram p) :
    toffoliCount (inverse p)=0 ∧ measurementCount (inverse p)=toffoliCount p := by
  induction p with
  | nil => exact ⟨rfl,rfl⟩
  | cons i p ih =>
    have h := hp i (by simp)
    have t := ih (fun j hj => hp j (by simp [hj]))
    cases i <;> simp_all [ProperGate,inverse,undo,toffoliCount_append,measurementCount_append,
      toffoliCount,measurementCount,Nat.add_comm]

theorem ready_zero (p : Program) (hp : ProperProgram p) (ht : toffoliCount p=0) (s : State) :
    Ready p s := by
  induction p generalizing s with
  | nil => trivial
  | cons i p ih =>
    have hi := hp i (by simp)
    have tail : ProperProgram p := fun j hj => hp j (by simp [hj])
    cases i with
    | measureX t c0 c1 => contradiction
    | CCX a b t => simp [toffoliCount] at ht
    | X t =>
      refine ⟨hi,trivial,ih tail ?_ _⟩
      simpa [toffoliCount] using ht
    | CX a t =>
      refine ⟨hi,trivial,ih tail ?_ _⟩
      simpa [toffoliCount] using ht

theorem copy_ready (j : Wire) (xs ys : List Wire) (s : State)
    (hn : (j::xs++ys).Nodup) (clean : ∀q∈ys,s.basis q=false) :
    Ready (copyRegister (some j) xs ys) s := by
  induction xs generalizing ys s with
  | nil => trivial
  | cons x xs ih =>
    cases ys with
    | nil => trivial
    | cons y ys =>
      have ct := List.nodup_iff_count.mp hn
      have nj : j≠y := by
        intro bad;have h:=ct y;subst j
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have nx : x≠y := by
        intro bad;have h:=ct y;subst x
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      have nd : (j::xs++ys).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q;have h:=ct q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      have yt : y∉ys := by
        intro bad
        have h:=ct y;have pos:=List.count_pos_iff.mpr bad
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
        omega
      change ProperGate (.CCX j x y) ∧ s.basis y=false ∧ _
      refine ⟨⟨nj,nx⟩,clean y (by simp),ih ys _ nd ?_⟩
      intro q hq
      simpa only [copyGate,run,writeBit,Function.update_of_ne (show q≠y from fun e=>yt (e ▸ hq))]
        using clean q (by simp [hq])

end ECDSAAdd.Entrant.CleanInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

def restoreScalars (p a d e u j b h : Wire) : Program :=
  [.measureX u [] [.CZ j p], .CCX j b u,
   .CCX p u d, .CX p a, .CCX p h a, .CX d a, .CCX a u e]

def restoreAt (L : Layout) (J B : Wire) : Program :=
  restoreScalars L.parity L.lower L.one L.sign (lowY L) J B L.rmsb

def subtract (L : Layout) : Program :=
  notRegister L.r ++ Affine.add (sources L) L.r (L.carry.take 255) (lowY L) ++ notRegister L.r

def eraseCopy (j : Wire) : List Wire → List Wire → Program
  | x::xs,y::ys => [.measureX y [] [.CZ j x]] ++ eraseCopy j xs ys
  | _,_ => []

def unseed (L : Layout) : Program :=
  [.CX L.parity L.r0,
    .measureX L.sign [] [.CZ L.lower (lowY L)],
    .measureX L.one [] [.CZ L.parity (lowY L)],
    .measureX L.lower [] [.CZ L.parity L.rmsb],
    .CX L.r0 L.parity]

def unprepare (L : Layout) (J B : Wire) : Program :=
  (signComplement (lowY L) L.r).reverse ++ (rightShift L).reverse ++
    unseed L ++ eraseCopy J L.r.tail L.y.tail ++ [.measureX (lowY L) [] [.CZ J B]]

def program (L : Layout) (J B : Wire) : Program :=
  clearParity L J ++ restoreAt L J B ++ subtract L ++ unprepare L J B

theorem restoreScalars_counts (p a d e u j b h : Wire) :
    toffoliCount (restoreScalars p a d e u j b h)=4 ∧
      measurementCount (restoreScalars p a d e u j b h)=1 := by
  simp [restoreScalars,toffoliCount,measurementCount]

theorem eraseCopy_counts (j : Wire) (xs ys : List Wire) (hl : xs.length=ys.length) :
    toffoliCount (eraseCopy j xs ys)=0 ∧ measurementCount (eraseCopy j xs ys)=ys.length := by
  induction xs generalizing ys with
  | nil => have h : ys=[] := List.eq_nil_of_length_eq_zero hl.symm; simp [h,eraseCopy,toffoliCount,measurementCount]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have t := ih ys (by simpa using hl)
      simp [eraseCopy,toffoliCount,measurementCount,t.1,t.2,Nat.add_comm]

theorem counts (L : Layout) (hw : L.Widths) (J B : Wire) :
    toffoliCount (program L J B)=515 ∧ measurementCount (program L J B)=770 := by
  have w:=BalancedCleanup.widths L.toLayout hw
  have r:=restoreScalars_counts L.parity L.lower L.one L.sign (lowY L) J B L.rmsb
  have a:=arithmetic_counts L hw
  unfold arithmetic at a
  have c:=clearParity_counts L hw J
  have e:=eraseCopy_counts J L.r.tail L.y.tail (by simp [List.length_tail,w.2.1,w.2.2.1])
  have sc:=signComplement_counts (lowY L) L.r
  have rt:=rotate_counts L.r
  simp only [program,restoreAt,subtract,unprepare,rightShift,unseed,arithmetic,
    toffoliCount_append,measurementCount_append,toffoliCount_reverse,measurementCount_reverse,
    c.1,c.2,r.1,r.2,a.1,a.2,e.1,e.2,sc.1,sc.2,rt.1,rt.2.1,
    (notRegister_counts L.r).1,(notRegister_counts L.r).2,List.length_tail,w.2.2.1]
  norm_num [toffoliCount,measurementCount]

theorem restoreScalars_inverse (p a d e u j b h : Wire)
    (hn : [p,a,d,e,u,j,b,h].Nodup) (s : State) (m : List Bool)
    (he : s.basis e=(s.basis a && s.basis u))
    (ha : s.basis a=((s.basis p && s.basis h) ^^ s.basis p ^^ s.basis d))
    (hd : s.basis d=(s.basis p && s.basis u))
    (hu : s.basis u=(s.basis j && s.basis b)) :
    run (restoreScalars p a d e u j b h) m
      ⟨s.phase,erasedBasis p a d e u j s.basis⟩=s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  rcases hn with ⟨⟨n01,n02,n03,n04,n05,n06,n07⟩,
    ⟨⟨n12,n13,n14,n15,n16,n17⟩,
    ⟨⟨n23,n24,n25,n26,n27⟩,
    ⟨⟨n34,n35,n36,n37⟩,
    ⟨⟨n45,n46,n47⟩,⟨⟨n56,n57⟩,n67⟩⟩⟩⟩⟩⟩
  have r01 : a≠p := Ne.symm n01
  have r02 : d≠p := Ne.symm n02
  have r03 : e≠p := Ne.symm n03
  have r04 : u≠p := Ne.symm n04
  have r05 : j≠p := Ne.symm n05
  have r06 : b≠p := Ne.symm n06
  have r07 : h≠p := Ne.symm n07
  have r12 : d≠a := Ne.symm n12
  have r13 : e≠a := Ne.symm n13
  have r14 : u≠a := Ne.symm n14
  have r15 : j≠a := Ne.symm n15
  have r16 : b≠a := Ne.symm n16
  have r17 : h≠a := Ne.symm n17
  have r23 : e≠d := Ne.symm n23
  have r24 : u≠d := Ne.symm n24
  have r25 : j≠d := Ne.symm n25
  have r26 : b≠d := Ne.symm n26
  have r27 : h≠d := Ne.symm n27
  have r34 : u≠e := Ne.symm n34
  have r35 : j≠e := Ne.symm n35
  have r36 : b≠e := Ne.symm n36
  have r37 : h≠e := Ne.symm n37
  have r45 : j≠u := Ne.symm n45
  have r46 : b≠u := Ne.symm n46
  have r47 : h≠u := Ne.symm n47
  have r56 : b≠j := Ne.symm n56
  have r57 : h≠j := Ne.symm n57
  have r67 : h≠b := Ne.symm n67
  have erased := EntryHalf5.eraseAnd j p u r45 n04
    (⟨s.phase,erasedBasis p a d e u j s.basis⟩ : State) m (by
      simp [erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67])
  change run ([.measureX u [] [.CZ j p]] ++
      [.CCX j b u,.CCX p u d,.CX p a,.CCX p h a,.CX d a,.CCX a u e]) m _=s
  rw [run_append,run_take,erased]
  apply State.extensionality
  · simp only [run]
  · funext q
    by_cases qa : q=a
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    by_cases qd : q=d
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    by_cases qe : q=e
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    by_cases qu : q=u
    · subst q
      simp [run,erasedBasis,writeBit,Function.update,n01,n02,n03,n04,n05,n06,n07,n12,n13,n14,n15,n16,n17,n23,n24,n25,n26,n27,n34,n35,n36,n37,n45,n46,n47,n56,n57,n67,r01,r02,r03,r04,r05,r06,r07,r12,r13,r14,r15,r16,r17,r23,r24,r25,r26,r27,r34,r35,r36,r37,r45,r46,r47,r56,r57,r67,ha,hd,he,hu,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    simp [run,erasedBasis,writeBit,Function.update,qa,qd,qe,qu]
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

def affineSub (bs : List Affine.Bit) (ys cs : List Wire) (ci : Wire) : Program :=
  notRegister ys ++ Affine.add bs ys cs ci ++ notRegister ys

theorem affine_value_lt (bs : List Affine.Bit) (s : BasisState) : Affine.value bs s<2^bs.length := by
  induction bs with
  | nil => simp [Affine.value]
  | cons b bs ih =>
    have h : (b.value s).toNat≤1 := by cases b.value s <;> decide
    simp only [Affine.value,List.length_cons,Nat.pow_succ]
    omega

theorem complement_inverse (A Y C N : Nat) (hA : A<N) (hY : Y<N) (hC : C≤1) :
    N-1-((A+(N-1-((A+Y+C)%N))+C)%N)=Y := by
  by_cases small : A+Y+C<N
  · rw [Nat.mod_eq_of_lt small]
    have equal : A+(N-1-(A+Y+C))+C=N-1-Y := by omega
    rw [equal,Nat.mod_eq_of_lt (by omega)]
    omega
  · have bound : A+Y+C-N<N := by omega
    have equal : A+Y+C=(A+Y+C-N)+N := by omega
    rw [equal,Nat.add_mod_right,Nat.mod_eq_of_lt bound]
    have inside : A+(N-1-(A+Y+C-N))+C=(N-1-Y)+N := by omega
    rw [inside,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega

theorem affineSub_spec (bits : List Affine.Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈Affine.sites bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hvalid : ∀b∈bits,b.Valid) :
    let out := run (affineSub bits ys carry cin) m s
    out.phase=s.phase ∧ (∀q,q∉ys → out.basis q=s.basis q) ∧
      regValue ys out.basis=2^ys.length-1-
        ((Affine.value bits s.basis+(2^ys.length-1-regValue ys s.basis)+(s.basis cin).toNat)%2^ys.length) := by
  have nd := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1
  have away (q : Wire) (hq : q∈cin::carry) : q∉ys := by
    intro bad
    have h:=List.nodup_iff_count.mp hn q
    have a:=List.count_pos_iff.mpr hq
    have b:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  let u : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have first (record : List Bool) : run (notRegister ys) record s=u := notRegister_correct ys nd s record
  have keep (q : Wire) (hq : q∉ys) : u.basis q=s.basis q := by simp [u,hq]
  have clean : ∀q∈carry,u.basis q=false := by
    intro q hq
    exact (keep q (away q (by simp [hq]))).trans (hclean q hq)
  have src : Affine.value bits u.basis=Affine.value bits s.basis := by
    apply Affine.value_congr
    intro q hq
    exact keep q (fun bad => hs q hq (by simp [bad]))
  have ci : u.basis cin=s.basis cin := keep cin (away cin (by simp))
  have inverted : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    rw [regValue_congr ys u.basis (fun q => !s.basis q) (by intro q hq;simp [u,hq]),regValue_complement]
  obtain ⟨phase,same,value⟩ := Affine.add_correct bits ys carry cin hn hs hl hc u m clean hvalid
  let v := run (Affine.add bits ys carry cin) m u
  have outvalue : regValue ys (fun q => if q∈ys then !v.basis q else v.basis q)=
      2^ys.length-1-regValue ys v.basis := by
    rw [regValue_congr ys _ (fun q => !v.basis q) (by intro q hq;simp [hq]),regValue_complement]
  have zeroM := (notRegister_counts ys).2
  simp only [affineSub,List.append_assoc,run_append,run_take,zeroM,List.take_zero,List.drop_zero]
  rw [first]
  change (run (notRegister ys) _ v).phase=s.phase ∧ _
  rw [notRegister_correct ys nd]
  refine ⟨phase,?_,?_⟩
  · intro q hq
    simp only [hq,if_false]
    exact (same q hq).trans (keep q hq)
  · rw [outvalue,value,src,inverted,ci]

theorem affineSub_inverse (bits : List Affine.Bit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin::(ys++carry)).Nodup)
    (hs : ∀q∈Affine.sites bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m n : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hvalid : ∀b∈bits,b.Valid) :
    run (affineSub bits ys carry cin) n (run (Affine.add bits ys carry cin) m s)=s := by
  let t:=run (Affine.add bits ys carry cin) m s
  have a:=Affine.add_correct bits ys carry cin hn hs hl hc s m hclean hvalid
  have away (q : Wire) (hq : q∈cin::carry) : q∉ys := by
    intro bad
    have h:=List.nodup_iff_count.mp hn q
    have x:=List.count_pos_iff.mpr hq
    have y:=List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h x
    omega
  have clean : ∀q∈carry,t.basis q=false := fun q hq =>
    (a.2.1 q (away q (by simp [hq]))).trans (hclean q hq)
  have b:=affineSub_spec bits ys carry cin hn hs hl hc t n clean hvalid
  have src : Affine.value bits t.basis=Affine.value bits s.basis := by
    apply Affine.value_congr
    intro q hq
    exact a.2.1 q (fun bad => hs q hq (by simp [bad]))
  have ci : t.basis cin=s.basis cin := a.2.1 cin (away cin (by simp))
  have val : regValue ys (run (affineSub bits ys carry cin) n t).basis=regValue ys s.basis := by
    rw [b.2.2,src,ci,a.2.2]
    exact complement_inverse _ _ _ _ (by simpa [hl] using affine_value_lt bits s.basis)
      (regValue_lt ys s.basis) (by cases s.basis cin <;> decide)
  apply State.extensionality
  · exact b.1.trans a.1
  · funext q
    by_cases qy : q∈ys
    · exact regValue_equal_bits ys _ _ val q qy
    · exact (b.2.1 q qy).trans (a.2.1 q qy)
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5 CleanInverse5
attribute [local irreducible] run

theorem rotateRight_proper (r : List Wire) (hn : r.Nodup) : ProperProgram (rotateRight r) := by
  induction r with
  | nil => simp [rotateRight,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,ProperProgram]
    | cons b r =>
      have nd:=List.nodup_cons.mp hn
      have ne : a≠b := fun e=>nd.1 (by simp [e])
      exact (properProgram_append _ _).mpr
        ⟨by simp [swapBits,ProperProgram,ProperGate,ne,Ne.symm ne],ih nd.2⟩

theorem rightShift_proper (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ProperProgram (rightShift L) := by
  have len:=BalancedCleanup.widths L.toLayout hw
  have nd:=EntryHalf5.target_nodup L hn
  have lt : 254<L.low.length := by rw [len.1];decide
  have ix : 254<L.r.length := by rw [len.2.1];decide
  have eq : L.r.getD 254 0=L.low[254] := by
    rw [List.getD_eq_getElem _ _ ix]
    exact (List.getElem_append_left' lt [L.rmsb]).symm
  have away : L.rmsb∉L.low := fun h=>List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h (by simp)
  have ne : L.r.getD 254 0≠L.rmsb := by
    rw [eq]
    exact fun e=>away (e ▸ List.getElem_mem lt)
  exact (properProgram_append _ _).mpr
    ⟨rotateRight_proper L.r nd,by simpa [ProperProgram,ProperGate] using ne⟩

theorem seed_ready (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State)
    (zp : s.basis L.parity=false) (za : s.basis L.lower=false)
    (zd : s.basis L.one=false) (ze : s.basis L.sign=false) :
    Ready (productsSeed L) s := by
  have nd : [L.r0,L.rmsb,L.parity,L.lower,L.one,L.sign,lowY L].Nodup := by
    cases hy : L.ylow with
    | nil => have h:=hw.2.1;simp [hy] at h
    | cons a as =>
      apply List.nodup_iff_count.mpr
      intro q
      have h:=List.nodup_iff_count.mp hn q
      simp only [Layout.wires,BalancedCleanup.Layout.wires,lowY,hy,List.getD_cons_zero,
        List.count_append,List.count_cons,List.count_nil] at h ⊢
      omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03,n04,n05,n06⟩,⟨⟨n12,n13,n14,n15,n16⟩,
    ⟨⟨n23,n24,n25,n26⟩,⟨⟨n34,n35,n36⟩,⟨⟨n45,n46⟩,n56⟩⟩⟩⟩⟩
  simp [productsSeed,Ready,CleanTarget,ProperGate,run,writeBit,Function.update,
    zp,za,zd,ze,n01,n02,n03,n04,n05,n06,n12,n13,n14,n15,n16,n23,n24,n25,n26,
    n34,n35,n36,n45,n46,n56,Ne.symm n01,Ne.symm n02,Ne.symm n03,Ne.symm n04,
    Ne.symm n05,Ne.symm n06,Ne.symm n12,Ne.symm n13,Ne.symm n14,Ne.symm n15,
    Ne.symm n16,Ne.symm n23,Ne.symm n24,Ne.symm n25,Ne.symm n26,
    Ne.symm n34,Ne.symm n35,Ne.symm n36,Ne.symm n45,Ne.symm n46,Ne.symm n56]

theorem prepare_ready (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (s : State)
    (hy : regValue L.y s.basis=0) (hc : ∀q∈work L,s.basis q=false)
    (hz : s.basis L.sign=false) : Ready (prepare L J B) s := by
  have len:=BalancedCleanup.widths L.toLayout hw
  have yhead:=y_cons L hw
  have y0 : lowY L∈L.y := by rw [yhead];simp
  have yn : L.y.Nodup := by
    have nd:=allND L hn
    exact (List.nodup_append'.mp (List.nodup_append'.mp
      (List.nodup_append'.mp nd).2.1).1).2.1
  have ya : lowY L∉L.y.tail := by rw [yhead] at yn;exact (List.nodup_cons.mp yn).1
  have notY (q : Wire) (h : q∉L.wires) : q∉L.y :=
    fun bad=>h (data_member L q (by simp [bad]))
  have nj : J≠lowY L := fun e=>notY J hJ (e.symm ▸ y0)
  have nb : B≠lowY L := fun e=>notY B hB (e.symm ▸ y0)
  have ys : ∀q∈L.y,s.basis q=false := (regValue_zero _ _).mp hy
  let u:=run [.CCX J B (lowY L)] [] s
  have nd : (J::L.r.tail++L.y.tail).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have jp : J∉L.r.tail++L.y.tail := by
      intro bad
      rcases List.mem_append.mp bad with bad|bad
      · exact hJ (data_member L J (by simp [List.mem_of_mem_tail bad]))
      · exact hJ (data_member L J (by simp [List.mem_of_mem_tail bad]))
    have c:=List.nodup_iff_count.mp (copyND L hn) q
    by_cases eq : q=J
    · subst q;simp [jp,List.count_eq_zero.mpr jp]
    · simpa [List.count_cons,eq,Ne.symm eq] using c
  have tail := copy_ready J L.r.tail L.y.tail u nd (by
    intro q hq
    have ne : q≠lowY L := fun e=>ya (e ▸ hq)
    simpa only [u,run,writeBit,Function.update_of_ne ne] using ys q (List.mem_of_mem_tail hq))
  have copy : Ready (copyControl L J B) s := by
    change ProperGate (.CCX J B (lowY L)) ∧ s.basis (lowY L)=false ∧ _
    exact ⟨⟨nj,nb⟩,ys _ y0,tail⟩
  let v:=run (copyControl L J B) [] s
  have cp:=copyControl_spec L hw hn J B hJ hB (s.basis J) (s.basis B)
    (regValue L.r s.basis) s [] rfl hy rfl rfl
  have fl (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : v.basis q=false := by
    have away : q∉L.y := by
      intro bad
      have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
        simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
        tauto
      exact flagAway L hn q mem (by simp [bad])
    rw [show v.basis q=s.basis q from cp.2.2.2 q away]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact hc _ (by simp [work])
    · exact hc _ (by simp [work])
    · exact hc _ (by simp [work])
    · exact hz
  have seed:=seed_ready L hw hn v (fl _ (by simp)) (fl _ (by simp))
    (fl _ (by simp)) (fl _ (by simp))
  have shift : ∀t,Ready (rightShift L) t :=
    ready_zero _ (rightShift_proper L hw hn) (by
      simp [rightShift,toffoliCount_append,(rotate_counts L.r).1,toffoliCount])
  have nr : lowY L∉L.r := by
    have d:=allND L hn
    have dis:=(List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp d).2.1).1).2.2
    exact fun bad=>List.disjoint_left.mp dis bad y0
  have comp : ∀t,Ready (signComplement (lowY L) L.r) t :=
    ready_zero _ (BalancedCleanup.complement_proper _ _ nr) (signComplement_counts _ _).1
  rw [prepare_shape]
  apply (ready_append _ _ _).mpr
  refine ⟨?_,comp _⟩
  apply (ready_append _ _ _).mpr
  refine ⟨?_,shift _⟩
  exact (ready_append _ _ _).mpr ⟨copy,seed⟩
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

theorem clear_xor (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParity L J) m s=⟨s.phase,writeBit s.basis L.parity
      (s.basis L.parity ^^ s.basis (lowY L) ^^
        ((!s.basis J) && decide (EntryHalf5.threshold<R.natAbs)))⟩ := by
  let u : State := ⟨s.phase,writeBit s.basis L.parity
    (s.basis L.parity ^^ s.basis (lowY L))⟩
  have pa := flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity :=
    fun e=>pa (e ▸ hq)
  have lp : L.lower≠L.parity := by
    have nd:=List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have jp : J≠L.parity := fun e=>hJ (by simp [e,Layout.wires,BalancedCleanup.Layout.wires])
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hR
    intro q hq
    simp [u,writeBit,away q (by simp [hq])]
  have core:=EntryHalf5.recoverParity_xor L hw hn J hJ (s.basis J) R hr u m ur
    (by simp [u,writeBit,jp]) (by simpa [u,writeBit,lp] using hl)
    (fun q hq=>by simpa [u,writeBit,away q (by simp [hq])] using hc q hq)
  have first : run [.CX (lowY L) L.parity] [] s=u := by simp [run,u]
  change run ([.CX (lowY L) L.parity]++EntryHalf5.recoverParity L J) m s=_
  rw [run_append,show measurementCount [.CX (lowY L) L.parity]=0 from rfl,
    List.take_zero,List.drop_zero,first,core]
  apply State.extensionality
  · rfl
  · funext q
    by_cases qp : q=L.parity
    · subst q;simp [u,writeBit]
    · simp [u,writeBit,qp]

theorem clear_involution (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (R : Int) (hr : Centered R) (s : State) (m n : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (clearParity L J) n (run (clearParity L J) m s)=s := by
  let u:=run (clearParity L J) m s
  have a:=clear_xor L hw hn J hJ R hr s m hR hl hc
  have pa:=flagAway L hn L.parity (by simp)
  have away (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e=>pa (e ▸ hq)
  have same (q : Wire) (hq : q≠L.parity) : u.basis q=s.basis q := by
    rw [show u= _ from a]
    simp [writeBit,hq]
  have lp : L.lower≠L.parity := by
    have nd:=List.nodup_iff_count.mp (scalarND L hn) L.lower
    intro e;simp [e,List.count_cons] at nd;omega
  have jp : J≠L.parity := fun e=>hJ (by simp [e,Layout.wires,BalancedCleanup.Layout.wires])
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have yp : lowY L≠L.parity := away (lowY L) (by
    simp only [List.mem_append];exact Or.inl (Or.inr y0))
  have ur : regValue L.r u.basis=encodeWord 256 R := by
    apply Eq.trans (regValue_congr _ _ _ (fun q hq=>same q (away q (by simp [hq])))) hR
  have b:=clear_xor L hw hn J hJ R hr u n ur ((same _ lp).trans hl)
    (fun q hq=>(same q (away q (by simp [hq]))).trans (hc q hq))
  change run (clearParity L J) n u=s
  rw [b]
  apply State.extensionality
  · rw [show u= _ from a]
  · funext q
    by_cases qp : q=L.parity
    · subst q
      simp only [writeBit,Function.update_self]
      rw [same (lowY L) yp,same J jp]
      rw [show u= _ from a]
      simp [writeBit,yp,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]
    · simp only [writeBit,Function.update_of_ne qp]
      exact same q qp
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5 CleanInverse5
attribute [local irreducible] run

def programC (L : Layout) (J B : Wire) : Program :=
  clearParity L J ++ restoreAt L J B ++ affineSub (sources L) L.r (L.carry.take 255) (lowY L) ++
    CleanInverse5.inverse (prepare L J B)

theorem programC_counts (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) :
    toffoliCount (programC L J B)=515 ∧ measurementCount (programC L J B)=770 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have k:=CleanInverse5.counts (prepare L J B) (ready_proper _ _ ready)
  have c:=clearParity_counts L hw J
  have r:=restoreScalars_counts L.parity L.lower L.one L.sign (lowY L) J B L.rmsb
  have a:=arithmetic_counts L hw
  have p:=prepare_counts L hw J B
  unfold arithmetic at a
  simp only [programC,restoreAt,affineSub,toffoliCount_append,measurementCount_append,
    k.1,k.2,c.1,c.2,r.1,r.2,a.1,a.2,p.1,
    (notRegister_counts L.r).1,(notRegister_counts L.r).2]
  decide

theorem inverse_forward (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (programC L J B) m (run (EntryRetained5.program L J B) [] s)=s := by
  let a:=run (prepare L J B) [] s
  let b:=run (arithmetic L) [] a
  let c:=run (eraseScalarsAt L J B) [] b
  have prep:=prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  change Prepared L J B Jv Bv Y s a at prep
  have pref:=prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have prefix_run : run (prefixProgram L J B) [] s=b := by
    simp only [prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [prefix_run] at pref
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  have erased:=eraseScalarsAt_run L hw hn J B hJ hB hJB b [] ee aa dd uu
  change c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ at erased
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have restore:=restoreScalars_inverse L.parity L.lower L.one L.sign (lowY L) J B L.rmsb en b
  have undoRestore (n : List Bool) : run (restoreAt L J B) n c=b := by
    rw [erased]
    exact restore n ee aa dd uu
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have undoClear (n : List Bool) :
      run (clearParity L J) n (run (clearParity L J) [] c)=c :=
    clear_involution L hw hn J hJ _ rc c [] n cR ca cCarry
  have undoAdd (n : List Bool) :
      run (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) n b=a := by
    exact affineSub_inverse _ _ _ _ (arithmeticND L hw hn) (sources_away L hw hn)
      (by rw [sources_length,(BalancedCleanup.widths L.toLayout hw).2.1])
      (by simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).2.1]) a [] n
      (fun q hq=>prep.carry q (List.mem_of_mem_take hq)) (sources_valid L hn)
  have undoPrep (n : List Bool) : run (CleanInverse5.inverse (prepare L J B)) n a=s :=
    CleanInverse5.inverse_run _ _ (prepare_ready L hw hn J B hJ hB s hY hc hz) n
  have forward_run : run (EntryRetained5.program L J B) [] s=run (clearParity L J) [] c := by
    simp only [EntryRetained5.program,prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [forward_run,programC]
  simp only [List.append_assoc,run_append,run_take]
  rw [undoClear,undoRestore,undoAdd,undoPrep]
end ECDSAAdd.Entrant.FirstInverse5


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5
attribute [local irreducible] run

def putWord : List Wire → Nat → BasisState → BasisState
  | [],_,s => s
  | q::qs,v,s => writeBit (putWord qs (v/2) s) q (decide (v%2=1))

theorem putWord_outside (xs : List Wire) (v : Nat) (s : BasisState) (q : Wire) (hq : q∉xs) :
    putWord xs v s q=s q := by
  induction xs generalizing v with
  | nil => rfl
  | cons a xs ih =>
    have h : q≠a ∧ q∉xs := by simpa using hq
    simp only [putWord,writeBit,Function.update_of_ne h.1,ih _ h.2]

theorem putWord_value (xs : List Wire) (hn : xs.Nodup) (v : Nat) (hv : v<2^xs.length)
    (s : BasisState) : regValue xs (putWord xs v s)=v := by
  induction xs generalizing v with
  | nil =>
    have h : v=0 := by simpa using hv
    subst v
    rfl
  | cons a xs ih =>
    have nd:=List.nodup_cons.mp hn
    have lt : v/2<2^xs.length := by rw [List.length_cons,Nat.pow_succ] at hv;omega
    have tail : regValue xs (putWord (a::xs) v s)=regValue xs (putWord xs (v/2) s) := by
      apply regValue_congr
      intro q hq
      have ne : q≠a := fun e=>nd.1 (e ▸ hq)
      simp [putWord,writeBit,ne]
    change (if putWord (a::xs) v s a then 1 else 0)+2*regValue xs (putWord (a::xs) v s)=v
    rw [tail,ih nd.2 _ lt]
    simp only [putWord,writeBit,Function.update_self]
    have mod:=Nat.mod_lt v (by decide : 0<2)
    have div:=Nat.mod_add_div v 2
    by_cases odd : v%2=1 <;> simp [odd] <;> omega

theorem inverse_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hY : regValue L.y s.basis=encodeWord 256 (if Jv then Y else 0))
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    let out:=run (programC L J B) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis (encodeWord 256 Y) 0 out.basis := by
  let t : State:=⟨s.phase,putWord L.r (encodeWord 256 Y) (putWord L.y 0 s.basis)⟩
  have len:=BalancedCleanup.widths L.toLayout hw
  have nd:=allND L hn
  have nr:=EntryHalf5.target_nodup L hn
  have ny : L.y.Nodup := by
    exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.1
  have dis : List.Disjoint L.r L.y :=
    (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.2
  have outside (q : Wire) (qr : q∉L.r) (qy : q∉L.y) : t.basis q=s.basis q := by
    simp only [t,putWord_outside _ _ _ q qr,putWord_outside _ _ _ q qy]
  have tr : regValue L.r t.basis=encodeWord 256 Y :=
    putWord_value L.r nr _ (by rw [len.2.1];exact encodeWord_bound 256 Y) _
  have ty : regValue L.y t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (putWord_value L.y ny 0 (Nat.two_pow_pos _) s.basis)
    intro q hq
    apply putWord_outside
    exact fun bad=>List.disjoint_left.mp dis bad hq
  have noData (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (data_member L q (by simp [bad]))
    · exact hq (data_member L q (by simp [bad]))
  have workAway (q : Wire) (hq : q∈work L) : q∉L.r ∧ q∉L.y := by
    have n:=List.nodup_iff_count.mp nd q
    have w:=List.count_pos_iff.mpr hq
    constructor <;> intro bad <;> have b:=List.count_pos_iff.mpr bad
    all_goals
      simp only [work,List.count_append,List.count_cons,List.count_nil] at w
      simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,BalancedCleanup.Layout.low,
        List.count_append,List.count_cons,List.count_nil] at n b
      omega
  have tc : ∀q∈work L,t.basis q=false := fun q hq=>
    (outside q (workAway q hq).1 (workAway q hq).2).trans (hc q hq)
  have signAway : L.sign∉L.r ∧ L.sign∉L.y := by
    have h:=flagAway L hn L.sign (by simp)
    exact ⟨fun a=>h (by simp [a]),fun a=>h (by simp [a])⟩
  have tz : t.basis L.sign=false := (outside _ signAway.1 signAway.2).trans hz
  have tj : t.basis J=Jv := (outside J (noData J hJ).1 (noData J hJ).2).trans hj
  have tb : t.basis B=Bv := (outside B (noData B hB).1 (noData B hB).2).trans hb
  have f:=EntryRetained5.program_frame L hw hn J B hJ hB hJB Jv Bv Y hy t [] tr ty tc tz tj tb
  have ss : PairFrame L.r L.y t.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) s.basis :=
    ⟨hR,hY,fun q qr qy=>(outside q qr qy).symm⟩
  have eq : run (EntryRetained5.program L J B) [] t=s := by
    apply State.extensionality
    · exact f.1
    · exact PairFrame.unique _ _ _ _ _ _ _ f.2 ss
  have inv:=inverse_forward L hw hn J B hJ hB hJB Jv Bv Y hy t m tr ty tc tz tj tb
  rw [eq] at inv
  dsimp only
  rw [inv]
  exact ⟨rfl,tr,ty,outside⟩
end ECDSAAdd.Entrant.FirstInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.CleanInverse5
open Arithmetic Challenge Baselines RecordedQuantum

theorem inverse_support (p : Program) : wires (inverse p)⊆wires p := by
  induction p with
  | nil => simp [inverse]
  | cons i p ih =>
    cases i <;> simp only [inverse,wires_append,Finset.union_subset_iff]
    all_goals constructor
    all_goals first
      | exact ih.trans (Finset.subset_union_right)
      | intro q hq
        simp_all [undo,wires,Instr.wires,correctionWires] <;> tauto

theorem inverse_physical (p : Program) (hp : GatePhysical p) : GatePhysical (inverse p) := by
  induction p with
  | nil => simp [inverse,GatePhysical]
  | cons i p ih =>
    have ht : GatePhysical p := fun j hj=>hp j (by simp [hj])
    have hi:=hp i (by simp)
    rw [inverse,gatePhysical_append]
    refine ⟨ih ht,?_⟩
    cases i <;> simp_all [undo,GatePhysical,PhysicalInstr,ProperGate]

theorem inverse_slots (p : Program) (hp : ProperProgram p) :
    gateSlots (inverse p)≤gateSlots p+toffoliCount p := by
  induction p with
  | nil => simp [inverse,gateSlots]
  | cons i p ih =>
    have hi:=hp i (by simp)
    have h:=ih (fun j hj=>hp j (by simp [hj]))
    cases i <;> simp_all [ProperGate,inverse,undo,gateSlots_append,gateSlots,
      instructionSlots,toffoliCount] <;> omega
end ECDSAAdd.Entrant.CleanInverse5

namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField EntryRetained5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem programC_support (L : Layout) (hw : L.Widths) (J B : Wire) :
    wires (programC L J B)⊆retSites L J B := by
  have old:=EntryRetained5.program_support L hw J B
  have parts : ((wires (prepare L J B)⊆retSites L J B ∧ wires (arithmetic L)⊆retSites L J B) ∧
      wires (eraseScalarsAt L J B)⊆retSites L J B) ∧ wires (clearParity L J)⊆retSites L J B := by
    simpa only [EntryRetained5.program,prefixProgram,wires_append,Finset.union_subset_iff] using old
  have r (q : Wire) (hq : q∈L.r) : q∈retSites L J B := by simp [retSites,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈retSites L J B := by simp [retSites,hq]
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have erase : wires (restoreAt L J B)⊆retSites L J B := by
    intro q hq
    simp only [restoreAt,restoreScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    have hu:=y (lowY L) y0
    have hh:=r L.rmsb rh
    have hp : L.parity∈retSites L J B := by simp [retSites]
    have ha : L.lower∈retSites L J B := by simp [retSites]
    have hd : L.one∈retSites L J B := by simp [retSites]
    have he : L.sign∈retSites L J B := by simp [retSites]
    have hj : J∈retSites L J B := by simp [retSites]
    have hb : B∈retSites L J B := by simp [retSites]
    aesop

  have notr : wires (notRegister L.r)⊆retSites L J B := by
    rw [notRegister_wires]
    intro q hq
    exact r q (List.mem_toFinset.mp hq)
  have sub : wires (affineSub (sources L) L.r (L.carry.take 255) (lowY L))⊆retSites L J B := by
    simp only [affineSub,wires_append,Finset.union_subset_iff]
    exact ⟨⟨notr,parts.1.1.2⟩,notr⟩
  simp only [programC,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨parts.2,erase⟩,sub⟩,(CleanInverse5.inverse_support _).trans parts.1.1.1⟩

theorem programC_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (programC L J B) := by
  have old:=EntryRetained5.program_physical L hw hn J B hJ hB hJB
  have parts : ((GatePhysical (prepare L J B) ∧ GatePhysical (arithmetic L)) ∧
      GatePhysical (eraseScalarsAt L J B)) ∧ GatePhysical (clearParity L J) := by
    simpa only [EntryRetained5.program,prefixProgram,gatePhysical_append] using old
  have n:=erasePorts_nodup L hw hn J B hJ hB hJB
  have ctr : (lowY L)≠J ∧ L.parity≠L.lower ∧ (lowY L)≠L.one ∧ L.parity≠L.one ∧
      L.rmsb≠L.lower ∧ L.one≠L.lower ∧ L.lower≠L.sign ∧ (lowY L)≠L.sign ∧ J≠lowY L ∧ B≠lowY L := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at n
    rcases n with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
      ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
    exact ⟨uJ,pA,Ne.symm dU,pD,Ne.symm aH,Ne.symm aD,aE,Ne.symm eU,
      Ne.symm uJ,Ne.symm uB⟩
  have restore : GatePhysical (restoreAt L J B) := by
    simp [restoreAt,restoreScalars,GatePhysical,PhysicalInstr,ProperGate,ctr.1,ctr.2.1,
      ctr.2.2.1,ctr.2.2.2.1,ctr.2.2.2.2.1,ctr.2.2.2.2.2.1,
      ctr.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.2]
  have sub : GatePhysical (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) := by
    simp only [affineSub,gatePhysical_append]
    exact ⟨⟨notRegister_physical _,parts.1.1.2⟩,notRegister_physical _⟩
  simp only [programC,gatePhysical_append]
  exact ⟨⟨⟨parts.2,restore⟩,sub⟩,CleanInverse5.inverse_physical _ parts.1.1.1⟩

theorem programC_slots (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) : gateSlots (programC L J B)≤10000 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have inv:=CleanInverse5.inverse_slots _ (CleanInverse5.ready_proper _ _ ready)
  have prep:=prepare_slots_le L hw J B
  have arith:=arithmetic_slots L hw
  have par:=clearParity_slots_le L hw J
  have pc:=prepare_counts L hw J B
  have xr:=notRegister_gateSlots L.r
  have len:=BalancedCleanup.widths L.toLayout hw
  have rest : gateSlots (restoreAt L J B)=8 := rfl
  simp only [programC,affineSub,gateSlots_append,show Affine.add (sources L) L.r
    (L.carry.take 255) (lowY L)=arithmetic L from rfl,xr,len.2.1,arith,rest]
  omega
end ECDSAAdd.Entrant.FirstInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField

def jointInv (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G] ++ programC L J G ++ [.X G]


theorem jointInv_counts (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) :
    toffoliCount (jointInv L J G)=515 ∧ measurementCount (jointInv L J G)=770 := by
  have h:=programC_counts L hw hn J G hJ hG
  simpa only [jointInv,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using h

private theorem outside_layout (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem jointInv_frame (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
    (hY : regValue L.y s.basis = encodeWord 256 (if Jv then Y else 0))
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (jointInv L J G) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 Y) 0 out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layout L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=encodeWord 256 (if Jv then Y else 0) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (programC L J G)
    (m.take (measurementCount (programC L J G))) a=t
  have result := inverse_frame L hw hn J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (programC L J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (jointInv L J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [jointInv,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]

end ECDSAAdd.Entrant.FirstInverse5

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.FirstInverse5
open Arithmetic BalancedCircuit BalancedField Secp256k1
attribute [local irreducible] run

theorem unary_half (b : Bool) (Z : Fp) :
    halfResult (signedY b (centerFp Z))=centerFp ((if b then -Z else Z)/2) := by
  have h:=signedY_bounds b (centerFp Z) (centerFp_bounds Z)
  have q0 : 0≤BalancedField.q := (BalancedField.constants).1.le
  have bounds : -(2*BalancedField.q)≤signedY b (centerFp Z) ∧
      signedY b (centerFp Z)≤2*BalancedField.q := by
    unfold Centered at h
    omega
  have hh:=halfResult_center _ bounds
  cases b <;> simpa only [signedY,Bool.false_eq_true,if_false,if_true,Int.cast_neg,centerFp_cast] using hh

theorem source_word (b : Bool) (Z : Fp) :
    encodeWord 256 (if b then centerFp Z else 0)=centerWord (if b then Z else 0) := by
  cases b
  · simp [centerWord,centerFp,encodeWord,show (0:Int)≤q from (constants).1.le]
  · rfl

theorem work_no_data (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈work L) :
    q∉L.r ∧ q∉L.y := by
  have nd:=allND L hn
  have h:=List.nodup_iff_count.mp nd q
  have w:=List.count_pos_iff.mpr hq
  constructor <;> intro bad <;> have b:=List.count_pos_iff.mpr bad
  all_goals
    simp only [work,List.count_append,List.count_cons,List.count_nil] at w
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at h b
    omega

theorem jointInv_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin
      (centerWord ((if origin J && !origin G then -Z else Z)/2))
      (centerWord (if origin J then Z else 0))) (jointInv L J G)
      (PairFrame L.r L.y origin (centerWord Z) 0) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have rr : regValue L.r s.basis=encodeWord 256
      (halfResult (signedY (origin J && !origin G) (centerFp Z))) := by
    rw [unary_half]
    exact h.1
  have yy : regValue L.y s.basis=encodeWord 256 (if origin J then centerFp Z else 0) := by
    rw [source_word]
    exact h.2.1
  have out:=jointInv_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m rr yy hc ((h.2.2 _ sa.1 sa.2).trans sign)
    (h.2.2 _ (outside J hJ).1 (outside J hJ).2) (h.2.2 _ (outside G hG).1 (outside G hG).2)
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩

theorem matrix_inverse (J G : Bool) (X Y : Fp)
    (hz : (if J then 2*X+(if G then -Y else Y) else Y)=0) :
    let Z:=if J then Y else 2*X+(if G then -Y else Y)
    X=(if J && !G then -Z else Z)/2 ∧ Y=(if J then Z else 0) := by
  have two : (2:Fp)≠0 := by decide
  cases J
  · simp only [Bool.false_eq_true,if_false,Bool.false_and] at hz ⊢
    rw [hz]
    cases G <;> simp [mul_div_cancel_left₀ X two]
  · simp only [if_true,Bool.true_and] at hz ⊢
    refine ⟨?_,trivial⟩
    cases G <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false] at hz ⊢
    all_goals apply (eq_div_iff two).mpr
    · linear_combination hz
    · linear_combination hz
end ECDSAAdd.Entrant.FirstInverse5


/-! ## Hosting the two carries that have no physical site in the 1,588 layout -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

/-- Carry #4 (virtual `516`) and carry #254 (virtual `1541`). -/
def cLo (L : Layout) : Wire := L.carry.getD 4 0
def cHi (L : Layout) : Wire := L.carry.getD 254 0

theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s)=s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (Equiv.swap a b (Equiv.swap a b q))=s.basis q
    rw [Equiv.swap_apply_self]

/-- A program may run with two clean sites exchanged. -/
theorem rebind_swap_run (a b : Wire) (P : Program) (s : State) (m : List Bool)
    (ha : s.basis a=false) (hb : s.basis b=false)
    (oa : (run P m s).basis a=false) (ob : (run P m s).basis b=false) :
    run (renameProgram (Equiv.swap a b) P) m s=run P m s := by
  have eq := ECDSAAdd.run_rename (Equiv.swap a b) (Equiv.swap a b).injective P m s
  rw [pullState_zero_swap a b s ha hb,
    ←pullState_zero_swap a b (run P m s) oa ob] at eq
  have both := congrArg (pullState (Equiv.swap a b)) eq
  simpa only [pull_swap_invol] using both

/-! ### Records -/

theorem append_split (l r : List Bool) (n : Nat) (hl : l.length≤n)
    (hr : l.length<n → r=[]) : (l++r).take n=l ∧ (l++r).drop n=r := by
  rcases Nat.lt_or_ge l.length n with h|h
  · have e := hr h
    subst e
    simp only [List.append_nil]
    exact ⟨List.take_of_length_le hl,List.drop_eq_nil_of_le hl⟩
  · have e : l.length=n := le_antisymm hl h
    subst e
    simp

/-- Replace a block `P` by a block `Q` whose first `k` records are extra. -/
theorem context_eq (Pre P Q Post : Program) (k : Nat) (s : State) (m : List Bool)
    (hpre : measurementCount Pre=0) (hq : measurementCount Q=k+measurementCount P)
    (hrun : ∀r,run Q r (run Pre [] s)=run P (r.drop k) (run Pre [] s)) :
    run (Pre++Q++Post) m s=
      run (Pre++P++Post) ((m.drop k).take (measurementCount P)++m.drop (measurementCount Q)) s := by
  let A := (m.drop k).take (measurementCount P)
  let B := m.drop (measurementCount Q)
  have lenA : A.length≤measurementCount P := List.length_take_le _ _
  have short : A.length<measurementCount P → B=[] := by
    intro h
    have hA : A.length=(m.drop k).length := by
      simp only [A,List.length_take] at h ⊢
      omega
    have : m.length≤measurementCount Q := by
      simp only [List.length_drop] at hA
      omega
    exact List.drop_eq_nil_of_le this
  have sp := append_split A B (measurementCount P) lenA short
  rw [List.append_assoc,run_append,hpre,List.take_zero,List.drop_zero,run_append,
    List.append_assoc,run_append,hpre,List.take_zero,List.drop_zero,run_append,sp.1,sp.2,
    hrun]
  congr 2
  simp only [A]
  rw [List.drop_take,hq,Nat.add_sub_cancel_left]

/-! ### The measured loan of `sign` (= lower∧lowY) and `lowY` (= J∧B) -/

def loanW (e a u j b lo hi : Wire) (P : Program) : Program :=
  [.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]]++
    renameProgram (Equiv.swap hi e) (renameProgram (Equiv.swap lo u) P)++
    [.CCX j b u,.CCX a u e]

theorem loanW_counts (e a u j b lo hi : Wire) (P : Program) :
    toffoliCount (loanW e a u j b lo hi P)=toffoliCount P+2 ∧
    measurementCount (loanW e a u j b lo hi P)=2+measurementCount P := by
  have r1 := renameProgram_counts (Equiv.swap lo u) P
  have r2 := renameProgram_counts (Equiv.swap hi e) (renameProgram (Equiv.swap lo u) P)
  simp only [loanW,toffoliCount_append,measurementCount_append,r1.1,r1.2,r2.1,r2.2,
    toffoliCount,measurementCount]
  omega

theorem loanW_run (e a u j b lo hi : Wire) (P : Program) (x : State) (r : List Bool)
    (nd : [e,a,u,j,b,lo,hi].Nodup)
    (he : x.basis e=(x.basis a && x.basis u)) (hu : x.basis u=(x.basis j && x.basis b))
    (ue : u∉wires P) (ee : e∉wires P)
    (keep : ∀t,(run P t x).basis a=x.basis a ∧ (run P t x).basis j=x.basis j ∧
      (run P t x).basis b=x.basis b)
    (lo0 : x.basis lo=false) (hi0 : x.basis hi=false)
    (loOut : ∀t,(run P t x).basis lo=false) (hiOut : ∀t,(run P t x).basis hi=false) :
    run (loanW e a u j b lo hi P) r x=run P (r.drop 2) x := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨ea,eu,ej,eb,elo,ehi⟩,⟨⟨au,aj,ab,alo,ahi⟩,⟨⟨uj,ub,ulo,uhi⟩,
    ⟨⟨jb,jlo,jhi⟩,⟨⟨blo,bhi⟩,lohi⟩⟩⟩⟩⟩
  let t := r.drop 2
  let x1 : State := ⟨x.phase,writeBit x.basis e false⟩
  let x2 : State := ⟨x.phase,writeBit (writeBit x.basis e false) u false⟩
  have step1 : run [.measureX e [] [.CZ a u]] (r.take 1) x=x1 :=
    EntryHalf5.eraseAnd a u e (Ne.symm ea) (Ne.symm eu) x _ he
  have step2 : run [.measureX u [] [.CZ j b]] ((r.drop 1).take 1) x1=x2 := by
    have h := EntryHalf5.eraseAnd j b u (Ne.symm uj) (Ne.symm ub) x1 ((r.drop 1).take 1) (by
      simp only [x1,writeBit,Function.update_of_ne (Ne.symm eu),Function.update_of_ne (Ne.symm ej),
        Function.update_of_ne (Ne.symm eb)]
      exact hu)
    simpa only [x1,x2] using h
  have unloan : run [.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]] (r.take 2) x=x2 := by
    have split : ([.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]] : Program)=
        [.measureX e [] [.CZ a u]]++[.measureX u [] [.CZ j b]] := rfl
    rw [split,run_append]
    have c1 : measurementCount ([.measureX e [] [.CZ a u]] : Program)=1 := rfl
    rw [c1,List.take_take,show min 1 2=1 from rfl,step1,List.drop_take]
    simpa only [show 2-1=1 from rfl] using step2
  -- running `P` on the zeroed state
  have w1 := G0CarryLoan5.run_write_outside P e ee x t false
  have w2 := G0CarryLoan5.run_write_outside P u ue x1 t false
  let y := run P t x
  have yrun : run P t x2=⟨y.phase,writeBit (writeBit y.basis e false) u false⟩ := by
    change run P t ⟨x1.phase,writeBit x1.basis u false⟩=_
    rw [w2]
    change (⟨(run P t ⟨x.phase,writeBit x.basis e false⟩).phase,
      writeBit (run P t ⟨x.phase,writeBit x.basis e false⟩).basis u false⟩ : State)=_
    rw [w1]
  have yu : y.basis u=x.basis u := run_preserves_outside P t x u ue
  have ye : y.basis e=x.basis e := run_preserves_outside P t x e ee
  have k := keep t
  -- rebinding the two hosts
  have inner : run (renameProgram (Equiv.swap lo u) P) t x2=run P t x2 := by
    apply rebind_swap_run lo u P x2 t
    · simp only [x2,writeBit,Function.update_of_ne (Ne.symm ulo),Function.update_of_ne (Ne.symm elo)]
      exact lo0
    · simp only [x2,writeBit,Function.update_self]
    · rw [yrun]
      simp only [writeBit,Function.update_of_ne (Ne.symm ulo),Function.update_of_ne (Ne.symm elo)]
      exact loOut t
    · rw [yrun]
      simp only [writeBit,Function.update_self]
  have outer : run (renameProgram (Equiv.swap hi e) (renameProgram (Equiv.swap lo u) P)) t x2=
      run P t x2 := by
    rw [rebind_swap_run hi e _ x2 t ?_ ?_ ?_ ?_,inner]
    · simp only [x2,writeBit,Function.update_of_ne (Ne.symm uhi),Function.update_of_ne (Ne.symm ehi)]
      exact hi0
    · simp only [x2,writeBit,Function.update_of_ne eu,Function.update_self]
    · rw [inner,yrun]
      simp only [writeBit,Function.update_of_ne (Ne.symm uhi),Function.update_of_ne (Ne.symm ehi)]
      exact hiOut t
    · rw [inner,yrun]
      simp only [writeBit,Function.update_of_ne eu,Function.update_self]
  have c2 : measurementCount ([.measureX e [] [.CZ a u],.measureX u [] [.CZ j b]] : Program)=2 := rfl
  rw [loanW,List.append_assoc,run_append,c2,unloan,run_append,run_take,outer,yrun]
  have ya : y.basis a=x.basis a := k.1
  have yj : y.basis j=x.basis j := k.2.1
  have yb : y.basis b=x.basis b := k.2.2
  change _=y
  apply State.extensionality
  · simp only [run]
  · funext q
    simp only [run,writeBit,Function.update_apply]
    by_cases qe : q=e
    · subst q
      simp [Ne.symm eu,Ne.symm ea,Ne.symm ej,Ne.symm eb,au,aj,ab,uj,ub,ya,yj,yb,ye,yu,he,hu,
        Ne.symm au,Ne.symm aj,Ne.symm ab,Ne.symm uj,Ne.symm ub,eu,ea,ej,eb]
    · by_cases qu : q=u
      · subst q
        simp [Ne.symm eu,Ne.symm uj,Ne.symm ub,uj,ub,yj,yb,yu,hu,eu,Ne.symm ej,Ne.symm eb,ej,eb]
      · simp [qe,qu]

end ECDSAAdd.Entrant.JointInverse1588


/-! ### Splitting the subtraction's adder after its first four source bits -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

def rAt (L : Layout) (i : Nat) : Wire := L.r.getD i 0
def cAt (L : Layout) (i : Nat) : Wire := L.carry.getD i 0

def pre4 (L : Layout) : Program :=
  Affine.majority (source L 0) (rAt L 0) (lowY L) (cAt L 0)++
  Affine.majority (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)++
  Affine.majority (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)++
  Affine.majority (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)

def inner (L : Layout) : Program :=
  Affine.add ((sources L).drop 4) (L.r.drop 4) ((L.carry.take 255).drop 4) (cAt L 3)

def post4 (L : Layout) : Program :=
  Affine.erase (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)++Affine.sum (source L 3) (rAt L 3) (cAt L 2)++
  Affine.erase (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)++Affine.sum (source L 2) (rAt L 2) (cAt L 1)++
  Affine.erase (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)++Affine.sum (source L 1) (rAt L 1) (cAt L 0)++
  Affine.erase (source L 0) (rAt L 0) (lowY L) (cAt L 0)++Affine.sum (source L 0) (rAt L 0) (lowY L)

theorem range_head : List.range 256=0::1::2::3::4::List.range' 5 251 := by decide

theorem shapes (L : Layout) (hw : L.Widths) :
    ∃ r1 r2 r3 r4 rt c0 c1 c2 c3 ct,
      L.r=L.r0::r1::r2::r3::r4::rt ∧ L.carry.take 255=c0::c1::c2::c3::ct ∧
      sources L=source L 0::source L 1::source L 2::source L 3::source L 4::
        (List.range' 5 251).map (source L) := by
  have len := hw
  obtain ⟨hrt,_,hc⟩ := len
  match hr : L.rtail, hcc : L.carry with
  | r1::r2::r3::r4::rt, c0::c1::c2::c3::ct =>
    refine ⟨r1,r2,r3,r4,rt++[L.rmsb],c0,c1,c2,c3,ct.take 251,?_,?_,?_⟩
    · simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,hr]
    · simp
    · simp only [sources,range_head,List.map_cons]
  | [],_ => simp [hr] at hrt
  | [_],_ => simp [hr] at hrt
  | [_,_],_ => simp [hr] at hrt
  | [_,_,_],_ => simp [hr] at hrt
  | _::_::_::_::_,[] => simp [hcc] at hc
  | _::_::_::_::_,[_] => simp [hcc] at hc
  | _::_::_::_::_,[_,_] => simp [hcc] at hc
  | _::_::_::_::_,[_,_,_] => simp [hcc] at hc

theorem add_split (L : Layout) (hw : L.Widths) :
    Affine.add (sources L) L.r (L.carry.take 255) (lowY L)=pre4 L++inner L++post4 L := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,hs⟩ := shapes L hw
  have hc' : L.carry.getD 0 0=c0 ∧ L.carry.getD 1 0=c1 ∧ L.carry.getD 2 0=c2 ∧
      L.carry.getD 3 0=c3 := by
    have t : ∀i,i<255 → L.carry.getD i 0=(L.carry.take 255).getD i 0 := by
      intro i hi
      simp only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hi]
    rw [t 0 (by decide),t 1 (by decide),t 2 (by decide),t 3 (by decide),hc]
    simp
  simp only [pre4,inner,post4,rAt,cAt,hr,hs,hc,hc'.1,hc'.2.1,hc'.2.2.1,hc'.2.2.2,
    List.getD_cons_zero,List.getD_cons_succ,List.drop_succ_cons,List.drop_zero,
    List.map_cons,Affine.add,List.append_assoc]

theorem pre4_counts (L : Layout) : toffoliCount (pre4 L)=4 ∧ measurementCount (pre4 L)=0 := by
  have a := Affine.bit_counts (source L 0) (rAt L 0) (lowY L) (cAt L 0)
  have b := Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have c := Affine.bit_counts (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)
  have d := Affine.bit_counts (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)
  simp only [pre4,toffoliCount_append,measurementCount_append,a.1,a.2.1,b.1,b.2.1,c.1,c.2.1,d.1,d.2.1]
  decide

theorem post4_counts (L : Layout) : toffoliCount (post4 L)=0 ∧ measurementCount (post4 L)=4 := by
  have a := Affine.bit_counts (source L 0) (rAt L 0) (lowY L) (cAt L 0)
  have b := Affine.bit_counts (source L 1) (rAt L 1) (cAt L 0) (cAt L 1)
  have c := Affine.bit_counts (source L 2) (rAt L 2) (cAt L 1) (cAt L 2)
  have d := Affine.bit_counts (source L 3) (rAt L 3) (cAt L 2) (cAt L 3)
  simp only [post4,toffoliCount_append,measurementCount_append,a.2.2.1,a.2.2.2.1,a.2.2.2.2.1,
    a.2.2.2.2.2,b.2.2.1,b.2.2.2.1,b.2.2.2.2.1,b.2.2.2.2.2,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,
    c.2.2.2.2.2,d.2.2.1,d.2.2.2.1,d.2.2.2.2.1,d.2.2.2.2.2]
  decide

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted measured inverse -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

/-- `clearParity` with carry #4 on `one` and carry #254 on `sign`. -/
def clearH (L : Layout) (J : Wire) : Program :=
  renameProgram (Equiv.swap (cHi L) L.sign) (renameProgram (Equiv.swap (cLo L) L.one) (clearParity L J))

/-- The subtraction with carry #4 on `lowY` and carry #254 on `sign` inside source bits 4..255. -/
def affineH (L : Layout) (J B : Wire) : Program :=
  notRegister L.r++pre4 L++loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)++
    post4 L++notRegister L.r

def programH (L : Layout) (J B : Wire) : Program :=
  clearH L J++restoreAt L J B++affineH L J B++CleanInverse5.inverse (prepare L J B)

theorem carry_mem (L : Layout) (hw : L.Widths) (i : Nat) (hi : i<256) : L.carry.getD i 0∈L.carry := by
  have len : i<L.carry.length := by rw [hw.2.2];exact hi
  rw [List.getD_eq_getElem _ _ len]
  exact List.getElem_mem len

theorem carry_take_mem (L : Layout) (hw : L.Widths) (i : Nat) (hi : i<255) :
    L.carry.getD i 0∈L.carry.take 255 := by
  have len : i<(L.carry.take 255).length := by simp [hw.2.2,hi]
  have eq : L.carry.getD i 0=(L.carry.take 255).getD i 0 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hi]
  rw [eq,List.getD_eq_getElem _ _ len]
  exact List.getElem_mem len

/-- The scalars and the two hosted carries are distinct. -/
theorem hosts_distinct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.one≠cLo L ∧ L.one≠cHi L ∧ L.parity≠cLo L ∧ L.parity≠cHi L ∧ L.one≠L.sign ∧
      cLo L≠cHi L ∧ L.parity≠L.one ∧ L.parity≠L.sign := by
  have nd := allND L hn
  have lo := carry_mem L hw 4 (by decide)
  have hi := carry_mem L hw 254 (by decide)
  have cd : (L.carry).Nodup :=
    (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.1
  have loHi : cLo L≠cHi L := by
    intro e
    have := (List.Nodup.getElem_inj_iff cd (i:=4) (j:=254) (hi:=by rw [hw.2.2];decide)
      (hj:=by rw [hw.2.2];decide)).mp (by
        simp only [cLo,cHi,List.getD_eq_getElem _ _ (show 4<L.carry.length by rw [hw.2.2];decide),
          List.getD_eq_getElem _ _ (show 254<L.carry.length by rw [hw.2.2];decide)] at e
        exact e)
    omega
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have sc := scalarND L hn
  have dataIn (q : Wire) (hq : q∈L.carry) : q∈L.r++L.y++L.carry := by
    simp only [List.mem_append]; tauto
  have nO (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.one := fun e => flags L.one (by simp) (e ▸ hq)
  have nP (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => flags L.parity (by simp) (e ▸ hq)
  have os : L.one≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.one
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have ps : L.parity≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have po : L.parity≠L.one := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  exact ⟨Ne.symm (nO _ (dataIn _ lo)),Ne.symm (nO _ (dataIn _ hi)),
    Ne.symm (nP _ (dataIn _ lo)),Ne.symm (nP _ (dataIn _ hi)),os,loHi,po,ps⟩

/-- The scalars, the two hosted carries and the controls are distinct. -/
theorem ports_distinct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    [L.sign,L.lower,lowY L,J,B,cLo L,cHi L].Nodup ∧ L.one≠cLo L ∧ L.one≠cHi L ∧
      L.parity≠cLo L ∧ L.parity≠cHi L ∧ L.one≠L.sign ∧ cLo L≠cHi L ∧ L.parity≠L.one ∧
      L.parity≠L.sign := by
  have nd := allND L hn
  have lo := carry_mem L hw 4 (by decide)
  have hi := carry_mem L hw 254 (by decide)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have cd : (L.carry).Nodup :=
    (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).2.1
  have loHi : cLo L≠cHi L := by
    intro e
    have := (List.Nodup.getElem_inj_iff cd (i:=4) (j:=254) (hi:=by rw [hw.2.2];decide)
      (hj:=by rw [hw.2.2];decide)).mp (by
        simp only [cLo,cHi,List.getD_eq_getElem _ _ (show 4<L.carry.length by rw [hw.2.2];decide),
          List.getD_eq_getElem _ _ (show 254<L.carry.length by rw [hw.2.2];decide)] at e
        exact e)
    omega
  have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q∉L.r++L.y++L.carry := flagAway L hn q hq
  have sc := scalarND L hn
  have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
  have dataIn (q : Wire) (hq : q∈L.carry ∨ q∈L.y) : q∈L.r++L.y++L.carry := by
    simp only [List.mem_append]; tauto
  have jb : J≠B := by simpa using hJB
  -- scalar distinctness
  have sl : L.sign≠L.lower := by
    have h := List.nodup_iff_count.mp sc L.sign
    intro e; rw [←e] at h; simp [List.count_cons] at h; omega
  have nS (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.sign := fun e => flags L.sign (by simp) (e ▸ hq)
  have nL (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.lower := fun e => flags L.lower (by simp) (e ▸ hq)
  have nO (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.one := fun e => flags L.one (by simp) (e ▸ hq)
  have nP (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠L.parity := fun e => flags L.parity (by simp) (e ▸ hq)
  have nJ (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠J := fun e => notData J hJ (e ▸ hq)
  have nB (q : Wire) (hq : q∈L.r++L.y++L.carry) : q≠B := fun e => notData B hB (e ▸ hq)
  have sJ : L.sign≠J := fun e => hJ (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have sB : L.sign≠B := fun e => hB (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have lJ : L.lower≠J := fun e => hJ (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have lB : L.lower≠B := fun e => hB (e ▸ (by simp [Layout.wires,BalancedCleanup.Layout.wires]))
  have yc : lowY L≠cLo L ∧ lowY L≠cHi L := by
    have d := (List.nodup_append'.mp nd).2.1
    have yc := (List.nodup_append'.mp d).2.2
    exact ⟨fun e => List.disjoint_left.mp yc (List.mem_append_right _ y0) (e ▸ lo),
      fun e => List.disjoint_left.mp yc (List.mem_append_right _ y0) (e ▸ hi)⟩
  have os : L.one≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.one
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have ps : L.parity≠L.sign := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  have po : L.parity≠L.one := by
    have h := List.nodup_iff_count.mp sc L.parity
    intro e; rw [e] at h; simp [List.count_cons] at h; omega
  refine ⟨?_,Ne.symm (nO _ (dataIn _ (Or.inl lo))),Ne.symm (nO _ (dataIn _ (Or.inl hi))),
    Ne.symm (nP _ (dataIn _ (Or.inl lo))),Ne.symm (nP _ (dataIn _ (Or.inl hi))),os,loHi,po,ps⟩
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true]
  refine ⟨⟨sl,Ne.symm (nS _ (dataIn _ (Or.inr y0))),sJ,sB,Ne.symm (nS _ (dataIn _ (Or.inl lo))),
    Ne.symm (nS _ (dataIn _ (Or.inl hi)))⟩,⟨Ne.symm (nL _ (dataIn _ (Or.inr y0))),lJ,lB,
    Ne.symm (nL _ (dataIn _ (Or.inl lo))),Ne.symm (nL _ (dataIn _ (Or.inl hi)))⟩,
    ⟨nJ _ (dataIn _ (Or.inr y0)),nB _ (dataIn _ (Or.inr y0)),yc.1,yc.2⟩,
    ⟨jb,fun e => nJ _ (dataIn _ (Or.inl lo)) e.symm,fun e => nJ _ (dataIn _ (Or.inl hi)) e.symm⟩,
    ⟨fun e => nB _ (dataIn _ (Or.inl lo)) e.symm,fun e => nB _ (dataIn _ (Or.inl hi)) e.symm⟩,loHi⟩

end ECDSAAdd.Entrant.JointInverse1588


/-! ### Facts about the four leading majorities and the inner adder -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

theorem source_mem (L : Layout) (i : Nat) (hi : i<256) : source L i∈sources L :=
  List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩

theorem source_site (L : Layout) (i : Nat) (hi : i<256) (q : Wire) (hq : q∈(source L i).wires) :
    q∈Affine.sites (sources L) :=
  List.mem_flatMap.mpr ⟨source L i,source_mem L i hi,hq⟩

/-- Positions of the first four targets and carries. -/
theorem atoms (L : Layout) (hw : L.Widths) :
    ∃ r1 r2 r3 r4 rt c0 c1 c2 c3 ct,
      L.r=L.r0::r1::r2::r3::r4::rt ∧ L.carry.take 255=c0::c1::c2::c3::ct ∧
      rAt L 0=L.r0 ∧ rAt L 1=r1 ∧ rAt L 2=r2 ∧ rAt L 3=r3 ∧
      cAt L 0=c0 ∧ cAt L 1=c1 ∧ cAt L 2=c2 ∧ cAt L 3=c3 := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,_⟩ := shapes L hw
  have t : ∀i,i<255 → L.carry.getD i 0=(L.carry.take 255).getD i 0 := by
    intro i hi
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hi]
  refine ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | simp [rAt,hr]
    | (simp only [cAt]; rw [t _ (by decide),hc]; simp)

theorem maj_keep (b : Affine.Bit) (hb : b.Valid) (y cin co : Wire)
    (hn : [y,cin,co].Nodup) (ha : ∀q∈b.wires,q∉[y,cin,co]) (s : State) (m : List Bool) :
    (run (Affine.majority b y cin co) m s).phase=s.phase ∧
    ∀q,q≠co → (run (Affine.majority b y cin co) m s).basis q=s.basis q := by
  rw [Affine.majority_correct b hb y cin co hn ha s m]
  exact ⟨rfl,fun q hq => by simp [writeBit,hq]⟩

theorem pre4_run (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool) :
    (run (pre4 L) m s).phase=s.phase ∧
    ∀q,q≠cAt L 0 → q≠cAt L 1 → q≠cAt L 2 → q≠cAt L 3 → (run (pre4 L) m s).basis q=s.basis q := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have nd := arithmeticND L hw hn
  have away := sources_away L hw hn
  rw [hr,hc] at nd
  have sub : [lowY L,L.r0,r1,r2,r3,c0,c1,c2,c3].Sublist
      (lowY L::(L.r0::r1::r2::r3::r4::rt++c0::c1::c2::c3::ct)) := by
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons₂;apply List.Sublist.cons₂
    apply List.Sublist.cons
    apply List.sublist_append_of_sublist_right
    apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂;apply List.Sublist.cons₂
    exact List.nil_sublist _
  have nd9 := nd.sublist sub
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd9
  rcases nd9 with ⟨⟨u0,u1,u2,u3,uc0,uc1,uc2,uc3⟩,⟨⟨a1,a2,a3,a0c0,a0c1,a0c2,a0c3⟩,
    ⟨⟨b2,b3,b1c0,b1c1,b1c2,b1c3⟩,⟨⟨c23,c2c0,c2c1,c2c2,c2c3⟩,⟨⟨d0,d1,d2,d3⟩,
    ⟨⟨g01,g02,g03⟩,⟨⟨g12,g13⟩,g23⟩⟩⟩⟩⟩⟩⟩
  have src (i : Nat) (hi : i<4) (y cin co : Wire) (hy : y∈L.r)
      (hcin : cin=lowY L ∨ cin∈L.carry.take 255) (hco : co∈L.carry.take 255) :
      ∀q∈(source L i).wires,q∉[y,cin,co] := by
    intro q hq bad
    have aw := away q (source_site L i (by omega) q hq)
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false,not_or] at aw bad
    rcases bad with rfl|rfl|rfl
    · exact aw.2.1 hy
    · rcases hcin with rfl|h
      · exact aw.1 rfl
      · exact aw.2.2 h
    · exact aw.2.2 hco
  have valid (i : Nat) (hi : i<4) := sources_valid L hn _ (source_mem L i (by omega))
  have rm (i : Nat) (hi : i<4) : rAt L i∈L.r := by
    rw [hr]
    interval_cases i <;> simp [e0,e1,e2,e3]
  have cm (i : Nat) (hi : i<4) : cAt L i∈L.carry.take 255 := by
    rw [hc]
    interval_cases i <;> simp [f0,f1,f2,f3]
  have k0 := maj_keep (source L 0) (valid 0 (by decide)) (rAt L 0) (lowY L) (cAt L 0)
    (by rw [e0,f0];simp [Ne.symm u0,uc0,a0c0])
    (src 0 (by decide) _ _ _ (rm 0 (by decide)) (Or.inl rfl) (cm 0 (by decide)))
  have k1 := maj_keep (source L 1) (valid 1 (by decide)) (rAt L 1) (cAt L 0) (cAt L 1)
    (by rw [e1,f0,f1];simp [b1c0,b1c1,g01])
    (src 1 (by decide) _ _ _ (rm 1 (by decide)) (Or.inr (cm 0 (by decide))) (cm 1 (by decide)))
  have k2 := maj_keep (source L 2) (valid 2 (by decide)) (rAt L 2) (cAt L 1) (cAt L 2)
    (by rw [e2,f1,f2];simp [c2c1,c2c2,g12])
    (src 2 (by decide) _ _ _ (rm 2 (by decide)) (Or.inr (cm 1 (by decide))) (cm 2 (by decide)))
  have k3 := maj_keep (source L 3) (valid 3 (by decide)) (rAt L 3) (cAt L 2) (cAt L 3)
    (by rw [e3,f2,f3];simp [d2,d3,g23])
    (src 3 (by decide) _ _ _ (rm 3 (by decide)) (Or.inr (cm 2 (by decide))) (cm 3 (by decide)))
  have z (b : Affine.Bit) (y cin co : Wire) : measurementCount (Affine.majority b y cin co)=0 :=
    (Affine.bit_counts b y cin co).2.1
  simp only [pre4,run_append,measurementCount_append,z,Nat.add_zero,List.take_zero,List.drop_zero]
  refine ⟨?_,?_⟩
  · rw [(k3 _ _).1,(k2 _ _).1,(k1 _ _).1,(k0 _ _).1]
  · intro q h0 h1 h2 h3
    rw [(k3 _ _).2 q h3,(k2 _ _).2 q h2,(k1 _ _).2 q h1,(k0 _ _).2 q h0]

/-- Source bits 4..255 do not read `sign`. -/
theorem source_high_sites (L : Layout) (i : Nat) (hi : 4 ≤ i) :
    (source L i).wires⊆[L.parity,L.lower,L.one] := by
  intro q hq
  unfold source at hq
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)] at hq
  split_ifs at hq <;> simp_all [Affine.Bit.wires] <;> tauto

theorem inner_sites (L : Layout) (q : Wire) (hq : q∈Affine.sites ((sources L).drop 4)) :
    q∈[L.parity,L.lower,L.one] := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  simp only [sources,← List.map_drop,List.mem_map] at hb
  obtain ⟨i,hi,rfl⟩ := hb
  have : 4 ≤ i := by
    obtain ⟨n,hn,eq⟩ := List.getElem_of_mem hi
    rw [List.getElem_drop,List.getElem_range] at eq
    omega
  exact source_high_sites L i this hq

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted pieces run exactly like f2dcda16's pieces on reachable states -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

/-- `clearParity` never touches `one` or `sign`. -/
theorem clearParity_support (L : Layout) (hw : L.Widths) (J : Wire) :
    wires (clearParity L J)⊆(L.r++L.y++L.carry.take 255++[L.parity,L.lower,J]).toFinset := by
  let W := (L.r++L.y++L.carry.take 255++[L.parity,L.lower,J]).toFinset
  have data (q : Wire) (hq : q∈L.r++L.y++L.carry.take 255) : q∈W := by
    simp only [W,List.mem_toFinset,List.mem_append] at hq ⊢
    exact Or.inl hq
  have scalar (q : Wire) (hq : q∈[L.parity,L.lower,J]) : q∈W :=
    List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have hp := scalar L.parity (by simp)
  have ha := scalar L.lower (by simp)
  have hj := scalar J (by simp)
  have r (q : Wire) (hq : q∈L.r) : q∈W := data q (by simp [hq])
  have y (q : Wire) (hq : q∈L.y) : q∈W := data q (by simp [hq])
  have c (q : Wire) (hq : q∈L.carry.take 255) : q∈W := data q (by simp [hq])
  have rh := r L.rmsb (by simp [BalancedCleanup.Layout.r])
  have yu : lowY L∈L.y := by rw [y_cons L hw]; simp
  have u := y (lowY L) yu
  have ul : L.ylow[0]?.getD 0∈W := u
  have len := BalancedCleanup.widths L.toLayout hw
  have comp (ctl : Wire) (hctl : ctl∈W) : wires (signComplement ctl L.r)⊆W := by
    intro q hq
    have h := signComplement_wires_subset ctl L.r hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl|h
    · exact hctl
    · exact r q h
  have mag : wires (EntryHalf5.prepareMagnitude L)⊆W := by
    simp only [EntryHalf5.prepareMagnitude,BalancedCleanup.prepareSign,wires_append,
      Finset.union_subset_iff]
    exact ⟨by simp [wires,Instr.wires,Finset.insert_subset_iff,rh,ha],comp _ ha⟩
  have carry : wires (EntryHalf5.parityCarry L J)⊆W := by
    apply (DiagonalCarry5.support EntryHalf5.parityBits L.low (L.carry.take 255) L.lower J L.parity
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,len.1])
      (by simp [EntryHalf5.parityBits,DiagonalCarry5.literal_length,List.length_take,hw.2.2])).trans
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|hq|hq
    · exact hj
    · exact hp
    · exact ha
    · exact r q (List.mem_append_left _ hq)
    · exact c q hq
  simp only [clearParity,EntryHalf5.recoverParity,EntryHalf5.positiveParity,
    wires_append,wires_reverse,Finset.union_subset_iff]
  refine ⟨?_,⟨⟨?_,⟨mag,⟨carry,mag⟩⟩⟩,?_⟩⟩
  · intro q hq
    have h : q=L.ylow.getD 0 0 ∨ q=L.parity := by
      simpa [wires,Instr.wires] using hq
    rcases h with rfl|rfl
    · exact u
    · exact hp
  · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]
  · simp [wires,Instr.wires,Finset.insert_subset_iff,hj]

theorem clearParity_scalar_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J : Wire) (hJ : J∉L.wires) (q : Wire) (hq : q=L.one ∨ q=L.sign) :
    q∉wires (clearParity L J) := by
  intro used
  have m := List.mem_toFinset.mp (clearParity_support L hw J used)
  have flag : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
    rcases hq with rfl|rfl <;> simp
  have away := flagAway L hn q flag
  have sc := scalarND L hn
  have qj : q≠J := by
    intro e; apply hJ; rw [←e]
    rcases hq with rfl|rfl <;> simp [Layout.wires,BalancedCleanup.Layout.wires]
  have qp : q≠L.parity := by
    have h := List.nodup_iff_count.mp sc L.parity
    rcases hq with rfl|rfl <;> intro e <;> rw [e] at h <;> simp [List.count_cons] at h <;> omega
  have ql : q≠L.lower := by
    have h := List.nodup_iff_count.mp sc L.lower
    rcases hq with rfl|rfl <;> intro e <;> rw [e] at h <;> simp [List.count_cons] at h <;> omega
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((hr|hy)|hc)|rfl|rfl|rfl
  · exact away (by simp [hr])
  · exact away (by simp [hy])
  · exact away (by simp [List.mem_of_mem_take hc])
  · exact qp rfl
  · exact ql rfl
  · exact qj rfl

theorem clearH_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J : Wire) (hJ : J∉L.wires)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (hc : ∀q∈L.carry,s.basis q=false) (ho : s.basis L.one=false) (hs : s.basis L.sign=false) :
    run (clearH L J) m s=run (clearParity L J) m s := by
  have dist := hosts_distinct L hw hn
  have lo : cLo L∈L.carry := carry_mem L hw 4 (by decide)
  have hi : cHi L∈L.carry := carry_mem L hw 254 (by decide)
  have hc' : ∀q∈L.carry.take 255,s.basis q=false := fun q h => hc q (List.mem_of_mem_take h)
  have cx := clear_xor L hw hn J hJ R hr s m hR hl hc
  have same (q : Wire) (hq : q≠L.parity) : (run (clearParity L J) m s).basis q=s.basis q := by
    rw [cx]; simp [writeBit,hq]
  have innerEq : run (renameProgram (Equiv.swap (cLo L) L.one) (clearParity L J)) m s=
      run (clearParity L J) m s :=
    rebind_swap_run _ _ _ s m (hc _ lo) ho
      ((same _ (Ne.symm dist.2.2.1)).trans (hc _ lo))
      ((same _ (Ne.symm dist.2.2.2.2.2.2.1)).trans ho)
  rw [clearH,rebind_swap_run _ _ _ s m (hc _ hi) hs
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.1)).trans (hc _ hi))
    (by rw [innerEq];exact (same _ (Ne.symm dist.2.2.2.2.2.2.2)).trans hs),innerEq]

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted subtraction equals the original one on the restored-scalar state -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5
attribute [local irreducible] run

theorem carry_nodup (L : Layout) (hn : L.wires.Nodup) : L.carry.Nodup :=
  (List.nodup_append'.mp (List.nodup_append'.mp (allND L hn)).2.1).2.1

theorem carry_index_ne (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (i j : Nat)
    (hi : i<256) (hj : j<256) (hij : i≠j) : L.carry.getD i 0≠L.carry.getD j 0 := by
  intro e
  have li : i<L.carry.length := by rw [hw.2.2];exact hi
  have lj : j<L.carry.length := by rw [hw.2.2];exact hj
  rw [List.getD_eq_getElem _ _ li,List.getD_eq_getElem _ _ lj] at e
  exact hij ((List.Nodup.getElem_inj_iff (carry_nodup L hn)).mp e)

theorem carry_not_r (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈L.carry) : q∉L.r := by
  intro hr
  have nd := allND L hn
  have h := List.nodup_iff_count.mp nd q
  have a := List.count_pos_iff.mpr hr
  have b := List.count_pos_iff.mpr hq
  simp only [List.count_append] at h
  omega

theorem y_not_r (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈L.y) : q∉L.r := by
  intro hr
  have nd := allND L hn
  have h := List.nodup_iff_count.mp nd q
  have a := List.count_pos_iff.mpr hr
  have b := List.count_pos_iff.mpr hq
  simp only [List.count_append] at h
  omega

theorem y_not_carry (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈L.y) : q∉L.carry := by
  intro hc
  have nd := allND L hn
  have h := List.nodup_iff_count.mp nd q
  have a := List.count_pos_iff.mpr hc
  have b := List.count_pos_iff.mpr hq
  simp only [List.count_append] at h
  omega

/-- A wire away from the target register and the carries is kept by the four majorities. -/
theorem prefix_keep (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (b : State) (q : Wire)
    (hr : q∉L.r) (hc : ∀i,i<4 → q≠cAt L i) :
    (run (notRegister L.r++pre4 L) [] b).basis q=b.basis q ∧
      (run (notRegister L.r++pre4 L) [] b).phase=b.phase := by
  have nr := EntryHalf5.target_nodup L hn
  have mz := (notRegister_counts L.r).2
  rw [run_append,mz,List.take_zero,List.drop_zero,notRegister_correct L.r nr b []]
  have p := pre4_run L hw hn ⟨b.phase,fun w => if w∈L.r then !b.basis w else b.basis w⟩ []
  refine ⟨?_,p.1⟩
  rw [p.2 q (hc 0 (by decide)) (hc 1 (by decide)) (hc 2 (by decide)) (hc 3 (by decide))]
  simp [hr]

theorem inner_support (L : Layout) :
    wires (inner L)⊆(Affine.sites ((sources L).drop 4)++L.r.drop 4++
      (L.carry.take 255).drop 4++[cAt L 3]).toFinset :=
  Affine.add_support_to _ _ _ _ _ (fun q hq => by simp [hq]) (fun q hq => by simp [hq])
    (fun q hq => by simp [hq]) (by simp)

theorem inner_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (q : Wire)
    (hs : q∉[L.parity,L.lower,L.one]) (hr : q∉L.r) (hc : q∉L.carry) : q∉wires (inner L) := by
  intro used
  have m := List.mem_toFinset.mp (inner_support L used)
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((h|h)|h)|h
  · exact hs (inner_sites L q h)
  · exact hr (List.mem_of_mem_drop h)
  · exact hc (List.mem_of_mem_take (List.mem_of_mem_drop h))
  · exact hc (by rw [h];exact carry_mem L hw 3 (by decide))

/-- `Affine.add_correct` for the inner adder on any state with clean high carries. -/
theorem inner_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (x : State) (t : List Bool)
    (clean : ∀q∈(L.carry.take 255).drop 4,x.basis q=false) :
    (run (inner L) t x).phase=x.phase ∧
      ∀q,q∉L.r → (run (inner L) t x).basis q=x.basis q := by
  obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hc,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
  have nd := arithmeticND L hw hn
  have away := sources_away L hw hn
  have len := BalancedCleanup.widths L.toLayout hw
  have rl : L.r.length=256 := len.2.1
  rw [hr,hc] at nd
  have nd' : (c3::((r4::rt)++ct)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append] at h ⊢
    split_ifs at h ⊢ <;> omega
  have hd : (L.r.drop 4)=r4::rt := by rw [hr];rfl
  have cd : (L.carry.take 255).drop 4=ct := by rw [hc];rfl
  have s3 : cAt L 3=c3 := f3
  have res := Affine.add_correct ((sources L).drop 4) (r4::rt) ct c3 nd'
    (by
      intro q hq bad
      have aw := away q (List.mem_flatMap.mpr (by
        obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
        exact ⟨b,List.mem_of_mem_drop hb,hq⟩))
      rw [hr,hc] at aw
      apply aw
      simp only [List.mem_cons,List.mem_append] at bad ⊢
      rcases bad with rfl|(h|h)|h
      · simp
      · simp [h]
      · simp [h]
      · simp [h])
    (by
      have a : ((sources L).drop 4).length=252 := by simp [sources_length]
      have b : (r4::rt).length=252 := by
        have := congrArg List.length hr
        simp only [List.length_cons] at this ⊢
        omega
      rw [a,b])
    (by
      have b : (r4::rt).length=252 := by
        have := congrArg List.length hr
        simp only [List.length_cons] at this ⊢
        omega
      have c : ct.length=251 := by
        have := congrArg List.length hc
        simp only [List.length_cons,List.length_take,hw.2.2] at this
        omega
      rw [b,c])
    x t (by rw [←cd];exact clean)
    (fun b hb => sources_valid L hn b (List.mem_of_mem_drop hb))
  have shape : inner L=Affine.add ((sources L).drop 4) (r4::rt) ct c3 := by
    rw [inner,hd,cd,s3]
  rw [shape]
  refine ⟨res.1,fun q hq => res.2.1 q ?_⟩
  intro h
  apply hq
  rw [hr]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ h)))

theorem affineH_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (b : State) (m : List Bool)
    (he : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)))
    (hu : b.basis (lowY L)=(b.basis J && b.basis B))
    (hc : ∀q∈L.carry,b.basis q=false) :
    ∃m',run (affineH L J B) m b=run (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) m' b := by
  let Pre := notRegister L.r++pre4 L
  let Post := post4 L++notRegister L.r
  let Q := loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)
  have shapeS : affineSub (sources L) L.r (L.carry.take 255) (lowY L)=Pre++inner L++Post := by
    simp only [affineSub,add_split L hw,Pre,Post,List.append_assoc]
  have shapeH : affineH L J B=Pre++Q++Post := by
    simp only [affineH,Pre,Post,Q,List.append_assoc]
  refine ⟨(m.drop 2).take (measurementCount (inner L))++m.drop (measurementCount Q),?_⟩
  rw [shapeH,shapeS]
  apply context_eq Pre (inner L) Q Post 2 b m
  · simp only [Pre,measurementCount_append,(notRegister_counts _).2,(pre4_counts L).2]
  · exact (loanW_counts _ _ _ _ _ _ _ _).2
  · intro r
    let x := run Pre [] b
    -- distinctness
    have dist := ports_distinct L hw hn J B hJ hB hJB
    have nd7 := dist.1
    have flags (q : Wire) (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
        q∉L.r++L.y++L.carry := flagAway L hn q hq
    have notData (q : Wire) (hq : q∉L.wires) : q∉L.r++L.y++L.carry := fun bad => hq (data_member L q bad)
    have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
    have lowCarry (i : Nat) (hi : i<4) : cAt L i∈L.carry := carry_mem L hw i (by omega)
    have offData (q : Wire) (hq : q∉L.r++L.y++L.carry) : q∉L.r ∧ ∀i,i<4 → q≠cAt L i :=
      ⟨fun h => hq (by simp [h]),fun i hi e => hq (by rw [e];simp [lowCarry i hi])⟩
    have keepS := prefix_keep L hw hn b L.sign (offData _ (flags _ (by simp))).1 (offData _ (flags _ (by simp))).2
    have keepA := prefix_keep L hw hn b L.lower (offData _ (flags _ (by simp))).1 (offData _ (flags _ (by simp))).2
    have keepU := prefix_keep L hw hn b (lowY L) (y_not_r L hn _ y0)
      (fun i hi e => y_not_carry L hn _ y0 (by rw [e];exact lowCarry i hi))
    have keepJ := prefix_keep L hw hn b J (offData _ (notData _ hJ)).1 (offData _ (notData _ hJ)).2
    have keepB := prefix_keep L hw hn b B (offData _ (notData _ hB)).1 (offData _ (notData _ hB)).2
    have hiIdx (k : Nat) (hk : k=4 ∨ k=254) (i : Nat) (hi : i<4) : L.carry.getD k 0≠cAt L i :=
      carry_index_ne L hw hn k i (by omega) (by omega) (by omega)
    have keepLo := prefix_keep L hw hn b (cLo L) (carry_not_r L hn _ (carry_mem L hw 4 (by decide)))
      (hiIdx 4 (Or.inl rfl))
    have keepHi := prefix_keep L hw hn b (cHi L) (carry_not_r L hn _ (carry_mem L hw 254 (by decide)))
      (hiIdx 254 (Or.inr rfl))
    -- the inner adder's carries are clean at `x`
    have cleanX : ∀q∈(L.carry.take 255).drop 4,x.basis q=false := by
      intro q hq
      obtain ⟨r1,r2,r3,r4,rt,c0,c1,c2,c3,ct,hr,hct,e0,e1,e2,e3,f0,f1,f2,f3⟩ := atoms L hw
      have qc : q∈L.carry := List.mem_of_mem_take (List.mem_of_mem_drop hq)
      have ndc : (L.carry.take 255).Nodup := (carry_nodup L hn).sublist (List.take_sublist _ _)
      rw [hct] at ndc hq
      simp only [List.drop_succ_cons,List.drop_zero] at hq
      simp only [List.nodup_cons,List.mem_cons,not_or] at ndc
      have ne (i : Nat) (hi : i<4) : q≠cAt L i := by
        intro e
        interval_cases i
        · rw [f0] at e;exact ndc.1.2.2.2 (e ▸ hq)
        · rw [f1] at e;exact ndc.2.1.2.2 (e ▸ hq)
        · rw [f2] at e;exact ndc.2.2.1.2 (e ▸ hq)
        · rw [f3] at e;exact ndc.2.2.2.1 (e ▸ hq)
      exact ((prefix_keep L hw hn b q (carry_not_r L hn q qc) ne).1).trans (hc q qc)
    have inn (t : List Bool) := inner_correct L hw hn x t cleanX
    apply loanW_run L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L) x r nd7
    · rw [keepS.1,keepA.1,keepU.1];exact he
    · rw [keepU.1,keepJ.1,keepB.1];exact hu
    · exact inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e
        · exact flags L.parity (by simp) (by rw [←e];simp [y0])
        · exact flags L.lower (by simp) (by rw [←e];simp [y0])
        · exact flags L.one (by simp) (by rw [←e];simp [y0]))
        (y_not_r L hn _ y0) (y_not_carry L hn _ y0)
    · exact inner_free L hw hn _ (fun h => by
        have sc := scalarND L hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e <;>
          (have c := List.nodup_iff_count.mp sc L.sign
           rw [e] at c;simp [List.count_cons] at c;omega))
        (offData _ (flags _ (by simp))).1 (fun h => flags L.sign (by simp) (by simp [h]))
    · intro t
      have i := (inn t).2
      exact ⟨i _ (offData _ (flags _ (by simp))).1,i _ (offData _ (notData _ hJ)).1,
        i _ (offData _ (notData _ hB)).1⟩
    · exact keepLo.1.trans (hc _ (carry_mem L hw 4 (by decide)))
    · exact keepHi.1.trans (hc _ (carry_mem L hw 254 (by decide)))
    · intro t
      exact ((inn t).2 _ (carry_not_r L hn _ (carry_mem L hw 4 (by decide)))).trans
        (keepLo.1.trans (hc _ (carry_mem L hw 4 (by decide))))
    · intro t
      exact ((inn t).2 _ (carry_not_r L hn _ (carry_mem L hw 254 (by decide)))).trans
        (keepHi.1.trans (hc _ (carry_mem L hw 254 (by decide))))

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted joint inverse: f2dcda16's frame, unchanged -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Secp256k1
attribute [local irreducible] run

theorem inverseH_forward (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 Y) (hY : regValue L.y s.basis=0)
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    run (programH L J B) m (run (EntryRetained5.program L J B) [] s)=s := by
  let a:=run (prepare L J B) [] s
  let b:=run (arithmetic L) [] a
  let c:=run (eraseScalarsAt L J B) [] b
  have prep:=prepare_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  change Prepared L J B Jv Bv Y s a at prep
  have pref:=prefix_spec L hw hn J B hJ hB hJB Jv Bv Y hy s [] hR hY hc hz hj hb
  have prefix_run : run (prefixProgram L J B) [] s=b := by
    simp only [prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [prefix_run] at pref
  have dd : b.basis L.one=(b.basis L.parity && b.basis (lowY L)) := by
    rw [pref.parity,pref.u]
    exact pref.d
  have ee : b.basis L.sign=(b.basis L.lower && b.basis (lowY L)) := by
    rw [pref.a,pref.u]
    exact pref.e
  have uu : b.basis (lowY L)=(b.basis J && b.basis B) := by rw [pref.u,pref.j,pref.b]
  have aa:=scalar_erase_relation L hw Jv Bv Y hy b.basis pref.target pref.parity pref.a pref.d
  have erased:=eraseScalarsAt_run L hw hn J B hJ hB hJB b [] ee aa dd uu
  change c=⟨b.phase,erasedBasis L.parity L.lower L.one L.sign (lowY L) J b.basis⟩ at erased
  have en:=erasePorts_nodup L hw hn J B hJ hB hJB
  have restore:=restoreScalars_inverse L.parity L.lower L.one L.sign (lowY L) J B L.rmsb en b
  have undoRestore (n : List Bool) : run (restoreAt L J B) n c=b := by
    rw [erased]
    exact restore n ee aa dd uu
  have nd:=allND L hn
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have data : (L.r++L.y++L.carry).Nodup := (List.nodup_append'.mp nd).2.1
  have ry : (L.r++L.y).Nodup := (List.nodup_append'.mp data).1
  have rdy := (List.nodup_append'.mp ry).2.2
  have dyc := (List.nodup_append'.mp data).2.2
  have flag (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign]) : q∉L.r++L.y++L.carry := by
    have mem : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one] := by
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hq ⊢
      tauto
    exact flagAway L hn q mem
  have cSame (q : Wire) (hq : q∈L.r++L.carry) : c.basis q=b.basis q := by
    have qdata : q∈L.r++L.y++L.carry := by
      simp only [List.mem_append] at hq ⊢
      tauto
    have qu : q≠lowY L := by
      intro eq
      rcases List.mem_append.mp hq with qr|qc
      · exact List.disjoint_left.mp rdy qr (eq.symm ▸ y0)
      · exact List.disjoint_left.mp dyc (List.mem_append_right _ y0) (eq ▸ qc)
    have qf (f : Wire) (hf : f∈[L.parity,L.lower,L.one,L.sign]) : q≠f := fun e=>flag f hf (e ▸ qdata)
    rw [erased]
    exact erasedBasis_frame _ _ _ _ _ _ _ q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      exact not_or_intro (qf _ (by simp)) (not_or_intro (qf _ (by simp))
        (not_or_intro (qf _ (by simp)) qu)))
  have cR : regValue L.r c.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)) :=
    (regValue_congr _ _ _ (fun q hq=>cSame q (List.mem_append_left _ hq))).trans pref.target
  have cCarry : ∀q∈L.carry,c.basis q=false := fun q hq=>
    (cSame q (List.mem_append_right _ hq)).trans (pref.carry q hq)
  have ca : c.basis L.lower=false := by
    have ne : L.lower≠lowY L := by
      intro e;exact flag L.lower (by simp) (by simp [e,y0])
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,ne,ad]
  have bounds:=signedY_bounds (Jv && Bv) Y hy
  have rc : Centered (halfResult (signedY (Jv && Bv) Y)) := by
    apply (halfResult_spec _ ?_).1
    have hp:=constants
    unfold Centered at bounds
    omega
  have undoClear (n : List Bool) :
      run (clearParity L J) n (run (clearParity L J) [] c)=c :=
    clear_involution L hw hn J hJ _ rc c [] n cR ca cCarry
  have undoAdd (n : List Bool) :
      run (affineSub (sources L) L.r (L.carry.take 255) (lowY L)) n b=a := by
    exact affineSub_inverse _ _ _ _ (arithmeticND L hw hn) (sources_away L hw hn)
      (by rw [sources_length,(BalancedCleanup.widths L.toLayout hw).2.1])
      (by simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).2.1]) a [] n
      (fun q hq=>prep.carry q (List.mem_of_mem_take hq)) (sources_valid L hn)
  have undoPrep (n : List Bool) : run (CleanInverse5.inverse (prepare L J B)) n a=s :=
    CleanInverse5.inverse_run _ _ (prepare_ready L hw hn J B hJ hB s hY hc hz) n
  have forward_run : run (EntryRetained5.program L J B) [] s=run (clearParity L J) [] c := by
    simp only [EntryRetained5.program,prefixProgram,run_append,List.take_nil,List.drop_nil]
    rfl
  have notU (q : Wire) (hq : q=L.one ∨ q=L.sign) : q≠lowY L := by
    intro e
    have f := flagAway L hn q (by rcases hq with rfl|rfl <;> simp)
    exact f (by rw [e];simp [y0])
  have cOne : c.basis L.one=false := by
    have ad : L.lower≠L.one := by
      have h:=List.nodup_iff_count.mp en L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.one (Or.inl rfl)]
  have cSign : c.basis L.sign=false := by
    have sa : L.sign≠L.lower := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    have sd : L.sign≠L.one := by
      have h:=List.nodup_iff_count.mp en L.sign
      intro e;simp [e,List.count_cons] at h;omega
    rw [erased]
    simp [erasedBasis,writeBit,notU L.sign (Or.inr rfl),sa,sd]
  have undoClearH (n : List Bool) :
      run (clearH L J) n (run (clearParity L J) [] c)=c := by
    have cx := clear_xor L hw hn J hJ _ rc c [] cR ca cCarry
    have po : L.parity∉L.r := fun h => flag L.parity (by simp) (by simp [h])
    have keepC (q : Wire) (hq : q≠L.parity) : (run (clearParity L J) [] c).basis q=c.basis q := by
      rw [cx];simp [writeBit,hq]
    have dist := hosts_distinct L hw hn
    have sc := scalarND L hn
    have lp : L.lower≠L.parity := by
      have h:=List.nodup_iff_count.mp sc L.lower
      intro e;simp [e,List.count_cons] at h;omega
    rw [clearH_eq L hw hn J hJ _ rc _ n
      ((regValue_congr _ _ _ (fun q hq => keepC q (fun e => po (e ▸ hq)))).trans cR)
      ((keepC _ lp).trans ca)
      (fun q hq => (keepC q (fun e => flag L.parity (by simp) (by rw [←e];simp [hq]))).trans (cCarry q hq))
      ((keepC _ (Ne.symm dist.2.2.2.2.2.2.1)).trans cOne)
      ((keepC _ (Ne.symm dist.2.2.2.2.2.2.2)).trans cSign)]
    exact undoClear n
  have undoAddH (n : List Bool) : run (affineH L J B) n b=a := by
    obtain ⟨m',h⟩ := affineH_eq L hw hn J B hJ hB hJB b n ee uu pref.carry
    rw [h]
    exact undoAdd m'
  rw [forward_run,programH]
  simp only [List.append_assoc,run_append,run_take]
  rw [undoClearH,undoRestore,undoAddH,undoPrep]

theorem inverseH_frame (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (Jv Bv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
    (hY : regValue L.y s.basis=encodeWord 256 (if Jv then Y else 0))
    (hc : ∀q∈work L,s.basis q=false) (hz : s.basis L.sign=false)
    (hj : s.basis J=Jv) (hb : s.basis B=Bv) :
    let out:=run (programH L J B) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis (encodeWord 256 Y) 0 out.basis := by
  let t : State:=⟨s.phase,putWord L.r (encodeWord 256 Y) (putWord L.y 0 s.basis)⟩
  have len:=BalancedCleanup.widths L.toLayout hw
  have nd:=allND L hn
  have nr:=EntryHalf5.target_nodup L hn
  have ny : L.y.Nodup := by
    exact (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.1
  have dis : List.Disjoint L.r L.y :=
    (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp nd).2.1).1).2.2
  have outside (q : Wire) (qr : q∉L.r) (qy : q∉L.y) : t.basis q=s.basis q := by
    simp only [t,putWord_outside _ _ _ q qr,putWord_outside _ _ _ q qy]
  have tr : regValue L.r t.basis=encodeWord 256 Y :=
    putWord_value L.r nr _ (by rw [len.2.1];exact encodeWord_bound 256 Y) _
  have ty : regValue L.y t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (putWord_value L.y ny 0 (Nat.two_pow_pos _) s.basis)
    intro q hq
    apply putWord_outside
    exact fun bad=>List.disjoint_left.mp dis bad hq
  have noData (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (data_member L q (by simp [bad]))
    · exact hq (data_member L q (by simp [bad]))
  have workAway (q : Wire) (hq : q∈work L) : q∉L.r ∧ q∉L.y := by
    have n:=List.nodup_iff_count.mp nd q
    have w:=List.count_pos_iff.mpr hq
    constructor <;> intro bad <;> have b:=List.count_pos_iff.mpr bad
    all_goals
      simp only [work,List.count_append,List.count_cons,List.count_nil] at w
      simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,BalancedCleanup.Layout.low,
        List.count_append,List.count_cons,List.count_nil] at n b
      omega
  have tc : ∀q∈work L,t.basis q=false := fun q hq=>
    (outside q (workAway q hq).1 (workAway q hq).2).trans (hc q hq)
  have signAway : L.sign∉L.r ∧ L.sign∉L.y := by
    have h:=flagAway L hn L.sign (by simp)
    exact ⟨fun a=>h (by simp [a]),fun a=>h (by simp [a])⟩
  have tz : t.basis L.sign=false := (outside _ signAway.1 signAway.2).trans hz
  have tj : t.basis J=Jv := (outside J (noData J hJ).1 (noData J hJ).2).trans hj
  have tb : t.basis B=Bv := (outside B (noData B hB).1 (noData B hB).2).trans hb
  have f:=EntryRetained5.program_frame L hw hn J B hJ hB hJB Jv Bv Y hy t [] tr ty tc tz tj tb
  have ss : PairFrame L.r L.y t.basis
      (encodeWord 256 (halfResult (signedY (Jv && Bv) Y)))
      (encodeWord 256 (if Jv then Y else 0)) s.basis :=
    ⟨hR,hY,fun q qr qy=>(outside q qr qy).symm⟩
  have eq : run (EntryRetained5.program L J B) [] t=s := by
    apply State.extensionality
    · exact f.1
    · exact PairFrame.unique _ _ _ _ _ _ _ f.2 ss
  have inv:=inverseH_forward L hw hn J B hJ hB hJB Jv Bv Y hy t m tr ty tc tz tj tb
  rw [eq] at inv
  dsimp only
  rw [inv]
  exact ⟨rfl,tr,ty,outside⟩

end ECDSAAdd.Entrant.JointInverse1588

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Secp256k1

def jointH (L : BalancedCircuit.Layout) (J G : Wire) : Program :=
  [.X G] ++ programH L J G ++ [.X G]


private theorem outside_layoutH (L : BalancedCircuit.Layout) (q : Wire)
    (hq : q ∉ L.wires) : q ∉ L.r ∧ q ∉ L.y ∧ q ∉ BalancedCircuit.work L := by
  have zero := List.count_eq_zero.mpr hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    List.count_append,List.count_cons,List.count_nil] at zero
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_append,List.count_cons,List.count_nil] at pos
    omega
  constructor
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCleanup.Layout.y,List.count_append,List.count_cons,List.count_nil] at pos
    omega
  · intro h
    have pos := List.count_pos_iff.mpr h
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at pos
    omega

/-- Read the first sign directly from its history wire and restore that wire.
The two record lists of a later old/new comparison can be independent. -/
theorem jointH_frame (L : BalancedCircuit.Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J ∉ L.wires) (hG : G ∉ L.wires) (hJG : [J,G].Nodup)
    (Jv Gv : Bool) (Y : Int) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis = encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)))
    (hY : regValue L.y s.basis = encodeWord 256 (if Jv then Y else 0))
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false)
    (sign : s.basis L.sign=false) (j : s.basis J=Jv) (g : s.basis G=Gv) :
    let out := run (jointH L J G) m s
    out.phase=s.phase ∧ PairFrame L.r L.y s.basis
      (encodeWord 256 Y) 0 out.basis := by
  have apart : J≠G := fun eq => (List.nodup_cons.mp hJG).1 (List.mem_singleton.mpr eq)
  have away := outside_layoutH L G hG
  let a : State := ⟨s.phase,writeBit s.basis G (!s.basis G)⟩
  have head : run [Instr.X G] [] s=a := rfl
  have keep (q : Wire) (hq : q≠G) : a.basis q=s.basis q := by
    simp only [a,writeBit,Function.update_of_ne hq]
  have aR : regValue L.r a.basis=encodeWord 256 (halfResult (signedY (Jv && !Gv) Y)) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.1 (eq ▸ hq)))).trans hR
  have aY : regValue L.y a.basis=encodeWord 256 (if Jv then Y else 0) :=
    (regValue_congr _ _ _ (fun q hq => keep q (fun eq => away.2.1 (eq ▸ hq)))).trans hY
  have ac : ∀q∈BalancedCircuit.work L,a.basis q=false := by
    intro q hq
    exact (keep q (fun eq => away.2.2 (eq ▸ hq))).trans (clean q hq)
  have sign_mem : L.sign∈L.wires := by
    simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  have sg : L.sign≠G := fun eq => hG (eq ▸ sign_mem)
  have aj : a.basis J=Jv := (keep J apart).trans j
  have ag : a.basis G= !Gv := by simp only [a,writeBit,Function.update_self,g]
  generalize ht : run (programH L J G)
    (m.take (measurementCount (programH L J G))) a=t
  have result := inverseH_frame L hw hn J G hJ hG hJG Jv (!Gv) Y hy a
    (m.take (measurementCount (programH L J G))) aR aY ac ((keep _ sg).trans sign) aj ag
  rw [ht] at result
  let v : State := ⟨t.phase,writeBit t.basis G (!t.basis G)⟩
  have shape : run (jointH L J G) m s=v := by
    have xm : measurementCount [Instr.X G]=0 := rfl
    simp only [jointH,run_append,measurementCount_append,xm,Nat.zero_add,
      List.take_zero,List.drop_zero,head,ht] <;> rfl
  dsimp only
  rw [shape]
  refine ⟨result.1,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.1
    intro q hq
    have qg : q≠G := fun eq => away.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · apply Eq.trans (regValue_congr _ _ _ ?_) result.2.2.1
    intro q hq
    have qg : q≠G := fun eq => away.2.1 (eq ▸ hq)
    simp only [v,writeBit,Function.update_of_ne qg]
  · intro q hr hyq
    by_cases eq : q=G
    · subst q
      change (writeBit t.basis G (!t.basis G)) G=s.basis G
      simp only [writeBit,Function.update_self]
      rw [result.2.2.2 G away.1 away.2.1]
      simp only [a,writeBit,Function.update_self,Bool.not_not]
    · change (writeBit t.basis G (!t.basis G)) q=s.basis q
      rw [show (writeBit t.basis G (!t.basis G)) q=t.basis q by
        simp only [writeBit,Function.update_of_ne eq], result.2.2.2 q hr hyq,keep q eq]


theorem jointH_pair (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (origin : BasisState) (clean : ∀q∈work L,origin q=false) (sign : origin L.sign=false)
    (Z : Fp) :
    Triple (PairFrame L.r L.y origin
      (centerWord ((if origin J && !origin G then -Z else Z)/2))
      (centerWord (if origin J then Z else 0))) (jointH L J G)
      (PairFrame L.r L.y origin (centerWord Z) 0) := by
  have outside (q : Wire) (hq : q∉L.wires) : q∉L.r ∧ q∉L.y := by
    constructor <;> intro bad
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
    · exact hq (EntryRetained5.data_member L q (by simp [bad]))
  have sf:=flagAway L hn L.sign (by simp)
  have sa : L.sign∉L.r ∧ L.sign∉L.y :=
    ⟨fun bad=>sf (by simp [bad]),fun bad=>sf (by simp [bad])⟩
  intro s m h
  have hc : ∀q∈work L,s.basis q=false := fun q hq=>
    (h.2.2 q (work_no_data L hn q hq).1 (work_no_data L hn q hq).2).trans (clean q hq)
  have rr : regValue L.r s.basis=encodeWord 256
      (halfResult (signedY (origin J && !origin G) (centerFp Z))) := by
    rw [unary_half]
    exact h.1
  have yy : regValue L.y s.basis=encodeWord 256 (if origin J then centerFp Z else 0) := by
    rw [source_word]
    exact h.2.1
  have out:=jointH_frame L hw hn J G hJ hG hJG (origin J) (origin G) (centerFp Z)
    (centerFp_bounds Z) s m rr yy hc ((h.2.2 _ sa.1 sa.2).trans sign)
    (h.2.2 _ (outside J hJ).1 (outside J hJ).2) (h.2.2 _ (outside G hG).1 (outside G hG).2)
  exact ⟨out.1,out.2.1,out.2.2.1,fun q qr qy=>(out.2.2.2 q qr qy).trans (h.2.2 q qr qy)⟩


end ECDSAAdd.Entrant.JointInverse1588


/-! ### Resources of the hosted joint inverse -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] run

theorem inner_counts (L : Layout) (hw : L.Widths) :
    toffoliCount (inner L)=251 ∧ measurementCount (inner L)=251 := by
  have len := BalancedCleanup.widths L.toLayout hw
  have h := Affine.add_counts ((sources L).drop 4) (L.r.drop 4) ((L.carry.take 255).drop 4) (cAt L 3)
    (by simp [sources_length,len.2.1]) (by simp [List.length_take,hw.2.2,len.2.1])
  simp only [List.length_drop,len.2.1] at h
  exact h

theorem programH_counts (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) :
    toffoliCount (programH L J B)=517 ∧ measurementCount (programH L J B)=772 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have k:=CleanInverse5.counts (prepare L J B) (CleanInverse5.ready_proper _ _ ready)
  have c:=clearParity_counts L hw J
  have r:=restoreScalars_counts L.parity L.lower L.one L.sign (lowY L) J B L.rmsb
  have p:=prepare_counts L hw J B
  have i:=inner_counts L hw
  have w:=loanW_counts L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)
  have c1:=renameProgram_counts (Equiv.swap (cLo L) L.one) (clearParity L J)
  have c2:=renameProgram_counts (Equiv.swap (cHi L) L.sign)
    (renameProgram (Equiv.swap (cLo L) L.one) (clearParity L J))
  simp only [programH,clearH,restoreAt,affineH,toffoliCount_append,measurementCount_append,
    k.1,k.2,c.1,c.2,r.1,r.2,p.1,w.1,w.2,i.1,i.2,c1.1,c1.2,c2.1,c2.2,(pre4_counts L).1,(pre4_counts L).2,
    (post4_counts L).1,(post4_counts L).2,(notRegister_counts L.r).1,(notRegister_counts L.r).2]
  all_goals simp

theorem jointH_counts (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) :
    toffoliCount (jointH L J G)=517 ∧ measurementCount (jointH L J G)=772 := by
  have h:=programH_counts L hw hn J G hJ hG
  simpa only [jointH,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,Nat.zero_add,Nat.add_zero] using h

/-- Every wire of a two-swap renaming lies in the old support or is one of the two hosts. -/
theorem swap2_support (a b c d : Wire) (P : Program) (W : Finset Wire) (hP : wires P⊆W)
    (ha : a∈W) (hb : b∈W) (hc : c∈W) (hd : d∈W) :
    wires (renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P))⊆W := by
  rw [renameProgram_support,renameProgram_support]
  intro q hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hyW := hP hy
  have inner : Equiv.swap a b y∈W := by
    rw [Equiv.swap_apply_def]
    split_ifs <;> assumption
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

/-- A two-swap renaming avoids `a` and `c` when `P` avoids the hosts `b` and `d`. -/
theorem swap2_free (a b c d : Wire) (P : Program) (hb : b∉wires P) (hd : d∉wires P)
    (hac : a≠c) (had : a≠d) (hdb : d≠b) (q : Wire) (hq : q=a ∨ q=c) :
    q∉wires (renameProgram (Equiv.swap c d) (renameProgram (Equiv.swap a b) P)) := by
  rw [renameProgram_support,renameProgram_support]
  intro used
  obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp used
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have back : y=Equiv.swap a b (Equiv.swap c d q) := by
    rw [←ex]
    simp only [Equiv.swap_apply_self]
  rcases hq with rfl|rfl
  · rw [Equiv.swap_apply_of_ne_of_ne hac had,Equiv.swap_apply_left] at back
    exact hb (back ▸ hy)
  · rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne (Ne.symm had) hdb] at back
    exact hd (back ▸ hy)

end ECDSAAdd.Entrant.JointInverse1588


/-! ### Support, physicality and syntax slots of the hosted joint inverse -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

/-- `prepare` reads no carry. -/
theorem prepare_support (L : Layout) (hw : L.Widths) (J B : Wire) :
    wires (prepare L J B)⊆(L.r++L.y++[L.parity,L.lower,L.one,L.sign,J,B]).toFinset := by
  let W := (L.r++L.y++[L.parity,L.lower,L.one,L.sign,J,B]).toFinset
  have scalar (q : Wire) (hq : q∈[L.parity,L.lower,L.one,L.sign,J,B]) : q∈W :=
    List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have hp := scalar L.parity (by simp)
  have ha := scalar L.lower (by simp)
  have hd := scalar L.one (by simp)
  have he := scalar L.sign (by simp)
  have hj := scalar J (by simp)
  have hb := scalar B (by simp)
  have r (q : Wire) (hq : q∈L.r) : q∈W := by simp [W,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈W := by simp [W,hq]
  have r0 := r L.r0 (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  have rh := r L.rmsb (by simp [BalancedCleanup.Layout.r])
  have yu : lowY L∈L.y := by rw [y_cons L hw]; simp
  have u := y (lowY L) yu
  have len := BalancedCleanup.widths L.toLayout hw
  have idx : 254<L.r.length := by rw [len.2.1]; decide
  have ri := r (L.r.getD 254 0) (by rw [List.getD_eq_getElem _ _ idx]; exact List.getElem_mem _)
  have riAlt : L.r[254]?.getD 0∈W := ri
  have cp : wires (copyRegister (some J) L.r.tail L.y.tail)⊆W := by
    rw [copyRegister_wires _ _ _ (by simp [len.2.1,len.2.2.1])]
    split
    · exact Finset.empty_subset _
    · intro q hq
      simp only [List.mem_toFinset,List.mem_append,Option.toList_some,List.mem_singleton] at hq
      rcases hq with (rfl|hq)|hq
      · exact hj
      · exact r q (List.mem_of_mem_tail hq)
      · exact y q (List.mem_of_mem_tail hq)
  have rot : wires (rotateRight L.r)⊆W := by
    rw [(rotate_wires L.r).1,if_neg (by rw [len.2.1]; omega)]
    exact fun q hq => r q (List.mem_toFinset.mp hq)
  have comp (ctl : Wire) (hctl : ctl∈W) : wires (signComplement ctl L.r)⊆W := by
    intro q hq
    have h := signComplement_wires_subset ctl L.r hq
    simp only [List.mem_toFinset,List.mem_cons] at h
    rcases h with rfl|h
    · exact hctl
    · exact r q h
  have first : wires [Instr.CCX J B (lowY L)]⊆W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,hj,hb,u]
  have seeds : wires [Instr.CX L.r0 L.parity,Instr.CCX L.parity L.rmsb L.lower,
      Instr.CCX L.parity (lowY L) L.one,Instr.CCX L.lower (lowY L) L.sign,
      Instr.CX L.parity L.r0]⊆W := by
    simp [wires,Instr.wires,Finset.union_subset_iff,Finset.insert_subset_iff,r0,rh,hp,ha,hd,he,u]
  have extend : wires [Instr.CX (L.r.getD 254 0) L.rmsb]⊆W := by
    simp [wires,Instr.wires,Finset.insert_subset_iff,ri,riAlt,rh]
  simpa only [prepare,wires_append,Finset.union_subset_iff] using
    And.intro (And.intro (And.intro (And.intro (And.intro first cp) seeds) rot) extend) (comp _ u)

theorem pre4_post4_support (L : Layout) (hw : L.Widths) :
    wires (pre4 L)⊆wires (arithmetic L) ∧ wires (inner L)⊆wires (arithmetic L) ∧
      wires (post4 L)⊆wires (arithmetic L) := by
  have h : arithmetic L=pre4 L++inner L++post4 L := add_split L hw
  rw [h]
  simp only [wires_append]
  exact ⟨fun q hq => by simp [hq],fun q hq => by simp [hq],fun q hq => by simp [hq]⟩

theorem programH_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J B : Wire) :
    wires (programH L J B)⊆retSites L J B := by
  have old:=EntryRetained5.program_support L hw J B
  have parts : ((wires (prepare L J B)⊆retSites L J B ∧ wires (arithmetic L)⊆retSites L J B) ∧
      wires (eraseScalarsAt L J B)⊆retSites L J B) ∧ wires (clearParity L J)⊆retSites L J B := by
    simpa only [EntryRetained5.program,prefixProgram,wires_append,Finset.union_subset_iff] using old
  have r (q : Wire) (hq : q∈L.r) : q∈retSites L J B := by simp [retSites,hq]
  have y (q : Wire) (hq : q∈L.y) : q∈retSites L J B := by simp [retSites,hq]
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have hp : L.parity∈retSites L J B := by simp [retSites]
  have ha : L.lower∈retSites L J B := by simp [retSites]
  have hd : L.one∈retSites L J B := by simp [retSites]
  have he : L.sign∈retSites L J B := by simp [retSites]
  have hj : J∈retSites L J B := by simp [retSites]
  have hb : B∈retSites L J B := by simp [retSites]
  have hu := y (lowY L) y0
  have carryIn (i : Nat) (hi : i<255) : L.carry.getD i 0∈retSites L J B := by
    have m := carry_take_mem L hw i hi
    simp only [retSites,List.mem_toFinset,List.mem_append]
    exact Or.inl (Or.inr m)
  have erase : wires (restoreAt L J B)⊆retSites L J B := by
    intro q hq
    simp only [restoreAt,restoreScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    have hh:=r L.rmsb rh
    aesop
  have notr : wires (notRegister L.r)⊆retSites L J B := by
    rw [notRegister_wires]
    intro q hq
    exact r q (List.mem_toFinset.mp hq)
  have split := pre4_post4_support L hw
  have clearS : wires (clearH L J)⊆retSites L J B :=
    swap2_support _ _ _ _ _ _ parts.2 (carryIn 4 (by decide)) hd (carryIn 254 (by decide)) he
  have loan : wires (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L))⊆retSites L J B := by
    simp only [loanW,wires_append,Finset.union_subset_iff]
    refine ⟨⟨?_,swap2_support _ _ _ _ _ _ (split.2.1.trans parts.1.1.2) (carryIn 4 (by decide)) hu
      (carryIn 254 (by decide)) he⟩,?_⟩
    · simp [wires,Instr.wires,correctionWires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
    · simp [wires,Instr.wires,Finset.insert_subset_iff,Finset.union_subset_iff,he,ha,hu,hj,hb]
  have affine : wires (affineH L J B)⊆retSites L J B := by
    simp only [affineH,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨notr,split.1.trans parts.1.1.2⟩,loan⟩,split.2.2.trans parts.1.1.2⟩,notr⟩
  simp only [programH,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨clearS,erase⟩,affine⟩,(CleanInverse5.inverse_support _).trans parts.1.1.1⟩

theorem jointH_support (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) (J G : Wire) :
    wires (jointH L J G)⊆retSites L J G := by
  have g : G∈retSites L J G := by simp [retSites]
  have x : wires [Instr.X G]⊆retSites L J G := by
    intro q hq
    have : q=G := by simpa [wires,Instr.wires] using hq
    rw [this];exact g
  simp only [jointH,wires_append,Finset.union_subset_iff]
  exact ⟨⟨x,programH_support L hw hn J G⟩,x⟩

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The hosted carries never appear; physicality and slots -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem edge_support (L : Layout) :
    wires (pre4 L)⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,
      cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset ∧
    wires (post4 L)⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,
      cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset := by
  let W := (Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,
      cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset
  have src (i : Nat) (hi : i<256) : ∀q∈(source L i).wires,q∈W := fun q hq =>
    List.mem_toFinset.mpr (List.mem_append_left _ (source_site L i hi q hq))
  have t (q : Wire) (hq : q∈[rAt L 0,rAt L 1,rAt L 2,rAt L 3,lowY L,cAt L 0,cAt L 1,cAt L 2,cAt L 3]) :
      q∈W := List.mem_toFinset.mpr (List.mem_append_right _ hq)
  have b0 := Affine.local_support (source L 0) (rAt L 0) (lowY L) (cAt L 0) W (src 0 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  have b1 := Affine.local_support (source L 1) (rAt L 1) (cAt L 0) (cAt L 1) W (src 1 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  have b2 := Affine.local_support (source L 2) (rAt L 2) (cAt L 1) (cAt L 2) W (src 2 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  have b3 := Affine.local_support (source L 3) (rAt L 3) (cAt L 2) (cAt L 3) W (src 3 (by decide))
    (t _ (by simp)) (t _ (by simp)) (t _ (by simp))
  constructor
  · simp only [pre4,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨b0.1,b1.1⟩,b2.1⟩,b3.1⟩
  · simp only [post4,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨b3.2.1,b3.2.2⟩,b2.2.1⟩,b2.2.2⟩,b1.2.1⟩,b1.2.2⟩,b0.2.1⟩,b0.2.2⟩

theorem programH_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L) : q∉wires (programH L J B) := by
  have dist := ports_distinct L hw hn J B hJ hB hJB
  have hd := hosts_distinct L hw hn
  have nd7 := dist.1
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,
    not_false_eq_true,and_true] at nd7
  rcases nd7 with ⟨⟨sl,su,sj,sb,slo,shi⟩,⟨⟨lu,lj,lb,llo,lhi⟩,⟨⟨uj,ub,ulo,uhi⟩,
    ⟨⟨jb,jlo,jhi⟩,⟨⟨blo,bhi⟩,lohi⟩⟩⟩⟩⟩
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
  have qr : q∉L.r := carry_not_r L hn q qc
  have qy : q∉L.y := fun h => y_not_carry L hn q h qc
  have flagNe (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) :
      q≠f := fun e => flagAway L hn f hf (by rw [←e];simp [qc])
  have qJ : q≠J := fun e => hJ (e ▸ data_member L q (by simp [qc]))
  have qB : q≠B := fun e => hB (e ▸ data_member L q (by simp [qc]))
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have qu : q≠lowY L := fun e => qy (e ▸ y0)
  have qlow (i : Nat) (hi : i<4) : q≠cAt L i := by
    rcases hq with rfl|rfl
    · exact carry_index_ne L hw hn 4 i (by decide) (by omega) (by omega)
    · exact carry_index_ne L hw hn 254 i (by decide) (by omega) (by omega)
  have qsite (h : q∈Affine.sites (sources L)) : False := by
    have m := sources_sites L q h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
  have edge (P : Program) (hP : wires P⊆(Affine.sites (sources L)++[rAt L 0,rAt L 1,rAt L 2,rAt L 3,
      lowY L,cAt L 0,cAt L 1,cAt L 2,cAt L 3]).toFinset) : q∉wires P := by
    intro used
    have m := List.mem_toFinset.mp (hP used)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    have rmem (i : Nat) (hi : i<4) : rAt L i∈L.r := by
      have len := BalancedCleanup.widths L.toLayout hw
      have lt : i<L.r.length := by rw [len.2.1];omega
      simp only [rAt,List.getD_eq_getElem _ _ lt]
      exact List.getElem_mem lt
    rcases m with h|e|e|e|e|e|e|e|e|e
    · exact qsite h
    · exact qr (e ▸ rmem 0 (by decide))
    · exact qr (e ▸ rmem 1 (by decide))
    · exact qr (e ▸ rmem 2 (by decide))
    · exact qr (e ▸ rmem 3 (by decide))
    · exact qu e
    · exact qlow 0 (by decide) e
    · exact qlow 1 (by decide) e
    · exact qlow 2 (by decide) e
    · exact qlow 3 (by decide) e
  have es := edge_support L
  have clearF : q∉wires (clearH L J) :=
    swap2_free (cLo L) L.one (cHi L) L.sign (clearParity L J)
      (clearParity_scalar_free L hw hn J hJ L.one (Or.inl rfl))
      (clearParity_scalar_free L hw hn J hJ L.sign (Or.inr rfl))
      hd.2.2.2.2.2.1 (Ne.symm slo) (Ne.symm hd.2.2.2.2.1) q hq
  have restoreSub : wires (restoreAt L J B)⊆
      ([L.parity,L.lower,L.one,L.sign,lowY L,J,B,L.rmsb] : List Wire).toFinset := by
    intro x hx
    simp only [restoreAt,restoreScalars,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have rh : L.rmsb∈L.r := by simp [BalancedCleanup.Layout.r]
  have restoreF : q∉wires (restoreAt L J B) := by
    intro used
    have m := List.mem_toFinset.mp (restoreSub used)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with e|e|e|e|e|e|e|e
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
    · exact qr (e ▸ rh)
  have notrF : q∉wires (notRegister L.r) := by
    rw [notRegister_wires]
    exact fun h => qr (List.mem_toFinset.mp h)
  have innerF : q∉wires (renameProgram (Equiv.swap (cHi L) L.sign)
      (renameProgram (Equiv.swap (cLo L) (lowY L)) (inner L))) := by
    have sc := scalarND L hn
    exact swap2_free (cLo L) (lowY L) (cHi L) L.sign (inner L)
      (inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e
        · exact flagAway L hn L.parity (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.lower (by simp) (by rw [←e];simp [y0])
        · exact flagAway L hn L.one (by simp) (by rw [←e];simp [y0]))
        (y_not_r L hn _ y0) (y_not_carry L hn _ y0))
      (inner_free L hw hn _ (fun h => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e|e|e <;>
          (have c := List.nodup_iff_count.mp sc L.sign
           rw [e] at c;simp [List.count_cons] at c;omega))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h]))
        (fun h => flagAway L hn L.sign (by simp) (by simp [h])))
      hd.2.2.2.2.2.1 (Ne.symm slo) su q hq
  have edgeSub : wires ([.measureX L.sign [] [.CZ L.lower (lowY L)],.measureX (lowY L) [] [.CZ J B]] : Program)∪
      wires ([.CCX J B (lowY L),.CCX L.lower (lowY L) L.sign] : Program)⊆
      ([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro x hx
    simp only [wires,Instr.wires,correctionWires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false,Finset.union_empty] at hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have edgeF : q∉([L.sign,L.lower,lowY L,J,B] : List Wire).toFinset := by
    intro h
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with e|e|e|e|e
    · exact flagNe L.sign (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact qu e
    · exact qJ e
    · exact qB e
  have loanF : q∉wires (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)) := by
    simp only [loanW,wires_append,Finset.mem_union,not_or]
    refine ⟨⟨fun h => edgeF (edgeSub (Finset.mem_union_left _ h)),innerF⟩,
      fun h => edgeF (edgeSub (Finset.mem_union_right _ h))⟩
  have prepF : q∉wires (CleanInverse5.inverse (prepare L J B)) := by
    intro used
    have m := List.mem_toFinset.mp (prepare_support L hw J B (CleanInverse5.inverse_support _ used))
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with (h|h)|e|e|e|e|e|e
    · exact qr h
    · exact qy h
    · exact flagNe L.parity (by simp) e
    · exact flagNe L.lower (by simp) e
    · exact flagNe L.one (by simp) e
    · exact flagNe L.sign (by simp) e
    · exact qJ e
    · exact qB e
  simp only [programH,affineH,wires_append,Finset.mem_union,not_or]
  exact ⟨⟨⟨clearF,restoreF⟩,⟨⟨⟨⟨notrF,edge _ es.1⟩,loanF⟩,edge _ es.2⟩,notrF⟩⟩,prepF⟩

theorem jointH_free (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup)
    (q : Wire) (hq : q=cLo L ∨ q=cHi L) : q∉wires (jointH L J G) := by
  have core := programH_free L hw hn J G hJ hG hJG q hq
  have qc : q∈L.carry := by
    rcases hq with rfl|rfl
    · exact carry_mem L hw 4 (by decide)
    · exact carry_mem L hw 254 (by decide)
  have qG : q≠G := fun e => hG (e ▸ data_member L q (by simp [qc]))
  simp only [jointH,wires_append,Finset.mem_union,not_or]
  refine ⟨⟨?_,core⟩,?_⟩ <;> simp [wires,Instr.wires,qG]

end ECDSAAdd.Entrant.JointInverse1588


/-! ### Physicality and syntax slots -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField EntryRetained5 FirstInverse5 Challenge Baselines RecordedQuantum
attribute [local irreducible] wires

theorem programH_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) (hJB : [J,B].Nodup) :
    GatePhysical (programH L J B) := by
  have old:=EntryRetained5.program_physical L hw hn J B hJ hB hJB
  have parts : ((GatePhysical (prepare L J B) ∧ GatePhysical (arithmetic L)) ∧
      GatePhysical (eraseScalarsAt L J B)) ∧ GatePhysical (clearParity L J) := by
    simpa only [EntryRetained5.program,prefixProgram,gatePhysical_append] using old
  have n:=erasePorts_nodup L hw hn J B hJ hB hJB
  have ctr : (lowY L)≠J ∧ L.parity≠L.lower ∧ (lowY L)≠L.one ∧ L.parity≠L.one ∧
      L.rmsb≠L.lower ∧ L.one≠L.lower ∧ L.lower≠L.sign ∧ (lowY L)≠L.sign ∧ J≠lowY L ∧ B≠lowY L := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at n
    rcases n with ⟨⟨pA,pD,pE,pU,pJ,pB,pH⟩,⟨⟨aD,aE,aU,aJ,aB,aH⟩,
      ⟨⟨dE,dU,dJ,dB,dH⟩,⟨⟨eU,eJ,eB,eH⟩,⟨⟨uJ,uB,uH⟩,⟨⟨jB,jH⟩,bH⟩⟩⟩⟩⟩⟩
    exact ⟨uJ,pA,Ne.symm dU,pD,Ne.symm aH,Ne.symm aD,aE,Ne.symm eU,
      Ne.symm uJ,Ne.symm uB⟩
  have restore : GatePhysical (restoreAt L J B) := by
    simp [restoreAt,restoreScalars,GatePhysical,PhysicalInstr,ProperGate,ctr.1,ctr.2.1,
      ctr.2.2.1,ctr.2.2.2.1,ctr.2.2.2.2.1,ctr.2.2.2.2.2.1,
      ctr.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.2]
  have arith : GatePhysical (pre4 L) ∧ GatePhysical (inner L) ∧ GatePhysical (post4 L) := by
    have h := parts.1.1.2
    rw [show arithmetic L=pre4 L++inner L++post4 L from add_split L hw] at h
    simp only [gatePhysical_append] at h
    exact ⟨h.1.1,h.1.2,h.2⟩
  have clear : GatePhysical (clearH L J) :=
    gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ parts.2)
  have loan : GatePhysical (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L)) := by
    simp only [loanW,gatePhysical_append]
    refine ⟨⟨?_,gatePhysical_rename _ (Equiv.swap _ _).injective _
      (gatePhysical_rename _ (Equiv.swap _ _).injective _ arith.2.1)⟩,?_⟩
    · simp [GatePhysical,PhysicalInstr]
    · simp [GatePhysical,PhysicalInstr,ProperGate,ctr.2.2.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.2.2,
        ctr.2.2.2.2.2.2.1,ctr.2.2.2.2.2.2.2.1]
  have affine : GatePhysical (affineH L J B) := by
    simp only [affineH,gatePhysical_append]
    exact ⟨⟨⟨⟨notRegister_physical _,arith.1⟩,loan⟩,arith.2.2⟩,notRegister_physical _⟩
  simp only [programH,gatePhysical_append]
  exact ⟨⟨⟨clear,restore⟩,affine⟩,CleanInverse5.inverse_physical _ parts.1.1.1⟩

theorem jointH_physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) (hJG : [J,G].Nodup) :
    GatePhysical (jointH L J G) := by
  have core := programH_physical L hw hn J G hJ hG hJG
  have x : GatePhysical [Instr.X G] := by simp [GatePhysical,PhysicalInstr,ProperGate]
  simp only [jointH,gatePhysical_append]
  exact ⟨⟨x,core⟩,x⟩

theorem programH_slots (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J B : Wire) (hJ : J∉L.wires) (hB : B∉L.wires) : gateSlots (programH L J B)≤10006 := by
  let zero : State:=⟨false,fun _=>false⟩
  have ready:=prepare_ready L hw hn J B hJ hB zero
    ((regValue_zero _ _).mpr (by intro q hq;rfl)) (by intro q hq;rfl) rfl
  have inv:=CleanInverse5.inverse_slots _ (CleanInverse5.ready_proper _ _ ready)
  have prep:=prepare_slots_le L hw J B
  have arith:=arithmetic_slots L hw
  have par:=clearParity_slots_le L hw J
  have pc:=prepare_counts L hw J B
  have xr:=notRegister_gateSlots L.r
  have len:=BalancedCleanup.widths L.toLayout hw
  have rest : gateSlots (restoreAt L J B)=8 := rfl
  have split : gateSlots (pre4 L)+gateSlots (inner L)+gateSlots (post4 L)=4369 := by
    rw [←arith,show arithmetic L=pre4 L++inner L++post4 L from add_split L hw]
    simp only [gateSlots_append]
  have loanS : gateSlots (loanW L.sign L.lower (lowY L) J B (cLo L) (cHi L) (inner L))=
      gateSlots (inner L)+6 := by
    have a : gateSlots ([Instr.measureX L.sign [] [Correction.CZ L.lower (lowY L)],
        Instr.measureX (lowY L) [] [Correction.CZ J B]] : Program)=4 := rfl
    have b : gateSlots ([Instr.CCX J B (lowY L),Instr.CCX L.lower (lowY L) L.sign] : Program)=2 := rfl
    simp only [loanW,gateSlots_append,rename_gateSlots,a,b]
    omega
  simp only [programH,clearH,affineH,gateSlots_append,rename_gateSlots,xr,len.2.1,rest,loanS]
  omega

theorem jointH_slots (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (J G : Wire) (hJ : J∉L.wires) (hG : G∉L.wires) : gateSlots (jointH L J G)≤10008 := by
  have h := programH_slots L hw hn J G hJ hG
  have x : gateSlots [Instr.X G]=1 := rfl
  simp only [jointH,gateSlots_append,x]
  omega

end ECDSAAdd.Entrant.JointInverse1588


/-! ## The S2 first-packet kernel in the record's 1,588 layout -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
  EntryRetained5 FirstInverse5 Challenge Baselines
attribute [local irreducible] wires

/-- The record's half-kernel ports (f2dcda16's `loanPorts1592`). -/
def portsJ : BalancedCircuit.Layout := Q6EndpointCell.ports base (base 2409)

theorem portsJ_eq : portsJ=Q6EndpointCell.ports base (base 2409) := rfl

theorem portsJ_widths : portsJ.Widths := by rw [portsJ_eq];exact Q6EndpointCell.ports_widths base (base 2409)

theorem portsJ_nodup : portsJ.wires.Nodup := by
  rw [portsJ_eq]
  exact Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective (by
    intro member
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
    have same := base_injective eq
    have bound := Q6EndpointCell.ids_bound i hi
    omega)

theorem portsJ_outside (i : Nat) (hi : i=1028 ∨ i=1 ∨ i=1032 ∨ i=0) : base i∉portsJ.wires := by
  simp only [portsJ,Q6EndpointCell.ports,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,List.mem_map,List.mem_range'_1,
    or_false,base_injective.eq_iff]
  rcases hi with rfl|rfl|rfl|rfl <;> omega

theorem controls_nodup : [base 1028,base 1].Nodup := by
  simp [base_injective.eq_iff]

theorem cLo_eq : cLo portsJ=base 516 := by
  simp [cLo,portsJ,Q6EndpointCell.ports,wireBlock,List.getD_eq_getElem?_getD]

theorem cHi_eq : cHi portsJ=base 1541 := by
  simp [cHi,portsJ,Q6EndpointCell.ports,wireBlock,List.getD_eq_getElem?_getD]

/-- The joint inverse with virtual carry `719` on the open trit hole `s 0 4 = base 1032`. -/
def kernel : Program :=
  renameProgram (Equiv.swap (base 719) (base 1032)) (jointH portsJ (base 1028) (base 1))

/-- Record-length padding: 507 empty-correction erasures of the clean carry `base 512`
(the replaced half window has 1022 and the measured first swap 257 records). -/
def padding : Program := List.replicate 507 (Instr.measureX (base 512) [] [])

def padded : Program := kernel++padding

theorem pad_run (c : Wire) (n : Nat) (r : List Bool) (t : State) (hc : t.basis c=false) :
    run (List.replicate n (Instr.measureX c [] [])) r t=t := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have one : measureAndCorrect c [] [] (r.headD false) t=t := by
      apply State.extensionality
      · simp [measureAndCorrect,correct,hc]
      · funext q
        by_cases e : q=c
        · subst q;simp [measureAndCorrect,correct,writeBit,hc]
        · simp [measureAndCorrect,correct,writeBit,e]
    change run (Instr.measureX c [] []::List.replicate n (Instr.measureX c [] [])) r t=t
    simp only [run]
    rw [one]
    exact ih _

theorem pad_wires (c : Wire) (n : Nat) : wires (List.replicate n (Instr.measureX c [] []))⊆{c} := by
  induction n with
  | zero => simp [wires]
  | succ n ih =>
    rw [List.replicate_succ]
    intro q hq
    simp only [wires,Finset.mem_union] at hq
    rcases hq with h|h
    · simpa [Instr.wires,correctionWires] using h
    · exact ih h

theorem padding_counts : toffoliCount padding=0 ∧ measurementCount padding=507 := by
  have h (n : Nat) : toffoliCount (List.replicate n (Instr.measureX (base 512) [] []))=0 ∧
      measurementCount (List.replicate n (Instr.measureX (base 512) [] []))=n := by
    induction n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih =>
      rw [List.replicate_succ]
      simp [toffoliCount,measurementCount,ih.1,ih.2,Nat.add_comm]
  exact h 507

theorem padded_counts : toffoliCount padded=517 ∧ measurementCount padded=1279 := by
  have j := jointH_counts portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl)))
  have r := renameProgram_counts (Equiv.swap (base 719) (base 1032)) (jointH portsJ (base 1028) (base 1))
  have p := padding_counts
  simp only [padded,kernel,toffoliCount_append,measurementCount_append,r.1,r.2,j.1,j.2,p.1,p.2]
  all_goals simp

theorem padded_slots : gateSlots padded≤10515 := by
  have j := jointH_slots portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl)))
  have p : gateSlots padding=507 := by
    have h (n : Nat) : gateSlots (List.replicate n (Instr.measureX (base 512) [] []))=n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.replicate_succ,gateSlots_cons,ih]
        simp [instructionSlots]
        omega
    exact h 507
  simp only [padded,kernel,gateSlots_append,rename_gateSlots,p]
  omega

theorem padded_physical : GatePhysical padded := by
  have j := jointH_physical portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  have p : GatePhysical padding := by
    intro i hi
    rw [padding,List.mem_replicate] at hi
    rw [hi.2]
    simp [PhysicalInstr]
  simp only [padded,kernel,gatePhysical_append]
  exact ⟨gatePhysical_rename _ (Equiv.swap _ _).injective _ j,p⟩

theorem portsJ_r : portsJ.r=wireBlock base 2056 256 := by
  rw [portsJ_eq,Q6EndpointCell.ports_r,balancedSharedPorts_r]
theorem portsJ_y : portsJ.y=wireBlock base 770 256 := by
  rw [portsJ_eq,Q6EndpointCell.ports_y,balancedSharedPorts_y]
theorem portsJ_carry : portsJ.carry=wireBlock base 512 253++[base 1540,base 1541,base 1026] := rfl

theorem portsJ_take254 : portsJ.carry.take 254=wireBlock base 512 253++[base 1540] := by
  have wl : (wireBlock base 512 253).length=253 := wireBlock_length _ _ _
  rw [portsJ_carry,List.take_append,List.take_of_length_le (by omega),wl]
  rfl

theorem portsJ_take255 : portsJ.carry.take 255=portsJ.carry.take 254++[base 1541] := by
  have wl : (wireBlock base 512 253).length=253 := wireBlock_length _ _ _
  rw [portsJ_take254,portsJ_carry,List.take_append,List.take_of_length_le (by omega),wl]
  simp

/-- A numbered wire away from the three blocks and the three tail carries. -/
theorem off_ports (i : Nat) (hr : i<2056 ∨ 2312 ≤ i) (hy : i<770 ∨ 1026 ≤ i) (hc : i<512 ∨ 765 ≤ i)
    (h1 : i≠1540) (h2 : i≠1541) (h3 : i≠1026) :
    base i∉portsJ.r ∧ base i∉portsJ.y ∧ base i∉portsJ.carry := by
  refine ⟨?_,?_,?_⟩
  · rw [portsJ_r];exact OwnPlusHost.not_block i 2056 256 (by omega)
  · rw [portsJ_y];exact OwnPlusHost.not_block i 770 256 (by omega)
  · rw [portsJ_carry]
    intro h
    rcases List.mem_append.mp h with h|h
    · exact OwnPlusHost.not_block i 512 253 (by omega) h
    · simp only [List.mem_cons,List.not_mem_nil,or_false,base_injective.eq_iff] at h
      omega

/-- The sites the padded kernel may use: data words, the first 254 carries, the four scalars,
the controls `S0`, `G1` and the trit hole `s 0 4`. -/
def kernelSites : Finset Wire :=
  (portsJ.r++portsJ.y++portsJ.carry.take 254++
    [portsJ.parity,portsJ.lower,portsJ.one,portsJ.sign,base 1028,base 1,base 1032]).toFinset

theorem hole_free : base 1032∉wires (jointH portsJ (base 1028) (base 1)) := by
  have sup := jointH_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  intro used
  have m := List.mem_toFinset.mp (sup used)
  have off := off_ports 1032 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [retSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
  rcases m with ((h|h)|h)|h
  · exact off.1 h
  · exact off.2.1 h
  · exact off.2.2 (List.mem_of_mem_take h)
  · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
    omega

theorem padded_support : wires padded⊆kernelSites := by
  have sup := jointH_support portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
  have lo := jointH_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq] at lo
  have keep (q : Wire) (hq : q∈wires (jointH portsJ (base 1028) (base 1))) : q∈kernelSites := by
    have m := List.mem_toFinset.mp (sup hq)
    have q1541 : q≠base 1541 := fun e => lo _ (Or.inr e) hq
    simp only [retSites,List.mem_append] at m
    simp only [kernelSites,List.mem_toFinset,List.mem_append]
    rcases m with ((h|h)|h)|h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [portsJ_take255,List.mem_append,List.mem_singleton] at h
      rcases h with h|h
      · exact Or.inl (Or.inr h)
      · exact absurd h q1541
    · right
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  intro q hq
  simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at hq
  rcases hq with hq|hq
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
    by_cases a719 : a=base 719
    · subst a
      rw [Equiv.swap_apply_left]
      simp [kernelSites]
    · by_cases a1032 : a=base 1032
      · exact absurd (a1032 ▸ ha) hole_free
      · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032]
        exact keep a ha
  · have e : q=base 512 := Finset.mem_singleton.mp (pad_wires (base 512) 507 hq)
    subst e
    have m : base 512∈wireBlock base 512 253 :=
      List.mem_map.mpr ⟨512,by simp [List.mem_range'_1],rfl⟩
    simp only [kernelSites,List.mem_toFinset,List.mem_append,portsJ_take254]
    exact Or.inl (Or.inr (Or.inl m))

theorem padded_free (i : Nat) (hi : i=0 ∨ i=516 ∨ i=719 ∨ i=1541) : base i∉wires padded := by
  have lo := jointH_free portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup
  rw [cLo_eq,cHi_eq] at lo
  rcases hi with rfl|rfl|rfl|rfl
  · intro used
    have m := List.mem_toFinset.mp (padded_support used)
    have off := off_ports 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with ((h|h)|h)|h
    · exact off.1 h
    · exact off.2.1 h
    · exact off.2.2 (List.mem_of_mem_take h)
    · simp only [portsJ,Q6EndpointCell.ports,base_injective.eq_iff] at h
      omega
  all_goals
    intro used
    simp only [padded,kernel,wires_append,Finset.mem_union,renameProgram_support] at used
    rcases used with used|used
    · obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp used
      by_cases a719 : a=base 719
      · subst a719
        rw [Equiv.swap_apply_left,base_injective.eq_iff] at eq
        omega
      · by_cases a1032 : a=base 1032
        · subst a1032
          exact hole_free ha
        · rw [Equiv.swap_apply_of_ne_of_ne a719 a1032] at eq
          subst eq
          first
            | exact a719 rfl
            | exact lo _ (Or.inl rfl) ha
            | exact lo _ (Or.inr rfl) ha
    · have e := Finset.mem_singleton.mp (pad_wires (base 512) 507 used)
      rw [base_injective.eq_iff] at e
      omega

end ECDSAAdd.Entrant.JointInverse1588


/-! ### The padded kernel's frame on the replay state -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed Secp256k1 RecordedQuantum
  EntryRetained5 FirstInverse5 Challenge Baselines
attribute [local irreducible] wires

theorem off_data (i : Nat) (hr : i<2056 ∨ 2312 ≤ i) (hy : i<770 ∨ 1026 ≤ i) :
    base i∉portsJ.r ∧ base i∉portsJ.y := by
  refine ⟨?_,?_⟩
  · rw [portsJ_r];exact OwnPlusHost.not_block i 2056 256 (by omega)
  · rw [portsJ_y];exact OwnPlusHost.not_block i 770 256 (by omega)

theorem carry_work (i : Nat) (hi : 512 ≤ i ∧ i<765) : base i∈BalancedCircuit.work portsJ := by
  have m : base i∈wireBlock base 512 253 := List.mem_map.mpr ⟨i,by simp [List.mem_range'_1];omega,rfl⟩
  simp only [BalancedCircuit.work,List.mem_append,portsJ_carry]
  exact Or.inr (Or.inl m)

/-- On any replay state with clean scalar bank, clean flag and open trit hole, the padded kernel
performs f2dcda16's joint inverse `(±Z/2, J?Z:0) ↦ (Z,0)`. -/
theorem padded_pair (st : BasisState) (clean : ∀q∈BalancedCircuit.work portsJ,st q=false)
    (sign : st (base 2409)=false) (hole : st (base 1032)=false) (Z : Fp) :
    Triple (PairFrame portsJ.r portsJ.y st
      (centerWord ((if st (base 1028) && !st (base 1) then -Z else Z)/2))
      (centerWord (if st (base 1028) then Z else 0))) padded
      (PairFrame portsJ.r portsJ.y st (centerWord Z) 0) := by
  have j := jointH_pair portsJ portsJ_widths portsJ_nodup (base 1028) (base 1)
    (portsJ_outside 1028 (Or.inl rfl)) (portsJ_outside 1 (Or.inr (Or.inl rfl))) controls_nodup st clean
    (by simpa [portsJ_eq] using sign) Z
  intro s m input
  have a719 := off_data 719 (by omega) (by omega)
  have a1032 := off_data 1032 (by omega) (by omega)
  have a512 := off_data 512 (by omega) (by omega)
  let mk := m.take (measurementCount kernel)
  have out := j s mk input
  have in719 : s.basis (base 719)=false :=
    (input.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have in1032 : s.basis (base 1032)=false := (input.2.2 _ a1032.1 a1032.2).trans hole
  have o719 : (run (jointH portsJ (base 1028) (base 1)) mk s).basis (base 719)=false :=
    (out.2.2.2 _ a719.1 a719.2).trans (clean _ (carry_work 719 (by omega)))
  have o1032 : (run (jointH portsJ (base 1028) (base 1)) mk s).basis (base 1032)=false :=
    (out.2.2.2 _ a1032.1 a1032.2).trans hole
  have k : run kernel mk s=run (jointH portsJ (base 1028) (base 1)) mk s :=
    rebind_swap_run _ _ _ s mk in719 in1032 o719 o1032
  have o512 : (run (jointH portsJ (base 1028) (base 1)) mk s).basis (base 512)=false :=
    (out.2.2.2 _ a512.1 a512.2).trans (clean _ (carry_work 512 (by omega)))
  have shape : run padded m s=run (jointH portsJ (base 1028) (base 1)) mk s := by
    rw [padded,run_append,k,padding]
    exact pad_run (base 512) 507 _ _ o512
  rw [shape]
  exact out

end ECDSAAdd.Entrant.JointInverse1588

/-! ### Syntax-slot comparison with the replaced half window -/
set_option maxRecDepth 100000
namespace ECDSAAdd.Entrant.JointInverse1588
open Arithmetic MappedCompressed Challenge

/-- Checked by kernel evaluation (`decide +kernel`): the replaced inverse half has at least 9500 slots
(it has 16440), so the padded joint inverse (≤ 10515) never increases the slot count. -/
theorem half_slots_lower : 9500≤gateSlots (Q6EndpointCell.half false base (base 2409)) := by
  decide +kernel

end ECDSAAdd.Entrant.JointInverse1588

namespace ECDSAAdd.Entrant.JointInverse1588

/-- Toffoli saving of the S2 (multiply) first body: the 1020-T G1 half window and the 0-T final
measured swap become the 517-T padded joint inverse. -/
def saving (divide : Bool) : Nat := if divide then 0 else 503

end ECDSAAdd.Entrant.JointInverse1588
