import ECDSAAdd.Arithmetic.ConstantBorrow
import ECDSAAdd.Framework.WireRename
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.ZeroSeededConstantCompare

def prepare (x c : Wire) : Program := [.X c,.CX x c]
def release (x c : Wire) : Program := [.CX x c,.X c]

theorem prepare_run (x c : Wire) (hxc : x≠c) (s : State) (m : List Bool) :
    run (prepare x c) m s=
      ⟨s.phase,writeBit s.basis c (s.basis c ^^ !s.basis x)⟩ := by
  simp only [prepare,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=c
  · subst q
    simp only [writeBit,Function.update_self,Function.update_of_ne hxc]
    cases s.basis c <;> cases s.basis x <;> rfl
  · simp [writeBit,hq]

theorem release_run (x c : Wire) (_hxc : x≠c) (s : State) (m : List Bool) :
    run (release x c) m s=
      ⟨s.phase,writeBit s.basis c (s.basis c ^^ !s.basis x)⟩ := by
  simp only [release,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=c
  · subst q
    simp only [writeBit,Function.update_self]
    cases s.basis c <;> cases s.basis x <;> rfl
  · simp [writeBit,hq]

theorem prepare_equiv (x cin c : Wire) (hn : [x,cin,c].Nodup)
    (s : State) (m : List Bool) (hz : s.basis cin=false) :
    run (prepare x c) m s=run (constantBorrow true x cin c) m s := by
  have hxc : x≠c := by
    intro e
    exact (List.nodup_cons.mp hn).1 (by simp [e])
  rw [prepare_run x c hxc,constantBorrow_correct true x cin c hn,hz]
  cases s.basis x <;> rfl

theorem release_equiv (x cin c : Wire) (hn : [x,cin,c].Nodup)
    (s : State) (m n : List Bool) (hz : s.basis cin=false)
    (hc : s.basis c= !s.basis x) :
    run (release x c) m s=run (constantBorrowErase true x cin c) n s := by
  have hxc : x≠c := by
    intro e
    exact (List.nodup_cons.mp hn).1 (by simp [e])
  have known : s.basis c=carryBit (!s.basis x) true (s.basis cin) := by
    rw [hz,hc]
    cases s.basis x <;> rfl
  rw [release_run x c hxc,constantBorrowErase_correct true x cin c hn s n known,hc]
  cases s.basis x <;> rfl

def program : List Wire → List Wire → Wire → Wire → Program
  | x::x'::xs,c::cs,_,target =>
      prepare x c++compareConstantLt (x'::xs) cs c target 0++release x c
  | [x],_,_,target => prepare x target
  | _,_,_,_ => []

theorem counts (xs carry : List Wire) (cin target : Wire)
    (hc : carry.length+1=xs.length) :
    toffoliCount (program xs carry cin target)=xs.length-1 ∧
    measurementCount (program xs carry cin target)=xs.length-2 := by
  cases xs with
  | nil => simp at hc
  | cons x xs =>
    cases xs with
    | nil => simp [program,prepare,toffoliCount,measurementCount]
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have h := compareConstantLt_counts (x'::xs) cs c target 0 (by simpa using hc)
        simp only [program,toffoliCount_append,measurementCount_append,h.1,h.2]
        simp [prepare,release,toffoliCount,measurementCount]

theorem equiv (xs carry : List Wire) (cin target : Wire)
    (hn : (target::cin::(xs++carry)).Nodup)
    (hc : carry.length+1=xs.length) (s : State) (m : List Bool)
    (hz : s.basis cin=false) (hw : ∀q∈carry,s.basis q=false) :
    run (program xs carry cin target) m s=
      run (compareConstantLt xs carry cin target 1) m s := by
  have cnt := List.nodup_iff_count.mp hn
  cases xs with
  | nil => simp at hc
  | cons x xs =>
    cases xs with
    | nil =>
      have nd : [x,cin,target].Nodup := by
        apply List.nodup_iff_count.mpr
        intro q
        have h := cnt q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
      simpa only [program,compareConstantLt,Nat.one_mod,decide_true] using
        prepare_equiv x cin target nd s m hz
    | cons x' xs =>
      cases carry with
      | nil => simp at hc
      | cons c cs =>
        have nd : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have tailND : (target::c::((x'::xs)++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have xc : x≠c := by
          intro e
          exact (List.nodup_cons.mp nd).1 (by simp [e])
        have xt : x≠target := by
          intro e
          have h := cnt target
          simp only [e,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have ct : c≠target := by
          intro e
          have h := cnt target
          simp only [e,List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have ci : cin≠c := by simpa using (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
        have it : cin≠target := by
          intro e
          have h := cnt target
          simp only [e,List.count_cons,beq_self_eq_true,if_true] at h
          omega
        let u := run (prepare x c) m s
        have ue : u=⟨s.phase,writeBit s.basis c (!s.basis x)⟩ := by
          change run (prepare x c) m s=_
          simp only [prepare_run x c xc,hw c (by simp),Bool.false_xor]
        have uc : ∀q∈cs,u.basis q=false := by
          intro q hq
          have qc : q≠c := by
            intro e
            have h := cnt c
            simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
            have pos : 0<cs.count c := List.count_pos_iff.mpr (e ▸ hq)
            omega
          rw [ue]
          simpa [writeBit,qc] using hw q (by simp [hq])
        let t := run (compareConstantLt (x'::xs) cs c target 0) m u
        have tail := compareConstantLt_correct (x'::xs) cs c target 0 tailND
          (by simpa using hc) (by positivity) u m uc
        have tc : t.basis c= !t.basis x := by
          rw [tail.2.1 c ct,tail.2.1 x xt,ue]
          simp [writeBit,xc]
        have tz : t.basis cin=false := by
          rw [tail.2.1 cin it,ue]
          simp [writeBit,ci,hz]
        have finish := release_equiv x cin c nd t
          (m.drop (measurementCount (compareConstantLt (x'::xs) cs c target 0)))
          (m.drop (measurementCount (compareConstantLt (x'::xs) cs c target 0))) tz tc
        have prepM : measurementCount (prepare x c)=0 := rfl
        have oldM : measurementCount (constantBorrow true x cin c)=0 :=
          (constantBorrow_counts true x cin c).2.1
        have preAny (records : List Bool) : run (prepare x c) records s=u := rfl
        have oldAny (records : List Bool) : run (constantBorrow true x cin c) records s=u :=
          (prepare_equiv x cin c nd s records hz).symm.trans (preAny records)
        have ht : run (compareConstantLt (x'::xs) cs c target 0) m u=t := rfl
        simpa only [program,compareConstantLt,Nat.one_mod,
          show 1/2=0 from rfl,decide_true,run_append,run_take,
          measurementCount_append,prepM,oldM,Nat.zero_add,List.drop_zero,
          preAny,oldAny,ht] using finish

theorem equiv_records (xs carry : List Wire) (cin target : Wire)
    (hn : (target::cin::(xs++carry)).Nodup)
    (hc : carry.length+1=xs.length) (s : State) (m n : List Bool)
    (hz : s.basis cin=false) (hw : ∀q∈carry,s.basis q=false) :
    run (program xs carry cin target) m s=
      run (compareConstantLt xs carry cin target 1) n s := by
  rw [equiv xs carry cin target hn hc s m hz hw]
  have hk : 1<2^xs.length := by
    cases xs with
    | nil => simp at hc
    | cons x rest =>
      simp only [List.length_cons,Nat.pow_succ]
      have hp : 0<2^rest.length := by positivity
      omega
  have a := compareConstantLt_correct xs carry cin target 1 hn hc hk s m hw
  have b := compareConstantLt_correct xs carry cin target 1 hn hc hk s n hw
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases hq : q=target
    · subst q
      exact a.2.2.trans b.2.2.symm
    · exact (a.2.1 q hq).trans (b.2.1 q hq).symm

private theorem prepare_support (x cin c : Wire) :
    wires (prepare x c) ⊆ wires (constantBorrow true x cin c) := by
  intro q hq
  simp [prepare,constantBorrow,mappedMajority,wires,Instr.wires] at hq ⊢
  tauto

private theorem release_support (x cin c : Wire) :
    wires (release x c) ⊆ wires (constantBorrow true x cin c) := by
  intro q hq
  simp [release,constantBorrow,mappedMajority,wires,Instr.wires] at hq ⊢
  tauto

theorem support (xs carry : List Wire) (cin target : Wire) :
    wires (program xs carry cin target) ⊆
      wires (compareConstantLt xs carry cin target 1) := by
  cases xs with
  | nil => simp [program,compareConstantLt,wires]
  | cons x rest =>
    cases rest with
    | nil => exact prepare_support x cin target
    | cons x' rest =>
      cases carry with
      | nil => simp [program,compareConstantLt,wires]
      | cons c cs =>
        intro q hq
        have p := prepare_support x cin c
        have r := release_support x cin c
        simp only [program,compareConstantLt,Nat.one_mod,
          show 1/2=0 from rfl,decide_true,wires_append,Finset.mem_union] at hq ⊢
        have hp : q∈wires (prepare x c) → q∈wires (constantBorrow true x cin c) := fun h => p h
        have hr : q∈wires (release x c) → q∈wires (constantBorrow true x cin c) := fun h => r h
        tauto

end ECDSAAdd.Arithmetic.ZeroSeededConstantCompare
#print axioms ECDSAAdd.Arithmetic.ZeroSeededConstantCompare.equiv
#print axioms ECDSAAdd.Arithmetic.ZeroSeededConstantCompare.counts
#print axioms ECDSAAdd.Arithmetic.ZeroSeededConstantCompare.equiv_records
#print axioms ECDSAAdd.Arithmetic.ZeroSeededConstantCompare.support
