import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Baselines.SlotMapped

/-! A literal carry prefix with a controlled read and independent measured
carry cleanup. No literal register is allocated. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 150000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagonalCarry5
open Arithmetic RecordedQuantum Challenge

def value : List Bool→Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def literal : Nat→Nat→List Bool
  | 0,_ => []
  | n+1,k => decide (k%2=1)::literal n (k/2)

def bit (b : Bool) : MappedBit := {wire:=none,flip:=b}

def chain : List Bool→List Wire→List Wire→Wire→Wire→Wire→Program
  | b::bs,x::xs,c::cs,cin,ctl,target =>
      mappedMajority (bit b) x cin c++chain bs xs cs c ctl target++mappedEraseCarry (bit b) x cin c
  | [],[],[],cin,ctl,target => [.CCX ctl cin target]
  | _,_,_,_,_,_ => []

theorem literal_length (n k : Nat) : (literal n k).length=n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [literal,ih]

theorem literal_value (n k : Nat) (hk : k<2^n) : value (literal n k)=k := by
  induction n generalizing k with
  | zero =>
    have h : k=0 := by simpa using hk
    simp [literal,value,h]
  | succ n ih =>
    have hd : k/2<2^n := by rw [pow_succ] at hk; omega
    have sp := Nat.mod_add_div k 2
    have sm := Nat.mod_lt k (by decide : 0<2)
    rw [literal,value,ih _ hd]
    by_cases odd : k%2=1 <;> simp [odd] <;> omega

theorem counts (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length) :
    toffoliCount (chain bs xs cs cin ctl target)=bs.length+1 ∧
    measurementCount (chain bs xs cs cin ctl target)=bs.length := by
  induction bs generalizing xs cs cin with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    simp [chain,ex,ec,toffoliCount,measurementCount]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have rest := ih xs cs c (by simpa using hx) (by simpa using hc)
        have one := mappedBit_counts (bit b) x cin c
        simp only [chain,toffoliCount_append,measurementCount_append,one.1,one.2.1,
          one.2.2.1,one.2.2.2.1,rest.1,rest.2,List.length_cons]
        omega

private theorem threshold (b a c : Bool) (K X n : Nat) :
    (2^(n+1)≤a.toNat+2*X+(b.toNat+2*K)+c.toNat) ↔
      (2^n≤X+K+(carryBit b a c).toNat) := by
  rw [pow_succ]
  cases b <;> cases a <;> cases c <;> simp [carryBit] <;> omega

private theorem reg_cons (x : Wire) (xs : List Wire) (s : BasisState) :
    regValue (x::xs) s=(s x).toNat+2*regValue xs s := by
  cases h : s x <;> simp [regValue,h]

theorem correct (bs : List Bool) (xs cs : List Wire) (cin ctl target : Wire)
    (hn : (ctl::target::cin::(xs++cs)).Nodup)
    (hx : xs.length=bs.length) (hc : cs.length=bs.length)
    (s : State) (m : List Bool) (clean : ∀q∈cs,s.basis q=false) :
    (run (chain bs xs cs cin ctl target) m s).phase=s.phase ∧
    (∀q,q≠target → (run (chain bs xs cs cin ctl target) m s).basis q=s.basis q) ∧
    (run (chain bs xs cs cin ctl target) m s).basis target=
      (s.basis target ^^ (s.basis ctl && decide (2^bs.length≤regValue xs s.basis+value bs+(s.basis cin).toNat))) := by
  induction bs generalizing xs cs cin s m with
  | nil =>
    have ex : xs=[] := List.eq_nil_of_length_eq_zero hx
    have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
    subst xs cs
    have ot : ctl≠target := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have ct : cin≠target := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
    simp only [chain,run]
    refine ⟨trivial,?_,?_⟩
    · intro q hq; simp [writeBit,hq]
    · cases hi : s.basis cin <;> simp [writeBit,value,regValue,hi]
  | cons b bs ih =>
    cases xs with
    | nil => simp at hx
    | cons x xs =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have cnt := List.nodup_iff_count.mp hn
        have loc : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
          omega
        have restND : (ctl::target::c::(xs++cs)).Nodup := by
          apply List.nodup_iff_count.mpr
          intro q
          have h := cnt q
          simp only [List.count_cons,List.count_append] at h ⊢
          omega
        have tc : target≠c := by
          intro bad; have h := cnt c; subst target
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have tx : target≠x := by
          intro bad; have h := cnt x; subst target
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have ti : target≠cin := by
          intro bad; have h := cnt cin; subst target
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have oc : ctl≠c := by
          intro bad; have h := cnt c; subst ctl
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
          omega
        have cxs : c∉xs := by
          intro h; have a := cnt c; have p := List.count_pos_iff.mpr h
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at a
          omega
        have ccs : c∉cs := by
          intro h; have a := cnt c; have p := List.count_pos_iff.mpr h
          simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at a
          omega
        have xc : x≠c := fun h => (List.nodup_cons.mp loc).1 (by simp [h])
        have ic : cin≠c := fun h => (List.nodup_cons.mp (List.nodup_cons.mp loc).2).1 (by simp [h])
        let C := carryBit b (s.basis x) (s.basis cin)
        let u : State := ⟨s.phase,writeBit s.basis c C⟩
        have first (rec : List Bool) : run (mappedMajority (bit b) x cin c) rec s=u := by
          rw [mappedMajority_correct _ _ _ _ loc (by simp [bit])]
          simp [u,bit,MappedBit.value,clean c (by simp),C]
        have uf (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,hq]
        have clean' : ∀q∈cs,u.basis q=false := by
          intro q hq
          rw [uf q (fun h => ccs (h ▸ hq))]
          exact clean q (by simp [hq])
        have rest := ih xs cs c restND (by simpa using hx) (by simpa using hc) u m clean'
        let v := run (chain bs xs cs c ctl target) m u
        have vx : v.basis x=s.basis x := (rest.2.1 x tx.symm).trans (uf x xc)
        have vi : v.basis cin=s.basis cin := (rest.2.1 cin ti.symm).trans (uf cin ic)
        have vc : v.basis c=C := by rw [rest.2.1 c tc.symm]; simp [u,writeBit]
        have erase (rec : List Bool) : run (mappedEraseCarry (bit b) x cin c) rec v=
            ⟨v.phase,writeBit v.basis c false⟩ := by
          apply mappedEraseCarry_correct _ _ _ _ loc (by simp [bit])
          simp [bit,MappedBit.value,vx,vi,vc,C]
        have zeroM : measurementCount (mappedMajority (bit b) x cin c)=0 := (mappedBit_counts _ _ _ _).2.1
        simp only [chain,List.append_assoc,run_append,run_take,zeroM,List.take_zero,List.drop_zero]
        rw [first,erase]
        refine ⟨rest.1,?_,?_⟩
        · intro q hq
          by_cases qc : q=c
          · subst q; simp [writeBit,clean c (by simp)]
          · simp only [writeBit,Function.update_of_ne qc]
            exact (rest.2.1 q hq).trans (uf q qc)
        · simp only [writeBit,Function.update_of_ne tc]
          rw [rest.2.2]
          have word : regValue xs u.basis=regValue xs s.basis :=
            regValue_congr _ _ _ (fun q hq => uf q (fun h => cxs (h ▸ hq)))
          rw [uf target tc,uf ctl oc,word]
          have uc : u.basis c=C := by simp [u,writeBit]
          rw [uc]
          have hthr := threshold b (s.basis x) (s.basis cin) (value bs) (regValue xs s.basis) bs.length
          simp only [C,List.length_cons,value,reg_cons,hthr]

end ECDSAAdd.Entrant.DiagonalCarry5
