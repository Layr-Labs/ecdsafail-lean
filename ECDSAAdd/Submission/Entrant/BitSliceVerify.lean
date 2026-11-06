import ECDSAAdd.Submission.Entrant.Prelude
namespace ECDSAAdd.Entrant.BitSliceVerify
open ECDSAAdd Arithmetic
open MeasuredCodec5 (bitsOf bitRun corrSim)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 30000
set_option maxHeartbeats 400000
abbrev Cols := List Nat
def get (s : Cols) (q : Wire) : Nat := (s[q]?).getD 0
def step (mask : Nat) (i : Instr) (s : Cols) : Cols :=
  match i with
  | .X t => s.set t (get s t ^^^ mask)
  | .CX c t => s.set t (get s t ^^^ get s c)
  | .CCX a b t => s.set t (get s t ^^^ (get s a &&& get s b))
  | .measureX t _ _ => s.set t 0
def corr : List Correction → Cols → Nat
  | [], _ => 0
  | .Z t::cs, s => get s t ^^^ corr cs s
  | .CZ a b::cs, s => (get s a &&& get s b) ^^^ corr cs s
def safeStep (i : Instr) (s : Cols) : Bool :=
  match i with
  | .measureX t c0 c1 =>
      let z := s.set t 0
      (corr c0 z == 0) && (corr c1 z == get s t)
  | _ => true
def eval (mask : Nat) : Program → Cols → Bool × Cols
  | [], s => (true,s)
  | i::p,s => let rest:=eval mask p (step mask i s); (safeStep i s && rest.1, rest.2)


def Rel (s : Cols) (x row : Nat) : Prop := ∀ q : Wire, x.testBit q=(get s q).testBit row

theorem get_set (s : Cols) (t v : Nat) (ht : t<s.length) (q : Nat) :
    get (s.set t v) q=if q=t then v else get s q := by
  simp only [get,List.getElem?_set]
  by_cases h:q=t
  · subst q; simp [ht]
  · simp [h,Ne.symm h]

theorem flip_bit (x t q : Nat) :
    (x ^^^ 2^t).testBit q=if q=t then !x.testBit q else x.testBit q := by
  have h:=congrFun (MeasuredCodec5.bitsOf_flip x t) q
  by_cases hq:q=t
  · subst q; simpa [MeasuredCodec5.bitsOf,writeBit] using h
  · simpa [MeasuredCodec5.bitsOf,writeBit,Function.update_of_ne hq,hq] using h

theorem clear_bit (x t q : Nat) :
    (MeasuredCodec5.clear x t).testBit q=if q=t then false else x.testBit q := by
  have h:=congrFun (MeasuredCodec5.bitsOf_clear x t) q
  by_cases hq:q=t
  · subst q; simpa [MeasuredCodec5.bitsOf,writeBit] using h
  · simpa [MeasuredCodec5.bitsOf,writeBit,Function.update_of_ne hq,hq] using h

theorem rel_xor (s : Cols) (x row t v : Nat) (ht:t<s.length) (hr:Rel s x row) :
    Rel (s.set t (get s t ^^^ v)) (if v.testBit row then x ^^^ 2^t else x) row := by
  intro q
  rw [get_set s t _ ht q]
  by_cases hq:q=t
  · subst q
    cases hv:v.testBit row <;> simp [hv,Nat.testBit_xor,flip_bit,hr t]
  · cases hv:v.testBit row <;> simp [hv,hq,Ne.symm hq,flip_bit,hr q]

theorem rel_clear (s : Cols) (x row t : Nat) (ht:t<s.length) (hr:Rel s x row) :
    Rel (s.set t 0) (MeasuredCodec5.clear x t) row := by
  intro q
  rw [get_set s t _ ht q,clear_bit]
  by_cases hq:q=t <;> simp [hq,hr q]

def target : Instr→Nat
  | .X t => t
  | .CX _ t => t
  | .CCX _ _ t => t
  | .measureX t _ _ => t

theorem length_step (mask : Nat) (i : Instr) (s : Cols) : (step mask i s).length=s.length := by
  cases i <;> simp [step]

theorem step_rel (mask row : Nat) (hm:mask.testBit row=true) (i : Instr)
    (s : Cols) (x : Nat) (ht:target i<s.length) (hr:Rel s x row) :
    Rel (step mask i s) (MeasuredCodec5.bitStep i x) row := by
  cases i with
  | X t => simpa only [step,MeasuredCodec5.bitStep,hm,if_true] using rel_xor s x row t mask ht hr
  | CX a t =>
    simpa only [step,MeasuredCodec5.bitStep,hr a] using rel_xor s x row t (get s a) ht hr
  | CCX a b t =>
    simpa only [step,MeasuredCodec5.bitStep,Nat.testBit_and,hr a,hr b] using
      rel_xor s x row t (get s a &&& get s b) ht hr
  | measureX t c0 c1 => exact rel_clear s x row t ht hr



theorem corr_rel (cs : List Correction) (s : Cols) (x row : Nat) (hr:Rel s x row) :
    (corr cs s).testBit row=corrSim cs false x := by
  induction cs with
  | nil => simp [corr,MeasuredCodec5.corrSim]
  | cons i cs ih =>
    cases i with
    | Z t =>
      change (get s t ^^^ corr cs s).testBit row=corrSim cs (false ^^ x.testBit t) x
      rw [Nat.testBit_xor,MeasuredCodec5.corrSim_xor]
      simp only [Bool.false_xor,←hr t,ih]
    | CZ a b =>
      change ((get s a &&& get s b) ^^^ corr cs s).testBit row=
        corrSim cs (false ^^ (x.testBit a && x.testBit b)) x
      rw [Nat.testBit_xor,MeasuredCodec5.corrSim_xor,Nat.testBit_and]
      simp only [Bool.false_xor,←hr a,←hr b,ih]

theorem safeStep_sound (i : Instr) (s : Cols) (x row : Nat) (ht:target i<s.length)
    (hr:Rel s x row) (hs:safeStep i s=true) : MeasuredCodec5.safeStep i x=true := by
  cases i with
  | X t => rfl
  | CX a t => rfl
  | CCX a b t => rfl
  | measureX t c0 c1 =>
    have hc:=rel_clear s x row t ht hr
    have h0:=corr_rel c0 (s.set t 0) (MeasuredCodec5.clear x t) row hc
    have h1:=corr_rel c1 (s.set t 0) (MeasuredCodec5.clear x t) row hc
    have parts: corr c0 (s.set t 0)=0 ∧ corr c1 (s.set t 0)=get s t := by
      simpa only [safeStep,Bool.and_eq_true,beq_iff_eq] using hs
    rw [parts.1] at h0
    rw [parts.2] at h1
    simp only [MeasuredCodec5.safeStep,←h0,←h1,←hr t,Nat.zero_testBit,BEq.rfl,Bool.and_self]

theorem eval_sound (mask row : Nat) (hm:mask.testBit row=true) (P : Program)
    (s : Cols) (x : Nat) (bound:∀i∈P,target i<s.length) (hr:Rel s x row)
    (hs:(eval mask P s).1=true) :
    MeasuredCodec5.safe P x=true ∧ Rel (eval mask P s).2 (bitRun P x) row := by
  induction P generalizing s x with
  | nil => exact ⟨rfl,hr⟩
  | cons i P ih =>
    have parts:safeStep i s=true ∧ (eval mask P (step mask i s)).1=true := by
      simpa only [eval,Bool.and_eq_true] using hs
    have hi:=bound i (by simp)
    have hr':=step_rel mask row hm i s x hi hr
    have hb:∀j∈P,target j<(step mask i s).length := by
      intro j hj
      rw [length_step]
      exact bound j (by simp [hj])
    have rest:=ih (step mask i s) (MeasuredCodec5.bitStep i x) hb hr' parts.2
    refine ⟨?_,rest.2⟩
    simp only [MeasuredCodec5.safe,Bool.and_eq_true]
    exact ⟨safeStep_sound i s x row hi hr parts.1,rest.1⟩



def packBits : List Bool→Nat
  | [] => 0
  | b::bs => Nat.bit b (packBits bs)

theorem pack_testBit (bs : List Bool) (r : Nat) :
    (packBits bs).testBit r=(bs[r]?).getD false := by
  induction bs generalizing r with
  | nil => simp [packBits]
  | cons b bs ih =>
    cases r with
    | zero => cases b <;> simp [packBits,Nat.bit,Nat.testBit_zero]
    | succ r => simpa only [packBits,Nat.testBit_bit_succ,List.getElem?_cons_succ] using ih r

theorem pack_rows (xs : List Nat) (q r : Nat) :
    (packBits (xs.map (fun x=>x.testBit q))).testBit r=((xs[r]?).getD 0).testBit q := by
  rw [pack_testBit,List.getElem?_map]
  cases h:xs[r]? <;> simp



def physicalCheck : Instr→Bool
  | .X _ => true
  | .CX c t => decide (c≠t)
  | .CCX a b t => decide (a≠t ∧ b≠t)
  | .measureX _ _ _ => true

theorem physicalCheck_sound (i : Instr) (h:physicalCheck i=true) :
    RecordedQuantum.PhysicalInstr (.gate i) := by
  cases i <;> simp_all [physicalCheck,RecordedQuantum.PhysicalInstr,ProperGate]

theorem physical_of_check (P : Program) (h:P.all physicalCheck=true) : GatePhysical P := by
  intro i hi
  exact physicalCheck_sound i ((List.all_eq_true.mp h) i hi)

theorem wires_of_instructions (P : Program) (S : Finset Wire)
    (h:∀i∈P,i.wires⊆S) : wires P⊆S := by
  induction P with
  | nil => simp [wires]
  | cons i P ih =>
    rw [wires]
    exact Finset.union_subset (h i (by simp)) (ih (fun j hj=>h j (by simp [hj])))

def boundCheck (n : Nat) (i : Instr) : Bool := decide (i.wires⊆Finset.range n)

theorem support_of_check (P : Program) (n : Nat) (h:P.all (boundCheck n)=true) :
    wires P⊆Finset.range n := by
  apply wires_of_instructions
  intro i hi
  have z:boundCheck n i=true := (List.all_eq_true.mp h) i hi
  exact of_decide_eq_true z

end ECDSAAdd.Entrant.BitSliceVerify
