import ECDSAAdd.Arithmetic.BalancedCleanupOffsetChainProof
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

def value : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*value bs

def sumWords : List Bool → List Bool → Bool → List Bool
  | b::bs,y::ys,c => sumBit b y c::sumWords bs ys (carryBit b y c)
  | _,_,_ => []

def compareDecision : List Bool → List Bool → Bool → Bool
  | a::as,y::ys,c => compareDecision as ys (carryBit a (!y) c)
  | [],[],c => !c
  | _,_,_ => false

def borrowDecision : List Bool → List Bool → Bool → Bool
  | a::as,y::ys,c => borrowDecision as ys (carryBit (!a) y c)
  | [],[],c => c
  | _,_,_ => false

theorem carry_complement (A Y C : Bool) : carryBit A (!Y) C= !(carryBit (!A) Y (!C)) := by
  cases A <;> cases Y <;> cases C <;> rfl

theorem sumWords_length (ks ys : List Bool) (h : ks.length=ys.length) (C : Bool) :
    (sumWords ks ys C).length=ys.length := by
  induction ys generalizing ks C with
  | nil => have e := List.eq_nil_of_length_eq_zero (by simpa using h); subst ks; rfl
  | cons y ys ih =>
    cases ks with
    | nil => simp at h
    | cons k ks => simpa only [sumWords,List.length_cons] using congrArg Nat.succ (ih ks (by simpa using h) _)

theorem sumWords_value (ks ys : List Bool) (h : ks.length=ys.length) (C : Bool) :
    value (sumWords ks ys C)=(value ks+value ys+C.toNat)%2^ys.length := by
  induction ys generalizing ks C with
  | nil =>
    have e := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst ks
    simp [sumWords,value,Nat.mod_one]
  | cons y ys ih =>
    cases ks with
    | nil => simp at h
    | cons k ks =>
      rw [sumWords,value,ih ks (by simpa using h)]
      exact sum_value_step k y C (value ks) (value ys) ys.length

theorem decision_factor (ks xs ys : List Bool) (hk : ks.length=ys.length)
    (hx : xs.length=ys.length) (C D : Bool) :
    decision ks xs ys C D=compareDecision xs (sumWords ks ys C) D := by
  induction ys generalizing ks xs C D with
  | nil =>
    have e := List.eq_nil_of_length_eq_zero (by simpa using hk)
    have f := List.eq_nil_of_length_eq_zero (by simpa using hx)
    subst ks xs
    rfl
  | cons y ys ih =>
    cases ks with
    | nil => simp at hk
    | cons k ks =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        exact ih ks xs (by simpa using hk) (by simpa using hx) _ _

theorem compare_borrow (xs ys : List Bool) (h : xs.length=ys.length) (C : Bool) :
    compareDecision xs ys C=borrowDecision xs ys (!C) := by
  induction ys generalizing xs C with
  | nil => have e := List.eq_nil_of_length_eq_zero (by simpa using h); subst xs; rfl
  | cons y ys ih =>
    cases xs with
    | nil => simp at h
    | cons a xs =>
      simpa only [compareDecision,borrowDecision,carry_complement,Bool.not_not] using
        ih xs (by simpa using h) (carryBit a (!y) C)

theorem borrow_value (xs ys : List Bool) (h : xs.length=ys.length) (C : Bool) :
    borrowDecision xs ys C=decide (value xs<value ys+C.toNat) := by
  induction ys generalizing xs C with
  | nil =>
    have e := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst xs
    cases C <;> rfl
  | cons y ys ih =>
    cases xs with
    | nil => simp at h
    | cons a xs =>
      rw [borrowDecision,ih xs (by simpa using h)]
      apply decide_eq_decide.mpr
      exact (borrow_threshold a y C (value xs) (value ys)).symm

theorem decision_value (ks xs ys : List Bool) (hk : ks.length=ys.length)
    (hx : xs.length=ys.length) (C : Bool) :
    decision ks xs ys C true=decide (value xs<(value ks+value ys+C.toNat)%2^ys.length) := by
  rw [decision_factor ks xs ys hk hx C true,
    compare_borrow xs (sumWords ks ys C) (by rw [sumWords_length ks ys hk]; exact hx),
    borrow_value xs (sumWords ks ys C) (by rw [sumWords_length ks ys hk]; exact hx)]
  simp only [Bool.not_true,Bool.toNat_false,Nat.add_zero,sumWords_value ks ys hk C]

theorem mapped_value_map (bits : List MappedBit) (s : BasisState) :
    value (bits.map (fun b => b.value s))=mappedValue bits s := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [List.map_cons,value,mappedValue,ih]

theorem word_value_map (xs : List Wire) (s : BasisState) : value (xs.map s)=regValue xs s := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,value,regValue,List.foldr_cons,ih]
    cases s a <;> rfl

/-- Actual generic full-width offset comparator, exact on every input word.
No bounded compare window or assumed circuit oracle occurs in its premises.
The modulo is the physical n-bit offset sum, discharged by callers' range lemmas. -/
theorem chain_compare (bits : List MappedBit) (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hn : (target::cinC::cinB::(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false)
    (hi : s.basis cinB=true) :
    run (chain bits xs ys cs ds cinC cinB target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        decide (regValue xs s.basis<(mappedValue bits s.basis+regValue ys s.basis+
          (s.basis cinC).toNat)%2^ys.length))⟩ := by
  have h := chain_run bits xs ys cs ds cinC cinB target hn ha hb hx hc hd s m hcc hdd
  have v := decision_value (bits.map (fun b => b.value s.basis)) (xs.map s.basis)
    (ys.map s.basis) (by simpa using hb) (by simpa using hx) (s.basis cinC)
  rw [mapped_value_map,word_value_map,word_value_map,List.length_map] at v
  rw [hi,v] at h
  exact h

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.chain_compare
