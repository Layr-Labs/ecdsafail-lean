import ECDSAAdd.Math.SignedSquare

namespace ECDSAAdd.Arithmetic

def signedDiagValue (X n : Nat) : Nat :=
  if n=0 then 0 else X+(2^(n-1)-1-X%2^(n-1))*2^n

theorem signedDiagValue_step (b : Bool) (Y k : Nat) (hk : 1≤k) (_hY : Y<2^k) :
    signedDiagValue (b.toNat+2*Y) (k+1)+2*Y=
      4*signedDiagValue Y k+(if b then 1 else 2^(k+1)) := by
  let H := 2^(k-1)
  let M := 2^k
  have hH : 0<H := by positivity
  have hm : M=2*H := by
    have he : (k-1)+1=k := by omega
    calc
      M = 2^k := rfl
      _ = 2^((k-1)+1) := congrArg (2^·) he.symm
      _ = 2^(k-1)*2 := by rw [Nat.pow_succ]
      _ = 2*H := by simp [H,Nat.mul_comm]
  have hr : Y%H<H := Nat.mod_lt Y hH
  have split : Y%H+H*(Y/H)=Y := Nat.mod_add_div Y H
  have hb : b.toNat≤1 := by cases b <;> simp
  have low : b.toNat+2*(Y%H)<M := by rw [hm]; omega
  have decomp : b.toNat+2*Y=(b.toNat+2*(Y%H))+M*(Y/H) := by
    calc
      b.toNat+2*Y = b.toNat+2*(Y%H+H*(Y/H)) :=
        congrArg (fun z => b.toNat+2*z) split.symm
      _ = (b.toNat+2*(Y%H))+M*(Y/H) := by rw [hm]; ring
  have xmod : (b.toNat+2*Y)%M=b.toNat+2*(Y%H) := by
    rw [decomp,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt low]
  have pk : 2^(k+1)=2*M := by rw [Nat.pow_succ]; simp [M,Nat.mul_comm]
  have hkn : k≠0 := by omega
  have hks : k+1≠0 := by omega
  simp only [signedDiagValue,hkn,hks,if_false]
  rw [show k+1-1=k by omega]
  change (b.toNat+2*Y)+(M-1-(b.toNat+2*Y)%M)*2^(k+1)+2*Y=
    4*(Y+(H-1-Y%H)*M)+(if b then 1 else 2^(k+1))
  cases b
  · simp only [Bool.toNat_false,Nat.zero_add,Bool.false_eq_true,if_false] at xmod ⊢
    rw [xmod,pk]
    have hs1 : (M-1-2*(Y%H))+(2*(Y%H)+1)=M := by rw [hm]; omega
    have hs2 : (H-1-Y%H)+(Y%H+1)=H := by omega
    have hab : M-1-2*(Y%H)=2*(H-1-Y%H)+1 := by rw [hm]; omega
    rw [hab]
    ring
  · simp only [Bool.toNat_true,if_true] at xmod ⊢
    rw [xmod,pk]
    have hs1 : (M-1-(1+2*(Y%H)))+(2*(Y%H)+2)=M := by rw [hm]; omega
    have hs2 : (H-1-Y%H)+(Y%H+1)=H := by omega
    nlinarith [congrArg (fun z => z*(2*M)) hs1,
      congrArg (fun z => 4*z*M) hs2]

def signedRawValue : List Wire → BasisState → Nat
  | [], _ => 0
  | c::[], base => 2*(base c).toNat
  | c::d::tail, base =>
      2*signedDeltaValue c (d::tail) base+4*signedRawValue (d::tail) base

def signedTopTerm : List Wire → BasisState → Nat
  | [], _ => 0
  | c::[], base => 2*(base c).toNat
  | _::d::tail, base => 4*signedTopTerm (d::tail) base

theorem signedTopTerm_congr (xs : List Wire) (s t : BasisState)
    (h : ∀q∈xs,s q=t q) : signedTopTerm xs s=signedTopTerm xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [signedTopTerm,h x (by simp)]
    | cons y ys =>
      simp only [signedTopTerm]
      rw [ih (fun q hq => h q (by simp [hq]))]

theorem signedRawValue_rows_top (xs : List Wire) (base : BasisState) :
    signedRawValue xs base=signedRowsValue xs base+signedTopTerm xs base := by
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    cases xs with
    | nil => simp [signedRawValue,signedRowsValue,signedTopTerm]
    | cons d tail =>
      simp only [signedRawValue,signedRowsValue,signedTopTerm]
      rw [ih]
      omega

theorem signedTopTerm_bound (xs : List Wire) (base : BasisState) (hn : 1≤xs.length) :
    signedTopTerm xs base≤2^(2*xs.length-1) := by
  induction xs with
  | nil => simp at hn
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases h : base x <;> simp [signedTopTerm,h]
    | cons y ys =>
      let rest := y::ys
      have hi : signedTopTerm rest base≤2^(2*rest.length-1) := by
        simpa [rest] using ih (by simp)
      change 4*signedTopTerm rest base≤2^(2*(rest.length+1)-1)
      have hlen : 1≤rest.length := by simp [rest]
      have he : 2*(rest.length+1)-1=(2*rest.length-1)+2 := by omega
      rw [he,Nat.pow_add]
      norm_num
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left 4 hi

theorem signedRawValue_bound (xs : List Wire) (base : BasisState) (hn : 1≤xs.length) :
    signedRawValue xs base<2^(2*xs.length) := by
  rw [signedRawValue_rows_top]
  have hr := signedRowsValue_bound xs base hn
  have ht := signedTopTerm_bound xs base hn
  have hp : 2^xs.length≤2^(2*xs.length-1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hs : 0<2^xs.length := Nat.two_pow_pos _
  have he : 2*xs.length=(2*xs.length-1)+1 := by omega
  rw [he,Nat.pow_succ]
  omega

theorem signedRawValue_correct (xs : List Wire) (base : BasisState) (hn : xs≠[]) :
    signedRawValue xs base=(regValue xs base)^2+
      signedDiagValue (regValue xs base) xs.length := by
  induction xs with
  | nil => contradiction
  | cons c xs ih =>
    cases xs with
    | nil =>
      cases hc : base c <;> simp [signedRawValue,signedDiagValue,regValue,hc]
    | cons d tail =>
      let rest := d::tail
      have hi := ih (by simp)
      have hk : 1≤rest.length := by simp [rest]
      have hY := regValue_lt rest base
      have step := signedDiagValue_step (base c) (regValue rest base) rest.length hk hY
      have rval : regValue (c::rest) base=(base c).toNat+2*regValue rest base := by
        change (if base c then 1 else 0)+2*regValue rest base=_
        cases base c <;> rfl
      cases hb : base c
      · have st : signedDiagValue (2*regValue rest base) (rest.length+1)+
            2*regValue rest base=
            4*signedDiagValue (regValue rest base) rest.length+2^(rest.length+1) := by
          simpa [hb] using step
        simp only [signedRawValue,signedDeltaValue,hb,Bool.false_eq_true,if_false]
        rw [rval,hb]
        simp only [Bool.toNat_false,Nat.zero_add,List.length_cons]
        change 2*(2^(d::tail).length-regValue (d::tail) base)+4*signedRawValue (d::tail) base=
          (2*regValue (d::tail) base)^2+
            signedDiagValue (2*regValue (d::tail) base) ((d::tail).length+1)
        rw [hi]
        rw [Nat.pow_succ] at st
        have hsub : (2^(d::tail).length-regValue (d::tail) base)+
            regValue (d::tail) base=2^(d::tail).length :=
          Nat.sub_add_cancel (Nat.le_of_lt (regValue_lt (d::tail) base))
        nlinarith
      · have st : signedDiagValue (1+2*regValue rest base) (rest.length+1)+
            2*regValue rest base=
            4*signedDiagValue (regValue rest base) rest.length+1 := by
          simpa [hb] using step
        simp only [signedRawValue,signedDeltaValue,hb,if_true]
        rw [rval,hb]
        simp only [Bool.toNat_true,List.length_cons]
        change 2*(regValue (d::tail) base+1)+4*signedRawValue (d::tail) base=
          (1+2*regValue (d::tail) base)^2+
            signedDiagValue (1+2*regValue (d::tail) base) ((d::tail).length+1)
        rw [hi]
        nlinarith

end ECDSAAdd.Arithmetic
