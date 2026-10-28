import ECDSAAdd.Arithmetic.CuccaroStreamedSquareC

set_option maxRecDepth 5000000
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

private theorem prime_pos : 0<SquareReduction.p := by
  norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]

theorem addModValue_cast (S O : Nat) :
    (addModValue S O : ZMod SquareReduction.p)=(S : ZMod SquareReduction.p)+O := by
  simp only [addModValue,ZMod.natCast_mod,Nat.cast_add]

theorem subModValue_cast (S O : Nat) :
    (subModValue S O : ZMod SquareReduction.p)=(O : ZMod SquareReduction.p)-S := by
  have hs := Nat.mod_lt S prime_pos
  simp only [subModValue,ZMod.natCast_mod]
  rw [Nat.cast_sub (by omega : S%SquareReduction.p≤O+SquareReduction.p)]
  simp only [Nat.cast_add,ZMod.natCast_self,add_zero,ZMod.natCast_mod]

theorem addCMinusOneValue_cast (H O : Nat) :
    (addCMinusOneValue H O : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)+(SquareReduction.c-1)*(H : ZMod SquareReduction.p) := by
  simp only [addCMinusOneValue,addModValue_cast,subModValue_cast,Nat.cast_mul]
  norm_num [SquareReduction.c]
  ring

theorem subCMinusOneValue_cast (H O : Nat) :
    (subCMinusOneValue H O : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)-(SquareReduction.c-1)*(H : ZMod SquareReduction.p) := by
  simp only [subCMinusOneValue,addModValue_cast,subModValue_cast,Nat.cast_mul]
  norm_num [SquareReduction.c]
  ring

theorem radix_cast : (2^256 : ZMod SquareReduction.p)=SquareReduction.c := by
  have hn : 2^256=SquareReduction.p+SquareReduction.c := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have h := congrArg (fun n : Nat => (n : ZMod SquareReduction.p)) hn
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add,ZMod.natCast_self,zero_add] using h

theorem addRotateProductValue_cast (P O : Nat) (hb : P<2^256) :
    (addRotateProductValue P O false : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)+(P : ZMod SquareReduction.p)*2^128 := by
  have hhigh : P/2^128<2^128 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0<2^128)).mpr
    simpa only [←Nat.pow_add,show 128+128=256 by omega] using hb
  simp only [addRotateProductValue,addRotate128Value,Bool.false_eq_true,if_false,
    addCMinusOneValue_cast,addModValue_cast,Nat.mod_eq_of_lt hhigh]
  have split := congrArg (fun n : Nat => (n : ZMod SquareReduction.p))
    (Nat.mod_add_div P (2^128))
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at split ⊢
  have radix : ((2 : ZMod SquareReduction.p)^128)^2=SquareReduction.c := by
    rw [←pow_mul]
    exact radix_cast
  rw [←split,←radix]
  ring

theorem subRotateProductValue_cast (P O : Nat) :
    (subRotateProductValue P O true : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)-(P : ZMod SquareReduction.p)*2^128 := by
  simp only [subRotateProductValue,subRotate128Value,if_true,
    subModValue_cast,subCMinusOneValue_cast,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat]
  have split := congrArg (fun n : Nat => (n : ZMod SquareReduction.p))
    (Nat.mod_add_div P (2^128))
  have highSplit := congrArg (fun n : Nat => (n : ZMod SquareReduction.p))
    (Nat.mod_add_div (P/2^128) (2^128))
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at split highSplit
  have divDiv : (P/2^128)/2^128=P/2^256 := by
    rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  rw [divDiv] at highSplit
  have radix : ((2 : ZMod SquareReduction.p)^128)^2=SquareReduction.c := by
    rw [←pow_mul]
    exact radix_cast
  rw [←radix,←split]
  linear_combination -highSplit

theorem shiftedFull_cast (P j : Nat) (hj : j≤256) (hb : P<2^256) :
    (rotatedFullValue P j : ZMod SquareReduction.p)+
      (SquareReduction.c-1)*(highFullValue P j : ZMod SquareReduction.p)=
      (P : ZMod SquareReduction.p)*2^j := by
  have hpow : 2^(256-j)*2^j=(2^256 : Nat) := by
    rw [←Nat.pow_add,Nat.sub_add_cancel hj]
  have split := Nat.mod_add_div (P%2^256) (2^(256-j))
  have ident : rotatedFullValue P j+2^256*highFullValue P j=
      (P%2^256)*2^j+highFullValue P j := by
    unfold rotatedFullValue highFullValue
    have expanded := congrArg (fun n => n*2^j) split
    dsimp only at expanded
    rw [Nat.add_mul] at expanded
    have term : (2^(256-j)*(P%2^256/2^(256-j)))*2^j=
        2^256*(P%2^256/2^(256-j)) := by
      calc
        _ = (2^(256-j)*2^j)*(P%2^256/2^(256-j)) := by ring
        _ = _ := by rw [hpow]
    rw [term] at expanded
    nlinarith only [expanded]
  have castIdent := congrArg (fun n : Nat => (n : ZMod SquareReduction.p)) ident
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at castIdent
  have modCast : ((P%2^256 : Nat) : ZMod SquareReduction.p)=P := by
    rw [Nat.mod_eq_of_lt hb]
  rw [radix_cast,modCast] at castIdent
  linear_combination castIdent

theorem subTimesProductValue_cast (P O : Nat) (hb : P<2^256) :
    (subTimesProductValue P O : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)-SquareReduction.c*(P : ZMod SquareReduction.p) := by
  have h4 := shiftedFull_cast P 4 (by omega) hb
  have h6 := shiftedFull_cast P 6 (by omega) hb
  have h10 := shiftedFull_cast P 10 (by omega) hb
  have h32 := shiftedFull_cast P 32 (by omega) hb
  simp only [subTimesProductValue,subTimesCValue,subShiftFullValue,
    addShiftFullValue,addCMinusOneValue_cast,subCMinusOneValue_cast,
    addModValue_cast,subModValue_cast,Nat.mod_eq_of_lt hb]
  have hn : (SquareReduction.c : ZMod SquareReduction.p)=
      1+2^4-2^6+2^10+2^32 := by norm_num [SquareReduction.c]
  linear_combination -h4+h6-h10-h32+(P : ZMod SquareReduction.p)*hn

def streamedSquareValue (A B O : Nat) : Nat :=
  branchCMiddleValue (A+B)
    (subTimesProductValue (B^2)
      (addRotateProductValue (B^2) (branchAValue A O) false))

theorem streamedSquareValue_cast (A B O : Nat) (ha : A<2^128) (hb : B<2^128) :
    (streamedSquareValue A B O : ZMod SquareReduction.p)=
      (O : ZMod SquareReduction.p)-(A+2^128*B : Nat)^2 := by
  have ha2 : A^2<2^256 := by
    simpa only [show 2*128=256 by omega] using square_bound A 128 ha
  have hb2 : B^2<2^256 := by
    simpa only [show 2*128=256 by omega] using square_bound B 128 hb
  simp only [streamedSquareValue,branchCMiddleValue,branchAValue,
    subRotateProductValue_cast,subTimesProductValue_cast _ _ hb2,
    addRotateProductValue_cast _ _ hb2,addRotateProductValue_cast _ _ ha2,
    subModValue_cast,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have radix : ((2 : ZMod SquareReduction.p)^128)^2=SquareReduction.c := by
    rw [←pow_mul]
    exact radix_cast
  rw [←radix]
  ring

theorem streamedSquareValue_lt (A B O : Nat) :
    streamedSquareValue A B O<SquareReduction.p := by
  unfold streamedSquareValue branchCMiddleValue subRotateProductValue
    subRotate128Value
  simp only [if_true]
  exact Nat.mod_lt _ prime_pos

theorem streamedSquareValue_exact (A B O : Nat) (ha : A<2^128) (hb : B<2^128) :
    streamedSquareValue A B O=
      (O+SquareReduction.p-((A+2^128*B)^2)%SquareReduction.p)%SquareReduction.p := by
  have cast := streamedSquareValue_cast A B O ha hb
  have target := subModValue_cast ((A+2^128*B)^2) O
  simp only [Nat.cast_pow] at target
  have hv := congrArg ZMod.val (cast.trans target.symm)
  rw [ZMod.val_natCast_of_lt (streamedSquareValue_lt A B O),
    ZMod.val_natCast_of_lt (show subModValue ((A+2^128*B)^2) O<SquareReduction.p
      from Nat.mod_lt _ prime_pos)] at hv
  exact hv

end ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
