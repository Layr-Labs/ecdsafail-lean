import ECDSAAdd.Submission.Entrant.FrontierEntryErase

set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField Secp256k1

theorem half_encoding (Y : Int) (hy : Centered Y) :
    encodeWord 256 Y=(originalParity Y).toNat+2*encodeWord 255 (Y/2) := by
  have h := constants
  have Yb : -((2^256:Nat):Int)≤Y ∧ Y<((2^256:Nat):Int) := by
    unfold Centered at hy
    norm_num only [Nat.reducePow] at h ⊢
    omega
  have Hb : -((2^255:Nat):Int)≤Y/2 ∧ Y/2<((2^255:Nat):Int) := by
    unfold Centered at hy
    norm_num only [Nat.reducePow] at h ⊢
    omega
  have a := BalancedFold.encode_shift 256 Y Yb
  have b := BalancedFold.encode_shift 255 (Y/2) Hb
  have p := originalParity_value Y
  have neg : Y/2<0 ↔ Y<0 := by omega
  simp only [neg] at b
  by_cases n : Y<0 <;> simp only [n,if_true,if_false] at a b
  all_goals
    cases pv : originalParity Y <;> simp only [pv,Bool.false_eq_true,if_true,if_false,
      Bool.toNat_false,Bool.toNat_true] at p ⊢ <;> norm_num only [Nat.reducePow] at a b <;> omega

theorem encode_add (n : Nat) (X Y : Int) :
    (encodeWord n X+encodeWord n Y)%2^n=encodeWord n (X+Y) := by
  have cast : (((encodeWord n X+encodeWord n Y)%2^n:Nat):Int)=
      (encodeWord n (X+Y):Int) := by
    push_cast
    simp only [encodeWord_cast,Nat.cast_pow,Nat.cast_ofNat]
    exact (Int.add_emod X Y (2^n)).symm
  exact_mod_cast cast

theorem add_complement (U : Bool) (K C : Int) :
    (encodeWord 256 C+(if U then 2^256-1-encodeWord 256 K else encodeWord 256 K)+U.toNat)%2^256=
      encodeWord 256 (signedY U K+C) := by
  cases U
  · simpa [signedY,Int.add_comm] using encode_add 256 C K
  · have kb := encodeWord_bound 256 K
    have c := encodeWord_cast 256 C
    have k := encodeWord_cast 256 K
    have out := encodeWord_cast 256 (-K+C)
    have casts : (((encodeWord 256 C+(2^256-1-encodeWord 256 K)+1)%2^256:Nat):Int)=
        (encodeWord 256 (-K+C):Int) := by
      rw [Int.natCast_emod,Int.natCast_add,Int.natCast_add,
        Int.natCast_sub (by omega),Int.natCast_sub (by norm_num)]
      norm_num only [Nat.reducePow,Int.natCast_pow,Int.natCast_one] at kb c k out ⊢
      omega
    simpa only [Bool.toNat_true,signedY,if_true] using (show
      (encodeWord 256 C+(2^256-1-encodeWord 256 K)+1)%2^256=encodeWord 256 (-K+C) by exact_mod_cast casts)

theorem folded_encoding (U : Bool) (Y : Int) (hy : Centered Y) :
    (EntryHalf5.virtualSource (originalParity Y) (negative Y) U+
      (if U then 2^256-1-encodeWord 256 (Y/2) else encodeWord 256 (Y/2))+U.toNat)%2^256=
      encodeWord 256 (halfResult (signedY U Y)) := by
  rw [EntryHalf5.virtualSource_value,add_complement,EntryHalf5.unary_half_formula U Y hy]
  cases U <;> simp [signedY]

end ECDSAAdd.Entrant.EntryRetained5
