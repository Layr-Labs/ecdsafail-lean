import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Arithmetic.Reduction
import ECDSAAdd.Arithmetic.SignedHalf
import ECDSAAdd.Math.SkywalkRails

namespace ECDSAAdd.Arithmetic

/-- Signed interpretation of a physical little-endian word. -/
def signedRegValue (r : List Wire) (s : BasisState) : Int :=
  signedDecode r.length (regValue r s)

/-- The physical MSB supplies the exact two's-complement sign correction. -/
theorem signedRegValue_msb (lo : List Wire) (sign : Wire) (s : BasisState) :
    signedRegValue (lo++[sign]) s=(regValue (lo++[sign]) s:Int)-
      if s sign then ((2^(lo.length+1):Nat):Int) else 0 := by
  have hh := regValue_highBit lo sign s
  unfold signedRegValue signedDecode
  simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel]
  cases hs : s sign with
  | false =>
    have hb : regValue (lo++[sign]) s<2^lo.length := by
      have hn : ¬2^lo.length≤regValue (lo++[sign]) s := by
        intro h
        have ht := hh.mpr h
        rw [hs] at ht
        contradiction
      omega
    simp [hb]
  | true =>
    have hb : 2^lo.length≤regValue (lo++[sign]) s := hh.mp hs
    simp [Nat.not_lt.mpr hb]

/-- Negative signed value is equivalent to an asserted physical most significant bit. -/
theorem signedRegValue_neg_iff (lo : List Wire) (sign : Wire) (s : BasisState) :
    signedRegValue (lo++[sign]) s<0 ↔ s sign=true := by
  have hh := regValue_highBit lo sign s
  have hb := regValue_lt (lo++[sign]) s
  simp only [List.length_append,List.length_singleton] at hb
  unfold signedRegValue signedDecode
  simp only [List.length_append,List.length_singleton,Nat.add_sub_cancel]
  cases hs : s sign with
  | false =>
    have hlow : regValue (lo++[sign]) s<2^lo.length := by
      have hn : ¬2^lo.length≤regValue (lo++[sign]) s := by
        intro h
        have ht := hh.mpr h
        rw [hs] at ht
        contradiction
      omega
    rw [if_pos hlow]
    simp
  | true =>
    have hhigh : 2^lo.length≤regValue (lo++[sign]) s := hh.mp hs
    rw [if_neg (Nat.not_lt.mpr hhigh)]
    have hi : (regValue (lo++[sign]) s:Int)<((2^(lo.length+1):Nat):Int) :=
      Int.ofNat_lt.mpr hb
    have hneg : (regValue (lo++[sign]) s:Int)-((2^(lo.length+1):Nat):Int)<0 := by
      omega
    simpa using hneg

/-- Boolean arithmetic sign used by SkywalkRails is exactly the physical MSB. -/
theorem signedRegValue_sign (lo : List Wire) (sign : Wire) (s : BasisState) :
    s sign=SkywalkRails.neg (signedRegValue (lo++[sign]) s) := by
  have hh := signedRegValue_neg_iff lo sign s
  cases hs : s sign with
  | false =>
    have hn : ¬signedRegValue (lo++[sign]) s<0 := by
      intro h
      have ht := hh.mp h
      rw [hs] at ht
      contradiction
    simp [SkywalkRails.neg,hn]
  | true =>
    have hn : signedRegValue (lo++[sign]) s<0 := hh.mpr hs
    simp [SkywalkRails.neg,hn]

/-- Connect the same register convention to the independent Clifford half helper. -/
theorem signedRegValue_halfDecode (lo : List Wire) (sign : Wire) (s : BasisState) :
    signedRegValue (lo++[sign]) s=
      signedHalfDecode (lo.length+1) (s sign) (regValue (lo++[sign]) s) := by
  rw [signedRegValue_msb]
  simp only [signedHalfDecode,Nat.cast_pow,Nat.cast_ofNat]

/-- Subtracting a whole even word modulus cannot change parity. -/
theorem signedDecode_mod_two (w X : Nat) (hw : 0<w) :
    signedDecode w X%2=(X:Int)%2 := by
  have hp : 2^w=2*2^(w-1) := by
    calc
      2^w = 2^((w-1)+1) := by congr 1; omega
      _ = 2^(w-1)*2 := pow_succ _ _
      _ = 2*2^(w-1) := Nat.mul_comm _ _
  have hc := congrArg (fun a : Nat => (a:Int)) hp
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hc
  have hm : ((2^w:Nat):Int)%2=0 := by rw [hc]; omega
  unfold signedDecode
  split_ifs with h
  · rfl
  · rw [Int.sub_emod,hm]
    simp

/-- Exact logical evenness forces the physical low bit to zero before relabelled half. -/
theorem signedRegValue_even_iff (low : Wire) (tail : List Wire) (s : BasisState) :
    signedRegValue (low::tail) s%2=0 ↔ s low=false := by
  unfold signedRegValue
  rw [signedDecode_mod_two (low::tail).length (regValue (low::tail) s) (by simp)]
  cases hs : s low <;> simp [regValue,hs]

private theorem signed_int_spec_of_raw (q : Wire) (x y carry : List Wire) (p : Program)
    (hx : x.length=y.length) (hc : carry.length+1=y.length)
    (Q D : Bool) (A B : Int)
    (hlo : -((2^(y.length-1):Nat):Int)≤signedIntegerValue D A B)
    (hhi : signedIntegerValue D A B<((2^(y.length-1):Nat):Int))
    (hraw : ∀ X Y : Nat,
      {{ q=Q,x=X,y=Y,carry=0 }} p
      {{ q=Q,x=X,y=(signedWordValue y.length D X Y),carry=0 }}) :
    Triple (fun s => s q=Q ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0)
      p (fun s => s q=Q ∧ signedRegValue x s=A ∧
        signedRegValue y s=signedIntegerValue D A B ∧ regValue carry s=0) := by
  intro s m hin
  let X := regValue x s.basis
  let Y := regValue y s.basis
  have hX : X<2^y.length := by simpa only [X,hx] using regValue_lt x s.basis
  have hA : signedDecode y.length X=A := by
    have hh := hin.2.1
    change signedDecode x.length X=A at hh
    rw [hx] at hh
    exact hh
  have hB : signedDecode y.length Y=B := hin.2.2.1
  obtain ⟨hp,ho⟩ := hraw X Y s m ⟨⟨⟨hin.1,rfl⟩,rfl⟩,hin.2.2.2⟩
  have hw : 0<y.length := by omega
  have hv := signedWordValue_lift y.length D X Y hw hX
    (by rw [hA,hB]; exact hlo) (by rw [hA,hB]; exact hhi)
  rw [hA,hB] at hv
  refine ⟨hp,ho.1.1.1,?_,?_,ho.2⟩
  · unfold signedRegValue
    rw [ho.1.1.2]
    exact hin.2.1
  · unfold signedRegValue
    rw [ho.1.2]
    exact hv

/-- Native signed-add gate lifts to the exact unbounded integer rail operation,
provided the separately proved output bound fits the chosen signed word. -/
theorem signedAdd_int_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (A B : Int)
    (hlo : -((2^(y.length-1):Nat):Int)≤signedIntegerValue Q A B)
    (hhi : signedIntegerValue Q A B<((2^(y.length-1):Nat):Int)) :
    Triple (fun s => s q=Q ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0)
      (signedAdd q x y carry) (fun s => s q=Q ∧ signedRegValue x s=A ∧
        signedRegValue y s=signedIntegerValue Q A B ∧ regValue carry s=0) :=
  signed_int_spec_of_raw q x y carry _ hx hc Q Q A B hlo hhi
    (fun X Y => signedAdd_spec q x y carry hn hx hc Q X Y)

/-- The inverse gate preserves the same physical control and reverses its signed direction. -/
theorem signedSub_int_spec (q : Wire) (x y carry : List Wire)
    (hn : (q::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (Q : Bool) (A B : Int)
    (hlo : -((2^(y.length-1):Nat):Int)≤signedIntegerValue (!Q) A B)
    (hhi : signedIntegerValue (!Q) A B<((2^(y.length-1):Nat):Int)) :
    Triple (fun s => s q=Q ∧ signedRegValue x s=A ∧ signedRegValue y s=B ∧ regValue carry s=0)
      (signedSub q x y carry) (fun s => s q=Q ∧ signedRegValue x s=A ∧
        signedRegValue y s=signedIntegerValue (!Q) A B ∧ regValue carry s=0) :=
  signed_int_spec_of_raw q x y carry _ hx hc Q (!Q) A B hlo hhi
    (fun X Y => signedSub_spec q x y carry hn hx hc Q X Y)

/-- Physical Clifford half and its relabelled view implement the exact signed
integer half. The physical low-bit premise follows from logical evenness. -/
theorem skywalkSignedHalf_int (low sign : Wire) (mid : List Wire)
    (hsl : sign≠low) (hlo : low∉mid++[sign]) (s : State) (m : List Bool)
    (he : signedRegValue (low::(mid++[sign])) s.basis%2=0) :
    signedRegValue (skywalkHalfView low (mid++[sign]))
      (run (skywalkSignedHalf sign low) m s).basis =
      signedRegValue (low::(mid++[sign])) s.basis/2 := by
  let tail := mid++[sign]
  let t := run (skywalkSignedHalf sign low) m s
  have hbit : s.basis low=false := (signedRegValue_even_iff low tail s.basis).mp he
  have hsign : t.basis low=s.basis sign := by
    change (run (skywalkSignedHalf sign low) m s).basis low=s.basis sign
    rw [skywalkSignedHalf_correct sign low hsl s m hbit]
    simp [writeBit]
  have hraw : regValue (low::tail) s.basis=2*regValue tail s.basis := by
    simp [regValue,hbit]
  have hwidth : (low::mid).length+1=tail.length+1 := by simp [tail]
  have hin := signedRegValue_halfDecode (low::mid) sign s.basis
  change signedRegValue (low::tail) s.basis=
    signedHalfDecode ((low::mid).length+1) (s.basis sign) (regValue (low::tail) s.basis) at hin
  rw [hwidth,hraw] at hin
  have hout := signedRegValue_halfDecode tail low t.basis
  have hv := skywalkSignedHalf_value sign low tail hsl hlo s m hbit
  change regValue (tail++[low]) t.basis=
    regValue tail s.basis+2^tail.length*(s.basis sign).toNat at hv
  rw [hsign,hv,signedHalfDecode_half] at hout
  change signedRegValue (tail++[low]) t.basis=signedRegValue (low::tail) s.basis/2
  rw [hout,hin]

end ECDSAAdd.Arithmetic
