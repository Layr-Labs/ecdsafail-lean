import ECDSAAdd.Arithmetic.NativeFirstDirectForwardProof
import ECDSAAdd.Arithmetic.NativeFirstPrefixMath
import ECDSAAdd.Arithmetic.CompactSkywalkTickOutputSpec

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
open NativeFirstPrefixMath
attribute [local irreducible] run forward

private theorem block_one (w : Nat → Wire) (a : Nat) :
    wireBlock w a 1=[w a] := by simp [wireBlock,List.range']
private theorem cons_value (h : Wire) (r : List Wire) (s : BasisState) :
    regValue (h::r) s=(s h).toNat+2*regValue r s := by
  cases hb : s h <;> simp [regValue,hb]

/-- Actual source parity follows from the original word equality. -/
theorem source_parity (w : Nat → Wire) (s : BasisState) (x : Nat)
    (hb : regValue (wireBlock w 770 258) s=x) :
    s (w 770)=oddBit (x : Int) := by
  have split : w 770::wireBlock w 771 257=wireBlock w 770 258 := by
    simpa [block_one] using wireBlock_append w 770 1 257
  rw [←split,cons_value] at hb
  cases he : s (w 770)
  · have hi : (x : Int)%2=0 := by simp only [he,Bool.toNat_false] at hb; omega
    simp [he,oddBit,hi]
  · have hi : (x : Int)%2≠0 := by simp only [he,Bool.toNat_true] at hb; omega
    simp [he,oddBit,hi]

/-- The positive magnitude is represented by the actual unsigned H word. -/
theorem h_nat_value (x : Nat) :
    hValue (p : Int) (x : Int)=
      ((x/2+(if oddBit (x : Int) then hConstant else 0) : Nat) : Int) := by
  cases he : oddBit (x : Int) <;>
    simp [hValue,hConstant,he,Int.natCast_ediv]

private theorem decode_positive (n V : Nat) (hv : V<2^(n-1)) (hm : V<2^n) :
    signedDecode n (V%2^n)=(V : Int) := by
  rw [Nat.mod_eq_of_lt hm,signedDecode,if_pos hv]
private theorem decode_negative (n U Q : Nat) (hq : Q≤2^n)
    (hlo : 2^(n-1)≤U+(2^n-Q)) (hhi : U+(2^n-Q)<2^n) :
    signedDecode n ((U+(2^n-Q))%2^n)=(U : Int)-(Q : Int) := by
  rw [Nat.mod_eq_of_lt hhi,signedDecode,if_neg (by omega)]
  have sum : ((2^n-Q : Nat) : Int)+(Q : Int)=((2^n : Nat) : Int) := by
    exact_mod_cast Nat.sub_add_cancel hq
  rw [Nat.cast_add]
  omega
private theorem odd_difference (X P Q : Nat) (hp : 2*Q+1=P)
    (ho : (X : Int)%2≠0) :
    ((X/2 : Nat) : Int)-(Q : Int)=((X : Int)-(P : Int))/2 := by
  have hi : 2*(Q : Int)+1=(P : Int) := by exact_mod_cast hp
  simp only [Int.natCast_ediv,Nat.cast_ofNat]
  omega

/-- Arithmetic is checked on abstract scalars before specializing the modulus. -/
theorem k_decode_value (x : Nat) (hx : x<p) :
    signedDecode 258 ((x/2+kConstant false (oddBit (x : Int)))%2^258)=
      kValue (p : Int) (x : Int) := by
  have pp : p<2^256 := by norm_num [p]
  have qp : 2*((p-1)/2)+1=p := by norm_num [p]
  by_cases he : (x : Int)%2=0
  · have flag : oddBit (x : Int)=false := by simp [oddBit,he]
    have kc : kConstant false false=p := rfl
    have kv : kValue (p : Int) (x : Int)=(p : Int)+(x : Int)/2 := by simp [kValue,flag]
    rw [flag,kc,decode_positive 258 (x/2+p) (by omega) (by omega),kv]
    simp only [Nat.cast_add,Int.natCast_ediv,Nat.cast_ofNat]
    omega
  · have flag : oddBit (x : Int)=true := by simp [oddBit,he]
    have kc : kConstant false true=2^258-(p-1)/2 := rfl
    have kv : kValue (p : Int) (x : Int)=((x : Int)-(p : Int))/2 := by simp [kValue,flag]
    rw [flag,kc,decode_negative 258 (x/2) ((p-1)/2) (by omega) (by omega) (by omega),kv]
    exact odd_difference x p ((p-1)/2) qp he

private theorem first_layout (w : Nat → Wire) :
    compactSkywalkTickLayout w 0=skywalkPoolTick w 0 := by rfl
private theorem first_pre : compactSkywalkTickPreWidth 0=258 := by rfl
private theorem first_post : compactSkywalkTickPostWidth 0=258 := by rfl

private theorem first_a_retained (w : Nat → Wire) :
    (compactSkywalkTickARelease w 0).retained=wireBlock w 1 258 := by
  unfold compactSkywalkTickARelease
  rw [first_post,compactSkywalkTick_half w 0 (by omega),first_pre]
  rw [compactSkywalkSignWord_retained _ 258 (by omega) (by simp [wireBlock_length])]
  simpa only [wireBlock_length] using List.take_length (l := wireBlock w 1 258)
private theorem first_b_retained (w : Nat → Wire) :
    (compactSkywalkTickBRelease w 0).retained=wireBlock w 770 258 := by
  unfold compactSkywalkTickBRelease
  rw [first_post,compactSkywalkTick_b w 0 (by omega),first_pre]
  rw [compactSkywalkSignWord_retained _ 258 (by omega) (by simp [wireBlock_length])]
  simpa only [wireBlock_length] using List.take_length (l := wireBlock w 770 258)
private theorem clean_full (r : List Wire) (s : BasisState) :
    (compactSkywalkSignWord r r.length).Clean s := by
  simp [compactSkywalkSignWord,CompactSkywalkSignReleaseLayout.Clean]
private theorem first_clean (w : Nat → Wire) (s : BasisState) :
    (compactSkywalkTickARelease w 0).Clean s ∧
      (compactSkywalkTickBRelease w 0).Clean s := by
  have a := clean_full (wireBlock w 1 258) s
  have b := clean_full (wireBlock w 770 258) s
  simp only [wireBlock_length] at a b
  unfold compactSkywalkTickARelease compactSkywalkTickBRelease
  rw [compactSkywalkTick_half w 0 (by omega),compactSkywalkTick_b w 0 (by omega),first_pre,first_post]
  exact ⟨a,b⟩

private theorem output_zero (w : Nat → Wire) (u : BasisState) (A B : Int)
    (t : SkywalkRails.Tick) (step : SkywalkRails.step ⟨A,B,false⟩=t)
    (ha : signedRegValue (wireBlock w 1 258) u=t.h)
    (hb : signedRegValue (wireBlock w 770 258) u=t.k)
    (hg : u (w 0)=t.g) (hs : u (w 1028)=t.s)
    (previous : u (w 1797)=false) (carry : regValue (wireBlock w 1540 257) u=0) :
    CompactSkywalkTickOutput w 0 A B false u := by
  simp only [CompactSkywalkTickOutput,first_a_retained,first_b_retained,first_layout,step,
    skywalkPoolTick,skywalkPoolPreviousId,if_pos rfl]
  exact ⟨ha,hb,hg,hs,previous,carry,(first_clean w u).1,(first_clean w u).2⟩

/-- Semantic transport is proved for abstract input/output states. -/
private theorem transport_native (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s z : State)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false)
    (out : z.phase=s.phase ∧
      regValue (wireBlock w 0 258) z.basis=
        2*(x/2+(if s.basis (w 770) then hConstant else 0))+(!(s.basis (w 770))).toNat ∧
      regValue (wireBlock w 770 258) z.basis=(x/2+kConstant false (s.basis (w 770)))%2^258 ∧
      z.basis (w 0)=!(s.basis (w 770)) ∧ z.basis (w 1028)=s.basis (w 770) ∧
      (∀q,q∉mutable w → z.basis q=s.basis q)) :
    z.phase=s.phase ∧ CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int))
      (x : Int) false z.basis := by
  have parity := source_parity w s.basis x hin.b
  rw [parity] at out
  let H := x/2+(if oddBit (x : Int) then hConstant else 0)
  have hp : (H : Int)=hValue (p : Int) (x : Int) := (h_nat_value x).symm
  have bound := secp_word_bounds x hx
  have hbound : H<2^256 := by omega
  have bvalue : signedRegValue (wireBlock w 770 258) z.basis=kValue (p : Int) (x : Int) := by
    rw [signedRegValue,wireBlock_length,out.2.2.1]
    exact k_decode_value x hx
  have split : w 0::wireBlock w 1 257=wireBlock w 0 258 := by
    simpa [block_one] using wireBlock_append w 0 1 257
  have packed := out.2.1
  rw [←split,cons_value,out.2.2.2.1] at packed
  have half : regValue (wireBlock w 1 257) z.basis=H := by omega
  have outside (i : Nat) (hi : i<1798) (ha : 257 ≤ i)
      (hb : i < 770 ∨ 1028 ≤ i) (hs : i ≠ 1028) : w i∉mutable w := by
    simp only [mutable,List.mem_append,List.mem_singleton,not_or]
    exact ⟨⟨block_not_mem w hn i 0 257 hi (by omega) (by omega),
      block_not_mem w hn i 770 258 hi (by omega) hb⟩,
      index_ne w hn i 1028 hi (by omega) hs⟩
  have ze : z.basis (w 258)=false :=
    (out.2.2.2.2.2 _ (outside 258 (by omega) (by omega) (by omega) (by omega))).trans ext
  have rawH : regValue (wireBlock w 1 258) z.basis=H := by
    rw [←wireBlock_append w 1 257 1,regValue_append,half,block_one]
    simp [regValue,ze]
  have avalue : signedRegValue (wireBlock w 1 258) z.basis=hValue (p : Int) (x : Int) := by
    rw [signedRegValue,wireBlock_length,rawH,signedDecode,if_pos (by omega)]
    exact hp
  have previous : z.basis (w 1797)=false :=
    (out.2.2.2.2.2 _ (outside 1797 (by omega) (by omega) (by omega) (by omega))).trans hin.cin
  have carry : regValue (wireBlock w 1540 257) z.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [out.2.2.2.2.2 _ (outside i (by omega) (by omega) (by omega) (by omega))]
    exact (regValue_zero _ _).mp hin.carry _ (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
  have step : SkywalkRails.step ⟨(x : Int)+(p : Int),(x : Int),false⟩=
      directTick (p : Int) (x : Int) := by
    simpa [initp,SkywalkRails.encode,SkywalkRails.signed] using secp_first_step x hx
  exact ⟨out.1,output_zero w z.basis _ _ (directTick (p : Int) (x : Int)) step
    avalue bvalue out.2.2.2.1 out.2.2.2.2.1 previous carry⟩

/-- The existing caller's clean Ext condition is used only at this seam. -/
theorem forward_native_output (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (m : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    (run (forward w) m s).phase=s.phase ∧
    CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int)) (x : Int) false
      (run (forward w) m s).basis :=
  transport_native w hn x hx s (run (forward w) m s) hin ext (forward_spec w hn x hx s m hin)

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.source_parity
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.h_nat_value
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.k_decode_value
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.forward_native_output
