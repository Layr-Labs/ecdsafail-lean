import ECDSAAdd.Arithmetic.BalancedInverseComposeRaw

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

private theorem top_half (U H : Nat) (P N : Bool)
    (hH : 0<H) (hU : U/(2*H)=N.toNat) :
    (if P then if N then U-2*H else U+2*H else U)/2/H=(N ^^ P).toNat := by
  have div := Nat.mod_add_div U (2*H)
  have rem := Nat.mod_lt U (show 0<2*H by omega)
  rw [hU] at div
  cases P <;> cases N
  · simpa only [Bool.false_eq_true,if_false,Bool.xor_false,Bool.toNat_false,
      Nat.div_div_eq_div_mul,Nat.mul_comm] using hU
  · simpa only [Bool.false_eq_true,if_false,Bool.xor_false,Bool.toNat_true,
      Nat.div_div_eq_div_mul,Nat.mul_comm] using hU
  · simp only [if_true,Bool.false_eq_true,if_false,Bool.false_xor,
      Bool.toNat_true,Nat.div_div_eq_div_mul]
    rw [Nat.add_div_right _ (show 0<2*H by omega)]
    simpa using hU
  · simp only [if_true,Bool.true_xor,Bool.not_true,Bool.toNat_false,
      Nat.div_div_eq_div_mul]
    apply Nat.div_eq_of_lt
    simp only [Bool.toNat_true,Nat.mul_one] at div
    omega

private theorem top_bit_split (M x y : Nat) (b v : Bool)
    (hx : x<M) (hy : y<M) (h : x+M*b.toNat=y+M*v.toNat) : b=v := by
  cases b <;> cases v <;> simp at h ⊢ <;> omega

private theorem restore_word (U B H : Nat) (P N : Bool)
    (hs : U/(2*H)=N.toNat)
    (hw : (if P then if N then U-2*H else U+2*H else U)=
      2*(B+H*(N ^^ P).toNat)+P.toNat) :
    P.toNat+2*(B+H*N.toNat)=U := by
  have div := Nat.mod_add_div U (2*H)
  rw [hs] at div
  cases P <;> cases N <;> simp at div hw ⊢ <;> omega


/-- A prepared upper word determines its physical highest bit. -/
theorem prepared_one (L : Layout) (hw : L.Widths) (T : Int)
    (ht : -(2*q)≤T ∧ T≤2*q) (s : State)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    s.basis L.one=(decide (T<0) ^^ originalParity T) := by
  have shape : foldTarget L=(L.rtail++[L.rmsb])++[L.one] := by
    simp [foldTarget,List.append_assoc]
  have len : (L.rtail++[L.rmsb]).length=255 := by simp [hw.1]
  have split := regValue_append (L.rtail++[L.rmsb]) [L.one] s.basis
  rw [←shape,hword,len] at split
  have low := regValue_lt (L.rtail++[L.rmsb]) s.basis
  rw [len] at low
  have one : regValue [L.one] s.basis=(s.basis L.one).toNat := by
    cases h : s.basis L.one <;> simp [regValue,h]
  rw [one] at split
  have top := top_half (encodeWord 257 T) (2^255)
    (originalParity T) (decide (T<0)) (Nat.two_pow_pos _)
    (by simpa only [show 2*2^255=modulusWord from by norm_num [modulusWord]] using raw_sign T ht)
  change toggledWord T/2/2^255=(decide (T<0) ^^ originalParity T).toNat at top
  have div := Nat.mod_add_div (toggledWord T/2) (2^255)
  rw [top] at div
  have rem := Nat.mod_lt (toggledWord T/2) (Nat.two_pow_pos 255)
  exact top_bit_split (2^255) (regValue (L.rtail++[L.rmsb]) s.basis)
    ((toggledWord T/2)%2^255) (s.basis L.one) (decide (T<0) ^^ originalParity T)
    low rem (split.symm.trans div.symm)


/-- The actual inverse preparation restores the full raw 257-bit encoding. -/
theorem undoPreparation_word (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T) (hr : s.basis L.r0=false)
    (hl : s.basis L.lower=decide (T<0))
    (hm : s.basis L.minus=minusController T) (hu : s.basis L.plus=plusController T)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    regValue (rawTarget L) (run (undoPreparation L) m s).basis=encodeWord 257 T := by
  let P := originalParity T
  let N := decide (T<0)
  have one := prepared_one L hw T ht s hword
  have actual := undoPreparation_run L hn P N s m hp one hr hl hm hu
  let mid := L.rtail++[L.rmsb]
  have shape : rawTarget L=L.r0::(mid++[L.one]) := by
    simp [mid,rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc]
  have fshape : foldTarget L=mid++[L.one] := by simp [mid,foldTarget,List.append_assoc]
  have len : mid.length=255 := by simp [mid,hw.1]
  have split := regValue_append mid [L.one] s.basis
  rw [←fshape,hword,len] at split
  have b : regValue [L.one] s.basis=(N ^^ P).toNat := by
    simp only [regValue,List.foldr_cons,List.foldr_nil,Nat.mul_zero,Nat.add_zero,one]
    cases h : N ^^ P <;> rfl
  rw [b] at split
  have raw := raw_sign T ht
  have clear := cleared_low_word T ht
  have nd := rawTargetND L hn
  rw [shape] at nd
  have lowAway := (List.nodup_cons.mp nd).1
  have middle : regValue mid (run (undoPreparation L) m s).basis=regValue mid s.basis := by
    apply regValue_congr
    intro a ha
    have data : a∈L.r++L.y++L.carry := by
      have r : a∈L.r := by
        simp only [mid,List.mem_append,List.mem_singleton] at ha
        simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
          List.mem_append,List.mem_cons,List.mem_singleton]
        tauto
      exact List.mem_append_left _ (List.mem_append_left _ r)
    have away (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (e ▸ data)
    have ar : a≠L.r0 := fun e => lowAway (by simp [←e,ha])
    rw [actual]
    simp [writeBit,ar,away L.one (by simp),away L.plus (by simp),
      away L.minus (by simp),away L.lower (by simp)]
  have sND : [L.r0,L.one,L.plus,L.minus,L.lower].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at sND
  rcases sND with ⟨⟨h01,h02,h03,h04⟩,⟨h12,h13,h14⟩,⟨h23,h24⟩,h34⟩
  have lout : (run (undoPreparation L) m s).basis L.r0=P := by
    rw [actual]
    simp only [writeBit,Function.update_of_ne h04,Function.update_of_ne h03,
      Function.update_of_ne h02,Function.update_of_ne h01,Function.update_self]
  have hout : (run (undoPreparation L) m s).basis L.one=N := by
    rw [actual]
    simp only [writeBit,Function.update_of_ne h14,Function.update_of_ne h13,
      Function.update_of_ne h12,Function.update_self]
  rw [shape]
  change (if (run (undoPreparation L) m s).basis L.r0 then 1 else 0)+
    2*regValue (mid++[L.one]) (run (undoPreparation L) m s).basis=_
  rw [lout,regValue_append,middle,len]
  have high : regValue [L.one] (run (undoPreparation L) m s).basis=N.toNat := by
    simp only [regValue,List.foldr_cons,List.foldr_nil,Nat.mul_zero,Nat.add_zero,hout]
    cases h : N <;> rfl
  rw [high]
  have pow : modulusWord=2*2^255 := by norm_num [modulusWord]
  change encodeWord 257 T/modulusWord=N.toNat at raw
  change toggledWord T=2*(toggledWord T/2)+P.toNat at clear
  have pv : (if P then 1 else 0)=P.toNat := by cases P <;> rfl
  rw [pv]
  change (if P then if N then encodeWord 257 T-modulusWord else
    encodeWord 257 T+modulusWord else encodeWord 257 T)=_ at clear
  rw [pow] at raw clear
  rw [split] at clear
  exact restore_word (encodeWord 257 T) (regValue mid s.basis) (2^255) P N
    raw clear

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.prepared_one
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.undoPreparation_word
