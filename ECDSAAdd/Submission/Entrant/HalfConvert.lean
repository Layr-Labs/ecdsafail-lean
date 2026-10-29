import ECDSAAdd.Arithmetic.BalancedTranscriptSupport
import ECDSAAdd.Arithmetic.BalancedConvertPhysical
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.Rotate

/-! Halving boundary conversion for the balanced field replay.

For a canonical field word `v = x.val` the balanced representative of `x/2`
is fixed by the low bit `k = v mod 2` alone: `2·(x/2) = v + k·p`, so
`centered (x/2) = ⌊v/2⌋ - k·(p-1)/2`.  The conversion therefore needs no
comparison: move the low bit into the flag, rotate the word right by one,
add `k·(2^256-(p-1)/2)` with one 256-bit mapped adder, and clear the flag from
the sign bit.  The inverse subtracts the same masked constant, rotates left
and moves the flag back into the low bit, returning the canonical word of
`2x`.  Each direction costs one adder (255 Toffolis), against 765 for the
compare-add-uncompare converter of `BalancedConvert`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HalfConvert
open ECDSAAdd.Arithmetic ECDSAAdd.Arithmetic.BalancedField ECDSAAdd.Arithmetic.BalancedConvert
open Secp256k1 RecordedQuantum

/-- `2^256 - (p-1)/2`, the two's-complement offset of `-(p-1)/2`. -/
def halfC : Nat := 2^255+2^31+489

def correction (L : Layout) : List MappedBit :=
  (List.range 256).map fun i =>
    {wire:=if halfC.testBit i then some L.flag else none,flip:=false}

def lowBit (L : Layout) : Wire := L.low.headD L.msb

/-- Canonical `x` to the balanced word of `x/2`. -/
def center (L : Layout) : Program :=
  [.CX (lowBit L) L.flag,.CX L.flag (lowBit L)]++rotateRight L.word++
    mappedAdd (correction L) L.word L.carry L.cin++[.CX L.msb L.flag]

/-- Balanced word of `x` to the canonical word of `2x`. -/
def canonical (L : Layout) : Program :=
  [.CX L.msb L.flag]++mappedSub (correction L) L.word L.carry L.cin++
    rotateLeft L.word++[.CX L.flag (lowBit L),.CX (lowBit L) L.flag]

/-! Arithmetic of the halving identity. -/

private instance : NeZero p := ⟨p_prime.ne_zero⟩

private theorem p_eq : p=115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  norm_num [p]

private theorem q_eq : q=57896044618658097711785492504343953926634992332820282019728792003954417335831 := by
  norm_num [q,p]

private theorem pow256 : (2:Nat)^256=115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  norm_num

private theorem halfC_eq : halfC=57896044618658097711785492504343953926634992332820282019728792003958712304105 := by
  norm_num [halfC]

private theorem sparseF_eq : BalancedCircuit.sparseF=4294968273 := by norm_num [BalancedCircuit.sparseF]

theorem half_val (x : Fp) :
    (x/2 : Fp).val=if x.val%2=0 then x.val/2 else (x.val+p)/2 := by
  have hv : x.val<p := ZMod.val_lt x
  have hpo : p%2=1 := by norm_num [p]
  have two : (2:Fp)≠0 := by decide
  have key : ∀ w : Nat,w<p → ((w:Nat):Fp)*2=x → (x/2 : Fp).val=w := by
    intro w hw h
    have e : x/2=((w:Nat):Fp) := by rw [div_eq_iff two]; exact h.symm
    rw [e,ZMod.val_natCast_of_lt hw]
  by_cases he : x.val%2=0
  · rw [if_pos he]
    apply key _ (by omega)
    have e : x.val/2*2=x.val := by omega
    calc ((x.val/2 : Nat):Fp)*2=((x.val/2*2 : Nat):Fp) := by rw [Nat.cast_mul]; norm_num
      _=x := by rw [e,ZMod.natCast_zmod_val]
  · rw [if_neg he]
    apply key _ (by omega)
    have e : (x.val+p)/2*2=x.val+p := by omega
    calc (((x.val+p)/2 : Nat):Fp)*2=(((x.val+p)/2*2 : Nat):Fp) := by rw [Nat.cast_mul]; norm_num
      _=x := by rw [e,Nat.cast_add,ZMod.natCast_self,add_zero,ZMod.natCast_zmod_val]

theorem threshold_half (x : Fp) : threshold (x/2)=decide (x.val%2=1) := by
  have hv : x.val<p := ZMod.val_lt x
  have hp := p_eq
  unfold threshold
  rw [half_val,q_eq]
  by_cases he : x.val%2=0
  · rw [if_pos he]
    simp only [decide_eq_decide]
    omega
  · rw [if_neg he]
    simp only [decide_eq_decide]
    omega

theorem centerWord_half (x : Fp) :
    centerWord (x/2)=((if x.val%2=1 then halfC else 0)+x.val/2)%2^256 := by
  have hv : x.val<p := ZMod.val_lt x
  have hp := p_eq
  rw [centerWord_value,threshold_half,half_val,pow256,halfC_eq,sparseF_eq]
  by_cases he : x.val%2=0
  · have h1 : ¬x.val%2=1 := by omega
    rw [if_pos he]
    simp only [h1,decide_false,Bool.false_eq_true,if_false]
    omega
  · have h1 : x.val%2=1 := by omega
    rw [if_neg he]
    simp only [h1,decide_true,if_true]
    omega

/-! The masked constant. -/

private def virtual (b : Bool) : Nat :=
  (List.range 256).foldr (fun i n => (if halfC.testBit i then b else false).toNat+2*n) 0

private theorem virtual_value (b : Bool) : virtual b=if b then halfC else 0 := by
  cases b <;> decide

private theorem correction_list (is : List Nat) (L : Layout) (s : BasisState) :
    mappedValue (is.map (fun i => ({wire:=(if halfC.testBit i then some L.flag else none),flip:=false} : MappedBit))) s=
    is.foldr (fun i n => (if halfC.testBit i then s L.flag else false).toNat+2*n) 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons,ih]
    cases hi : halfC.testBit i <;> simp [MappedBit.value,hi]

theorem correction_value (L : Layout) (s : BasisState) :
    mappedValue (correction L) s=if s L.flag then halfC else 0 := by
  rw [correction,correction_list]
  exact virtual_value _

theorem correction_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (correction L)) : w=L.flag := by
  obtain ⟨b,hb,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  cases hf : halfC.testBit i
  · simp [hf] at hw
  · simpa [hf] using hw

theorem correction_length (L : Layout) : (correction L).length=256 := by simp [correction]

/-! Gate-level helpers. -/

private theorem run_four (A B C D : Program) (m : List Bool) (s : State) :
    ∃ m1 m2 m3 m4 : List Bool,
      run (A++B++C++D) m s=run D m4 (run C m3 (run B m2 (run A m1 s))) :=
  ⟨m.take (measurementCount A),(m.drop (measurementCount A)).take (measurementCount B),
    ((m.drop (measurementCount A)).drop (measurementCount B)).take (measurementCount C),
    ((m.drop (measurementCount A)).drop (measurementCount B)).drop (measurementCount C),
    by simp only [List.append_assoc,run_append]⟩

private theorem swap_in (a f : Wire) (ha : a≠f) (s : State) (m : List Bool)
    (hf : s.basis f=false) :
    (run [.CX a f,.CX f a] m s).phase=s.phase ∧
    (run [.CX a f,.CX f a] m s).basis f=s.basis a ∧
    (run [.CX a f,.CX f a] m s).basis a=false ∧
    ∀ q,q≠a → q≠f → (run [.CX a f,.CX f a] m s).basis q=s.basis q := by
  refine ⟨rfl,?_,?_,?_⟩
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hf]
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hf]
  · intro q hqa hqf
    simp [run,writeBit,Function.update_apply,hqa,hqf]

private theorem swap_out (a f : Wire) (ha : a≠f) (s : State) (m : List Bool)
    (hz : s.basis a=false) :
    (run [.CX f a,.CX a f] m s).phase=s.phase ∧
    (run [.CX f a,.CX a f] m s).basis a=s.basis f ∧
    (run [.CX f a,.CX a f] m s).basis f=false ∧
    ∀ q,q≠a → q≠f → (run [.CX f a,.CX a f] m s).basis q=s.basis q := by
  refine ⟨rfl,?_,?_,?_⟩
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hz]
  · simp [run,writeBit,Function.update_apply,ha,Ne.symm ha,hz]
  · intro q hqa hqf
    simp [run,writeBit,Function.update_apply,hqa,hqf]

private theorem cx_one (c t : Wire) (s : State) (m : List Bool) :
    (run [.CX c t] m s).phase=s.phase ∧
    (run [.CX c t] m s).basis t=(s.basis t ^^ s.basis c) ∧
    ∀ q,q≠t → (run [.CX c t] m s).basis q=s.basis q := by
  refine ⟨rfl,?_,?_⟩
  · simp [run,writeBit]
  · intro q hq
    simp [run,writeBit,Function.update_apply,hq]

/-- Shape of a width-checked layout: the low bit heads the word. -/
private theorem word_shape (L : Layout) (hw : L.Widths) :
    ∃ a rest,lowBit L=a ∧ L.word=a::rest := by
  cases h : L.low with
  | nil => have e := hw.1; rw [h] at e; simp at e
  | cons a tl => exact ⟨a,tl++[L.msb],by simp [lowBit,h],by simp [Layout.word,h]⟩

private theorem word_nodup (L : Layout) (hn : L.wires.Nodup) : L.word.Nodup :=
  (List.nodup_append'.mp (List.nodup_cons.mp (layout_add L hn)).2).1

private theorem reg_cons (a : Wire) (rest : List Wire) (s : BasisState) :
    regValue (a::rest) s=(if s a then 1 else 0)+2*regValue rest s := rfl

/-- Canonical-to-balanced halving conversion, with all work restored, every
measurement record and arbitrary incoming phase. -/
theorem center_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=x.val)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (center L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=centerWord (x/2) ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  obtain ⟨a,rest,hlow,hword⟩ := word_shape L hw
  have len := word_length L hw
  have cy : L.carry.length+1=L.word.length := by rw [hw.2,len]
  have nd := word_nodup L hn
  rw [hword] at nd
  have aRest : a∉rest := (List.nodup_cons.mp nd).1
  have aw : a∈L.word := by rw [hword]; simp
  have fa : a≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ aw)
  have hflag : s.basis L.flag=false := hc _ (by simp [work])
  have restFlag : L.flag∉rest := fun h => layout_away L hn L.flag (by simp) (by rw [hword]; simp [h])
  dsimp only
  obtain ⟨m1,m2,m3,m4,e⟩ := run_four [.CX (lowBit L) L.flag,.CX L.flag (lowBit L)]
    (rotateRight L.word) (mappedAdd (correction L) L.word L.carry L.cin) [.CX L.msb L.flag] m s
  rw [show center L=[.CX (lowBit L) L.flag,.CX L.flag (lowBit L)]++rotateRight L.word++
    mappedAdd (correction L) L.word L.carry L.cin++[.CX L.msb L.flag] from rfl,e,hlow]
  generalize e1 : run [.CX a L.flag,.CX L.flag a] m1 s=s1
  generalize e2 : run (rotateRight L.word) m2 s1=s2
  generalize e3 : run (mappedAdd (correction L) L.word L.carry L.cin) m3 s2=s3
  generalize e4 : run [.CX L.msb L.flag] m4 s3=s4
  -- stage one: the low bit moves into the flag
  have h1 := swap_in a L.flag fa s m1 hflag
  rw [e1] at h1
  let R := regValue rest s.basis
  have hxv : x.val=(if s.basis a then 1 else 0)+2*R := by rw [←hx,hword]; rfl
  have restSame : regValue rest s1.basis=R := by
    apply regValue_congr
    intro q hq
    exact h1.2.2.2 q (fun e => aRest (e ▸ hq)) (fun e => restFlag (e ▸ hq))
  have v1 : regValue L.word s1.basis=2*R := by
    rw [hword,reg_cons,h1.2.2.1,restSame]; simp
  -- stage two: halve by rotation
  have r2 := rotateRight_spec L.word (word_nodup L hn) (2*R) (by omega) s1 m2 v1
  have f2 := (rotate_frame L.word s1 m2).2.1
  rw [e2] at r2 f2
  have v2 : regValue L.word s2.basis=R := by
    have h := r2.2
    change regValue L.word s2.basis=2*R/2 at h
    omega
  have clean2 (q : Wire) (hq : q∈scratch L) : s2.basis q=false := by
    have away := scratch_away L hn q hq
    have qa : q≠a := fun e => away.1 (e ▸ aw)
    rw [f2 q away.1,h1.2.2.2 q qa away.2]
    exact hc q (by simp [work,hq])
  have flag2 : s2.basis L.flag=s.basis a := by
    rw [f2 _ (layout_away L hn _ (by simp)),h1.2.1]
  -- stage three: add the masked offset
  have p3 := mappedAdd_correct (correction L) L.word L.carry L.cin (layout_add L hn)
    (fun q hq => (correction_sources L q hq).symm ▸ flag_away L hn)
    (by rw [correction_length,len]) cy s2 m3 (fun q hq => clean2 q (by simp [scratch,hq]))
  rw [e3] at p3
  have v3 : regValue L.word s3.basis=centerWord (x/2) := by
    rw [p3.2.2,correction_value,flag2,v2,clean2 _ (by simp [scratch]),len,centerWord_half,hxv]
    cases s.basis a
    · simp only [Bool.false_eq_true,if_false,Bool.toNat_false,Nat.add_zero]
      have h : ¬((0+2*R)%2=1) := by omega
      rw [if_neg h,show (0+2*R)/2=R by omega]
    · simp only [if_true,Bool.toNat_false,Nat.add_zero]
      have h : (1+2*R)%2=1 := by omega
      rw [if_pos h,show (1+2*R)/2=R by omega]
  have flag3 : s3.basis L.flag=s.basis a := (p3.2.1 _ (layout_away L hn _ (by simp))).trans flag2
  have msb3 : s3.basis L.msb=s.basis a := by
    have m := word_msb L hw s3.basis _ (threshold (x/2)) v3 (center_threshold (x/2))
    rw [m,threshold_half,hxv]
    cases s.basis a
    · simp only [Bool.false_eq_true,if_false,decide_eq_false_iff_not]; omega
    · simp only [if_true,decide_eq_true_eq]; omega
  -- stage four: the sign bit clears the flag
  have p4 := cx_one L.msb L.flag s3 m4
  rw [e4] at p4
  have frame : ∀q,q∉L.word → s4.basis q=s.basis q := by
    intro q hq
    by_cases hf : q=L.flag
    · subst q
      rw [p4.2.1,flag3,msb3,Bool.xor_self,hflag]
    · have qa : q≠a := fun e => hq (e ▸ aw)
      rw [p4.2.2 q hf,p3.2.1 q hq,f2 q hq,h1.2.2.2 q qa hf]
  refine ⟨p4.1.trans (p3.1.trans (r2.1.trans h1.1)),?_,work_of_frame L hn s s4 hc frame,frame⟩
  rw [←v3]
  apply regValue_congr
  intro q hq
  exact p4.2.2 q (fun e => layout_away L hn L.flag (by simp) (e ▸ hq))

/-- Balanced-to-canonical doubling conversion. -/
theorem canonical_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (x : Fp) (s : State) (m : List Bool) (hx : regValue L.word s.basis=centerWord x)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (canonical L) m s
    t.phase=s.phase ∧ regValue L.word t.basis=(2*x).val ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.word → t.basis q=s.basis q) := by
  obtain ⟨a,rest,hlow,hword⟩ := word_shape L hw
  have len := word_length L hw
  have cy : L.carry.length+1=L.word.length := by rw [hw.2,len]
  have nd := word_nodup L hn
  rw [hword] at nd
  have aRest : a∉rest := (List.nodup_cons.mp nd).1
  have aw : a∈L.word := by rw [hword]; simp
  have fa : a≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ aw)
  have hflag : s.basis L.flag=false := hc _ (by simp [work])
  have restFlag : L.flag∉rest := fun h => layout_away L hn L.flag (by simp) (by rw [hword]; simp [h])
  have flagWord : L.flag∉L.word := layout_away L hn L.flag (by simp)
  let y : Fp := 2*x
  have hy : y/2=x := by
    have two : (2:Fp)≠0 := by decide
    change (2*x)/2=x
    rw [mul_comm,mul_div_cancel_right₀ x two]
  let k : Bool := decide (y.val%2=1)
  let R := y.val/2
  have hpow : (2:Nat)^256=2*2^255 := by norm_num
  have yv : y.val<p := ZMod.val_lt y
  have hp := p_eq
  have cw : centerWord x=(if k then halfC else 0)+R := by
    rw [←hy,centerWord_half,halfC_eq,pow256]
    simp only [k,R]
    by_cases h : y.val%2=1
    · simp only [h,decide_true,if_true]; omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false]; omega
  dsimp only
  obtain ⟨m1,m2,m3,m4,e⟩ := run_four [.CX L.msb L.flag]
    (mappedSub (correction L) L.word L.carry L.cin) (rotateLeft L.word)
    [.CX L.flag (lowBit L),.CX (lowBit L) L.flag] m s
  rw [show canonical L=[.CX L.msb L.flag]++mappedSub (correction L) L.word L.carry L.cin++
    rotateLeft L.word++[.CX L.flag (lowBit L),.CX (lowBit L) L.flag] from rfl,e,hlow]
  generalize e1 : run [.CX L.msb L.flag] m1 s=s1
  generalize e2 : run (mappedSub (correction L) L.word L.carry L.cin) m2 s1=s2
  generalize e3 : run (rotateLeft L.word) m3 s2=s3
  generalize e4 : run [.CX L.flag a,.CX a L.flag] m4 s3=s4
  -- stage one: the sign bit becomes the flag
  have sm : s.basis L.msb=threshold x := word_msb L hw s.basis _ (threshold x) hx (center_threshold x)
  have hk : threshold x=k := by rw [←hy,threshold_half]
  have p1 := cx_one L.msb L.flag s m1
  rw [e1] at p1
  have flag1 : s1.basis L.flag=k := by rw [p1.2.1,hflag,sm,hk,Bool.false_xor]
  have clean1 (q : Wire) (hq : q∈scratch L) : s1.basis q=false := by
    rw [p1.2.2 q (scratch_away L hn q hq).2]
    exact hc q (by simp [work,hq])
  have v1 : regValue L.word s1.basis=centerWord x := by
    rw [←hx]
    apply regValue_congr
    intro q hq
    exact p1.2.2 q (fun e => flagWord (e ▸ hq))
  -- stage two: remove the masked offset
  have p2 := mappedSub_correct (correction L) L.word L.carry L.cin (layout_add L hn)
    (fun q hq => (correction_sources L q hq).symm ▸ flag_away L hn)
    (by rw [correction_length,len]) cy s1 m2 (fun q hq => clean1 q (by simp [scratch,hq]))
    (clean1 _ (by simp [scratch]))
  rw [e2] at p2
  have v2 : regValue L.word s2.basis=R := by
    rw [p2.2.2,correction_value,flag1,v1,cw,len,pow256]
    cases k
    · simp only [Bool.false_eq_true,if_false]; omega
    · simp only [if_true]; rw [halfC_eq]; omega
  have flag2 : s2.basis L.flag=k := (p2.2.1 _ flagWord).trans flag1
  -- stage three: double by rotation
  have r3 := rotateLeft_spec L.word (word_nodup L hn) R (by rw [len]; omega) s2 m3 v2
  have f3 := (rotate_frame L.word s2 m3).2.2.2
  rw [e3] at r3 f3
  have v3 : regValue L.word s3.basis=2*R := r3.2
  have flag3 : s3.basis L.flag=k := (f3 _ flagWord).trans flag2
  have parts : (if s3.basis a then 1 else 0)+2*regValue rest s3.basis=2*R := by
    rw [←reg_cons,←hword]; exact v3
  have a3 : s3.basis a=false := by
    cases h : s3.basis a
    · rfl
    · rw [h] at parts; simp at parts; omega
  have rest3 : regValue rest s3.basis=R := by rw [a3] at parts; simp at parts; omega
  -- stage four: the flag returns to the low bit
  have p4 := swap_out a L.flag fa s3 m4 a3
  rw [e4] at p4
  have rest4 : regValue rest s4.basis=R := by
    rw [←rest3]
    apply regValue_congr
    intro q hq
    exact p4.2.2.2 q (fun e => aRest (e ▸ hq)) (fun e => restFlag (e ▸ hq))
  have v4 : regValue L.word s4.basis=y.val := by
    rw [hword,reg_cons,p4.2.1,flag3,rest4]
    simp only [k,R]
    by_cases h : y.val%2=1
    · simp only [h,decide_true,if_true]; omega
    · simp only [h,decide_false,Bool.false_eq_true,if_false]; omega
  have frame : ∀q,q∉L.word → s4.basis q=s.basis q := by
    intro q hq
    by_cases hf : q=L.flag
    · subst q
      rw [p4.2.2.1,hflag]
    · have qa : q≠a := fun e => hq (e ▸ aw)
      rw [p4.2.2.2 q qa hf,f3 q hq,p2.2.1 q hq,p1.2.2 q hf]
  exact ⟨p4.1.trans (r3.1.trans (p2.1.trans p1.1)),v4,work_of_frame L hn s s4 hc frame,frame⟩

/-! Resources, support and physical form. -/

theorem counts (L : Layout) (hw : L.Widths) :
    toffoliCount (center L)=255 ∧ measurementCount (center L)=255 ∧
    toffoliCount (canonical L)=255 ∧ measurementCount (canonical L)=255 := by
  have w : L.word.length=256 := word_length L hw
  have cy : L.carry.length+1=L.word.length := by rw [hw.2,w]
  have len : (correction L).length=L.word.length := by rw [correction_length,w]
  have a := mappedAdd_counts (correction L) L.word L.carry L.cin len cy
  have b := mappedSub_counts (correction L) L.word L.carry L.cin len cy
  have r := rotate_counts L.word
  simp [center,canonical,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,
    r.1,r.2.1,r.2.2.1,r.2.2.2,w,toffoliCount,measurementCount]

private theorem lowBit_mem (L : Layout) (hw : L.Widths) : lowBit L∈L.word := by
  obtain ⟨a,rest,hlow,hword⟩ := word_shape L hw
  rw [hlow,hword]; simp

private theorem word_sub (L : Layout) (q : Wire) (hq : q∈L.word) : q∈L.wires.toFinset := by
  simp only [Layout.word,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  simp only [Layout.wires,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem support (L : Layout) (hw : L.Widths) :
    wires (center L)⊆L.wires.toFinset ∧ wires (canonical L)⊆L.wires.toFinset := by
  have c := mappedAdd_wires_subset (correction L) L.word L.carry L.cin
  have d := mappedSub_wires_subset (correction L) L.word L.carry L.cin
  have r := rotate_wires L.word
  have lb := word_sub L _ (lowBit_mem L hw)
  have fl : L.flag∈L.wires.toFinset := by simp [Layout.wires]
  have ms : L.msb∈L.wires.toFinset := by simp [Layout.wires]
  have mapped (q : Wire) (hq : q∈(mappedWires (correction L)++L.word++L.carry++[L.cin]).toFinset) :
      q∈L.wires.toFinset := by
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with hq|hq|hq|hq
    · have e := correction_sources L q hq
      simp [Layout.wires,e]
    · exact word_sub L q hq
    · simp [Layout.wires,hq]
    · simp [Layout.wires,hq]
  have rot (q : Wire) (hq : q∈(if L.word.length<2 then ∅ else L.word.toFinset)) :
      q∈L.wires.toFinset := by
    split at hq
    · simp at hq
    · exact word_sub L q (List.mem_toFinset.mp hq)
  have cxs (a b : Wire) (ha : a∈L.wires.toFinset) (hb : b∈L.wires.toFinset) :
      wires [.CX a b,.CX b a]⊆L.wires.toFinset := by
    intro q hq
    have h : q=a ∨ q=b := by simp [wires,Instr.wires] at hq; tauto
    rcases h with rfl|rfl <;> assumption
  have cx1 : wires [.CX L.msb L.flag]⊆L.wires.toFinset := by
    intro q hq
    have h : q=L.msb ∨ q=L.flag := by simp [wires,Instr.wires] at hq; tauto
    rcases h with rfl|rfl <;> assumption
  constructor
  · intro q hq
    simp only [center,wires_append,Finset.mem_union] at hq
    rcases hq with ((hq|hq)|hq)|hq
    · exact cxs _ _ lb fl hq
    · exact rot q (r.1 ▸ hq)
    · exact mapped q (c hq)
    · exact cx1 hq
  · intro q hq
    simp only [canonical,wires_append,Finset.mem_union] at hq
    rcases hq with ((hq|hq)|hq)|hq
    · exact cx1 hq
    · exact mapped q (d hq)
    · exact rot q (r.2 ▸ hq)
    · exact cxs _ _ fl lb hq

theorem physical (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (center L) ∧ GatePhysical (canonical L) := by
  have nd : (L.cin::L.word++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have src : ∀ b∈correction L,∀q∈b.wire,q∉L.cin::L.word++L.carry := by
    intro b hb q hq
    have e : q=L.flag := correction_sources L q (List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩)
    subst q
    have fa := flag_away L hn
    simpa using fa
  have mf : L.msb≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ (by simp [Layout.word]))
  have lf : lowBit L≠L.flag := fun e => layout_away L hn L.flag (by simp) (e ▸ lowBit_mem L hw)
  have cx : GatePhysical [.CX L.msb L.flag] := by simp [GatePhysical,PhysicalInstr,ProperGate,mf]
  have sin : GatePhysical [.CX (lowBit L) L.flag,.CX L.flag (lowBit L)] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,lf,Ne.symm lf]
  have sout : GatePhysical [.CX L.flag (lowBit L),.CX (lowBit L) L.flag] := by
    simp [GatePhysical,PhysicalInstr,ProperGate,lf,Ne.symm lf]
  have ma := mappedAdd_physical _ _ _ _ nd src
  have nt := notRegister_physical L.word
  have ms : GatePhysical (mappedSub (correction L) L.word L.carry L.cin) := by
    simpa only [mappedSub,gatePhysical_append] using And.intro (And.intro nt ma) nt
  have rot := rotate_physical L.word (word_nodup L hn)
  simp only [center,canonical,gatePhysical_append]
  exact ⟨⟨⟨⟨sin,rot.1⟩,ma⟩,cx⟩,⟨⟨⟨cx,ms⟩,rot.2⟩,sout⟩⟩

end ECDSAAdd.Entrant.HalfConvert
