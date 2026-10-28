import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Math.MeasuredCanonicalCore

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.MeasuredCanonicalModLayout

/-- Only the output and two temporary flags change within the canonical core. -/
def mutable (L : MeasuredCanonicalModLayout) : List Wire := L.out++[L.high,L.flag]
def Frame (L : MeasuredCanonicalModLayout) (base : BasisState) (O : Nat) (H F : Bool)
    (s : BasisState) : Prop :=
  regValue L.out s=O ∧ s L.high=H ∧ s L.flag=F ∧
    ∀q,q∉L.mutable → s q=base q

theorem protected_away (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.src++L.carry++[L.cin]) : q∉L.mutable := by
  intro bad
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have b := List.count_pos_iff.mpr bad
  simp only [wires,mutable,List.count_append,List.count_cons,List.count_nil] at h a b
  omega

theorem flags_away (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup) :
    L.high∉L.out ∧ L.flag∉L.extended ∧ L.cin∉L.extended ∧ L.high≠L.flag := by
  constructor
  · intro bad; have h := List.nodup_iff_count.mp hn L.high
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  constructor
  · intro bad; have h := List.nodup_iff_count.mp hn L.flag
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  constructor
  · intro bad; have h := List.nodup_iff_count.mp hn L.cin
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  · intro bad; have h := List.nodup_iff_count.mp hn L.flag
    simp only [wires,bad,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega

theorem Frame.source (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (O : Nat) (H F : Bool) (hf : L.Frame base O H F s) :
    regValue L.src s=regValue L.src base :=
  regValue_congr _ _ _ (fun q hq => hf.2.2.2 q (L.protected_away hn q (by simp [hq])))

theorem Frame.clean (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base s : BasisState) (O : Nat) (H F : Bool) (hf : L.Frame base O H F s)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    (∀q∈L.carry,s q=false) ∧ s L.cin=false := by
  constructor
  · intro q hq
    exact (hf.2.2.2 q (L.protected_away hn q (by simp [hq]))).trans (hc q hq)
  · exact (hf.2.2.2 L.cin (L.protected_away hn L.cin (by simp))).trans hi

theorem extended_value (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (s : BasisState) : regValue L.extended s=regValue L.out s+2^n*(s L.high).toNat := by
  rw [extended,regValue_append,hw.out]
  simp [regValue,Bool.toNat,Bool.cond_eq_ite]

theorem extended_decode (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (s : BasisState) (V : Nat) (hv : regValue L.extended s=V) :
    regValue L.out s=V%2^n ∧ s L.high=decide (2^n≤V) := by
  have bound : regValue L.out s<2^n := by simpa [hw.out] using regValue_lt L.out s
  rw [L.extended_value n hw] at hv
  cases hh : s L.high
  · simp only [hh,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hv
    subst V
    simp [Nat.mod_eq_of_lt bound,show ¬2^n≤regValue L.out s by omega]
  · simp only [hh,Bool.toNat_true,Nat.mul_one] at hv
    rw [←hv,Nat.add_mod_right,Nat.mod_eq_of_lt bound]
    simp

theorem Frame.afterExtended (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (base s t : BasisState) (O V : Nat) (H F : Bool)
    (hf : L.Frame base O H F s) (he : ∀q,q∉L.extended → t q=s q)
    (hv : regValue L.extended t=V) :
    L.Frame base (V%2^n) (decide (2^n≤V)) F t := by
  have flags := L.flags_away hn
  have decoded := L.extended_decode n hw t V hv
  refine ⟨decoded.1,decoded.2,(he L.flag flags.2.1).trans hf.2.2.1,?_⟩
  intro q hq
  have ex : q∉L.extended := by
    intro bad
    apply hq
    simp only [mutable,extended,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at bad ⊢
    tauto
  exact (he q ex).trans (hf.2.2.2 q hq)

theorem sum_frame (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (base : BasisState) (A X : Nat)
    (hs : regValue L.src base=A) (hb : A+X<2^(n+1))
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base X false false) L.sum
      (L.Frame base ((A+X)%2^n) (decide (2^n≤A+X)) false) := by
  have nd : (L.cin::(L.extended++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  let bits := mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)]
  have bw : mappedWires bits=L.src := by
    simp only [bits,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      Option.toList_none,List.nil_append,List.append_nil]
    exact mappedRead_wires L.src false
  have away : ∀q∈mappedWires bits,q∉L.cin::(L.extended++L.carry) := by
    rw [bw]
    intro q hq bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h b
    omega
  have len : bits.length=L.extended.length := by simp [bits,mappedRead,extended,hw.src,hw.out]
  have carryLen : L.carry.length+1=L.extended.length := by simp [hw.carry,extended,hw.out]
  intro s m hf
  have clean := Frame.clean L hn base s.basis X false false hf hc hi
  have val : mappedValue bits s.basis=A := by
    rw [show bits=mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)] from rfl,
      mappedValue_append,mappedRead_value]
    simp only [mappedValue,MappedBit.value,Option.map_none,Option.getD_none,Bool.xor_false,
      Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
    rw [Frame.source L hn base s.basis X false false hf,hs]
  have ext : regValue L.extended s.basis=X := by
    rw [L.extended_value n hw,hf.1,hf.2.1]
    simp
  obtain ⟨hp,he,hv⟩ := mappedAdd_correct bits L.extended L.carry L.cin nd away len carryLen s m clean.1
  have total : regValue L.extended (run (mappedAdd bits L.extended L.carry L.cin) m s).basis=A+X := by
    rw [hv,val,ext,clean.2,Bool.toNat_false,Nat.add_zero]
    simp [extended,hw.out,Nat.mod_eq_of_lt hb]
  exact ⟨hp,Frame.afterExtended L n hw hn base s.basis _ X (A+X) false false hf he total⟩

theorem ge_frame (L : MeasuredCanonicalModLayout) (n p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (hp : p<2^n)
    (base : BasisState) (O : Nat) (H F : Bool)
    (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base O H F)
      (compareConstantGe L.out (L.carry.take (L.out.length-1)) L.cin L.flag p)
      (L.Frame base O H (F ^^ decide (p≤O))) := by
  have nd : (L.flag::L.cin::(L.out++L.carry.take (L.out.length-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have carryLen : (L.carry.take (L.out.length-1)).length+1=L.out.length := by
    simp [hw.carry,hw.out]; omega
  have away := L.flags_away hn
  intro s m hf
  have clean := Frame.clean L hn base s.basis O H F hf hc hi
  obtain ⟨phase,same,value⟩ := compareConstantGe_correct L.out (L.carry.take (L.out.length-1))
    L.cin L.flag p nd carryLen (by simpa [hw.out] using hp) s m clean.2
    (fun q hq => clean.1 q (List.mem_of_mem_take hq))
  refine ⟨phase,?_,(same L.high away.2.2.2).trans hf.2.1,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    exact same q (fun bad => away.2.1 (by simp [extended,←bad,hq]))
  · simpa [hf.1,hf.2.2.1] using value
  · intro q hq
    have ne : q≠L.flag := fun bad => hq (by simp [mutable,bad])
    exact (same q ne).trans (hf.2.2.2 q hq)

theorem cx_flag_frame (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base : BasisState) (O : Nat) (H F : Bool) :
    Triple (L.Frame base O H F) [.CX L.high L.flag] (L.Frame base O H (F ^^ H)) := by
  have away := L.flags_away hn
  intro s m hf
  simp only [run]
  refine ⟨by trivial,?_,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    have ne : q≠L.flag := fun bad => away.2.1 (by simp [extended,←bad,hq])
    simp [writeBit,ne]
  · simpa [writeBit,away.2.2.2] using hf.2.1
  · simp [writeBit,hf.2.1,hf.2.2.1]
  · intro q hq
    have ne : q≠L.flag := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2.2 q hq

theorem cx_high_frame (L : MeasuredCanonicalModLayout) (hn : L.wires.Nodup)
    (base : BasisState) (O : Nat) (H F : Bool) :
    Triple (L.Frame base O H F) [.CX L.flag L.high] (L.Frame base O (H ^^ F) F) := by
  have away := L.flags_away hn
  intro s m hf
  simp only [run]
  refine ⟨by trivial,?_,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    have ne : q≠L.high := fun bad => away.1 (bad ▸ hq)
    simp [writeBit,ne]
  · simp [writeBit,hf.2.1,hf.2.2.1]
  · simpa [writeBit,Ne.symm away.2.2.2] using hf.2.2.1
  · intro q hq
    have ne : q≠L.high := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2.2 q hq

theorem correction_frame (L : MeasuredCanonicalModLayout) (n c : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (hcb : c<2^(n+1)) (base : BasisState)
    (O V : Nat) (H F : Bool) (hv : (if F then c else 0)+O+2^n*H.toNat=V)
    (hvb : V<2^(n+1)) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base O H F) (mappedConstAdd (some L.flag) L.extended L.carry L.cin c)
      (L.Frame base (V%2^n) (decide (2^n≤V)) F) := by
  have nd : (L.cin::(L.extended++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have srcAway : ∀q∈some L.flag,q∉L.cin::(L.extended++L.carry) := by
    intro q hq bad
    have eq : q=L.flag := by simpa [eq_comm] using hq
    subst q
    have h := List.nodup_iff_count.mp hn L.flag
    have pos := List.count_pos_iff.mpr bad
    simp only [wires,extended,List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  have carryLen : L.carry.length+1=L.extended.length := by simp [extended,hw.carry,hw.out]
  have cBound : c<2^L.extended.length := by simpa [extended,hw.out] using hcb
  intro s m hf
  have clean := Frame.clean L hn base s.basis O H F hf hc hi
  obtain ⟨phase,same,value⟩ := mappedConstAdd_correct (some L.flag) L.extended L.carry L.cin c
    nd srcAway carryLen cBound s m clean.1
  have total : regValue L.extended (run (mappedConstAdd (some L.flag) L.extended L.carry L.cin c) m s).basis=V := by
    rw [value,L.extended_value n hw,hf.1,hf.2.1,clean.2,Bool.toNat_false,Nat.add_zero]
    simp only [mappedEnabled,Option.map_some,Option.getD_some,hf.2.2.1]
    rw [show (if F then c else 0)+(O+2^n*H.toNat)=V by omega]
    simp [extended,hw.out,Nat.mod_eq_of_lt hvb]
  exact ⟨phase,Frame.afterExtended L n hw hn base s.basis _ O V H F hf same total⟩

theorem erase_frame (L : MeasuredCanonicalModLayout) (n : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (base : BasisState) (A R : Nat) (H : Bool)
    (ha : regValue L.src base=A) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base R H (decide (R<A)))
      (eraseLtChain L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag)
      (L.Frame base R H false) := by
  have nd : (L.flag::L.cin::(L.out++L.src++L.carry.take (L.out.length-1))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q; have h := List.nodup_iff_count.mp hn q
    have takeBound := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have carryLen : (L.carry.take (L.out.length-1)).length+1=L.src.length := by
    simp [hw.carry,hw.out,hw.src]; omega
  have away := L.flags_away hn
  intro s m hf
  have clean := Frame.clean L hn base s.basis R H (decide (R<A)) hf hc hi
  have src : regValue L.src s.basis=A := (Frame.source L hn base s.basis R H _ hf).trans ha
  have pred : s.basis L.flag=decide (regValue L.out s.basis<
      regValue L.src s.basis+(s.basis L.cin).toNat) := by
    rw [hf.1,src,clean.2,Bool.toNat_false,Nat.add_zero,hf.2.2.1]
  rw [eraseLtChain_correct L.out L.src _ L.cin L.flag nd (hw.out.trans hw.src.symm)
    carryLen s m (fun q hq => clean.1 q (List.mem_of_mem_take hq)) pred]
  refine ⟨by trivial,?_,?_,?_,?_⟩
  · apply Eq.trans (regValue_congr _ _ _ ?_) hf.1
    intro q hq
    have ne : q≠L.flag := fun bad => away.2.1 (by simp [extended,←bad,hq])
    simp [writeBit,ne]
  · simpa [writeBit,away.2.2.2] using hf.2.1
  · simp [writeBit]
  · intro q hq
    have ne : q≠L.flag := fun bad => hq (by simp [mutable,bad])
    simpa [writeBit,ne] using hf.2.2.2 q hq

/-- Functional composition of the complete canonical modular-add core.
The single reduction flag and extended high bit both return to zero. -/
theorem program_frame (L : MeasuredCanonicalModLayout) (n c p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (base : BasisState) (A X : Nat) (ha : regValue L.src base=A)
    (hA : A<p) (hX : X<p) (hc : ∀q∈L.carry,base q=false) (hi : base L.cin=false) :
    Triple (L.Frame base X false false) (L.program c p)
      (L.Frame base ((A+X)%p) false false) := by
  let B := 2^n
  let S := A+X
  let U := S%B
  let Q := decide (B≤S)
  let D := decide (p≤U)
  let r := decide (p≤S)
  let R := S%p
  let V := S+(if r then c else 0)
  have ppos : 0<p := by omega
  have bpos : 0<B := by dsimp [B]; positivity
  have pb : p<B := by dsimp [B]; omega
  have wideBound : S<2^(n+1) := by dsimp [S]; rw [Nat.pow_succ]; omega
  have doubleBound : S<2*B := by
    dsimp [B]
    rw [Nat.pow_succ] at wideBound
    omega
  have cBound : c<2^(n+1) := by rw [Nat.pow_succ]; omega
  have Rb : R<B := lt_trans (Nat.mod_lt S ppos) pb
  have combined : (D ^^ Q)=r := canonical_flag_bool B c p A X hpc hcp hA hX
  have split : U+B*Q.toNat=S := by
    by_cases small : S<B
    · simp [U,Q,Nat.mod_eq_of_lt small,show ¬B≤S by omega]
    · have mod : S%B=S-B := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
      simp only [U,Q,mod,show B≤S by omega,decide_true,Bool.toNat_true,Nat.mul_one]
      omega
  have corrected : V=R+B*r.toNat := by
    have eq := canonical_corrected_extended B c p A X hpc hA hX
    by_cases reduce : p≤S <;> simpa [V,R,r,S,reduce] using eq
  have Vb : V<2^(n+1) := by
    have bound := canonical_corrected_bound B c p A X hpc hcp hA hX
    rw [Nat.pow_succ]
    by_cases reduce : p≤S <;> simpa [V,r,S,B,reduce,Nat.mul_comm] using bound
  have low : V%B=R := by
    rw [corrected,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt Rb]
  have high : decide (B≤V)=r := by
    rw [corrected]
    cases hr : r <;> simp [hr,show ¬B≤R by omega]
  have flagPred : r=decide (R<A) := by
    apply decide_eq_decide.mpr
    simpa [R,S,Nat.add_comm] using (exactFold_recover_flag X A p hX hA).symm
  have s1 := L.sum_frame n hw hn base A X ha wideBound hc hi
  have s2 : Triple (L.Frame base U Q false)
      (compareConstantGe L.out (L.carry.take (L.out.length-1)) L.cin L.flag p)
      (L.Frame base U Q D) := by
    simpa [D] using L.ge_frame n p hw hn npos pb base U Q false hc hi
  have s3 : Triple (L.Frame base U Q D) [.CX L.high L.flag] (L.Frame base U Q r) := by
    simpa only [combined] using L.cx_flag_frame hn base U Q D
  have s4 : Triple (L.Frame base U Q r)
      (mappedConstAdd (some L.flag) L.extended L.carry L.cin c) (L.Frame base R r r) := by
    have val : (if r then c else 0)+U+2^n*Q.toNat=V := by
      change (if r then c else 0)+U+B*Q.toNat=V
      dsimp [V]
      omega
    have h := L.correction_frame n c hw hn cBound base U V Q r val Vb hc hi
    change Triple (L.Frame base U Q r)
      (mappedConstAdd (some L.flag) L.extended L.carry L.cin c)
      (L.Frame base (V%B) (decide (B≤V)) r) at h
    simpa only [low,high] using h
  have s5 : Triple (L.Frame base R r r) [.CX L.flag L.high] (L.Frame base R false r) := by
    simpa using L.cx_high_frame hn base R r r
  have s6 : Triple (L.Frame base R false r)
      (eraseLtChain L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag)
      (L.Frame base R false false) := by
    rw [flagPred]
    exact L.erase_frame n hw hn npos base A R false ha hc hi
  have all := (((s1.seq s2).seq s3).seq s4).seq s5 |>.seq s6
  simpa only [program,List.append_assoc] using all

/-- All valid canonical inputs and all measurement outcomes: exact sum
modulo p, phase restoration and full workspace/control/source preservation. -/
theorem program_correct (L : MeasuredCanonicalModLayout) (n c p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (npos : 0<n) (hpc : p+c=2^n) (hcp : 0<c)
    (A X : Nat) (hA : A<p) (hX : X<p) (s : State) (m : List Bool)
    (ha : regValue L.src s.basis=A) (hx : regValue L.out s.basis=X)
    (hh : s.basis L.high=false) (hf : s.basis L.flag=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hi : s.basis L.cin=false) :
    (run (L.program c p) m s).phase=s.phase ∧
    regValue L.out (run (L.program c p) m s).basis=(A+X)%p ∧
    ∀q,q∉L.out → (run (L.program c p) m s).basis q=s.basis q := by
  have initial : L.Frame s.basis X false false s.basis := ⟨hx,hh,hf,fun _ _ => rfl⟩
  obtain ⟨phase,post⟩ := L.program_frame n c p hw hn npos hpc hcp s.basis A X ha hA hX hc hi s m initial
  refine ⟨phase,post.1,?_⟩
  intro q hq
  by_cases high : q=L.high
  · subst q; exact post.2.1.trans hh.symm
  by_cases flag : q=L.flag
  · subst q; exact post.2.2.1.trans hf.symm
  exact post.2.2.2 q (by simpa only [mutable,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using ⟨hq,high,flag⟩)

end ECDSAAdd.Arithmetic.MeasuredCanonicalModLayout
