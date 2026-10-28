import ECDSAAdd.Arithmetic.TriangularSquare
import ECDSAAdd.Arithmetic.Reduction

namespace ECDSAAdd.Arithmetic

/-- 固定来源及工作区，只允许目标寄存器改变。 -/
def SquareFrame (dst : List Wire) (base : BasisState) (V : Nat) (s : BasisState) : Prop :=
  regValue dst s=V ∧ ∀ w,w∉dst → s w=base w

private theorem sub_nd (r xs : List Wire) (h : r.Sublist xs) (hn : xs.Nodup) : r.Nodup := h.nodup hn

private theorem row_nd (c cin : Wire) (xs dst pad mask carry : List Wire)
    (hn : (cin::(c::xs)++dst++pad++mask++carry).Nodup) :
    (c::cin::((xs++pad.take xs.length)++mask.take (2*xs.length)++dst++carry.take (2*xs.length-1))).Nodup := by
  apply List.nodup_iff_count.mpr; intro w
  have h := List.nodup_iff_count.mp hn w
  have hp := (List.take_sublist xs.length pad).count_le w
  have hm := (List.take_sublist (2*xs.length) mask).count_le w
  have hc := (List.take_sublist (2*xs.length-1) carry).count_le w
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

/-- 一行的完整frame；补零、mask、carry的未用尾部也保持。 -/
theorem squareRow_frame (sub : Bool) (c cin : Wire) (xs dst pad mask carry : List Wire)
    (hn : (cin::(c::xs)++dst++pad++mask++carry).Nodup)
    (hd : dst.length=2*xs.length) (hx : 0<xs.length)
    (hp : xs.length≤pad.length) (hm : 2*xs.length≤mask.length)
    (hk : 2*xs.length-1≤carry.length)
    (base : BasisState) (hz : regValue (pad++mask++carry) base=0) (hi : base cin=false) (A : Nat) :
    Triple (SquareFrame dst base A) (squareRow sub c xs pad mask dst carry cin)
      (SquareFrame dst base
        (if sub then (A+2^dst.length-(if base c then regValue xs base else 0))%2^dst.length
         else (A+(if base c then regValue xs base else 0))%2^dst.length)) := by
  have nd := row_nd c cin xs dst pad mask carry hn
  let src := xs++pad.take xs.length
  let tmp := mask.take (2*xs.length)
  let cy := carry.take (2*xs.length-1)
  have hs : src.length=tmp.length := by simp [src,tmp,hp,hm]; omega
  have ht : tmp.length=dst.length := by simp [tmp,hm,hd]
  have hc : cy.length+1=dst.length := by simp [cy,hk,hd]; omega
  have notdst (w : Wire) (hw : w∈cin::(c::xs)++pad++mask++carry) : w∉dst := by
    intro hdw
    have h := List.nodup_iff_count.mp hn w
    have hc := List.count_pos_iff.mpr hw
    have hd := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at h hc
    omega
  intro s m h
  have keep (w : Wire) (hw : w∈cin::(c::xs)++pad++mask++carry) : s.basis w=base w := h.2 w (notdst w hw)
  have ctl : s.basis c=base c := keep c (by simp)
  have cin0 : s.basis cin=false := (keep cin (by simp)).trans hi
  have clean (r : List Wire) (hr : r⊆pad++mask++carry) : regValue r s.basis=0 := by
    apply (regValue_zero _ _).mpr; intro w hw
    rw [keep w (by have hh := hr hw; simp only [List.mem_cons,List.mem_append] at hh ⊢; tauto)]
    exact (regValue_zero _ _).mp hz w (hr hw)
  have srcval : regValue src s.basis=regValue xs base := by
    rw [regValue_append,clean (pad.take xs.length) (by intro w hw; simp [List.mem_of_mem_take hw]),Nat.mul_zero,Nat.add_zero]
    exact regValue_congr _ _ _ (fun w hw => keep w (by simp [hw]))
  have tzero : regValue tmp s.basis=0 := clean tmp (by intro w hw; simp [List.mem_of_mem_take hw])
  have kzero : regValue cy s.basis=0 := clean cy (by intro w hw; simp [List.mem_of_mem_take hw])
  have pre : ((s.basis c=base c ∧ regValue src s.basis=regValue xs base) ∧ regValue tmp s.basis=0) ∧ regValue dst s.basis=A := ⟨⟨⟨ctl,srcval⟩,tzero⟩,h.1⟩
  cases sub
  · have spec := measuredMaskedAddInPlace_spec c cin src tmp dst cy nd hs ht hc (base c) (regValue xs base) A s m ⟨⟨pre,cin0⟩,kzero⟩
    have frame := measuredMaskedAddInPlace_frame c cin src tmp dst cy nd hs ht hc s m tzero cin0 kzero
    exact ⟨spec.1,spec.2.1.1.2,fun w hw => (frame w hw).trans (h.2 w hw)⟩
  · have spec := measuredMaskedSubInPlace_spec c cin src tmp dst cy nd hs ht hc (base c) (regValue xs base) A s m ⟨⟨pre,cin0⟩,kzero⟩
    have frame := measuredMaskedSubInPlace_frame c cin src tmp dst cy nd hs ht hc s m tzero cin0 kzero
    exact ⟨spec.1,spec.2.1.1.2,fun w hw => (frame w hw).trans (h.2 w hw)⟩

private theorem zero_tail (a b : Wire) (dst : List Wire) (base : BasisState)
    (ha : base a=false) (hb : base b=false) :
    ∀ s, SquareFrame (a::b::dst) base 0 s ↔ SquareFrame dst base 0 s := by
  intro s
  constructor
  · intro h
    have hz := (regValue_zero _ _).mp h.1
    refine ⟨(regValue_zero _ _).mpr (fun w hw => hz w (by simp [hw])),?_⟩
    intro w hw
    by_cases hwa : w=a
    · subst w; exact (hz a (by simp)).trans ha.symm
    by_cases hwb : w=b
    · subst w; exact (hz b (by simp)).trans hb.symm
    exact h.2 w (by simp [hwa,hwb,hw])
  · intro h
    have hz := (regValue_zero _ _).mp h.1
    refine ⟨(regValue_zero _ _).mpr ?_,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with hwa|hw
      · subst w
        by_cases hh : a∈dst
        · exact hz a hh
        · exact (h.2 a hh).trans ha
      rcases List.mem_cons.mp hw with hwb|hw
      · subst w
        by_cases hh : b∈dst
        · exact hz b hh
        · exact (h.2 b hh).trans hb
      exact hz w hw
    · intro w hw; exact h.2 w (fun hmem => hw (by simp [hmem]))

private theorem diagonal (c a b : Wire) (dst : List Wire)
    (hn : (c::a::b::dst).Nodup) (base : BasisState)
    (ha : base a=false) (hb : base b=false) (V : Nat) :
    Triple (SquareFrame dst base V) [.CX c a]
      (SquareFrame (a::b::dst) base ((base c).toNat+4*V)) ∧
    Triple (SquareFrame (a::b::dst) base ((base c).toNat+4*V)) [.CX c a]
      (SquareFrame dst base V) := by
  have hca : c≠a := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have had : a∉dst := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
  have hbd : b∉dst := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
  have hcd : c∉dst := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hba : b≠a := by
    intro h; subst b; simp at hn
  have cx (s : State) (m : List Bool) :
      run [.CX c a] m s=⟨s.phase,writeBit s.basis a (s.basis a ^^ s.basis c)⟩ := by rfl
  have tail (s : BasisState) (v : Bool) : regValue dst (writeBit s a v)=regValue dst s :=
    regValue_congr _ _ _ (fun w hw => by simp [writeBit,show w≠a from fun h => had (h ▸ hw)])
  constructor
  · intro s m h
    have va := (h.2 a had).trans ha
    have vb := (h.2 b hbd).trans hb
    have vc := h.2 c hcd
    rw [cx]
    refine ⟨rfl,?_,?_⟩
    · change (if (writeBit s.basis a (s.basis a ^^ s.basis c)) a then 1 else 0)+
        2*((if (writeBit s.basis a (s.basis a ^^ s.basis c)) b then 1 else 0)+2*regValue dst _)=_
      rw [tail]
      cases hC : base c <;> simp [writeBit,hba,va,vb,vc,h.1,hC] <;> omega
    · intro w hw
      have hh : w≠a ∧ w≠b ∧ w∉dst := by simpa using hw
      simpa [writeBit,hh.1] using h.2 w hh.2.2
  · intro s m h
    have vc : s.basis c=base c := h.2 c (by simp [hca,hcd,show c≠b from fun e => by subst c; simp at hn])
    have vals : s.basis a=base c ∧ s.basis b=false ∧ regValue dst s.basis=V := by
      have hv := h.1
      change (if s.basis a then 1 else 0)+2*((if s.basis b then 1 else 0)+2*regValue dst s.basis)=_ at hv
      cases hc : base c <;> cases hA : s.basis a <;> cases hB : s.basis b <;> simp [hc,hA,hB] at hv ⊢ <;> omega
    rw [cx]
    refine ⟨rfl,(tail _ _).trans vals.2.2,?_⟩
    intro w hw
    by_cases hwa : w=a
    · subst w; simp [writeBit,vals.1,vc,ha]
    by_cases hwb : w=b
    · subst w; simp [writeBit,hba,vals.2.1,hb]
    simpa [writeBit,hwa] using h.2 w (by simp [hwa,hwb,hw])

/-- 平方及独立清理的全记录规格，来源和整个工作区均逐线保持。 -/
theorem triangularSquare_correct (xs dst pad mask carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++mask++carry).Nodup)
    (hd : dst.length=2*xs.length)
    (hp : xs.length-1≤pad.length) (hm : 2*(xs.length-1)≤mask.length)
    (hk : 2*(xs.length-1)-1≤carry.length)
    (base : BasisState) (hz : regValue (pad++mask++carry) base=0)
    (hi : base cin=false) (hbase : regValue dst base=0) :
    Triple (SquareFrame dst base 0) (triangularSquare xs dst pad mask carry cin)
      (SquareFrame dst base ((regValue xs base)^2)) ∧
    Triple (SquareFrame dst base ((regValue xs base)^2)) (triangularSquareClear xs dst pad mask carry cin)
      (SquareFrame dst base 0) := by
  induction xs generalizing dst with
  | nil =>
    have he : dst=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst dst
    constructor <;> intro s m h <;> simpa [triangularSquare,triangularSquareClear,run,SquareFrame,regValue] using And.intro (show s.phase=s.phase from rfl) h
  | cons c xs ih =>
    cases dst with
    | nil => simp at hd
    | cons a ds =>
      cases ds with
      | nil => simp at hd; omega
      | cons b dst =>
        have hd' : dst.length=2*xs.length := by simp only [List.length_cons] at hd; omega
        have hn' : (cin::xs++dst++pad++mask++carry).Nodup := by
          apply List.nodup_iff_count.mpr; intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append] at h ⊢; omega
        have hnrow : (cin::(c::xs)++dst++pad++mask++carry).Nodup := by
          apply List.nodup_iff_count.mpr; intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append] at h ⊢; omega
        have hndiag : (c::a::b::dst).Nodup := by
          apply List.nodup_iff_count.mpr; intro w
          have h := List.nodup_iff_count.mp hn w
          simp only [List.count_cons,List.count_append] at h ⊢; omega
        have hzero := (regValue_zero _ _).mp hbase
        have ha : base a=false := hzero a (by simp)
        have hb : base b=false := hzero b (by simp)
        have htail : regValue dst base=0 := (regValue_zero _ _).mpr (fun w hw => hzero w (by simp [hw]))
        have hrec := ih dst hn' hd' (by simp only [List.length_cons] at hp; omega)
          (by simp only [List.length_cons] at hm; omega)
          (by simp only [List.length_cons] at hk; omega) htail
        let Y := regValue xs base
        let V := Y^2+(if base c then Y else 0)
        have hV : V<2^dst.length := by
          rw [hd']; exact square_row_bound (base c) Y xs.length (regValue_lt xs base)
        have hy : Y^2<2^dst.length := by dsimp [V] at hV; omega
        have heq : regValue (c::xs) base ^ 2=(base c).toNat+4*V := by
          have h := square_bit_row (base c) Y
          cases hc : base c <;> simpa [regValue,List.foldr_cons,hc,Y,V] using h
        have row :
            Triple (SquareFrame dst base (Y^2))
              (if xs=[] then [] else squareRow false c xs pad mask dst carry cin) (SquareFrame dst base V) ∧
            Triple (SquareFrame dst base V)
              (if xs=[] then [] else squareRow true c xs pad mask dst carry cin) (SquareFrame dst base (Y^2)) := by
          by_cases hx : xs=[]
          · subst xs
            constructor <;> intro s m h <;> simpa [Y,V,regValue,run] using And.intro (show s.phase=s.phase from rfl) h
          · have hpos : 0<xs.length := List.length_pos_iff.mpr hx
            have hf := squareRow_frame false c cin xs dst pad mask carry hnrow hd' hpos
              (by simpa using hp) (by simpa using hm) (by simpa using hk) base hz hi (Y^2)
            have hb' := squareRow_frame true c cin xs dst pad mask carry hnrow hd' hpos
              (by simpa using hp) (by simpa using hm) (by simpa using hk) base hz hi V
            have hvmod : (Y^2+(if base c then regValue xs base else 0))%2^dst.length=V := Nat.mod_eq_of_lt hV
            have hsub : (V+2^dst.length-(if base c then regValue xs base else 0))%2^dst.length=Y^2 := by
              rw [show V+2^dst.length-(if base c then regValue xs base else 0)=Y^2+2^dst.length by dsimp [V,Y]; omega,
                Nat.add_mod_right,Nat.mod_eq_of_lt hy]
            simpa only [hx,if_false,Bool.false_eq_true,if_neg Bool.false_ne_true,if_true,hvmod,hsub] using And.intro hf hb'
        have diag := diagonal c a b dst hndiag base ha hb V
        have z := zero_tail a b dst base ha hb
        constructor
        · have h := hrec.1.seq (row.1.seq diag.1)
          apply Triple.conseq (fun s hs => (z s).mp hs) ?_ (fun _ hs => hs)
          simpa only [triangularSquare,List.append_assoc,heq] using h
        · have h := diag.2.seq (row.2.seq hrec.2)
          apply Triple.conseq (fun _ hs => hs) ?_ (fun s hs => (z s).mpr hs)
          simpa only [triangularSquareClear,List.append_assoc,heq] using h

end ECDSAAdd.Arithmetic
