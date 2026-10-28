import ECDSAAdd.Arithmetic.SignedTriangularSquareResources
import ECDSAAdd.Math.SignedSquare
import ECDSAAdd.Arithmetic.TriangularSquareProof

namespace ECDSAAdd.Arithmetic

def xorFalseBasis (c : Wire) (ys : List Wire) (s : BasisState) : BasisState :=
  fun w => if w∈ys then s w ^^ !s c else s w

private theorem xorFalseBit_correct (c y : Wire) (hcy : c≠y) (s : State) (m : List Bool) :
    run [.X y,.CX c y] m s=
      ⟨s.phase,writeBit s.basis y (s.basis y ^^ !s.basis c)⟩ := by
  simp [run,writeBit,hcy]

/-- Exact all-state semantics of the Clifford false-controlled complement. -/
theorem xorWhenFalse_correct (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) :
    run (xorWhenFalse c ys) m s=⟨s.phase,xorFalseBasis c ys s.basis⟩ := by
  induction ys generalizing s with
  | nil =>
    apply congrArg (State.mk s.phase)
    funext w
    simp [xorFalseBasis]
  | cons y ys ih =>
    obtain ⟨hy,hys⟩ := List.nodup_cons.mp hnd
    have hcy : c≠y := fun h => hc (by simp [h])
    have hcs : c∉ys := fun h => hc (by simp [h])
    let s1 : State := ⟨s.phase,writeBit s.basis y (s.basis y ^^ !s.basis c)⟩
    rw [xorWhenFalse,run_append]
    simp only [measurementCount,List.take_zero,List.drop_zero]
    rw [xorFalseBit_correct c y hcy s [],
      show (⟨s.phase,writeBit s.basis y (s.basis y ^^ !s.basis c)⟩ : State)=s1 from rfl,
      ih hys hcs s1]
    apply congrArg (State.mk s.phase)
    funext w
    by_cases hwy : w=y
    · subst w
      simp [xorFalseBasis,hy,s1,writeBit]
    · by_cases hws : w∈ys
      · simp [xorFalseBasis,hws,hwy,s1,writeBit,hcy]
      · simp [xorFalseBasis,hws,hwy,s1,writeBit]

theorem xorWhenFalse_phase (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) :
    (run (xorWhenFalse c ys) m s).phase=s.phase := by
  rw [xorWhenFalse_correct c ys hnd hc]

theorem xorWhenFalse_control (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) :
    (run (xorWhenFalse c ys) m s).basis c=s.basis c := by
  rw [xorWhenFalse_correct c ys hnd hc]
  simp [xorFalseBasis,hc]

theorem xorWhenFalse_outside (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) (w : Wire) (hw : w∉ys) :
    (run (xorWhenFalse c ys) m s).basis w=s.basis w := by
  rw [xorWhenFalse_correct c ys hnd hc]
  simp [xorFalseBasis,hw]

theorem xorWhenFalse_value (c : Wire) (ys : List Wire) (hnd : ys.Nodup)
    (hc : c∉ys) (s : State) (m : List Bool) :
    regValue ys (run (xorWhenFalse c ys) m s).basis=
      if s.basis c then regValue ys s.basis else 2^ys.length-1-regValue ys s.basis := by
  rw [xorWhenFalse_correct c ys hnd hc]
  by_cases h : s.basis c
  · simp [h]
    apply regValue_congr
    intro w hw
    simp [xorFalseBasis,hw,h]
  · simp [h]
    rw [regValue_congr ys _ (fun w => !s.basis w) (by intro w hw; simp [xorFalseBasis,hw,h]),
      regValue_complement]

private theorem take_value_mod (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.take n) s=regValue r s%2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  rw [h,Nat.add_mul_mod_self_left]
  apply (Nat.mod_eq_of_lt ?_).symm
  simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s

private theorem drop_value_div (r : List Wire) (n : Nat) (hn : n≤r.length)
    (s : BasisState) : regValue (r.drop n) s=regValue r s/2^n := by
  have h := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hn] at h
  have hl : regValue (r.take n) s<2^n := by
    simpa only [List.length_take,Nat.min_eq_left hn] using regValue_lt (r.take n) s
  rw [h,Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),Nat.div_eq_of_lt hl,Nat.zero_add]

/-- Complementing a low prefix preserves the high quotient and complements
only the low residue. -/
theorem xorWhenFalse_prefix_value (c : Wire) (dst : List Wire) (k : Nat)
    (hnd : dst.Nodup) (hc : c∉dst) (hk : k≤dst.length) (s : State) (m : List Bool) :
    regValue dst (run (xorWhenFalse c (dst.take k)) m s).basis=
      if s.basis c then regValue dst s.basis
      else (2^k-1-regValue dst s.basis%2^k)+2^k*(regValue dst s.basis/2^k) := by
  let u := run (xorWhenFalse c (dst.take k)) m s
  have htakeN : (dst.take k).Nodup := (List.take_sublist k dst).nodup hnd
  have hctake : c∉dst.take k := fun h => hc (List.mem_of_mem_take h)
  have hlo := xorWhenFalse_value c (dst.take k) htakeN hctake s m
  have hhigh : regValue (dst.drop k) u.basis=regValue (dst.drop k) s.basis := by
    apply regValue_congr
    intro w hw
    apply xorWhenFalse_outside c (dst.take k) htakeN hctake s m
    intro ht
    exact List.disjoint_left.mp (List.disjoint_take_drop hnd (Nat.le_refl k)) ht hw
  have hsplitU := regValue_append (dst.take k) (dst.drop k) u.basis
  have hsplitS := regValue_append (dst.take k) (dst.drop k) s.basis
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at hsplitU hsplitS
  have hlowS := take_value_mod dst k hk s.basis
  have hhighS := drop_value_div dst k hk s.basis
  rw [List.length_take,Nat.min_eq_left hk] at hlo
  change regValue dst u.basis=_
  rw [hsplitU,hhigh,hlo,hlowS,hhighS]
  split
  · exact Nat.mod_add_div (regValue dst s.basis) (2^k)
  · rfl

theorem xorWhenFalse_frame (c : Wire) (dst : List Wire)
    (hnd : (c::dst).Nodup) (base : BasisState) (C : Bool) (A : Nat)
    (hC : base c=C) :
    Triple (SquareFrame dst base A) (xorWhenFalse c dst)
      (SquareFrame dst base (if C then A else 2^dst.length-1-A)) := by
  have hd : dst.Nodup := (List.nodup_cons.mp hnd).2
  have hc : c∉dst := (List.nodup_cons.mp hnd).1
  intro s m h
  have sc : s.basis c=C := (h.2 c hc).trans hC
  have hv := xorWhenFalse_value c dst hd hc s m
  have hp := xorWhenFalse_phase c dst hd hc s m
  refine ⟨hp,?_,?_⟩
  · simpa [sc,h.1] using hv
  · intro w hw
    exact (xorWhenFalse_outside c dst hd hc s m w hw).trans (h.2 w hw)

theorem xorWhenFalse_prefix_frame (c : Wire) (dst : List Wire) (k : Nat)
    (hnd : (c::dst).Nodup) (hk : k≤dst.length) (base : BasisState)
    (C : Bool) (A : Nat) (hC : base c=C) :
    Triple (SquareFrame dst base A) (xorWhenFalse c (dst.take k))
      (SquareFrame dst base (if C then A
        else (2^k-1-A%2^k)+2^k*(A/2^k))) := by
  have hd : dst.Nodup := (List.nodup_cons.mp hnd).2
  have hc : c∉dst := (List.nodup_cons.mp hnd).1
  intro s m h
  have sc : s.basis c=C := (h.2 c hc).trans hC
  have hv := xorWhenFalse_prefix_value c dst k hd hc hk s m
  have htN : (dst.take k).Nodup := (List.take_sublist k dst).nodup hd
  have hct : c∉dst.take k := fun hh => hc (List.mem_of_mem_take hh)
  have hp := xorWhenFalse_phase c (dst.take k) htN hct s m
  refine ⟨hp,?_,?_⟩
  · simpa [sc,h.1] using hv
  · intro w hw
    exact (xorWhenFalse_outside c (dst.take k) htN hct s m w
      (fun hh => hw (List.mem_of_mem_take hh))).trans (h.2 w hw)

/-- Exact ripple-add frame with a live arbitrary carry-in. -/
theorem addInPlace_cin_frame (cin : Wire) (src dst carry : List Wire)
    (hnd : (cin::src++dst++carry).Nodup) (hs : src.length=dst.length)
    (hc : carry.length+1=dst.length) (base : BasisState) (C : Bool)
    (hC : base cin=C) (hk : regValue carry base=0) (V : Nat) :
    Triple (SquareFrame dst base V) (addInPlace src dst carry cin)
      (SquareFrame dst base ((V+regValue src base+C.toNat)%2^dst.length)) := by
  have dis (w : Wire) (hw : w∈cin::src++carry) : w∉dst := by
    intro hdw
    have hn := List.nodup_iff_count.mp hnd w
    have h1 := List.count_pos_iff.mpr hw
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  intro s m h
  have sv : regValue src s.basis=regValue src base :=
    regValue_congr _ _ _ (fun w hw => h.2 w (dis w (by simp [hw])))
  have kv : regValue carry s.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => h.2 w (dis w (by simp [hw])))).trans hk
  have cv : s.basis cin=C := (h.2 cin (dis cin (by simp))).trans hC
  have runh := addInPlace_correct src dst carry cin hnd hs hc s m
    ((regValue_zero _ _).mp kv)
  refine ⟨runh.1,?_,?_⟩
  · rw [runh.2.2,sv,h.1,cv]
    congr 2
    omega
  · intro w hw
    exact (runh.2.1 w hw).trans (h.2 w hw)

def signedRowValue (C : Bool) (A S k : Nat) : Nat :=
  if C then (A+S+1)%2^(k+1) else (A+2^k-S)%2^(k+1)

/-- One signed row has exact all-record semantics, preserves every non-target
wire, and restores its measured ripple carries. -/
theorem signedSquareRow_frame (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (base : BasisState) (C : Bool) (hC : base c=C)
    (hz : regValue (pad++carry) base=0) (A : Nat) (hA : A<2^dst.length) :
    Triple (SquareFrame dst base A) (signedSquareRow c xs dst pad carry)
      (SquareFrame dst base (signedRowValue C A (regValue xs base) xs.length)) := by
  let src := xs++pad.take 1
  let cy := carry.take xs.length
  have ndc : (c::dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ndadd : (c::src++dst++cy).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    have hp' := (List.take_sublist 1 pad).count_le w
    have hc' := (List.take_sublist xs.length carry).count_le w
    simp only [src,cy,List.count_cons,List.count_append] at h ⊢
    omega
  have hs : src.length=dst.length := by simp [src,hd,hp]
  have hcy : cy.length+1=dst.length := by simp [cy,hc,hd]
  have srcv : regValue src base=regValue xs base := by
    have p0 : regValue (pad.take 1) base=0 := (regValue_zero _ _).mpr
      (fun w hw => (regValue_zero _ _).mp hz w (by simp [List.mem_of_mem_take hw]))
    simp [src,regValue_append,p0]
  have cy0 : regValue cy base=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hz w (by simp [List.mem_of_mem_take hw]))
  let P := if C then A else
    (2^xs.length-1-A%2^xs.length)+2^xs.length*(A/2^xs.length)
  let B := (P+regValue src base+C.toNat)%2^dst.length
  have h1 := xorWhenFalse_prefix_frame c dst xs.length ndc (by omega) base C A hC
  have h2 := addInPlace_cin_frame c src dst cy ndadd hs hcy base C hC cy0 P
  have h3 := xorWhenFalse_frame c dst ndc base C B hC
  have comp := h1.seq (h2.seq h3)
  have heq : (if C then B else 2^dst.length-1-B)=
      signedRowValue C A (regValue xs base) xs.length := by
    simp only [P,B,srcv]
    cases C with
    | true => simp [signedRowValue,hd]
    | false =>
      simp only [Bool.false_eq_true,if_false,Bool.toNat_false,Nat.add_zero]
      rw [hd] at hA
      have hS : regValue xs base<2^xs.length := regValue_lt xs base
      have hm : 0<2^xs.length := Nat.two_pow_pos _
      have hA2 : A<2*(2^xs.length) := by simpa [Nat.pow_succ,Nat.mul_comm] using hA
      rw [hd]
      simp only [signedRowValue,Bool.false_eq_true,if_false]
      rw [show 2^(xs.length+1)=2*(2^xs.length) by rw [Nat.pow_succ]; omega]
      exact signed_false_row_value A (regValue xs base) (2^xs.length) hm hA2 hS
  have final := Triple.conseq (fun _ h => h) comp
    (fun _ hpost => by simpa [heq] using hpost)
  simpa [signedSquareRow,src,cy,List.append_assoc] using final

theorem notRegister_frame (dst : List Wire) (hnd : dst.Nodup)
    (base : BasisState) (A : Nat) :
    Triple (SquareFrame dst base A) (notRegister dst)
      (SquareFrame dst base (2^dst.length-1-A)) := by
  intro s m h
  have nr := notRegister_correct dst hnd s m
  rw [nr]
  refine ⟨rfl,?_,?_⟩
  · change regValue dst _=_
    rw [regValue_congr dst _ (fun q => !s.basis q) (by intro q hq; simp [hq]),
      regValue_complement,h.1]
  · intro q hq
    simp [hq,h.2 q hq]

theorem signedSquareRowClear_frame (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (base : BasisState) (C : Bool) (hC : base c=C)
    (hz : regValue (pad++carry) base=0) (A : Nat) (hA : A<2^xs.length) :
    Triple (SquareFrame dst base (signedRowValue C A (regValue xs base) xs.length))
      (signedSquareRowClear c xs dst pad carry) (SquareFrame dst base A) := by
  let src := xs++pad.take 1
  let cy := carry.take xs.length
  have ndc : (c::dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have dstN : dst.Nodup := (List.nodup_cons.mp ndc).2
  have ndadd : (c::src++dst++cy).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hp' := (List.take_sublist 1 pad).count_le q
    have hc' := (List.take_sublist xs.length carry).count_le q
    simp only [src,cy,List.count_cons,List.count_append] at h ⊢
    omega
  have hs : src.length=dst.length := by simp [src,hd,hp]
  have hcy : cy.length+1=dst.length := by simp [cy,hc,hd]
  have srcv : regValue src base=regValue xs base := by
    have p0 : regValue (pad.take 1) base=0 := (regValue_zero _ _).mpr
      (fun q hq => (regValue_zero _ _).mp hz q (by simp [List.mem_of_mem_take hq]))
    simp [src,regValue_append,p0]
  have cy0 : regValue cy base=0 := (regValue_zero _ _).mpr
    (fun q hq => (regValue_zero _ _).mp hz q (by simp [List.mem_of_mem_take hq]))
  let B := signedRowValue C A (regValue xs base) xs.length
  let V1 := if C then B else 2^dst.length-1-B
  let V2 := 2^dst.length-1-V1
  let V3 := (V2+regValue src base+C.toNat)%2^dst.length
  let V4 := 2^dst.length-1-V3
  have h1 := xorWhenFalse_frame c dst ndc base C B hC
  have h2 := notRegister_frame dst dstN base V1
  have h3 := addInPlace_cin_frame c src dst cy ndadd hs hcy base C hC cy0 V2
  have h4 := notRegister_frame dst dstN base V3
  have h5 := xorWhenFalse_prefix_frame c dst xs.length ndc (by omega) base C V4 hC
  have comp := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  have heq : (if C then V4 else
      (2^xs.length-1-V4%2^xs.length)+2^xs.length*(V4/2^xs.length))=A := by
    have hS := regValue_lt xs base
    have pow : 2^dst.length=2*2^xs.length := by rw [hd,Nat.pow_succ]; omega
    cases C with
    | false =>
      have bfit : A+2^xs.length-regValue xs base<2^dst.length := by rw [pow]; omega
      have bEq : B=A+2^xs.length-regValue xs base := by
        simp only [B,signedRowValue,Bool.false_eq_true,if_false]
        have bf : A+2^xs.length-regValue xs base<2^(xs.length+1) := by simpa [hd] using bfit
        rw [Nat.mod_eq_of_lt bf]
      have v2Eq : V2=B := by
        dsimp [V1,V2]
        rw [bEq]
        omega
      have addfit : A+2^xs.length<2^dst.length := by rw [pow]; omega
      have v3Eq : V3=A+2^xs.length := by
        dsimp [V3]
        rw [v2Eq,srcv]
        simp only [bEq]
        rw [show A+2^xs.length-regValue xs base+regValue xs base=A+2^xs.length by omega,
          Nat.mod_eq_of_lt addfit]
      have v4Eq : V4=2^xs.length-1-A := by
        dsimp [V4]
        rw [v3Eq,pow]
        omega
      simp only [Bool.false_eq_true,if_false]
      rw [v4Eq]
      have lowfit : 2^xs.length-1-A<2^xs.length := by omega
      rw [Nat.mod_eq_of_lt lowfit,Nat.div_eq_of_lt lowfit]
      omega
    | true =>
      have bfit : A+regValue xs base+1<2^dst.length := by rw [pow]; omega
      have bEq : B=A+regValue xs base+1 := by
        simp only [B,signedRowValue,if_true]
        have bf : A+regValue xs base+1<2^(xs.length+1) := by simpa [hd] using bfit
        rw [Nat.mod_eq_of_lt bf]
      have v2Eq : V2=2^dst.length-1-B := by simp [V1,V2]
      have midfit : 2^dst.length-1-(A+regValue xs base+1)+regValue xs base+1<2^dst.length := by omega
      have v3Eq : V3=2^dst.length-1-A := by
        dsimp [V3]
        rw [v2Eq,srcv,bEq]
        rw [Nat.mod_eq_of_lt midfit]
        omega
      have v4Eq : V4=A := by dsimp [V4]; rw [v3Eq]; omega
      simp [v4Eq]
  have final := Triple.conseq (fun _ h => h) comp (fun _ h => by simpa [heq] using h)
  simpa [signedSquareRowClear,src,cy,B,V1,V2,V3,V4,List.append_assoc] using final

theorem signedSquareRow_roundtrip (c : Wire) (xs dst pad carry : List Wire)
    (hnd : (c::xs++dst++pad++carry).Nodup) (hd : dst.length=xs.length+1)
    (hp : 1≤pad.length) (hc : xs.length≤carry.length)
    (base : BasisState) (hz : regValue (pad++carry) base=0)
    (A : Nat) (hA : A<2^xs.length) :
    Triple (SquareFrame dst base A)
      (signedSquareRow c xs dst pad carry++signedSquareRowClear c xs dst pad carry)
      (SquareFrame dst base A) := by
  let C := base c
  have f := signedSquareRow_frame c xs dst pad carry hnd hd hp hc base C rfl hz A
    (hA.trans (Nat.pow_lt_pow_right (by decide) (by omega)))
  have r := signedSquareRowClear_frame c xs dst pad carry hnd hd hp hc base C rfl hz A hA
  exact f.seq r

end ECDSAAdd.Arithmetic
