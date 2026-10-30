import ECDSAAdd.Submission.Entrant.MainPre

/-! TrimSquare3 (debias): the first signed-row lowest carry of every plain `tsq2` leaf square is a copy
(make and clear), proved against the library; used for the two plain leaves of each `kg` group. -/

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.TrimSquare3
open ECDSAAdd ECDSAAdd.Arithmetic RecordedQuantum

/-- `addInPlace` whose lowest majority/erase pair is a copy of the lowest source bit. -/
def addDrop : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
      [.CX a c]++addInPlace (a'::as) (b'::bs) cs c++[.CX a c]++[.CX a b,.CX cin b]
  | x, y, carry, cin => addInPlace x y carry cin

theorem carryBit_of_copy (A Y C : Bool) (h : ((Y^^A) && (C^^A))=false) : carryBit A Y C=A := by
  cases A <;> cases Y <;> cases C <;> simp_all [carryBit]

def insF (K : Nat) (l : List Bool) : List Bool := (l++List.replicate K false).take K++false::l.drop K

theorem insF_take (K : Nat) (l : List Bool) : (insF K l).take K=(l++List.replicate K false).take K := by
  have : ((l++List.replicate K false).take K).length=K := by simp
  simp [insF,List.take_append_of_le_length (le_of_eq this.symm),this]

theorem insF_drop (K : Nat) (l : List Bool) : (insF K l).drop K=false::l.drop K := by
  have : ((l++List.replicate K false).take K).length=K := by simp
  simp [insF,List.drop_append_of_le_length (le_of_eq this.symm),this]

theorem insF_length (K : Nat) (l : List Bool) (h : K≤l.length) : (insF K l).length=l.length+1 := by
  simp [insF]; omega

theorem run_padTake (P : Program) (l : List Bool) (K : Nat) (s : State) (hK : measurementCount P=K) :
    run P ((l++List.replicate K false).take K) s=run P l s := by
  rw [← hK,run_take,run_pad_false]

theorem td (L1 L2 : List Bool) (n : Nat) (h : L1.length=n) :
    (L1++L2).take n=L1 ∧ (L1++L2).drop n=L2 := by subst h; simp

theorem glue (Pre X X' Post : Program) (K : Nat) (hK : K≤measurementCount X)
    (hm : measurementCount X'=measurementCount X+1) (s : State)
    (h : ∀ rP rX, run X rX (run Pre rP s)=run X' (insF K rX) (run Pre rP s)) (r : List Bool) :
    ∃ R, run (Pre++X++Post) r s=run (Pre++X'++Post) R s := by
  rw [← run_pad_false _ r (measurementCount Pre+measurementCount X)]
  generalize hr0 : r++List.replicate (measurementCount Pre+measurementCount X) false=r0
  have hl : measurementCount Pre+measurementCount X≤r0.length := by rw [← hr0]; simp
  have ta : (r0.take (measurementCount Pre)).length=measurementCount Pre := by simp; omega
  have hrX : ((r0.drop (measurementCount Pre)).take (measurementCount X)).length=measurementCount X := by
    simp; omega
  have li := insF_length K ((r0.drop (measurementCount Pre)).take (measurementCount X)) (by omega)
  refine ⟨r0.take (measurementCount Pre)++
    (insF K ((r0.drop (measurementCount Pre)).take (measurementCount X))++
      r0.drop (measurementCount Pre+measurementCount X)),?_⟩
  rw [List.append_assoc Pre,List.append_assoc Pre,run_append Pre,run_append Pre,run_append X,run_append X',
    (td _ _ _ ta).1,(td _ _ _ ta).2,hm,(td _ _ _ (by rw [li,hrX])).1,(td _ _ _ (by rw [li,hrX])).2,
    List.drop_drop,h]

theorem cx_run (a c : Wire) (m : List Bool) (s : State) :
    run [.CX a c] m s=⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis a)⟩ := rfl

theorem addDrop_run (a a' b b' c cin : Wire) (as bs cs : List Wire) (hnd : [a,b,cin,c].Nodup)
    (hrec : (c::((a'::as)++(b'::bs)++cs)).Nodup) (hl : (a'::as).length=(b'::bs).length)
    (hcl : cs.length+1=(b'::bs).length) (ha : a∉b'::bs) (rX : List Bool) (s : State)
    (hcopy : ((s.basis b^^s.basis a) && (s.basis cin^^s.basis a))=false)
    (hc0 : s.basis c=false) (hclean : ∀q∈cs,s.basis q=false) :
    run (addDrop (a::a'::as) (b::b'::bs) (c::cs) cin) rX s=
      run (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)
        (insF (measurementCount (addInPlace (a'::as) (b'::bs) cs c)) rX) s := by
  have hm : run (majority a b cin c) [] s=run [.CX a c] [] s := by
    rw [majority_correct a b cin c hnd,cx_run,carryBit_of_copy _ _ _ hcopy]
  have m0 : measurementCount (majority a b cin c)=0 := by simp [majority,measurementCount]
  set REC := addInPlace (a'::as) (b'::bs) cs c
  set K := measurementCount REC
  simp only [addDrop,addInPlace]
  rw [show [Instr.CX a c]++REC++[Instr.CX a c]++[Instr.CX a b,Instr.CX cin b]=
      ([Instr.CX a c]++REC)++([Instr.CX a c]++[Instr.CX a b,Instr.CX cin b]) by simp only [List.append_assoc],
    show majority a b cin c++REC++eraseCarry a b cin c++[Instr.CX a b,Instr.CX cin b]=
      (majority a b cin c++REC)++(eraseCarry a b cin c++[Instr.CX a b,Instr.CX cin b]) by
      simp only [List.append_assoc]]
  have mK1 : measurementCount ([Instr.CX a c]++REC)=K := rfl
  have mK2 : measurementCount (majority a b cin c++REC)=K := by
    rw [measurementCount_append,m0,Nat.zero_add]
  rw [run_append ([Instr.CX a c]++REC),run_append (majority a b cin c++REC),mK1,mK2,insF_take,insF_drop,
    run_padTake _ _ _ _ mK2,← run_take (majority a b cin c++REC),mK2]
  rw [run_append (majority a b cin c) REC,run_append [Instr.CX a c] REC,m0,List.take_zero,List.drop_zero,hm]
  have m1 : measurementCount [Instr.CX a c]=0 := rfl
  rw [m1,List.take_zero,List.drop_zero]
  generalize hu : run [Instr.CX a c] [] s=u
  have uc : u.basis c=s.basis a := by rw [← hu]; simp [run,writeBit,hc0]
  have hac : a≠c := by simp at hnd; tauto
  have ua : u.basis a=s.basis a := by
    rw [← hu]; simp [run,writeBit,Function.update,hac]
  have ucl : ∀q∈cs,u.basis q=false := by
    intro q hq; rw [← hu]
    have : q≠c := by intro e; subst e; simp at hrec; tauto
    simp [run,writeBit,Function.update,this,hclean q hq]
  have nd' : (c::((a'::as)++(b'::bs)++cs)).Nodup := hrec
  generalize hw : run REC (rX.take K) u=w
  have pres := (addInPlace_correct (a'::as) (b'::bs) cs c nd' hl hcl u (rX.take K) ucl).2.1
  have wc : w.basis c=s.basis a := by
    rw [← hw,pres c (by simp at hrec ⊢; tauto),uc]
  have wa : w.basis a=s.basis a := by rw [← hw,pres a ha,ua]
  have e1 : eraseCarry a b cin c=[.measureX c [] [.CZ a b,.CZ a cin,.CZ b cin]] := rfl
  rw [e1]
  have key : run [Instr.CX a c] [] w=run [Instr.measureX c [] [.CZ a b,.CZ a cin,.CZ b cin]] [false] w := by
    simp only [run,List.headD_cons,List.tail_cons,measureAndCorrect,correct,Bool.false_and,Bool.xor_false,
      Bool.false_eq_true,if_false]
    congr 1
    simp [writeBit,wc,wa]
  rw [run_append [Instr.CX a c],run_append [Instr.measureX c [] [.CZ a b,.CZ a cin,.CZ b cin]]]
  simp only [measurementCount,List.take_zero,List.drop_zero,List.take_succ_cons,List.drop_succ_cons,
    List.take_zero,Nat.add_zero]
  rw [key]

theorem top_keep (xs dst : List Wire) (m : List Bool) (s : State) (q : Wire) (hq : q∉dst) :
    (run (signedSquareTop xs dst) m s).basis q=s.basis q := by
  induction xs generalizing dst with
  | nil => rfl
  | cons x xs ih =>
    match xs, dst with
    | [], [] => rfl
    | [], [_] => rfl
    | [], _::z::_ =>
      simp only [signedSquareTop,run,writeBit]
      have : q≠z := by intro e; subst e; simp at hq
      simp [Function.update,this]
    | _::_, [] => rfl
    | _::_, [_] => rfl
    | y::ys, a::b::dst =>
      simp only [signedSquareTop]
      exact ih _ (by intro h; exact hq (by simp [h]))

theorem sub_nodup (c : Wire) (xs D dst pad carry : List Wire) (hD : D.Sublist dst)
    (h : (c::xs++dst++pad++carry).Nodup) : (c::xs++D++pad++carry).Nodup :=
  (((((List.Sublist.refl (c::xs)).append hD).append (List.Sublist.refl pad)).append
    (List.Sublist.refl carry))).nodup h

theorem rowClear_keep (c : Wire) (xs D pad carry : List Wire)
    (hnd : (c::xs++D++pad++carry).Nodup) (hd : D.length=xs.length+1) (hp : 1≤pad.length)
    (hc : xs.length≤carry.length) (s : State) (m : List Bool)
    (hclean : ∀q∈carry,s.basis q=false) (q : Wire) (hq : q∉D) :
    (run (signedSquareRowClear c xs D pad carry) m s).basis q=s.basis q := by
  have ndc : (c::D).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have Dn : D.Nodup := (List.nodup_cons.mp ndc).2
  have cD : c∉D := (List.nodup_cons.mp ndc).1
  have cDt : c∉D.take xs.length := fun h => cD (List.mem_of_mem_take h)
  have Dtn : (D.take xs.length).Nodup := (List.take_sublist _ _).nodup Dn
  have nda : (c::((xs++pad.take 1)++D++carry.take xs.length)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hnd w
    have t1 := (List.take_sublist 1 pad).count_le w
    have t2 := (List.take_sublist xs.length carry).count_le w
    simp only [List.count_cons,List.count_append] at h t1 t2 ⊢
    omega
  have carryD : ∀w∈carry,w∉D := by
    intro w hw hD
    have h := List.nodup_iff_count.mp hnd w
    have a := List.count_pos_iff.mpr hw
    have b := List.count_pos_iff.mpr hD
    simp only [List.count_cons,List.count_append] at h; omega
  have hs : (xs++pad.take 1).length=D.length := by simp [hd]; omega
  have hk : (carry.take xs.length).length+1=D.length := by simp [hd]; omega
  let P : State → Prop := fun st => ∀ w, w∉D → st.basis w=s.basis w
  have pX (E : List Wire) (hE : E.Sublist D) (st : State) (r : List Bool) (h : P st) :
      P (run (xorWhenFalse c E) r st) := by
    intro w hw
    rw [xorWhenFalse_outside c E (hE.nodup Dn) (fun h => cD (hE.subset h)) st r w
      (fun h => hw (hE.subset h))]
    exact h w hw
  have pN (st : State) (r : List Bool) (h : P st) : P (run (notRegister D) r st) := by
    intro w hw; rw [notRegister_correct D Dn]; simp only [hw,if_false]; exact h w hw
  have pA (st : State) (r : List Bool) (h : P st) :
      P (run (addInPlace (xs++pad.take 1) D (carry.take xs.length) c) r st) := by
    have ac := addInPlace_correct (xs++pad.take 1) D (carry.take xs.length) c nda hs hk st r
      (fun w hw => by rw [h w (carryD w (List.mem_of_mem_take hw))]; exact hclean w (List.mem_of_mem_take hw))
    intro w hw; rw [ac.2.1 w hw]; exact h w hw
  have p0 : P s := fun _ _ => rfl
  unfold signedSquareRowClear
  rw [run_append,run_append,run_append,run_append]
  exact pX _ (List.take_sublist _ _) _ _ (pN _ _ (pA _ _ (pN _ _ (pX D (List.Sublist.refl D) _ _ p0)))) q hq

theorem rowsClear_keep (xs dst pad carry : List Wire) (hnd : (xs++dst++pad++carry).Nodup)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) (q : Wire) (hq : q∉dst) :
    (run (signedSquareRowsClear xs dst pad carry) m s).basis q=s.basis q := by
  induction xs generalizing dst s m q with
  | nil => rfl
  | cons c xs ih =>
    match xs, hnd, hd, hc with
    | [], _, _, _ => rfl
    | d::tail, hnd, hd, hc =>
      simp only [List.length_cons] at hd hc
      have hD : ((dst.drop 1).take ((d::tail).length+1)).Sublist dst :=
        (List.take_sublist _ _).trans (List.drop_sublist _ _)
      have nd2 : ((d::tail)++dst.drop 2++pad++carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hnd w
        have t := (List.drop_sublist 2 dst).count_le w
        simp only [List.count_cons,List.count_append] at h t ⊢
        omega
      have nd1 : (c::(d::tail)++(dst.drop 1).take ((d::tail).length+1)++pad++carry).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hnd w
        have t := hD.count_le w
        simp only [List.count_cons,List.count_append] at h t ⊢
        omega
      have carryD : ∀w∈carry,w∉dst := by
        intro w hw hD'
        have h := List.nodup_iff_count.mp hnd w
        have a := List.count_pos_iff.mpr hw
        have b := List.count_pos_iff.mpr hD'
        simp only [List.count_cons,List.count_append] at h; omega
      simp only [signedSquareRowsClear]
      rw [run_append]
      have keep1 (w : Wire) (hw : w∉dst) := ih (dst.drop 2) nd2 (by simp; omega) (by simp; omega) s
        (m.take (measurementCount (signedSquareRowsClear (d::tail) (dst.drop 2) pad carry))) hclean w
        (fun h => hw (List.mem_of_mem_drop h))
      rw [rowClear_keep c (d::tail) _ pad carry nd1 (by simp; omega) hp (by simp; omega) _ _
        (fun w hw => by rw [keep1 w (carryD w hw)]; exact hclean w hw) q (fun h => hq (hD.subset h)),
        keep1 q hq]

theorem bit1_of_diag (y0 y1 x0 x1 : Wire) (ys xt : List Wire) (st : BasisState) (X : Nat)
    (hX : regValue (x0::x1::xt) st=X)
    (h : regValue (y0::y1::ys) st=(X^2+signedDiagValue X (x0::x1::xt).length)%2^(y0::y1::ys).length) :
    st y1=(st x0 ^^ st x1) := by
  have ey : regValue (y0::y1::ys) st=(st y0).toNat+2*((st y1).toNat+2*regValue ys st) := by
    cases h0 : st y0 <;> cases h1 : st y1 <;> simp [regValue,h0,h1]
  have ex : X=(st x0).toNat+2*((st x1).toNat+2*regValue xt st) := by
    rw [← hX]; cases h0 : st x0 <;> cases h1 : st x1 <;> simp [regValue,h0,h1]
  have d4 : 4∣2^(y0::y1::ys).length := by
    have : 2^(y0::y1::ys).length=4*2^ys.length := by
      simp only [List.length_cons,pow_succ]; ring
    rw [this]; exact Nat.dvd_mul_right 4 _
  have dg : signedDiagValue X (x0::x1::xt).length%4=X%4 := by
    unfold signedDiagValue
    simp only [List.length_cons,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    generalize (2^(xt.length+1+1-1)-1-X%2^(xt.length+1+1-1))=M
    have : 2^(xt.length+1+1)=4*2^xt.length := by simp only [pow_succ]; ring
    rw [this,show M*(4*2^xt.length)=4*(M*2^xt.length) by ring,Nat.add_mul_mod_self_left]
  have xm : X%4=(st x0).toNat+2*(st x1).toNat := by
    rw [ex]; cases st x0 <;> cases st x1 <;> simp <;> omega
  have sq : X^2%4=(st x0).toNat := by
    rw [Nat.pow_mod,xm]; cases st x0 <;> cases st x1 <;> rfl
  have vm : regValue (y0::y1::ys) st%4=(st y0).toNat+2*(st y1).toNat := by
    rw [ey]; cases st y0 <;> cases st y1 <;> simp <;> omega
  have key : regValue (y0::y1::ys) st%4=(X^2+X)%4 := by
    rw [h,Nat.mod_mod_of_dvd _ d4,Nat.add_mod,dg,← Nat.add_mod]
  rw [vm,Nat.add_mod,sq,xm] at key
  cases h0 : st x0 <;> cases h1 : st x1 <;> cases hy0 : st y0 <;> cases hy1 : st y1 <;>
    simp_all

def row3 (c : Wire) (xs D pad carry : List Wire) : Program :=
  xorWhenFalse c (D.take xs.length)++addDrop (xs++pad.take 1) D (carry.take xs.length) c++xorWhenFalse c D

def rows3 : List Wire → List Wire → List Wire → List Wire → Program
  | c::d::tail, dst, pad, carry =>
      row3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry++
        signedSquareRows (d::tail) (dst.drop 2) pad carry
  | xs, dst, pad, carry => signedSquareRows xs dst pad carry

def rowClear3 (c : Wire) (xs D pad carry : List Wire) : Program :=
  xorWhenFalse c D++(notRegister D++(addDrop (xs++pad.take 1) D (carry.take xs.length) c++
    (notRegister D++xorWhenFalse c (D.take xs.length))))

def rowsClear3 : List Wire → List Wire → List Wire → List Wire → Program
  | c::d::tail, dst, pad, carry =>
      signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++
        rowClear3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry
  | xs, dst, pad, carry => signedSquareRowsClear xs dst pad carry

/-- Square make with both dead lowest carries (first signed row and diagonal) copied. -/
def tsq3 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  rows3 xs dst pad carry++signedSquareTop xs dst++
    (notRegister dst++TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++notRegister dst)

def tsqc3 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++signedSquareTop xs dst++
    rowsClear3 xs dst pad carry

/-- Shapes of the first signed row's operands. -/
theorem row_shape (x0 x1 : Wire) (xt dst pad carry : List Wire)
    (hd : dst.length=2*(x0::x1::xt).length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    ∃ y0 y1 y2 Dt a' as c0 cs, (∃ yr, dst=y0::y1::y2::yr) ∧
      (dst.drop 1).take ((x1::xt).length+1)=y1::y2::Dt ∧ (y1::y2::Dt).Sublist (dst.drop 1) ∧
      (x1::xt)++pad.take 1=x1::a'::as ∧ carry.take (x1::xt).length=c0::cs ∧
      (a'::as).length=(y2::Dt).length ∧ cs.length+1=(y2::Dt).length := by
  obtain ⟨y0,y1,y2,yr,rfl⟩ : ∃ y0 y1 y2 yr, dst=y0::y1::y2::yr := by
    match dst, hd with
    | y0::y1::y2::yr, _ => exact ⟨y0,y1,y2,yr,rfl⟩
    | [], h => simp at h
    | [_], h => simp at h; try omega
    | [_,_], h => simp at h; try omega
  obtain ⟨p0,pt,rfl⟩ : ∃ p0 pt, pad=p0::pt := by
    match pad, hp with
    | p0::pt, _ => exact ⟨p0,pt,rfl⟩
  obtain ⟨c0,cr,rfl⟩ : ∃ c0 cr, carry=c0::cr := by
    match carry, hc with
    | c0::cr, _ => exact ⟨c0,cr,rfl⟩
    | [], h => simp at h hd
  obtain ⟨a',as,has⟩ : ∃ a' as, xt++[p0]=a'::as := by
    cases xt with
    | nil => exact ⟨p0,[],rfl⟩
    | cons x xs => exact ⟨x,xs++[p0],rfl⟩
  simp only [List.length_cons] at hd hc
  refine ⟨y0,y1,y2,yr.take xt.length,a',as,c0,cr.take xt.length,⟨yr,rfl⟩,?_,?_,?_,?_,?_,?_⟩
  · simp
  · simp only [List.drop_one,List.tail_cons]
    exact List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.take_sublist _ _))
  · simp [has]
  · simp
  · have := congrArg List.length has
    simp at this ⊢; omega
  · simp at hc ⊢; omega

theorem tsq3_exists (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hc0 : regValue carry s.basis=0) :
    ∃ R, run (tsq3 xs dst pad carry cin) records s=run (TrimSquare.tsq2 xs dst pad carry cin) R s := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt, xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,Dt,a',as,c0,cs,hy0,hD,hDs,hsrc,hcy,hl,hcl⟩ := row_shape x0 x1 xt dst pad carry hd hp hc
  have hDsub : (y1::y2::Dt).Sublist dst := hDs.trans (List.drop_sublist _ _)
  have hcsub : (c0::cs).Sublist carry := by rw [← hcy]; exact List.take_sublist _ _
  have y1d : y1∈dst := hDsub.subset List.mem_cons_self
  have cnt := fun w => List.nodup_iff_count.mp hn w
  -- the four control wires are distinct
  have m1 : x1∈x0::x1::xt := by simp
  have m0 : x0∈x0::x1::xt := by simp
  have mc0 : c0∈carry := hcsub.subset List.mem_cons_self
  have disj (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈dst) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjc (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjdc (w : Wire) (h1 : w∈dst) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h; omega
  have x01 : x0≠x1 := by
    intro e; have h := cnt x0; simp only [List.count_cons,List.count_append,e] at h; simp at h; omega
  have n1 : x1≠y1 := fun e => disj x1 m1 (by rw [e]; exact y1d)
  have n2 : x1≠x0 := Ne.symm x01
  have n3 : x1≠c0 := fun e => disjc x1 m1 (by rw [e]; exact mc0)
  have n4 : y1≠x0 := fun e => disj x0 m0 (by rw [← e]; exact y1d)
  have n5 : y1≠c0 := fun e => disjdc y1 y1d (by rw [e]; exact mc0)
  have n6 : x0≠c0 := fun e => disjc x0 m0 (by rw [e]; exact mc0)
  have hnd4 : [x1,y1,x0,c0].Nodup := by
    simp [List.nodup_cons,n1,n2,n3,n4,n5,n6]
  have hrec : (c0::((a'::as)++(y2::Dt)++cs)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have t1 := hcsub.count_le w
    have t2 := ((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).count_le w
    have t3 : (a'::as).count w≤xt.count w+pad.count w := by
      have e : (x1::xt)++pad.take 1=x1::a'::as := hsrc
      have := congrArg (List.count w) e
      have tp := (List.take_sublist 1 pad).count_le w
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    simp only [List.count_cons,List.count_append] at h t1 t2 t3 ⊢
    omega
  have ha : x1∉y2::Dt := fun h => disj _ m1 (((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).subset h)
  have carry0 : ∀q∈carry,s.basis q=false := (regValue_zero _ _).mp hc0
  have dst0 : ∀q∈dst,s.basis q=false := (regValue_zero _ _).mp h0
  set D := (dst.drop 1).take ((x1::xt).length+1)
  have Dn : D.Nodup := by
    rw [hD]; exact hDsub.nodup (by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      simp only [List.count_cons,List.count_append] at h; omega)
  have x0D : x0∉D := fun h => disj _ m0 (hDsub.subset (hD ▸ h))
  set Pre := xorWhenFalse x0 (D.take (x1::xt).length)
  set Post := xorWhenFalse x0 D++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
    (signedSquareTop (x0::x1::xt) dst++(notRegister dst++
      (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++notRegister dst))))
  set K := measurementCount (addInPlace (a'::as) (y2::Dt) cs c0)
  have e3 : tsq3 (x0::x1::xt) dst pad carry cin=
      Pre++addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [tsq3,rows3,row3,Pre,Post,D,List.append_assoc]
  have e2 : TrimSquare.tsq2 (x0::x1::xt) dst pad carry cin=
      Pre++addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [TrimSquare.tsq2,signedSquareRows,signedSquareRow,Pre,Post,D,List.append_assoc]
  rw [e3,e2]
  apply glue _ _ _ _ K
  · rw [hsrc,hD,hcy]; simp [addDrop,measurementCount_append,K,measurementCount]
  · rw [hsrc,hD,hcy]; simp [addDrop,addInPlace,measurementCount_append,K,majority,eraseCarry,measurementCount]
  · intro rP rX
    have u := xorWhenFalse_correct x0 (D.take (x1::xt).length) ((List.take_sublist _ _).nodup Dn)
      (fun h => x0D (List.mem_of_mem_take h)) s rP
    rw [show xorWhenFalse x0 (D.take (x1::xt).length)=Pre from rfl] at u
    rw [u,hsrc]
    rw [hD,hcy]
    have inL (w : Wire) (h : w∈(y1::y2::Dt).take (x1::xt).length) : w∈dst :=
      hDsub.subset (List.mem_of_mem_take h)
    have y1t : y1∈(y1::y2::Dt).take (x1::xt).length := by simp
    have nx1 : x1∉(y1::y2::Dt).take (x1::xt).length := fun h => disj _ m1 (inL _ h)
    have nx0 : x0∉(y1::y2::Dt).take (x1::xt).length := fun h => disj _ m0 (inL _ h)
    apply addDrop_run x1 a' y1 y2 c0 x0 as Dt cs hnd4 hrec hl hcl ha rX
    · simp only [xorFalseBasis,y1t,nx1,nx0,if_true,if_false,dst0 y1 y1d]
      cases s.basis x0 <;> cases s.basis x1 <;> rfl
    · have : c0∉(y1::y2::Dt).take (x1::xt).length := fun h => disjdc _ (inL _ h) mc0
      simp only [xorFalseBasis,this,if_false]; exact carry0 c0 mc0
    · intro q hq
      have qc : q∈carry := hcsub.subset (List.mem_cons_of_mem _ hq)
      have : q∉(y1::y2::Dt).take (x1::xt).length := fun h => disjdc _ (inL _ h) qc
      simp only [xorFalseBasis,this,if_false]; exact carry0 q qc

theorem tsqc3_exists (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    ∃ R, run (tsqc3 xs dst pad carry cin) records s=run (TrimSquare.tsqc2 xs dst pad carry cin) R s := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt, xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,Dt,a',as,c0,cs,⟨yr,hdst⟩,hD,hDs,hsrc,hcy,hl,hcl⟩ := row_shape x0 x1 xt dst pad carry hd hp hc
  have hDsub : (y1::y2::Dt).Sublist dst := hDs.trans (List.drop_sublist _ _)
  have hcsub : (c0::cs).Sublist carry := by rw [← hcy]; exact List.take_sublist _ _
  have y1d : y1∈dst := hDsub.subset List.mem_cons_self
  have cnt := fun w => List.nodup_iff_count.mp hn w
  have m1 : x1∈x0::x1::xt := by simp
  have m0 : x0∈x0::x1::xt := by simp
  have mc0 : c0∈carry := hcsub.subset List.mem_cons_self
  have disj (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈dst) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjc (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h a; omega
  have disjdc (w : Wire) (h1 : w∈dst) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h; omega
  have disjp (w : Wire) (h1 : w∈dst) (h2 : w∈pad) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_cons,List.count_append] at h; omega
  have cind (w : Wire) (h1 : w∈dst) : w≠cin := by
    intro e; subst e; have h := cnt w; have b := List.count_pos_iff.mpr h1
    simp only [List.count_cons,List.count_append] at h; simp at h; omega
  have x01 : x0≠x1 := by
    intro e; have h := cnt x0; simp only [List.count_cons,List.count_append,e] at h; simp at h; omega
  have n1 : x1≠y1 := fun e => disj x1 m1 (by rw [e]; exact y1d)
  have n2 : x1≠x0 := Ne.symm x01
  have n3 : x1≠c0 := fun e => disjc x1 m1 (by rw [e]; exact mc0)
  have n4 : y1≠x0 := fun e => disj x0 m0 (by rw [← e]; exact y1d)
  have n5 : y1≠c0 := fun e => disjdc y1 y1d (by rw [e]; exact mc0)
  have n6 : x0≠c0 := fun e => disjc x0 m0 (by rw [e]; exact mc0)
  have hnd4 : [x1,y1,x0,c0].Nodup := by simp [List.nodup_cons,n1,n2,n3,n4,n5,n6]
  have hrec : (c0::((a'::as)++(y2::Dt)++cs)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have t1 := hcsub.count_le w
    have t2 := ((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).count_le w
    have t3 : (a'::as).count w≤xt.count w+pad.count w := by
      have := congrArg (List.count w) hsrc
      have tp := (List.take_sublist 1 pad).count_le w
      simp only [List.count_cons,List.count_append] at this ⊢; omega
    simp only [List.count_cons,List.count_append] at h t1 t2 t3 ⊢
    omega
  have ha : x1∉y2::Dt := fun h => disj _ m1 (((List.sublist_cons_self y1 (y2::Dt)).trans hDsub).subset h)
  have carry0 : ∀q∈carry,s.basis q=false := (regValue_zero _ _).mp hc0
  set D := (dst.drop 1).take ((x1::xt).length+1)
  have Dn : D.Nodup := by
    rw [hD]; exact hDsub.nodup (by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      simp only [List.count_cons,List.count_append] at h; omega)
  have x0D : x0∉D := fun h => disj _ m0 (hDsub.subset (hD ▸ h))
  have inD (w : Wire) (h : w∈D) : w∈dst := hDsub.subset (hD ▸ h)
  have y1D : y1∈D := by rw [hD]; exact List.mem_cons_self
  -- the diagonal add, as the library program
  have ndDiag : (cin::(x0::x1::xt)++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have h := cnt w
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have diagE : ∀ r1, ∃ r1', run (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst
      (carry.take (dst.length-1)) cin) r1 s=run (mappedDiagAdd (x0::x1::xt) dst carry cin) r1' s := by
    intro r1
    obtain ⟨z0,b',bits,y,y',ys,c,cs',hz0,hdiag,hdst',hcar,_⟩ := TrimSquare.diag_shape (x0::x1::xt) dst carry hx hd hc
    rw [show z0=x0 by simpa using hz0.symm] at hdiag
    subst hdst'
    obtain ⟨hnd4',hrec',hsrc',hl',hcl',ha',hmem',hcin'⟩ :=
      TrimSquare.diag_side cin x0 (x1::xt) y y' ys pad carry b' bits c cs' hn hd hdiag hcar hc
    have sy := TrimSquare.bit0_of_square y x0 (y'::ys) (x1::xt) s.basis hval
    unfold mappedDiagAdd; rw [hdiag,hcar]
    exact ⟨_,TrimSquare.drop2_run x0 y y' c cin b' bits ys cs' hnd4' hrec' hsrc' hl' hcl' ha' r1 s
      (by rw [sy]; simp) (carry0 c (hmem' c List.mem_cons_self))
      (fun q hq => carry0 q (hmem' q (List.mem_cons_of_mem _ hq)))⟩
  set Pre := TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++
    (signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 D++notRegister D)))
  set Post := notRegister D++xorWhenFalse x0 (D.take (x1::xt).length)
  set K := measurementCount (addInPlace (a'::as) (y2::Dt) cs c0)
  have e3 : tsqc3 (x0::x1::xt) dst pad carry cin=
      Pre++addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [tsqc3,rowsClear3,rowClear3,Pre,Post,D,List.append_assoc]
  have e2 : TrimSquare.tsqc2 (x0::x1::xt) dst pad carry cin=
      Pre++addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [TrimSquare.tsqc2,signedSquareRowsClear,signedSquareRowClear,Pre,Post,D,List.append_assoc]
  rw [e3,e2]
  apply glue _ _ _ _ K
  · rw [hsrc,hD,hcy]; simp [addDrop,measurementCount_append,K,measurementCount]
  · rw [hsrc,hD,hcy]; simp [addDrop,addInPlace,measurementCount_append,K,majority,eraseCarry,measurementCount]
  · intro rP rX
    simp only [Pre]
    rw [run_append,run_append,run_append,run_append]
    generalize hr1 : List.take _ rP=r1
    obtain ⟨r1',e1⟩ := diagE r1
    rw [e1]
    have dc := mappedDiagAdd_correct cin (x0::x1::xt) dst carry ndDiag (by simp) hd hc s r1' hc0 hi0
    generalize hv1 : run (mappedDiagAdd (x0::x1::xt) dst carry cin) r1' s=v1
    rw [hv1] at dc
    have k1 (w : Wire) (hw : w∉dst) : v1.basis w=s.basis w := dc.2.2 w hw
    have b1 : v1.basis y1=(s.basis x0 ^^ s.basis x1) := by
      have xsame : regValue (x0::x1::xt) v1.basis=regValue (x0::x1::xt) s.basis :=
        regValue_congr _ _ _ (fun q hq => k1 q (fun h => disj q hq h))
      have val := dc.2.1
      rw [hval,hdst] at val
      have := bit1_of_diag y0 y1 x0 x1 (y2::yr) xt v1.basis (regValue (x0::x1::xt) s.basis) xsame
        (by rw [val])
      rw [this,k1 x0 (fun h => disj _ m0 h),k1 x1 (fun h => disj _ m1 h)]
    generalize hv2 : run (signedSquareTop (x0::x1::xt) dst) _ v1=v2
    have k2 (w : Wire) (hw : w∉dst) : v2.basis w=s.basis w := by rw [← hv2,top_keep _ _ _ _ w hw,k1 w hw]
    have b2 : v2.basis y1=v1.basis y1 := by
      rw [← hv2]
      apply run_preserves_outside
      rw [hdst]
      change y1∉wires (signedSquareTop (x1::xt) (y2::yr))
      intro h
      have := signedSquareTop_wires_subset (x1::xt) (y2::yr) h
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at this
      have nd := hn; rw [hdst] at nd
      simp only [List.cons_append,List.nodup_cons,List.nodup_append,List.mem_append,List.mem_cons,not_or] at nd
      grind
    have hd2 : (dst.drop 2).length=2*(x1::xt).length := by simp [hd]; omega
    have nd2 : ((x1::xt)++dst.drop 2++pad++carry).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      have t := (List.drop_sublist 2 dst).count_le w
      simp only [List.count_cons,List.count_append] at h t ⊢; omega
    generalize hv3 : run (signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry) _ v2=v3
    have k3 (w : Wire) (hw : w∉dst) : v3.basis w=s.basis w := by
      rw [← hv3,rowsClear_keep (x1::xt) (dst.drop 2) pad carry nd2 hd2 hp (by simp at hd hc ⊢; omega) v2 _
        (fun q hq => by rw [k2 q (fun h => disjdc q h hq)]; exact carry0 q hq) w
        (fun h => hw (List.mem_of_mem_drop h)),k2 w hw]
    have b3 : v3.basis y1=v2.basis y1 := by
      rw [← hv3]
      apply run_preserves_outside
      intro h
      have := (signedSquareRows_wires_subset (x1::xt) (dst.drop 2) pad carry hd2 (Or.inr hp)
        (by simp at hd hc ⊢; omega)).2 h
      simp only [List.mem_toFinset,List.mem_append] at this
      rcases this with ((h1|h1)|h1)|h1
      · exact disj y1 (List.mem_cons_of_mem _ h1) y1d
      · rw [hdst] at h1 hn; simp at h1
        simp only [List.cons_append,List.nodup_cons,List.nodup_append,List.mem_append,List.mem_cons,not_or] at hn
        grind
      · exact disjp y1 y1d h1
      · exact disjdc y1 y1d h1
    generalize hv4 : run (xorWhenFalse x0 D) _ v3=v4
    have xw : ∀ r, run (xorWhenFalse x0 D) r v3=⟨v3.phase,xorFalseBasis x0 D v3.basis⟩ :=
      fun r => xorWhenFalse_correct x0 D Dn x0D v3 r
    rw [xw] at hv4
    generalize hv5 : run (notRegister D) _ v4=v5
    rw [notRegister_correct D Dn] at hv5
    have k5 (w : Wire) (hw : w∉dst) : v5.basis w=s.basis w := by
      have wD : w∉D := fun h => hw (inD w h)
      rw [← hv5]; simp only [wD,if_false]; rw [← hv4]; simp only [xorFalseBasis,wD,if_false]; exact k3 w hw
    have b5 : v5.basis y1=s.basis x1 := by
      rw [← hv5]; simp only [y1D,if_true]; rw [← hv4]; simp only [xorFalseBasis,y1D,if_true]
      rw [b3,b2,b1,k3 x0 (fun h => disj _ m0 h)]
      cases s.basis x0 <;> cases s.basis x1 <;> rfl
    rw [hsrc,hD,hcy]
    apply addDrop_run x1 a' y1 y2 c0 x0 as Dt cs hnd4 hrec hl hcl ha rX
    · rw [b5,k5 x1 (fun h => disj _ m1 h),k5 x0 (fun h => disj _ m0 h)]; simp
    · rw [k5 c0 (fun h => disjdc _ h mc0)]; exact carry0 c0 mc0
    · intro q hq
      have qc : q∈carry := hcsub.subset (List.mem_cons_of_mem _ hq)
      rw [k5 q (fun h => disjdc _ h qc)]; exact carry0 q qc

theorem addDrop_gen (x y carry : List Wire) (cin : Wire) :
    addDrop x y carry cin=addInPlace x y carry cin ∨
    ∃ a a' as b b' bs c cs, x=a::a'::as ∧ y=b::b'::bs ∧ carry=c::cs := by
  unfold addDrop
  split
  · rename_i a a' as b b' bs c cs
    right; exact ⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · left; rfl

theorem addDrop_physical_gen (x y carry : List Wire) (cin : Wire)
    (h : GatePhysical (addInPlace x y carry cin)) : GatePhysical (addDrop x y carry cin) := by
  rcases addDrop_gen x y carry cin with e|⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · rw [e]; exact h
  · have hac : GatePhysical [Instr.CX a c] := by
      simp only [addInPlace,gatePhysical_append] at h
      intro i hi
      simp only [List.mem_singleton] at hi; subst hi
      exact h.1.1.1 _ (by simp [majority])
    simp only [addDrop,addInPlace,gatePhysical_append] at h ⊢
    exact ⟨⟨⟨hac,h.1.1.2⟩,hac⟩,h.2⟩

theorem addDrop_wires_gen (x y carry : List Wire) (cin : Wire) :
    wires (addDrop x y carry cin)⊆wires (addInPlace x y carry cin) := by
  rcases addDrop_gen x y carry cin with e|⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · rw [e]
  · simp only [addDrop,addInPlace,wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with ((hq|hq)|hq)|hq
    · left; left; left; simp [wires,majority,Instr.wires] at hq ⊢; tauto
    · exact Or.inl (Or.inl (Or.inr hq))
    · left; left; left; simp [wires,majority,Instr.wires] at hq ⊢; tauto
    · exact Or.inr hq

theorem addDrop_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addDrop x y carry cin)≤Challenge.gateSlots (addInPlace x y carry cin) := by
  rcases addDrop_gen x y carry cin with e|⟨a,a',as,b,b',bs,c,cs,rfl,rfl,rfl⟩
  · rw [e]
  · simp only [addDrop,addInPlace,Challenge.gateSlots_append]
    simp [Challenge.gateSlots,Challenge.instructionSlots,majority,eraseCarry]
    omega

theorem tsq3_form (xs dst pad carry : List Wire) (cin : Wire) :
    (tsq3 xs dst pad carry cin=TrimSquare.tsq2 xs dst pad carry cin ∧
      tsqc3 xs dst pad carry cin=TrimSquare.tsqc2 xs dst pad carry cin) ∨
    ∃ A B A' B' x y cy c,
      tsq3 xs dst pad carry cin=A++addDrop x y cy c++B ∧
      TrimSquare.tsq2 xs dst pad carry cin=A++addInPlace x y cy c++B ∧
      tsqc3 xs dst pad carry cin=A'++addDrop x y cy c++B' ∧
      TrimSquare.tsqc2 xs dst pad carry cin=A'++addInPlace x y cy c++B' := by
  match xs with
  | [] => left; exact ⟨rfl,rfl⟩
  | [_] => left; exact ⟨rfl,rfl⟩
  | c::d::tail =>
    right
    refine ⟨xorWhenFalse c (((dst.drop 1).take ((d::tail).length+1)).take (d::tail).length),
      xorWhenFalse c ((dst.drop 1).take ((d::tail).length+1))++signedSquareRows (d::tail) (dst.drop 2) pad carry++
        signedSquareTop (c::d::tail) dst++(notRegister dst++
          TrimSquare.drop2 (mappedDiagonal (c::d::tail)) dst (carry.take (dst.length-1)) cin++notRegister dst),
      TrimSquare.drop2 (mappedDiagonal (c::d::tail)) dst (carry.take (dst.length-1)) cin++
        signedSquareTop (c::d::tail) dst++signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++
        xorWhenFalse c ((dst.drop 1).take ((d::tail).length+1))++notRegister ((dst.drop 1).take ((d::tail).length+1)),
      notRegister ((dst.drop 1).take ((d::tail).length+1))++
        xorWhenFalse c (((dst.drop 1).take ((d::tail).length+1)).take (d::tail).length),
      (d::tail)++pad.take 1,(dst.drop 1).take ((d::tail).length+1),carry.take (d::tail).length,c,
      ?_,?_,?_,?_⟩
    · simp only [tsq3,rows3,row3,List.append_assoc]
    · simp only [TrimSquare.tsq2,signedSquareRows,signedSquareRow,List.append_assoc]
    · simp only [tsqc3,rowsClear3,rowClear3,List.append_assoc]
    · simp only [TrimSquare.tsqc2,signedSquareRowsClear,signedSquareRowClear,List.append_assoc]

theorem tsq3_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsq3 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsq3 xs dst pad carry cin) records s).basis=(regValue xs s.basis)^2 ∧
    ∀q,q∉dst → (run (tsq3 xs dst pad carry cin) records s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := tsq3_exists cin xs dst pad carry hn hx hd hp hc s records h0 hc0
  rw [hR]
  exact TrimSquare.tsq2_correct cin xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0 hi0

theorem tsqc3_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqc3 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqc3 xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (tsqc3 xs dst pad carry cin) records s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := tsqc3_exists cin xs dst pad carry hn hx hd hp hc s records hval hc0 hi0
  rw [hR]
  exact TrimSquare.tsqc2_correct cin xs dst pad carry hn hx hd hp hc s R hval hp0 hc0 hi0

theorem tsq3_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    (toffoliCount (tsq3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3 ∧
      measurementCount (tsq3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3) ∧
    (toffoliCount (tsqc3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3 ∧
      measurementCount (tsqc3 xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3) := by
  have h := TrimSquare.tsq2_counts xs dst pad carry cin hx hd hp hc
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt, xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,Dt,a',as,c0,cs,_,hD,_,hsrc,hcy,_,_⟩ := row_shape x0 x1 xt dst pad carry hd hp hc
  have cA : toffoliCount (addDrop (x1::a'::as) (y1::y2::Dt) (c0::cs) x0)+1=
      toffoliCount (addInPlace (x1::a'::as) (y1::y2::Dt) (c0::cs) x0) ∧
      measurementCount (addDrop (x1::a'::as) (y1::y2::Dt) (c0::cs) x0)+1=
      measurementCount (addInPlace (x1::a'::as) (y1::y2::Dt) (c0::cs) x0) := by
    simp only [addDrop,addInPlace,toffoliCount_append,measurementCount_append]
    simp [majority,eraseCarry,toffoliCount,measurementCount]; omega
  have e1 : tsq3 (x0::x1::xt) dst pad carry cin=
      xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length)++
        addDrop ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
        (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
        (signedSquareTop (x0::x1::xt) dst++(notRegister dst++
          (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++notRegister dst))))) := by
    simp only [tsq3,rows3,row3,List.append_assoc]
  have e2 : TrimSquare.tsq2 (x0::x1::xt) dst pad carry cin=
      xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length)++
        addInPlace ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
        (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
        (signedSquareTop (x0::x1::xt) dst++(notRegister dst++
          (TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++notRegister dst))))) := by
    simp only [TrimSquare.tsq2,signedSquareRows,signedSquareRow,List.append_assoc]
  have f1 : tsqc3 (x0::x1::xt) dst pad carry cin=
      TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++
      (signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(notRegister ((dst.drop 1).take ((x1::xt).length+1))++
      (addDrop ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
      (notRegister ((dst.drop 1).take ((x1::xt).length+1))++
        xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length))))))) := by
    simp only [tsqc3,rowsClear3,rowClear3,List.append_assoc]
  have f2 : TrimSquare.tsqc2 (x0::x1::xt) dst pad carry cin=
      TrimSquare.drop2 (mappedDiagonal (x0::x1::xt)) dst (carry.take (dst.length-1)) cin++
      (signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 ((dst.drop 1).take ((x1::xt).length+1))++(notRegister ((dst.drop 1).take ((x1::xt).length+1))++
      (addInPlace ((x1::xt)++pad.take 1) ((dst.drop 1).take ((x1::xt).length+1)) (carry.take (x1::xt).length) x0++
      (notRegister ((dst.drop 1).take ((x1::xt).length+1))++
        xorWhenFalse x0 (((dst.drop 1).take ((x1::xt).length+1)).take (x1::xt).length))))))) := by
    simp only [TrimSquare.tsqc2,signedSquareRowsClear,signedSquareRowClear,List.append_assoc]
  rw [e1,f1]; rw [e2,f2] at h
  rw [hsrc,hD,hcy] at h ⊢
  simp only [toffoliCount_append,measurementCount_append] at h ⊢
  omega

theorem tsq3_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin :: xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (tsq3 xs dst pad carry cin) ∧ GatePhysical (tsqc3 xs dst pad carry cin) := by
  have h := TrimSquare.tsq2_physical xs dst pad carry cin hn
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact h
  · rw [e2,e4] at h; rw [e1,e3]
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨⟨h.1.1.1,addDrop_physical_gen _ _ _ _ h.1.1.2⟩,h.1.2⟩,
      ⟨⟨h.2.1.1,addDrop_physical_gen _ _ _ _ h.2.1.2⟩,h.2.2⟩⟩

theorem tsq3_wires_subset (xs dst pad carry : List Wire) (cin : Wire)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    wires (tsq3 xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset ∧
    wires (tsqc3 xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
  have h := TrimSquare.tsq2_wires_subset xs dst pad carry cin hd hp hc
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact h
  · rw [e2,e4] at h; rw [e1,e3]
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨⟨h.1.1.1,(addDrop_wires_gen _ _ _ _).trans h.1.1.2⟩,h.1.2⟩,
      ⟨⟨h.2.1.1,(addDrop_wires_gen _ _ _ _).trans h.2.1.2⟩,h.2.2⟩⟩

theorem tsq3_gateSlots_le (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsq3 xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 ∧
    Challenge.gateSlots (tsqc3 xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 := by
  have h := TrimSquare.tsq2_gateSlots_le xs dst pad carry cin
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact h
  · rw [e2,e4] at h; rw [e1,e3]
    have d := addDrop_slots x y cy c
    simp only [Challenge.gateSlots_append] at h ⊢
    omega

theorem tsq3_wires_le (xs dst pad carry : List Wire) (cin : Wire) :
    wires (tsq3 xs dst pad carry cin)⊆wires (TrimSquare.tsq2 xs dst pad carry cin) ∧
    wires (tsqc3 xs dst pad carry cin)⊆wires (TrimSquare.tsqc2 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨subset_refl _,subset_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_wires_gen x y cy c
    simp only [wires_append]
    constructor
    · exact Finset.union_subset_union (Finset.union_subset_union (subset_refl _) d) (subset_refl _)
    · exact Finset.union_subset_union (Finset.union_subset_union (subset_refl _) d) (subset_refl _)

theorem tsq3_physical_of (xs dst pad carry : List Wire) (cin : Wire)
    (h1 : GatePhysical (TrimSquare.tsq2 xs dst pad carry cin))
    (h2 : GatePhysical (TrimSquare.tsqc2 xs dst pad carry cin)) :
    GatePhysical (tsq3 xs dst pad carry cin) ∧ GatePhysical (tsqc3 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨h1,h2⟩
  · rw [e2] at h1; rw [e4] at h2; rw [e1,e3]
    simp only [gatePhysical_append] at h1 h2 ⊢
    exact ⟨⟨⟨h1.1.1,addDrop_physical_gen _ _ _ _ h1.1.2⟩,h1.2⟩,
      ⟨⟨h2.1.1,addDrop_physical_gen _ _ _ _ h2.1.2⟩,h2.2⟩⟩

end ECDSAAdd.Entrant.TrimSquare3

namespace ECDSAAdd.Entrant
open Arithmetic

theorem sq_plain3_make (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqMake xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsq3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsq3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,trivial,fun q h _ => r.2.2 q h⟩

theorem sq_plain3_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare3.tsqc3 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare3.tsqc3_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩

end ECDSAAdd.Entrant
