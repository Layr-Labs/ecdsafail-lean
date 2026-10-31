import ECDSAAdd.Submission.Entrant.EndpointD
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Arithmetic.MappedSignedSquare
import ECDSAAdd.Arithmetic.MappedSquarePhysical
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Framework.RecordPadding
import ECDSAAdd.Baselines.SlotSignedSquare
import ECDSAAdd.Submission.Entrant.MainPre


/-! TrimRow: the lowest carry of the FIRST signed row of every leaf square is a copy.

Adapted from debias's TrimSquare3 (first signed-row carry) to the unnormalized signed-row
square `rows ++ top` used by the balanced diagonal-sharing leaves (`DiagSq.rawMake/rawClear`).
In the make, `dst = 0` on entry, so after the frame `D0 = !x0` and the first majority's
Toffoli `(D0 ^ x1) & (x0 ^ x1)` is always 0; its carry is `x1`. In the clear, `dst[1]`
is bit 1 of `x^2 + signedDiagValue x n`, i.e. `x0 ^ x1`; the clear frame turns it into `x1`,
so the AND is 0 again. Each such majority/erase pair becomes one CX. -/

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.TrimRow
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


/-- Unnormalized signed-row square make with the first-row lowest carry copied. -/
def mk (xs dst pad carry : List Wire) : Program :=
  rows3 xs dst pad carry++signedSquareTop xs dst

/-- Its clear. -/
def cl (xs dst pad carry : List Wire) : Program :=
  signedSquareTop xs dst++rowsClear3 xs dst pad carry

/-- Shapes of the first signed row's operands (carry only needs `xs.length-1` wires). -/
theorem row_shape (x0 x1 : Wire) (xt dst pad carry : List Wire)
    (hd : dst.length=2*(x0::x1::xt).length) (hp : 1≤pad.length)
    (hc : (x0::x1::xt).length-1≤carry.length) :
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
    | [], h => simp at h
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

theorem mk_exists (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hc0 : regValue carry s.basis=0) :
    ∃ R, run (mk xs dst pad carry) records s=
      run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) R s := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt, xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,Dt,a',as,c0,cs,hy0,hD,hDs,hsrc,hcy,hl,hcl⟩ := row_shape x0 x1 xt dst pad carry hd hp hc
  have hDsub : (y1::y2::Dt).Sublist dst := hDs.trans (List.drop_sublist _ _)
  have hcsub : (c0::cs).Sublist carry := by rw [← hcy]; exact List.take_sublist _ _
  have y1d : y1∈dst := hDsub.subset List.mem_cons_self
  have cnt := fun w => List.nodup_iff_count.mp hn w
  have m1 : x1∈x0::x1::xt := by simp
  have m0 : x0∈x0::x1::xt := by simp
  have mc0 : c0∈carry := hcsub.subset List.mem_cons_self
  have disj (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈dst) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_append] at h; omega
  have disjc (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_append] at h; omega
  have disjdc (w : Wire) (h1 : w∈dst) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_append] at h; omega
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
    signedSquareTop (x0::x1::xt) dst)
  set K := measurementCount (addInPlace (a'::as) (y2::Dt) cs c0)
  have e3 : mk (x0::x1::xt) dst pad carry=
      Pre++addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [mk,rows3,row3,Pre,Post,D,List.append_assoc]
  have e2 : signedSquareRows (x0::x1::xt) dst pad carry++signedSquareTop (x0::x1::xt) dst=
      Pre++addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [signedSquareRows,signedSquareRow,Pre,Post,D,List.append_assoc]
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

theorem cl_exists (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (records : List Bool)
    (hval : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hc0 : regValue carry s.basis=0) :
    ∃ R, run (cl xs dst pad carry) records s=
      run (signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry) R s := by
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
    simp only [List.count_append] at h; omega
  have disjc (w : Wire) (h1 : w∈x0::x1::xt) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_append] at h; omega
  have disjdc (w : Wire) (h1 : w∈dst) (h2 : w∈carry) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_append] at h; omega
  have disjp (w : Wire) (h1 : w∈dst) (h2 : w∈pad) : False := by
    have h := cnt w; have a := List.count_pos_iff.mpr h1; have b := List.count_pos_iff.mpr h2
    simp only [List.count_append] at h; omega
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
  have b1 : s.basis y1=(s.basis x0 ^^ s.basis x1) := by
    have lt := regValue_lt dst s.basis
    have val : regValue (y0::y1::y2::yr) s.basis=((regValue (x0::x1::xt) s.basis)^2+
        signedDiagValue (regValue (x0::x1::xt) s.basis) (x0::x1::xt).length)%2^(y0::y1::y2::yr).length := by
      rw [← hdst,← hval,Nat.mod_eq_of_lt lt]
    exact bit1_of_diag y0 y1 x0 x1 (y2::yr) xt s.basis _ rfl val
  set Pre := signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 D++notRegister D))
  set Post := notRegister D++xorWhenFalse x0 (D.take (x1::xt).length)
  set K := measurementCount (addInPlace (a'::as) (y2::Dt) cs c0)
  have e3 : cl (x0::x1::xt) dst pad carry=
      Pre++addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [cl,rowsClear3,rowClear3,Pre,Post,D,List.append_assoc]
  have e2 : signedSquareTop (x0::x1::xt) dst++signedSquareRowsClear (x0::x1::xt) dst pad carry=
      Pre++addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [signedSquareRowsClear,signedSquareRowClear,Pre,Post,D,List.append_assoc]
  rw [e3,e2]
  apply glue _ _ _ _ K
  · rw [hsrc,hD,hcy]; simp [addDrop,measurementCount_append,K,measurementCount]
  · rw [hsrc,hD,hcy]; simp [addDrop,addInPlace,measurementCount_append,K,majority,eraseCarry,measurementCount]
  · intro rP rX
    simp only [Pre]
    rw [run_append,run_append,run_append]
    generalize hv2 : run (signedSquareTop (x0::x1::xt) dst) _ s=v2
    have k2 (w : Wire) (hw : w∉dst) : v2.basis w=s.basis w := by rw [← hv2,top_keep _ _ _ _ w hw]
    have b2 : v2.basis y1=s.basis y1 := by
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

theorem form (xs dst pad carry : List Wire) :
    (mk xs dst pad carry=signedSquareRows xs dst pad carry++signedSquareTop xs dst ∧
      cl xs dst pad carry=signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry) ∨
    ∃ A B A' B' x y cy c,
      mk xs dst pad carry=A++addDrop x y cy c++B ∧
      signedSquareRows xs dst pad carry++signedSquareTop xs dst=A++addInPlace x y cy c++B ∧
      cl xs dst pad carry=A'++addDrop x y cy c++B' ∧
      signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry=A'++addInPlace x y cy c++B' := by
  match xs with
  | [] => left; exact ⟨rfl,rfl⟩
  | [_] => left; exact ⟨rfl,rfl⟩
  | c::d::tail =>
    right
    refine ⟨xorWhenFalse c (((dst.drop 1).take ((d::tail).length+1)).take (d::tail).length),
      xorWhenFalse c ((dst.drop 1).take ((d::tail).length+1))++signedSquareRows (d::tail) (dst.drop 2) pad carry++
        signedSquareTop (c::d::tail) dst,
      signedSquareTop (c::d::tail) dst++signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++
        xorWhenFalse c ((dst.drop 1).take ((d::tail).length+1))++notRegister ((dst.drop 1).take ((d::tail).length+1)),
      notRegister ((dst.drop 1).take ((d::tail).length+1))++
        xorWhenFalse c (((dst.drop 1).take ((d::tail).length+1)).take (d::tail).length),
      (d::tail)++pad.take 1,(dst.drop 1).take ((d::tail).length+1),carry.take (d::tail).length,c,
      ?_,?_,?_,?_⟩
    · simp only [mk,rows3,row3,List.append_assoc]
    · simp only [signedSquareRows,signedSquareRow,List.append_assoc]
    · simp only [cl,rowsClear3,rowClear3,List.append_assoc]
    · simp only [signedSquareRowsClear,signedSquareRowClear,List.append_assoc]

theorem counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (mk xs dst pad carry)+1=toffoliCount (signedSquareRows xs dst pad carry++signedSquareTop xs dst) ∧
      measurementCount (mk xs dst pad carry)+1=measurementCount (signedSquareRows xs dst pad carry++signedSquareTop xs dst)) ∧
    (toffoliCount (cl xs dst pad carry)+1=toffoliCount (signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry) ∧
      measurementCount (cl xs dst pad carry)+1=measurementCount (signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry)) := by
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
  set D := (dst.drop 1).take ((x1::xt).length+1)
  have e1 : mk (x0::x1::xt) dst pad carry=
      xorWhenFalse x0 (D.take (x1::xt).length)++
        addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++
        (xorWhenFalse x0 D++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
          signedSquareTop (x0::x1::xt) dst)) := by
    simp only [mk,rows3,row3,D,List.append_assoc]
  have e2 : signedSquareRows (x0::x1::xt) dst pad carry++signedSquareTop (x0::x1::xt) dst=
      xorWhenFalse x0 (D.take (x1::xt).length)++
        addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++
        (xorWhenFalse x0 D++(signedSquareRows (x1::xt) (dst.drop 2) pad carry++
          signedSquareTop (x0::x1::xt) dst)) := by
    simp only [signedSquareRows,signedSquareRow,D,List.append_assoc]
  have f1 : cl (x0::x1::xt) dst pad carry=
      signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 D++(notRegister D++
      (addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++
      (notRegister D++xorWhenFalse x0 (D.take (x1::xt).length)))))) := by
    simp only [cl,rowsClear3,rowClear3,D,List.append_assoc]
  have f2 : signedSquareTop (x0::x1::xt) dst++signedSquareRowsClear (x0::x1::xt) dst pad carry=
      signedSquareTop (x0::x1::xt) dst++(signedSquareRowsClear (x1::xt) (dst.drop 2) pad carry++
      (xorWhenFalse x0 D++(notRegister D++
      (addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++
      (notRegister D++xorWhenFalse x0 (D.take (x1::xt).length)))))) := by
    simp only [signedSquareRowsClear,signedSquareRowClear,D,List.append_assoc]
  rw [e1,e2,f1,f2]
  rw [hsrc,hD,hcy]
  simp only [toffoliCount_append,measurementCount_append]
  omega

theorem physical (xs dst pad carry : List Wire)
    (h1 : GatePhysical (signedSquareRows xs dst pad carry++signedSquareTop xs dst))
    (h2 : GatePhysical (signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry)) :
    GatePhysical (mk xs dst pad carry) ∧ GatePhysical (cl xs dst pad carry) := by
  rcases form xs dst pad carry with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨h1,h2⟩
  · rw [e2] at h1; rw [e4] at h2; rw [e1,e3]
    simp only [gatePhysical_append] at h1 h2 ⊢
    exact ⟨⟨⟨h1.1.1,addDrop_physical_gen _ _ _ _ h1.1.2⟩,h1.2⟩,
      ⟨⟨h2.1.1,addDrop_physical_gen _ _ _ _ h2.1.2⟩,h2.2⟩⟩

theorem wires_sub (xs dst pad carry : List Wire) :
    wires (mk xs dst pad carry)⊆wires (signedSquareRows xs dst pad carry++signedSquareTop xs dst) ∧
    wires (cl xs dst pad carry)⊆wires (signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry) := by
  rcases form xs dst pad carry with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨subset_refl _,subset_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_wires_gen x y cy c
    simp only [wires_append]
    constructor
    · exact Finset.union_subset_union (Finset.union_subset_union (subset_refl _) d) (subset_refl _)
    · exact Finset.union_subset_union (Finset.union_subset_union (subset_refl _) d) (subset_refl _)

theorem slots (xs dst pad carry : List Wire) :
    Challenge.gateSlots (mk xs dst pad carry)≤
      Challenge.gateSlots (signedSquareRows xs dst pad carry++signedSquareTop xs dst) ∧
    Challenge.gateSlots (cl xs dst pad carry)≤
      Challenge.gateSlots (signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry) := by
  rcases form xs dst pad carry with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨le_refl _,le_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_slots x y cy c
    simp only [Challenge.gateSlots_append]
    omega

end ECDSAAdd.Entrant.TrimRow


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

set_option Elab.async false

-- Known-output sum cleanup.
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.SumCleanup
open Arithmetic

theorem read_add (xs ys carry : List Wire) (cin : Wire) :
    mappedAdd (mappedRead xs false) ys carry cin=addInPlace xs ys carry cin := by
  induction xs generalizing ys carry cin with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases xs with
    | nil => cases ys with
      | nil => rfl
      | cons y ys => cases ys <;> rfl
    | cons a' xs =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        cases ys with
        | nil => rfl
        | cons b' ys =>
          cases carry with
          | nil => rfl
          | cons c cs =>
            simp only [mappedRead,List.map_cons,mappedAdd,mappedMajority,
              mappedEraseCarry,mappedSum,Bool.false_eq_true,if_false,addInPlace]
            rw [←ih (b'::ys) cs c]
            rfl

def sub (xs ys expected carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++KnownOutputAdder.program (mappedRead xs false) ys
    (mappedRead expected true) carry cin++notRegister ys

theorem sub_eq (xs ys expected carry : List Wire) (cin : Wire)
    (hn : (cin::ys++carry).Nodup)
    (hx : ∀q∈xs,q∉cin::ys++carry) (he : ∀q∈expected,q∉cin::ys++carry)
    (hl : xs.length=ys.length) (hel : expected.length=ys.length)
    (hcl : carry.length+1=ys.length) (s : State) (m : List Bool)
    (hc0 : ∀q∈carry,s.basis q=false) (hi0 : s.basis cin=false)
    (hval : regValue ys s.basis=regValue xs s.basis+regValue expected s.basis) :
    run (sub xs ys expected carry cin) m s=run (subInPlace xs ys carry cin) m s := by
  let u := run (notRegister ys) [] s
  have nd : ys.Nodup := (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
  have yc : cin∉ys := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : ys.Disjoint carry := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
  have out (q : Wire) (hq : q∉ys) : u.basis q=s.basis q := by
    dsimp only [u]
    rw [notRegister_correct ys nd]
    simp [hq]
  have ux : regValue xs u.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => out q (fun h => hx q hq (by simp [h])))
  have ue : regValue expected u.basis=regValue expected s.basis :=
    regValue_congr _ _ _ (fun q hq => out q (fun h => he q hq (by simp [h])))
  have uy : regValue ys u.basis=2^ys.length-1-regValue ys s.basis := by
    dsimp only [u]
    rw [notRegister_correct ys nd]
    have e : regValue ys (fun w => if w∈ys then !s.basis w else s.basis w)=regValue ys (fun w => !s.basis w) :=
      regValue_congr _ _ _ (fun q hq => by simp [hq])
    rw [e,regValue_complement]
  have ui : u.basis cin=false := (out cin yc).trans hi0
  have uc : ∀q∈carry,u.basis q=false := by
    intro q hq
    exact (out q (fun h => List.disjoint_left.mp dis h hq)).trans (hc0 q hq)
  have known : KnownOutputAdder.Ready (mappedRead xs false) (mappedRead expected true) ys
      (u.basis cin) u.basis := by
    apply KnownOutputAdder.ready_of_value
    · exact (mappedRead_length xs false).trans hl
    · exact (mappedRead_length expected true).trans hel
    rw [mappedRead_complement,mappedRead_value,hel,ux,ue,uy,ui]
    simp only [Bool.toNat_false,Nat.add_zero]
    have hy := regValue_lt ys s.basis
    have hp := Nat.two_pow_pos ys.length
    have small : regValue xs s.basis+(2^ys.length-1-regValue ys s.basis)<2^ys.length := by omega
    rw [Nat.mod_eq_of_lt small]
    omega
  have eq (record : List Bool) := KnownOutputAdder.program_eq_mappedAdd (mappedRead xs false)
    (mappedRead expected true) ys carry cin hn (by simpa only [mappedRead_wires] using hx)
    (by simpa only [mappedRead_wires] using he) ((mappedRead_length xs false).trans hl) ((mappedRead_length expected true).trans hel) hcl u record uc known
  simp only [read_add] at eq
  have mz := (notRegister_counts ys).2
  have counts := KnownOutputAdder.program_counts (mappedRead xs false) (mappedRead expected true)
    ys carry cin ((mappedRead_length xs false).trans hl) ((mappedRead_length expected true).trans hel) hcl
  have old := addInPlace_counts xs ys carry cin hl hcl
  have pre : run (notRegister ys) m s=u := by
    rw [←run_take (notRegister ys) m s,mz,List.take_zero]
  simp only [sub,subInPlace,List.append_assoc,run_append,run_take,mz,List.drop_zero,counts.2,old.2,pre]
  simp only [List.take_zero]
  exact congrArg (fun t => run (notRegister ys) (m.drop (ys.length-1)) t) (eq (m.take (ys.length-1)))

end ECDSAAdd.Entrant.SumCleanup


namespace ECDSAAdd.Entrant.SumCleanup
open Arithmetic Challenge

theorem sub_counts (xs ys expected carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (he : expected.length=ys.length)
    (hc : carry.length+1=ys.length) :
    toffoliCount (sub xs ys expected carry cin)=0 ∧
    measurementCount (sub xs ys expected carry cin)=ys.length-1 := by
  have a:=KnownOutputAdder.program_counts (mappedRead xs false) (mappedRead expected true) ys carry cin
    ((mappedRead_length _ _).trans hl) ((mappedRead_length _ _).trans he) hc
  have b:=notRegister_counts ys
  simp only [sub,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2]
  simp

theorem sub_support (xs ys expected carry : List Wire) (cin : Wire) :
    wires (sub xs ys expected carry cin)⊆(cin::xs++ys++expected++carry).toFinset := by
  have h:=KnownOutputAdder.program_support (mappedRead xs false) (mappedRead expected true) ys carry cin
  simp only [mappedRead_wires] at h
  intro q hq
  simp only [sub,wires_append,Finset.mem_union,notRegister_wires] at hq
  rcases hq with (hq|hq)|hq
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  · have hq:=h hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢; tauto
  · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto

theorem sub_physical (xs ys expected carry : List Wire) (cin : Wire)
    (hl : xs.length=ys.length) (he : expected.length=ys.length)
    (hc : carry.length+1=ys.length) (hn : (cin::ys++carry).Nodup)
    (hx : ∀q∈xs,q∉cin::ys++carry) (hex : ∀q∈expected,q∉cin::ys++carry) :
    GatePhysical (sub xs ys expected carry cin) := by
  have h:=KnownOutputAdder.program_physical (mappedRead xs false) (mappedRead expected true) ys carry cin
    ((mappedRead_length _ _).trans hl) ((mappedRead_length _ _).trans he) hc hn
  have bx : ∀b∈mappedRead xs false,∀q∈b.wire,q∉cin::ys++carry := by
    intro b hb q hq
    apply hx q
    rw [←mappedRead_wires xs false]
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  have be : ∀b∈mappedRead expected true,∀q∈b.wire,q∉cin::ys++carry := by
    intro b hb q hq
    apply hex q
    rw [←mappedRead_wires expected true]
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  simpa only [sub,gatePhysical_append] using And.intro (And.intro (notRegister_physical ys) (h bx be)) (notRegister_physical ys)

theorem xorBit_slots (b : MappedBit) (t : Wire) : gateSlots (KnownOutputAdder.xorBit b t)≤2 := by
  cases hw:b.wire <;> cases hf:b.flip <;>
    simp [KnownOutputAdder.xorBit,hw,hf,gateSlots,instructionSlots]

theorem prepare_slots (a d : MappedBit) (y c : Wire) : gateSlots (KnownOutputAdder.prepare a d y c)≤5 := by
  have a:=xorBit_slots a c
  have b:=xorBit_slots d c
  simp only [KnownOutputAdder.prepare,gateSlots_append]
  have h: gateSlots ([Instr.CX y c] : Program)=1 := rfl
  omega

theorem program_slots (xs ys : List Wire) (sums : List MappedBit) (carry : List Wire) (cin : Wire) :
    gateSlots (KnownOutputAdder.program (mappedRead xs false) ys sums carry cin)≤
      gateSlots (addInPlace xs ys carry cin) := by
  induction xs generalizing ys sums carry cin with
  | nil => cases ys <;> cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
      | cons b ys =>
        cases ys with
        | nil =>
          cases sums with
          | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
          | cons d ds => cases ds <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,mappedSum,gateSlots,instructionSlots]
        | cons b' ys => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
    | cons a' xs =>
      cases ys with
      | nil => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
      | cons b ys =>
        cases ys with
        | nil => cases sums <;> simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
        | cons b' ys =>
          cases sums with
          | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
          | cons d ds =>
            cases ds with
            | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
            | cons d' ds =>
              cases carry with
              | nil => simp [KnownOutputAdder.program,mappedRead,addInPlace,gateSlots]
              | cons c cs =>
                have ht:=ih (b'::ys) (d'::ds) cs c
                have hp:=prepare_slots ({wire:=some a',flip:=false} : MappedBit) d' b' c
                simp only [mappedRead,List.map_cons,KnownOutputAdder.program,addInPlace,
                  gateSlots_append,mappedEraseCarry,mappedSum,Bool.false_eq_true,if_false] at ht hp ⊢
                have hm : gateSlots (majority a b cin c)=6 := rfl
                simp only [Baselines.gateSlots_cons,Baselines.gateSlots_nil,instructionSlots] at ht hp ⊢
                omega

theorem sub_slots (xs ys expected carry : List Wire) (cin : Wire) :
    gateSlots (sub xs ys expected carry cin)≤gateSlots (subInPlace xs ys carry cin) := by
  have h:=program_slots xs ys (mappedRead expected true) carry cin
  simp only [sub,subInPlace,gateSlots_append]
  omega
end ECDSAAdd.Entrant.SumCleanup


namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)

def sumExpected : List Wire := R.lo++R.z.take (R.S.length-R.lo.length)
def scl0 : Program := SumCleanup.sub (R.hi++R.zS) R.S R.sumExpected
  (R.carry.take (R.S.length-1)) R.cin++R.m3

theorem sumExpected_length (w : R.W) : R.sumExpected.length=R.S.length := by
  have h4:=w.h4; have hh:=w.hh; have h5:=w.h5; have hS:=w.S; have hz:=w.z
  have lens:=R.lens w
  simp only [sumExpected,List.length_append,List.length_take,lens.1]
  omega

theorem sumExpected_value (w : R.W) (s : BasisState) (hz : regValue R.z s=0) :
    regValue R.sumExpected s=regValue R.lo s := by
  have z : regValue (R.z.take (R.S.length-R.lo.length)) s=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (List.mem_of_mem_take hq))
  simp [sumExpected,regValue_append,z]

theorem scl0_fresh (hn : R.all.Nodup) :
    (∀q∈R.hi++R.zS,q∉R.cin::R.S++R.carry.take (R.S.length-1)) ∧
    (∀q∈R.sumExpected,q∉R.cin::R.S++R.carry.take (R.S.length-1)) := by
  have aux (q : Wire) (hq : q∈R.bank ∨ q∈R.z) : q∉R.cin::R.S++R.carry.take (R.S.length-1) := by
    intro bad
    have cnt:=List.nodup_iff_count.mp hn q
    have ck:=(List.take_sublist (R.S.length-1) R.carry).count_le q
    have cb:=List.count_pos_iff.mpr bad
    simp only [all,List.count_cons,List.count_append] at cnt cb
    rcases hq with hq|hq <;> have pos:=List.count_pos_iff.mpr hq <;> omega
  constructor
  · intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · exact aux q (Or.inl (List.mem_of_mem_drop (show q∈R.bank.drop R.h from hq)))
    · exact aux q (Or.inr (List.mem_of_mem_take (show q∈R.z.take 1 from hq)))
  · intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · exact aux q (Or.inl (List.mem_of_mem_take (show q∈R.bank.take R.h from hq)))
    · exact aux q (Or.inr (List.mem_of_mem_take hq))

theorem scl0_eq (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hS : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) : run R.scl0 m s=run R.scl m s := by
  have h4:=w.h4; have hh:=w.hh; have h5:=w.h5; have hSlen:=w.S; have hcl:=w.carry
  have ln:=R.lens w
  have nd : (R.cin::R.S++R.carry.take (R.S.length-1)).Nodup := by
    apply knd hn
    intro q
    have ct:=(List.take_sublist (R.S.length-1) R.carry).count_le q
    simp only [all,List.count_cons,List.count_append]
    omega
  have lens : (R.hi++R.zS).length=R.S.length := by
    simp only [List.length_append,ln.2.1,ln.2.2.2.2.2.1]; omega
  have car : (R.carry.take (R.S.length-1)).length+1=R.S.length := by
    simp only [List.length_take]; omega
  have zero : regValue R.zS s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz0 q (List.mem_of_mem_take (show q∈R.z.take 1 from hq)))
  have value : regValue R.S s.basis=regValue (R.hi++R.zS) s.basis+regValue R.sumExpected s.basis := by
    rw [regValue_append,zero,R.sumExpected_value w s.basis hz0,hS]; omega
  have eq (record : List Bool) := SumCleanup.sub_eq (R.hi++R.zS) R.S R.sumExpected
    (R.carry.take (R.S.length-1)) R.cin nd (R.scl0_fresh hn).1 (R.scl0_fresh hn).2
    lens (R.sumExpected_length w) car s record
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)) hi0 value
  have count:=SumCleanup.sub_counts (R.hi++R.zS) R.S R.sumExpected
    (R.carry.take (R.S.length-1)) R.cin lens (R.sumExpected_length w) car
  have old:=subInPlace_counts (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin lens car
  simp only [scl0,scl,c4,run_append,count.2,old.2]
  rw [eq]

theorem scl0_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hS : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0)
    (hi0 : s.basis R.cin=false) :
    (run R.scl0 m s).phase=s.phase ∧ regValue R.S (run R.scl0 m s).basis=0 ∧
    ∀q,q∉R.S → (run R.scl0 m s).basis q=s.basis q := by
  rw [R.scl0_eq w hn s m hS hz0 hc0 hi0]
  exact R.scl_correct w hn s m hS hz0 hc0 hi0

theorem scl0_counts (w : R.W) : toffoliCount R.scl0=0 ∧
    measurementCount R.scl0=R.bank.length-R.h := by
  have ln:=R.lens w
  have h4:=w.h4;have hh:=w.hh;have h5:=w.h5;have hS:=w.S;have hcl:=w.carry
  have lens : (R.hi++R.zS).length=R.S.length := by
    simp only [List.length_append,ln.2.1,ln.2.2.2.2.2.1]; omega
  have car : (R.carry.take (R.S.length-1)).length+1=R.S.length := by simp only [List.length_take]; omega
  have a:=SumCleanup.sub_counts (R.hi++R.zS) R.S R.sumExpected
    (R.carry.take (R.S.length-1)) R.cin lens (R.sumExpected_length w) car
  have b:=copyRegister_counts none R.lo (R.S.take R.h) (by rw [ln.1,ln.2.2.2.2.2.2.2.2.2.1])
  simp only [scl0,m3,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,
    Option.isSome_none,Bool.false_eq_true,if_false]
  constructor
  · trivial
  · rw [hS]; omega

theorem scl0_slots : Challenge.gateSlots R.scl0≤Challenge.gateSlots R.scl := by
  have h:=SumCleanup.sub_slots (R.hi++R.zS) R.S R.sumExpected (R.carry.take (R.S.length-1)) R.cin
  simp only [scl0,scl,c4,Challenge.gateSlots_append]
  omega

theorem scl0_support (w : R.W) : wires R.scl0⊆R.all.toFinset := by
  have a:=SumCleanup.sub_support (R.hi++R.zS) R.S R.sumExpected (R.carry.take (R.S.length-1)) R.cin
  have p:=copyRegister_wires_subset none R.lo (R.S.take R.h)
  intro q hq
  simp only [scl0,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have hq:=a hq
    simp only [sumExpected,lo,hi,zS,List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at hq
    rcases hq with hq|hq|hq|hq|hq|hq|hq
    · simp [all,hq.symm]
    · have h:=List.mem_of_mem_drop hq; simp [all,h]
    · have h:=List.mem_of_mem_take hq; simp [all,h]
    · simp [all,hq]
    · have h:=List.mem_of_mem_take hq; simp [all,h]
    · have h:=List.mem_of_mem_take hq; simp [all,h]
    · have h:=List.mem_of_mem_take hq; simp [all,h]

  · have hq:=p hq
    simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append] at hq
    rcases hq with hq|hq
    · have h:=List.mem_of_mem_take (show q∈R.bank.take R.h from hq);simp [all,h]
    · have h:=List.mem_of_mem_take hq;simp [all,h]

theorem scl0_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.scl0 := by
  have h4:=w.h4;have hh:=w.hh;have h5:=w.h5;have hS:=w.S;have hcl:=w.carry
  have ln:=R.lens w
  have nd : (R.cin::R.S++R.carry.take (R.S.length-1)).Nodup := by
    apply knd hn;intro q
    have ct:=(List.take_sublist (R.S.length-1) R.carry).count_le q
    simp only [all,List.count_cons,List.count_append];omega
  have lens : (R.hi++R.zS).length=R.S.length := by
    simp only [List.length_append,ln.2.1,ln.2.2.2.2.2.1]; omega
  have car : (R.carry.take (R.S.length-1)).length+1=R.S.length := by simp only [List.length_take];omega
  have a:=SumCleanup.sub_physical (R.hi++R.zS) R.S R.sumExpected
    (R.carry.take (R.S.length-1)) R.cin lens (R.sumExpected_length w) car nd
    (R.scl0_fresh hn).1 (R.scl0_fresh hn).2
  have ndcp : (R.lo++R.S.take R.h).Nodup := by
    apply knd hn;intro q
    have cb:=(List.take_sublist R.h R.bank).count_le q
    have cs:=(List.take_sublist R.h R.S).count_le q
    simp only [all,lo,List.count_cons,List.count_append];omega
  have cp:=copyRegister_physical none R.lo (R.S.take R.h) ndcp (by simp)
  simpa only [scl0,m3,gatePhysical_append] using And.intro a cp
end ECDSAAdd.Entrant.KRegs


namespace ECDSAAdd.Entrant.SumKG
open Arithmetic KG
variable (K : KG)
def make : Program := K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7++K.R.m8++K.R.scl0
def clear : Program := K.R.smk++K.R.c8++K.R.c7++K.R.c6++K.Q5c++K.R.scl0++K.Q2c++K.Q1c
theorem make_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=0) (hX0 : regValue K.X s.basis=0)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (make K) m s).phase=s.phase ∧
    regValue K.R.dst (run (make K) m s).basis=(regValue K.R.bank s.basis)^2 ∧
    regValue K.R.S (run (make K) m s).basis=0 ∧
    regValue K.R.T (run (make K) m s).basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis ∧
    K.I1 (regValue K.R.lo s.basis) (run (make K) m s).basis ∧
    K.I2 (regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) (run (make K) m s).basis ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (make K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have bv := K.R.bank_value w s.basis
  rw [bv]
  generalize ha : regValue K.R.lo s.basis=a
  generalize hb : regValue K.R.hi s.basis=b
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  obtain ⟨a7,r8,e8⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7++K.R.m8) K.R.scl0 m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7) K.R.m8 a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6) K.R.m7 a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5) K.R.m6 a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.Q1++K.Q2++K.R.smk) K.Q5 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.Q1++K.Q2) K.R.smk a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.Q1 K.Q2 a2 s
  rw [show (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6++K.R.m7++K.R.m8++K.R.scl0 from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- Q1: a^2 into dlo
  have st1 := sp.mk1 s r1 (zero _ _ hd0 (fun q h => mt h)) (zero _ _ hX0 (fun q h => x1 h)) hp0 hc0 hz0 hi0
  rw [ha] at st1
  generalize run K.Q1 r1 s=s1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s1.basis q=s.basis q :=
    fun q h _ _ x => st1.2.2.2 q (fun y => h (mt y)) (fun y => x (x1 y))
  -- Q2: b^2 into dhi
  have dhi1 : regValue K.R.dhi s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hd0 (fun q h => md h))
  have X21 : regValue K.X2 s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x2 h))
  have hi1 : regValue K.R.hi s1.basis=b := (outV s1 G1 _ (fun q h => Or.inl (md h))).trans hb
  have st2 := sp.mk2 s1 r2 dhi1 X21 ((outV s1 G1 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s1 G1 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s1 G1 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [hi1] at st2
  generalize run K.Q2 r2 s1=s2 at st2 ⊢
  have F2 : ∀q,q∉K.R.dhi → q∉K.X2 → s2.basis q=s1.basis q := st2.2.2.2
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s2.basis q=s.basis q :=
    fun q h hS hT x => (F2 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo s2.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have I12 : K.I1 a s2.basis := sp.lc1 a s1.basis s2.basis (fun q hq => (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st1.2.2.1
  -- sum register
  have S2 : regValue K.R.S s2.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)))).trans hS0
  have st3 := K.R.smk_correct w hR s2 r3 S2 ((outV s2 G2 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s2 G2 K.R.carry (by intro q h; simp [h])).trans hc0) ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  have lo2 : regValue K.R.lo s2.basis=a := (outV s2 G2 K.R.lo (fun q h => Or.inl (mt h))).trans ha
  have hi2 : regValue K.R.hi s2.basis=b := (outV s2 G2 K.R.hi (fun q h => Or.inl (md h))).trans hb
  rw [lo2,hi2] at st3
  generalize run K.R.smk r3 s2=s3 at st3 ⊢
  have F3 := st3.2.2
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s3.basis q=s.basis q :=
    fun q h hS hT x => (F3 q hS).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo s3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi s3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st2.2.1
  have I13 : K.I1 a s3.basis := sp.lc1 a s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I12
  have I23 : K.I2 b s3.basis := sp.lc2 b s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st2.2.2.1
  -- Q5: T = (a+b)^2
  have back3 (q : Wire) (h1 : q∉K.R.dlo) (h2 : q∉K.X1) (h3 : q∉K.R.dhi) (h4 : q∉K.X2) (h5 : q∉K.R.S) :
      s3.basis q=s.basis q :=
    (F3 q h5).trans ((F2 q h3 h4).trans (st1.2.2.2 q h1 h2))
  have T3 : regValue K.R.T s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have X53 : regValue K.X5 s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x5 h))
  have st5 := sp.mk5 s3 r4 T3 X53 ((outV s3 G3 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s3 G3 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s3 G3 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [st3.2.1] at st5
  generalize run K.Q5 r4 s3=s5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → s5.basis q=s3.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G3 q h hS hT x)
  have dlo5 : regValue K.R.dlo s5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi5 : regValue K.R.dhi s5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S5 : regValue K.R.S s5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st3.2.1
  have I15 : K.I1 a s5.basis := sp.lc1 a s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I13
  have I25 : K.I2 b s5.basis := sp.lc2 b s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I23
  have sumLt : a+b<2^K.R.S.length := by
    have hp : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
    omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  -- T -= a^2
  have st6 : (run K.R.m6 r5 s5).phase=s5.phase ∧ regValue K.R.T (run K.R.m6 r5 s5).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.m6 r5 s5).basis q=s5.basis q := by
    unfold KRegs.m6
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.dlo++K.R.zA) K.R.T
      (K.R.carry.take (K.R.T.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) s5 r5
      (fun q hq => (regValue_zero _ _).mp ((outV s5 G5 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo5,outV s5 G5 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st5.2.1,G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt,ex]; omega
  generalize run K.R.m6 r5 s5=s6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hT).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo s6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi s6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  -- T -= b^2
  have st7 : (run K.R.m7 r6 s6).phase=s6.phase ∧ regValue K.R.T (run K.R.m7 r6 s6).basis=2*a*b ∧
      ∀q,q∉K.R.T → (run K.R.m7 r6 s6).basis q=s6.basis q := by
    unfold KRegs.m7
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.dhi++K.R.zB) K.R.T
      (K.R.carry.take (K.R.T.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) s6 r6
      (fun q hq => (regValue_zero _ _).mp ((outV s6 G6 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      st6.2.1,G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  generalize run K.R.m7 r6 s6=s7 at st7 ⊢
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s7.basis q=s.basis q :=
    fun q h hS hT x => (st7.2.2 q hT).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo s7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  have dhi7 : regValue K.R.dhi s7.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi6
  have D7 : regValue K.R.dst s7.basis=a^2+2^(2*K.R.h)*b^2 := by rw [K.R.dst_value w,dlo7,dhi7]
  -- dst += 2^h * 2ab
  have st8 : (run K.R.m8 r7 s7).phase=s7.phase ∧
      regValue K.R.dmid (run K.R.m8 r7 s7).basis=(2*a*b+(a^2+2^(2*K.R.h)*b^2)/2^K.R.h)%2^(2*K.R.bank.length-K.R.h) ∧
      ∀q,q∉K.R.dmid → (run K.R.m8 r7 s7).basis q=s7.basis q := by
    unfold KRegs.m8
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.T++K.R.zM) K.R.dmid (K.R.carry.take (K.R.dmid.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) s7 r7
      (fun q hq => (regValue_zero _ _).mp ((outV s7 G7 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,st7.2.1,outV s7 G7 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      show regValue K.R.dmid s7.basis=regValue K.R.dst s7.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) s7.basis,D7,
      G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,L4]
    simp
  generalize run K.R.m8 r7 s7=s8 at st8 ⊢
  have G8 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s8.basis q=s.basis q :=
    fun q h hS hT x => (st8.2.2 q (fun y => h (md y))).trans (G7 q h hS hT x)
  have D8 : regValue K.R.dst s8.basis=(a+2^K.R.h*b)^2 := by
    rw [K.R.dst_value_mid w,st8.2.1,kkeep st8.2.2 (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),D7]
    exact KRegs.kfinal a b K.R.h K.R.bank.length aLt bLt (by omega)
  -- facts between s5 and s8: only T and dmid changed
  have back8 (q : Wire) (hT : q∉K.R.T) (hd : q∉K.R.dst) : s8.basis q=s5.basis q :=
    (st8.2.2 q (fun y => hd (md y))).trans ((st7.2.2 q hT).trans (st6.2.2 q hT))
  have S8 : regValue K.R.S s8.basis=a+b := (regValue_congr _ _ _ (fun q hq => back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S5
  have T8 : regValue K.R.T s8.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st8.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1
  have I18 : K.I1 a s8.basis := sp.lc1 a s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I15
  have I28 : K.I2 b s8.basis := sp.lc2 b s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I25
  have I58 : K.I5 (a+b) s8.basis := sp.lc5 (a+b) s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st5.2.2.1
  -- clean the sum register
  have st9 := K.R.scl0_correct w hR s8 r8
    (by rw [S8,(outV s8 G8 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV s8 G8 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV s8 G8 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s8 G8 K.R.carry (by intro q h; simp [h])).trans hc0) ((G8 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl0 r8 s8=s9 at st9 ⊢
  refine ⟨st9.1.trans (st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,st9.2.1,?_,?_,?_,?_,?_⟩
  · rw [←D8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · rw [←T8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · exact sp.lc1 a s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I18
  · exact sp.lc2 b s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I28
  · exact sp.lc5 (a+b) s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I58
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · exact ((regValue_zero _ _).mp st9.2.1 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (st9.2.2 q hS).trans (G8 q hd hS hT hx)

theorem clear_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=(regValue K.R.bank s.basis)^2) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis)
    (hI1 : K.I1 (regValue K.R.lo s.basis) s.basis) (hI2 : K.I2 (regValue K.R.hi s.basis) s.basis)
    (hI5 : K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) s.basis)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (clear K) m s).phase=s.phase ∧
    regValue K.R.dst (run (clear K) m s).basis=0 ∧
    regValue K.R.S (run (clear K) m s).basis=0 ∧
    regValue K.R.T (run (clear K) m s).basis=0 ∧
    regValue K.X (run (clear K) m s).basis=0 ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (clear K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  rw [K.R.bank_value w s.basis] at hd0
  generalize ha : regValue K.R.lo s.basis=a at hd0 hT0 hI1 hI5
  generalize hb : regValue K.R.hi s.basis=b at hd0 hT0 hI2 hI5
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  have hp2 : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
  have sumLt : a+b<2^K.R.S.length := by omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have hX : (a+2^K.R.h*b)^2=(a^2+2^(2*K.R.h)*b^2)+2^K.R.h*(2*a*b) := by ring
  have hpos : 0<2^K.R.h := Nat.two_pow_pos _
  have XLt : (a+2^K.R.h*b)^2<2^(2*K.R.bank.length) := by
    have hsplit : 2^K.R.bank.length=2^K.R.h*2^(K.R.bank.length-K.R.h) := by rw [←pow_add]; congr 1; omega
    have hm := Nat.mul_le_mul_left (2^K.R.h) (show b+1≤2^(K.R.bank.length-K.R.h) by omega)
    rw [Nat.mul_add,Nat.mul_one,←hsplit] at hm
    exact square_bound _ _ (by omega)
  have aSq : a^2<2^(2*K.R.h) := square_bound _ _ aLt
  obtain ⟨a7,r8,e8⟩ := kseq (K.R.smk++K.R.c8++K.R.c7++K.R.c6++K.Q5c++K.R.scl0++K.Q2c) K.Q1c m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.R.smk++K.R.c8++K.R.c7++K.R.c6++K.Q5c++K.R.scl0) K.Q2c a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.R.smk++K.R.c8++K.R.c7++K.R.c6++K.Q5c) K.R.scl0 a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.R.smk++K.R.c8++K.R.c7++K.R.c6) K.Q5c a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.R.smk++K.R.c8++K.R.c7) K.R.c6 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.R.smk++K.R.c8) K.R.c7 a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.R.smk K.R.c8 a2 s
  rw [show (clear K)=K.R.smk++K.R.c8++K.R.c7++K.R.c6++K.Q5c++K.R.scl0++K.Q2c++K.Q1c from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- rebuild S
  have st1 := K.R.smk_correct w hR s r1 hS0 hz0 hc0 hi0
  rw [ha,hb] at st1
  generalize run K.R.smk r1 s=t1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t1.basis q=s.basis q := fun q _ h _ _ => st1.2.2 q h
  have T1 : regValue K.R.T t1.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have D1 : regValue K.R.dst t1.basis=(a+2^K.R.h*b)^2 := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hd0
  -- dst -= 2^h * 2ab
  have st2 : (run K.R.c8 r2 t1).phase=t1.phase ∧
      regValue K.R.dst (run K.R.c8 r2 t1).basis=a^2+2^(2*K.R.h)*b^2 ∧
      ∀q,q∉K.R.dmid → (run K.R.c8 r2 t1).basis q=t1.basis q := by
    unfold KRegs.c8
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.T++K.R.zM) K.R.dmid
      (K.R.carry.take (K.R.dmid.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) t1 r2
      (fun q hq => (regValue_zero _ _).mp ((outV t1 G1 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [K.R.dst_value_mid w,v,kkeep f (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),regValue_append,T1,outV t1 G1 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),
      show regValue K.R.dmid t1.basis=regValue K.R.dst t1.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) t1.basis,D1,L4]
    have hdiv : (a+2^K.R.h*b)^2/2^K.R.h=(a^2+2^(2*K.R.h)*b^2)/2^K.R.h+2*a*b := by
      rw [hX,Nat.add_mul_div_left _ _ hpos]
    have hmod : (a+2^K.R.h*b)^2%2^K.R.h=(a^2+2^(2*K.R.h)*b^2)%2^K.R.h := by
      rw [hX,Nat.add_mul_mod_self_left]
    have hq : (a+2^K.R.h*b)^2/2^K.R.h<2^(2*K.R.bank.length-K.R.h) := by
      rw [Nat.div_lt_iff_lt_mul hpos,←pow_add,show 2*K.R.bank.length-K.R.h+K.R.h=2*K.R.bank.length by omega]
      exact XLt
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod ((a+2^K.R.h*b)^2/2^K.R.h) (2*a*b) _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  generalize run K.R.c8 r2 t1=t2 at st2 ⊢
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t2.basis q=s.basis q :=
    fun q h hS hT x => (st2.2.2 q (fun y => h (md y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo t2.basis=a^2 := by
    rw [show regValue K.R.dlo t2.basis=regValue K.R.dst t2.basis%2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt aSq]
  have dhi2 : regValue K.R.dhi t2.basis=b^2 := by
    rw [show regValue K.R.dhi t2.basis=regValue K.R.dst t2.basis/2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt aSq,Nat.zero_add]
  have S2 : regValue K.R.S t2.basis=a+b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have T2 : regValue K.R.T t2.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans T1
  -- T += b^2
  have st3 : (run K.R.c7 r3 t2).phase=t2.phase ∧ regValue K.R.T (run K.R.c7 r3 t2).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.c7 r3 t2).basis q=t2.basis q := by
    unfold KRegs.c7
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.dhi++K.R.zB) K.R.T (K.R.carry.take (K.R.T.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t2 r3
      (fun q hq => (regValue_zero _ _).mp ((outV t2 G2 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      T2,G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega)]; ring
  generalize run K.R.c7 r3 t2=t3 at st3 ⊢
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t3.basis q=s.basis q :=
    fun q h hS hT x => (st3.2.2 q hT).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo t3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi t3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi2
  have S3 : regValue K.R.S t3.basis=a+b := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S2
  -- T += a^2
  have st4 : (run K.R.c6 r4 t3).phase=t3.phase ∧ regValue K.R.T (run K.R.c6 r4 t3).basis=(a+b)^2 ∧
      ∀q,q∉K.R.T → (run K.R.c6 r4 t3).basis q=t3.basis q := by
    unfold KRegs.c6
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.dlo++K.R.zA) K.R.T (K.R.carry.take (K.R.T.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t3 r4
      (fun q hq => (regValue_zero _ _).mp ((outV t3 G3 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo3,outV t3 G3 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st3.2.1,G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega),ex]; ring
  generalize run K.R.c6 r4 t3=t4 at st4 ⊢
  have G4 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t4.basis q=s.basis q :=
    fun q h hS hT x => (st4.2.2 q hT).trans (G3 q h hS hT x)
  have dlo4 : regValue K.R.dlo t4.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi4 : regValue K.R.dhi t4.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S4 : regValue K.R.S t4.basis=a+b := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S3
  have back4 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) : t4.basis q=s.basis q :=
    (st4.2.2 q h3).trans ((st3.2.2 q h3).trans ((st2.2.2 q (fun y => h2 (md y))).trans (st1.2.2 q h1)))
  -- clear T with the S-square cleanup
  have st5 := sp.cl5 t4 r5 (by rw [st4.2.1,S4])
    (by rw [S4]; exact sp.lc5 (a+b) s.basis t4.basis (fun q hq => (back4 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI5)
    ((outV t4 G4 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t4 G4 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t4 G4 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G4 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q5c r5 t4=t5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → t5.basis q=t4.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G4 q h hS hT x)
  have dlo5 : regValue K.R.dlo t5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo4
  have dhi5 : regValue K.R.dhi t5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi4
  have S5 : regValue K.R.S t5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S4
  -- clean S
  have st6 := K.R.scl0_correct w hR t5 r6
    (by rw [S5,(outV t5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV t5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV t5 G5 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV t5 G5 K.R.carry (by intro q h; simp [h])).trans hc0) ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl0 r6 t5=t6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hS).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo t6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi t6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  have T6 : regValue K.R.T t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.1
  have X56 : regValue K.X5 t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.2.1
  have back6 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) (h4 : q∉K.X5) : t6.basis q=s.basis q :=
    (st6.2.2 q h1).trans ((F5 q h3 h4).trans (back4 q h1 h2 h3))
  -- clear b^2
  have st7 := sp.cl2 t6 r7
    (by rw [dhi6,(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    (by rw [(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb]
        exact sp.lc2 b s.basis t6.basis (fun q hq => (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI2)
    ((outV t6 G6 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t6 G6 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t6 G6 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q2c r7 t6=t7 at st7 ⊢
  have F7 : ∀q,q∉K.R.dhi → q∉K.X2 → t7.basis q=t6.basis q := st7.2.2.2
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t7.basis q=s.basis q :=
    fun q h hS hT x => (F7 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo t7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  -- clear a^2
  have st8 := sp.cl1 t7 r8
    (by rw [dlo7,(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha])
    (by rw [(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha]
        exact sp.lc1 a s.basis t7.basis (fun q hq => ((F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).symm) hI1)
    ((outV t7 G7 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t7 G7 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t7 G7 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q1c r8 t7=t8 at st8 ⊢
  have F8 : ∀q,q∉K.R.dlo → q∉K.X1 → t8.basis q=t7.basis q := st8.2.2.2
  have k78 (r : List Wire) (h : ∀q∈r,q∉K.R.dlo ∧ q∉K.X1 ∧ q∉K.R.dhi ∧ q∉K.X2) :
      regValue r t8.basis=regValue r t6.basis :=
    regValue_congr _ _ _ (fun q hq => (F8 q (h q hq).1 (h q hq).2.1).trans (F7 q (h q hq).2.2.1 (h q hq).2.2.2))
  refine ⟨st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st4.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,?_,?_,?_,?_⟩
  · rw [K.R.dst_value w,st8.2.1,(regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1]; simp
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact st6.2.1
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact T6
  · rw [X,regValue_append,regValue_append,st8.2.2.1,
      (regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.2.1,
      k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩),X56]; simp
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · have a1 := (regValue_zero _ _).mp st6.2.1 q hS
      have a2 := (regValue_zero _ _).mp hS0 q hS
      rw [F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),a1,a2]
    · exact (F8 q (fun y => hd (mt y)) (fun y => hx (x1 y))).trans (G7 q hd hS hT hx)


theorem make_counts (w : K.R.W) :
    toffoliCount (make K)=toffoliCount K.Q1+toffoliCount K.Q2+toffoliCount K.Q5+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (make K)=measurementCount K.Q1+measurementCount K.Q2+measurementCount K.Q5+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl0_counts w
  have e : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7++K.R.m8)++K.R.scl0 := by
    simp only [make,List.append_assoc]
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,p.2.2.2.2.1,p.2.2.2.2.2.1,kextra]
  constructor <;> omega

theorem clear_counts (w : K.R.W) :
    toffoliCount (clear K)=toffoliCount K.Q1c+toffoliCount K.Q2c+toffoliCount K.Q5c+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (clear K)=measurementCount K.Q1c+measurementCount K.Q2c+measurementCount K.Q5c+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl0_counts w
  have e : (clear K)=K.R.smk++(K.R.c8++K.R.c7++K.R.c6)++K.Q5c++K.R.scl0++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,p.2.2.2.2.2.2.1,p.2.2.2.2.2.2.2,kextra]
  constructor <;> omega

theorem r_sub (q : Wire) (h : q∈K.R.all.toFinset) : q∈K.all.toFinset := by
  simp only [List.mem_toFinset,all,List.mem_append] at h ⊢; exact Or.inl h

theorem steps_support (w : K.R.W)
    (s1 : ECDSAAdd.wires K.Q1⊆K.all.toFinset) (s1c : ECDSAAdd.wires K.Q1c⊆K.all.toFinset)
    (s2 : ECDSAAdd.wires K.Q2⊆K.all.toFinset) (s2c : ECDSAAdd.wires K.Q2c⊆K.all.toFinset)
    (s5 : ECDSAAdd.wires K.Q5⊆K.all.toFinset) (s5c : ECDSAAdd.wires K.Q5c⊆K.all.toFinset) :
    ECDSAAdd.wires (make K)⊆K.all.toFinset ∧ ECDSAAdd.wires (clear K)⊆K.all.toFinset := by
  have p := K.R.piece_support w
  have sc := K.R.scl0_support w
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7++K.R.m8)++K.R.scl0 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8++K.R.c7++K.R.c6)++K.Q5c++K.R.scl0++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have lift {P : Program} (h : ECDSAAdd.wires P⊆K.R.all.toFinset) : ECDSAAdd.wires P⊆K.all.toFinset :=
    fun q hq => K.r_sub q (h hq)
  have ap {P Q : Program} (h1 : ECDSAAdd.wires P⊆K.all.toFinset) (h2 : ECDSAAdd.wires Q⊆K.all.toFinset) :
      ECDSAAdd.wires (P++Q)⊆K.all.toFinset := by rw [wires_append]; exact Finset.union_subset h1 h2
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap s1 s2) (lift p.1)) s5) (lift p.2.2.1)) (lift sc),
    ap (ap (ap (ap (ap (lift p.1) (lift p.2.2.2.1)) s5c) (lift sc)) s2c) s1c⟩

theorem steps_physical (w : K.R.W) (hn : K.all.Nodup)
    (p1 : GatePhysical K.Q1) (p1c : GatePhysical K.Q1c) (p2 : GatePhysical K.Q2) (p2c : GatePhysical K.Q2c)
    (p5 : GatePhysical K.Q5) (p5c : GatePhysical K.Q5c) :
    GatePhysical (make K) ∧ GatePhysical (clear K) := by
  have p := K.R.piece_physical (K.rnd hn)
  have sc := K.R.scl0_physical w (K.rnd hn)
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6++K.R.m7++K.R.m8)++K.R.scl0 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8++K.R.c7++K.R.c6)++K.Q5c++K.R.scl0++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap p1 p2) p.1) p5) p.2.2.1) sc,ap (ap (ap (ap (ap p.1 p.2.2.2.1) p5c) sc) p2c) p1c⟩

theorem steps_slots :
    Challenge.gateSlots (make K)+Challenge.gateSlots (clear K) ≤
      Challenge.gateSlots K.Q1+Challenge.gateSlots K.Q1c+Challenge.gateSlots K.Q2+Challenge.gateSlots K.Q2c+
      Challenge.gateSlots K.Q5+Challenge.gateSlots K.Q5c+2*(Challenge.gateSlots K.R.make+Challenge.gateSlots K.R.clear) := by
  have sc := K.R.scl0_slots
  simp only [make,clear,KRegs.smk,KRegs.scl,KRegs.make,KRegs.clear,Challenge.gateSlots_append] at sc ⊢
  omega

end ECDSAAdd.Entrant.SumKG

namespace ECDSAAdd.Entrant.SumKG
open Arithmetic KG
variable (K : KG)
theorem steps_slots2 :
    Challenge.gateSlots (make K)+Challenge.gateSlots (clear K) ≤
      Challenge.gateSlots K.Q1+Challenge.gateSlots K.Q1c+Challenge.gateSlots K.Q2+Challenge.gateSlots K.Q2c+
      Challenge.gateSlots K.Q5+Challenge.gateSlots K.Q5c+
      (2*(Challenge.gateSlots K.R.smk+Challenge.gateSlots K.R.scl)+Challenge.gateSlots (K.R.m6++K.R.m7++K.R.m8)+
      Challenge.gateSlots (K.R.c8++K.R.c7++K.R.c6)) := by
  have sc := K.R.scl0_slots
  simp only [make,clear,Challenge.gateSlots_append] at sc ⊢; omega
end ECDSAAdd.Entrant.SumKG

set_option Elab.async false

-- DIAGONAL COMPONENT DiagonalSemantics.lean
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
section DiagonalSharing
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
section SquareFirstRow
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.SquareHead
open Arithmetic

def headAdd : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as,b::b'::bs,k::ks,cin =>
      [.CX a k]++addInPlace (a'::as) (b'::bs) ks k++
        eraseCarry a b cin k++[.CX a b,.CX cin b]
  | xs,ys,carry,cin => addInPlace xs ys carry cin

theorem headAdd_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (headAdd xs ys carry cin)=measurementCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons a' as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons b' bs =>
          cases carry with
          | nil => rfl
          | cons k ks => simp [headAdd,addInPlace,measurementCount_append,majority,measurementCount]

theorem headAdd_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (s : State) (m : List Bool)
    (hk : carryBit (s.basis (xs.headD 0)) (s.basis (ys.headD 0)) (s.basis cin)=s.basis (xs.headD 0)) :
    run (headAdd xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  cases xs with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons a' as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons b' bs =>
          cases carry with
          | nil => rfl
          | cons k ks =>
            have h4 : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count_le_one.mpr
              intro q
              have h := List.nodup_iff_count_le_one.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have first (r : List Bool) : run [.CX a k] r s=run (majority a b cin k) r s := by
              rw [majority_correct a b cin k h4]
              simpa [run,List.headD] using congrArg (State.mk s.phase) (show
                writeBit s.basis k (s.basis k ^^ s.basis a)=
                writeBit s.basis k (s.basis k ^^ carryBit (s.basis a) (s.basis b) (s.basis cin)) by
                  simp_all)
            simp only [headAdd,addInPlace,List.append_assoc,run_append]
            have mc : measurementCount (majority a b cin k)=0 := rfl
            simp only [mc,measurementCount,List.take_zero,List.drop_zero]
            rw [first]

def firstRow (c : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse c (dst.take xs.length) ++
    headAdd (xs++pad.take 1) dst (carry.take xs.length) c ++ xorWhenFalse c dst

def firstClear (c : Wire) (xs dst pad carry : List Wire) : Program :=
  xorWhenFalse c dst ++ (notRegister dst ++
    (headAdd (xs++pad.take 1) dst (carry.take xs.length) c ++
      (notRegister dst ++ xorWhenFalse c (dst.take xs.length))))

theorem firstRow_eq (c : Wire) (xs dst pad carry : List Wire)
    (hn : (c::xs++dst++pad++carry).Nodup) (hx : 1≤xs.length)
    (hd : dst.length=xs.length+1) (s : State) (m : List Bool)
    (hz : regValue dst s.basis=0) :
    run (firstRow c xs dst pad carry) m s=run (signedSquareRow c xs dst pad carry) m s := by
  have dn : dst.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := List.nodup_iff_count_le_one.mp hn q
    simp only [List.count_cons,List.count_append] at h; omega
  have co : c∉dst := by
    intro h
    have a := List.count_pos_iff.mpr h
    have b := List.nodup_iff_count_le_one.mp hn c
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at b; omega
  have an : (c::(xs++pad.take 1)++dst++carry.take xs.length).Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have a := (List.take_sublist 1 pad).count_le q
    have b := (List.take_sublist xs.length carry).count_le q
    have h := List.nodup_iff_count_le_one.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  let p := xorWhenFalse c (dst.take xs.length)
  have pm : measurementCount p=0 := xorWhenFalse_measurementCount ..
  simp only [firstRow,signedSquareRow,List.append_assoc,run_append,headAdd_measurements,pm]
  congr 1
  apply headAdd_eq _ _ _ c an
  rw [xorWhenFalse_correct c (dst.take xs.length) ((List.take_sublist _ _).nodup dn)
    (fun h => co (List.mem_of_mem_take h))]
  have hm : dst.headD 0∈dst.take xs.length := by
    cases dst with
    | nil => simp at hd
    | cons b bs => cases xs <;> simp_all
  have zm := (regValue_zero dst s.basis).mp hz _ (List.mem_of_mem_take hm)
  have cp : c∉dst.take xs.length := fun h => co (List.mem_of_mem_take h)
  have yp : xorFalseBasis c (dst.take xs.length) s.basis (dst.headD 0)= !s.basis c := by
    simp only [xorFalseBasis,if_pos hm,zm,Bool.false_xor]
  have ci : xorFalseBasis c (dst.take xs.length) s.basis c=s.basis c := by
    simp only [xorFalseBasis,if_neg cp]
  change carryBit _ (xorFalseBasis c (dst.take xs.length) s.basis (dst.headD 0))
    (xorFalseBasis c (dst.take xs.length) s.basis c)=_
  rw [yp,ci]
  change carryBit (xorFalseBasis c (dst.take xs.length) s.basis ((xs++pad.take 1).headD 0))
    (!s.basis c) (s.basis c)=xorFalseBasis c (dst.take xs.length) s.basis ((xs++pad.take 1).headD 0)
  generalize xorFalseBasis c (dst.take xs.length) s.basis ((xs++pad.take 1).headD 0)=A
  cases A <;> cases s.basis c <;> rfl

theorem firstClear_eq (c : Wire) (xs dst pad carry : List Wire)
    (hn : (c::xs++dst++pad++carry).Nodup) (hx : 1≤xs.length)
    (hd : dst.length=xs.length+1) (s : State) (m : List Bool)
    (hl : s.basis (dst.headD 0)= (s.basis (xs.headD 0) ^^ s.basis c)) :
    run (firstClear c xs dst pad carry) m s=run (signedSquareRowClear c xs dst pad carry) m s := by
  have dn : dst.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have h := List.nodup_iff_count_le_one.mp hn q
    simp only [List.count_cons,List.count_append] at h; omega
  have co : c∉dst := by
    intro h
    have a := List.count_pos_iff.mpr h
    have b := List.nodup_iff_count_le_one.mp hn c
    simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at b; omega
  have an : (c::(xs++pad.take 1)++dst++carry.take xs.length).Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q
    have a := (List.take_sublist 1 pad).count_le q
    have b := (List.take_sublist xs.length carry).count_le q
    have h := List.nodup_iff_count_le_one.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have xm : xs.headD 0∈xs := by cases xs <;> simp_all
  have xo : xs.headD 0∉dst := by
    intro h
    have a := List.count_pos_iff.mpr h
    have b := List.count_pos_iff.mpr xm
    have z := List.nodup_iff_count_le_one.mp hn (xs.headD 0)
    simp only [List.count_cons,List.count_append] at z; omega
  have ym : dst.headD 0∈dst := by cases dst <;> simp_all
  have he : (xs++pad.take 1).headD 0=xs.headD 0 := by cases xs <;> simp_all
  simp only [firstClear,signedSquareRowClear,List.append_assoc,run_append,
    headAdd_measurements,xorWhenFalse_measurementCount,(notRegister_counts dst).2,
    List.take_zero,List.drop_zero]
  congr 1
  congr 1
  apply headAdd_eq _ _ _ c an
  rw [xorWhenFalse_correct c dst dn co,notRegister_correct dst dn]
  change carryBit
    ((if (xs++pad.take 1).headD 0∈dst then _ else _))
    ((if dst.headD 0∈dst then _ else _))
    ((if c∈dst then _ else _))=_
  rw [he]
  simp only [if_neg xo,if_pos ym,if_neg co,xorFalseBasis,hl]
  cases s.basis (xs.headD 0) <;> cases s.basis c <;> rfl

def rows (xs dst pad carry : List Wire) : Program :=
  match xs with
  | c::d::tail => firstRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry ++
      signedSquareRows (d::tail) (dst.drop 2) pad carry
  | _ => signedSquareRows xs dst pad carry

def rowsClear (xs dst pad carry : List Wire) : Program :=
  match xs with
  | c::d::tail => signedSquareRowsClear (d::tail) (dst.drop 2) pad carry ++
      firstClear c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry
  | _ => signedSquareRowsClear xs dst pad carry

theorem rows_measurements (xs dst pad carry : List Wire) :
    measurementCount (rows xs dst pad carry)=measurementCount (signedSquareRows xs dst pad carry) ∧
    measurementCount (rowsClear xs dst pad carry)=measurementCount (signedSquareRowsClear xs dst pad carry) := by
  cases xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons c xs => cases xs with
    | nil => exact ⟨rfl,rfl⟩
    | cons d tail => simp only [rows,rowsClear,signedSquareRows,signedSquareRowsClear,
        firstRow,firstClear,signedSquareRow,signedSquareRowClear,measurementCount_append,headAdd_measurements]; trivial

theorem rows_eq (xs dst pad carry : List Wire) (hn : (xs++dst++pad++carry).Nodup)
    (hd : dst.length=2*xs.length) (s : State) (m : List Bool) (hz : regValue dst s.basis=0) :
    run (rows xs dst pad carry) m s=run (signedSquareRows xs dst pad carry) m s := by
  cases xs with
  | nil => rfl
  | cons c xs => cases xs with
    | nil => rfl
    | cons d tail =>
      have rowSub : (((dst.drop 1).take ((d::tail).length+1))).Sublist dst :=
        (List.take_sublist _ _).trans (List.drop_sublist _ _)
      have nr : (c::(d::tail)++(dst.drop 1).take ((d::tail).length+1)++pad++carry).Nodup := by
        apply List.nodup_iff_count_le_one.mpr; intro q
        have a := rowSub.count_le q
        have h := List.nodup_iff_count_le_one.mp hn q
        simp only [List.count_cons,List.count_append] at h ⊢; omega
      have rl : ((dst.drop 1).take ((d::tail).length+1)).length=(d::tail).length+1 := by
        rw [List.length_take,List.length_drop]
        simp only [List.length_cons] at hd ⊢; omega
      have rz : regValue ((dst.drop 1).take ((d::tail).length+1)) s.basis=0 :=
        (regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp hz q (rowSub.subset h))
      have me : measurementCount (firstRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry)=
          measurementCount (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) := by
        simp only [firstRow,signedSquareRow,measurementCount_append,headAdd_measurements]
      simp only [rows,signedSquareRows,run_append,me]
      rw [firstRow_eq c (d::tail) _ pad carry nr (by simp) rl s _ rz]

theorem row_low (c : Wire) (xs dst : List Wire) (hx : 1≤xs.length)
    (s base : BasisState) (hl : 0<dst.length)
    (hc : s c=base c) (hs : ∀q∈xs,s q=base q)
    (hv : regValue dst s=signedRowValue (base c) 0 (regValue xs base) xs.length) :
    s (dst.headD 0) = (s (xs.headD 0) ^^ s c) := by
  have vy := regValue_bit dst 0 0 s hl
  have vx := regValue_bit xs 0 0 base (by omega)
  have hhead : s (xs.headD 0)=base (xs.headD 0) := hs _ (by cases xs <;> simp_all)
  have dx : dst.getD 0 0=dst.headD 0 := by cases dst <;> rfl
  have xx : xs.getD 0 0=xs.headD 0 := by cases xs <;> rfl
  norm_num only [Nat.pow_zero,Nat.div_one] at vy vx
  rw [dx,hv] at vy
  rw [xx] at vx
  have small := regValue_lt xs base
  have pos := Nat.two_pow_pos xs.length
  have even : 2^xs.length%2=0 := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : xs.length≠0)
    rw [hk,Nat.pow_succ,Nat.mul_mod]; simp
  rw [hhead,hc]
  cases hb : base c <;> simp only [signedRowValue,hb,Bool.false_eq_true,if_false,if_true,Nat.zero_add] at vy
  · rw [Nat.mod_eq_of_lt (show 2^xs.length-regValue xs base<2^(xs.length+1) by rw [Nat.pow_succ]; omega)] at vy
    cases hy : s (dst.headD 0) <;> cases ha : base (xs.headD 0) <;>
      simp only [hy,ha,hb,Bool.toNat_false,Bool.toNat_true,Bool.false_xor,Bool.true_xor,
        Bool.not_false,Bool.not_true,Bool.xor_false,Bool.xor_true] at * <;> omega
  · rw [Nat.mod_eq_of_lt (show regValue xs base+1<2^(xs.length+1) by rw [Nat.pow_succ]; omega)] at vy
    cases hy : s (dst.headD 0) <;> cases ha : base (xs.headD 0) <;>
      simp only [hy,ha,hb,Bool.toNat_false,Bool.toNat_true,Bool.false_xor,Bool.true_xor,
        Bool.not_false,Bool.not_true,Bool.xor_false,Bool.xor_true] at * <;> omega

def recordPad : Program → List Bool → List Bool
  | [], _ => []
  | .measureX _ _ _::p,[] => false::recordPad p []
  | .measureX _ _ _::p,b::bs => b::recordPad p bs
  | _::p,m => recordPad p m

theorem run_recordPad (p q : Program) (m n : List Bool) (s : State) :
    run (p++q) (recordPad p m++n) s=run q n (run p m s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [recordPad,List.cons_append,run]
    all_goals try exact ih m _
    cases m <;> simp [recordPad,ih]

theorem state_ext {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

theorem rows_roundtrip (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m n : List Bool) (h0 : regValue dst s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    run (rowsClear xs dst pad carry) n (run (rows xs dst pad carry) m s)=s := by
  cases xs with
  | nil => rfl
  | cons c xs => cases xs with
    | nil => rfl
    | cons d tail =>
      let rest := d::tail
      let row := (dst.drop 1).take (rest.length+1)
      let dst2 := dst.drop 2
      have rowSub : row.Sublist dst := (List.take_sublist _ _).trans (List.drop_sublist _ _)
      have dstSub : dst2.Sublist dst := List.drop_sublist _ _
      have nr : (c::rest++row++pad++carry).Nodup := by
        apply List.nodup_iff_count_le_one.mpr; intro q
        have a := rowSub.count_le q
        have h := List.nodup_iff_count_le_one.mp hn q
        simp only [rest,List.count_cons,List.count_append] at h ⊢; omega
      have nt : (rest++dst2++pad++carry).Nodup := by
        apply List.nodup_iff_count_le_one.mpr; intro q
        have a := dstSub.count_le q
        have h := List.nodup_iff_count_le_one.mp hn q
        simp only [rest,List.count_cons,List.count_append] at h ⊢; omega
      have dn : dst.Nodup := by
        apply List.nodup_iff_count_le_one.mpr; intro q
        have h := List.nodup_iff_count_le_one.mp hn q
        simp only [List.count_cons,List.count_append] at h; omega
      have rl : row.length=rest.length+1 := by
        dsimp [row,rest]; rw [List.length_take,List.length_drop]
        simp only [List.length_cons] at hd ⊢; omega
      have tl : dst2.length=2*rest.length := by
        dsimp [dst2,rest]; rw [List.length_drop]
        simp only [List.length_cons] at hd ⊢; omega
      have rz : regValue row s.basis=0 :=
        (regValue_zero _ _).mpr (fun q h => (regValue_zero _ _).mp h0 q (rowSub.subset h))
      let m1 := m.take (measurementCount (firstRow c rest row pad carry))
      let m2 := m.drop (measurementCount (firstRow c rest row pad carry))
      let n1 := n.take (measurementCount (signedSquareRowsClear rest dst2 pad carry))
      let n2 := n.drop (measurementCount (signedSquareRowsClear rest dst2 pad carry))
      let u := run (firstRow c rest row pad carry) m1 s
      have ue : u=run (signedSquareRow c rest row pad carry) m1 s :=
        firstRow_eq c rest row pad carry nr (by simp [rest]) rl s m1 rz
      have ff := signedSquareRow_frame c rest row pad carry nr rl hp (by simpa [rest] using hc)
        s.basis (s.basis c) rfl hw 0 (Nat.two_pow_pos _)
      have fu := ff s m1 ⟨rz,fun _ _ => rfl⟩
      rw [←ue] at fu
      have outside (q : Wire) (hq : q∈c::rest++pad++carry) : q∉row := by
        intro hr
        have a := List.count_pos_iff.mpr hq
        have b := List.count_pos_iff.mpr hr
        have z := List.nodup_iff_count_le_one.mp nr q
        simp only [List.count_cons,List.count_append] at a z; omega
      have high0 : regValue (dst2.drop rest.length) u.basis=0 := by
        apply (regValue_zero _ _).mpr; intro q hq
        have hdq : q∈dst := dstSub.subset (List.mem_of_mem_drop hq)
        have qr : q∉row := by
          intro hr
          have dis := List.disjoint_take_drop ((List.drop_sublist 1 dst).nodup dn) (Nat.le_refl (rest.length+1))
          apply List.disjoint_left.mp dis hr
          simpa [dst2,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hq
        exact (fu.2.2 q qr).trans ((regValue_zero _ _).mp h0 q hdq)
      have workU : regValue (pad++carry) u.basis=0 := by
        rw [←hw]
        apply regValue_congr; intro q hq
        exact fu.2.2 q (outside q (by simp only [List.mem_cons,List.mem_append] at hq ⊢; tauto))
      have mid := signedSquareRows_roundtrip rest dst2 pad carry nt tl (Or.inr hp) (by simp [rest] at hc ⊢; omega)
        u (recordPad (signedSquareRows rest dst2 pad carry) m2++n1) (regValue dst2 u.basis) rfl high0 workU
      rw [run_recordPad] at mid
      have middle : run (signedSquareRowsClear rest dst2 pad carry) n1
          (run (signedSquareRows rest dst2 pad carry) m2 u)=u := state_ext mid.1 mid.2
      have low := row_low c rest row (by simp [rest]) u.basis s.basis (by omega)
        (fu.2.2 c (outside c (by simp)))
        (fun q h => fu.2.2 q (outside q (by simp [h]))) fu.2.1
      have finEq := firstClear_eq c rest row pad carry nr (by simp [rest]) rl u n2 low
      have rr := signedSquareRowClear_frame c rest row pad carry nr rl hp (by simpa [rest] using hc)
        s.basis (s.basis c) rfl hw 0 (Nat.two_pow_pos _)
      have fin := rr u n2 fu.2
      have endEq : run (firstClear c rest row pad carry) n2 u=s := by
        rw [finEq]
        apply state_ext (fin.1.trans fu.1)
        funext q
        by_cases hq : q∈row
        · exact (regValue_eq_iff row _ _).mp (fin.2.1.trans rz.symm) q hq
        · exact fin.2.2 q hq
      simp only [rows,rowsClear,run_append]
      change run (firstClear c rest row pad carry) n2
        (run (signedSquareRowsClear rest dst2 pad carry) n1
          (run (signedSquareRows rest dst2 pad carry) m2 u))=s
      rw [middle,endEq]

theorem headAdd_sublist (xs ys carry : List Wire) (cin : Wire) :
    (headAdd xs ys carry cin).Sublist (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact .refl _
  | cons a as => cases as with
    | nil => exact .refl _
    | cons a' as => cases ys with
      | nil => exact .refl _
      | cons b bs => cases bs with
        | nil => exact .refl _
        | cons b' bs => cases carry with
          | nil => exact .refl _
          | cons k ks =>
            have h : ([Instr.CX a k] : Program).Sublist (majority a b cin k) := by simp [majority]
            exact ((h.append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem first_sublist (c : Wire) (xs dst pad carry : List Wire) :
    (firstRow c xs dst pad carry).Sublist (signedSquareRow c xs dst pad carry) ∧
    (firstClear c xs dst pad carry).Sublist (signedSquareRowClear c xs dst pad carry) := by
  have h := headAdd_sublist (xs++pad.take 1) dst (carry.take xs.length) c
  exact ⟨((List.Sublist.refl _).append h).append (List.Sublist.refl _),
    (List.Sublist.refl _).append ((List.Sublist.refl _).append (h.append ((List.Sublist.refl _).append (List.Sublist.refl _))))⟩

theorem rows_sublist (xs dst pad carry : List Wire) :
    (rows xs dst pad carry).Sublist (signedSquareRows xs dst pad carry) ∧
    (rowsClear xs dst pad carry).Sublist (signedSquareRowsClear xs dst pad carry) := by
  cases xs with
  | nil => exact ⟨.refl _,.refl _⟩
  | cons c xs => cases xs with
    | nil => exact ⟨.refl _,.refl _⟩
    | cons d tail => exact ⟨((first_sublist ..).1).append (List.Sublist.refl _),(List.Sublist.refl _).append ((first_sublist ..).2)⟩

theorem headAdd_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hy : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (headAdd xs ys carry cin)+1=toffoliCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => simp at hx
  | cons a as => cases as with
    | nil => simp at hx
    | cons a' as => cases ys with
      | nil => simp at hy
      | cons b bs => cases bs with
        | nil => simp at hy
        | cons b' bs => cases carry with
          | nil => simp at hc
          | cons k ks => simp [headAdd,addInPlace,majority,toffoliCount_append,toffoliCount]; omega

theorem first_toffoli (c : Wire) (xs dst pad carry : List Wire)
    (hx : 1≤xs.length) (hd : dst.length=xs.length+1) (hp : 1≤pad.length) (hc : xs.length≤carry.length) :
    toffoliCount (firstRow c xs dst pad carry)+1=toffoliCount (signedSquareRow c xs dst pad carry) ∧
    toffoliCount (firstClear c xs dst pad carry)+1=toffoliCount (signedSquareRowClear c xs dst pad carry) := by
  have h := headAdd_toffoli (xs++pad.take 1) dst (carry.take xs.length) c
    (by simp only [List.length_append,List.length_take]; omega) (by omega)
    (by simp only [List.length_take]; omega)
  simp only [firstRow,firstClear,signedSquareRow,signedSquareRowClear,toffoliCount_append] at *
  omega

theorem rows_toffoli (xs dst pad carry : List Wire) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (rows xs dst pad carry)+1=toffoliCount (signedSquareRows xs dst pad carry) ∧
    toffoliCount (rowsClear xs dst pad carry)+1=toffoliCount (signedSquareRowsClear xs dst pad carry) := by
  cases xs with
  | nil => simp at hx
  | cons c xs => cases xs with
    | nil => simp at hx
    | cons d tail =>
      have hl : ((dst.drop 1).take ((d::tail).length+1)).length=(d::tail).length+1 := by
        simp only [List.length_take,List.length_drop,List.length_cons] at hd ⊢; omega
      have h := first_toffoli c (d::tail) _ pad carry (by simp) hl hp (by simpa using hc)
      simp only [rows,rowsClear,signedSquareRows,signedSquareRowsClear,toffoliCount_append]
      omega

theorem wires_sublist {p q : Program} (h : p.Sublist q) : wires p⊆wires q := by
  induction h with
  | slnil => exact Finset.Subset.refl _
  | cons i h ih => exact ih.trans (by simp [wires])
  | cons₂ i h ih => simpa only [wires] using Finset.union_subset_union (Finset.Subset.refl _) ih

theorem slots_sublist {p q : Program} (h : p.Sublist q) : Challenge.gateSlots p≤Challenge.gateSlots q := by
  induction h <;> simp_all [Challenge.gateSlots] <;> omega

end ECDSAAdd.Entrant.SquareHead

end SquareFirstRow

section SquareLowRungs
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SquareBundle
open Arithmetic RecordedQuantum
def zeroHead : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as,b::b'::bs,k::ks,cin =>
      []++addInPlace (a'::as) (b'::bs) ks k++
        eraseCarry a b cin k++[.CX a b,.CX cin b]
  | xs,ys,carry,cin => addInPlace xs ys carry cin

theorem zeroHead_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (zeroHead xs ys carry cin)=measurementCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons a' as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons b' bs =>
          cases carry with
          | nil => rfl
          | cons k ks => simp [zeroHead,addInPlace,measurementCount_append,majority,measurementCount,Nat.add_assoc]

theorem zeroHead_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (s : State) (m : List Bool)
    (hk : carryBit (s.basis (xs.headD 0)) (s.basis (ys.headD 0)) (s.basis cin)=false) :
    run (zeroHead xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  cases xs with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons a' as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons b' bs =>
          cases carry with
          | nil => rfl
          | cons k ks =>
            have h4 : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count_le_one.mpr
              intro q
              have h := List.nodup_iff_count_le_one.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have first (r : List Bool) : run ([] : Program) r s=run (majority a b cin k) r s := by
              rw [majority_correct a b cin k h4]
              have h : carryBit (s.basis a) (s.basis b) (s.basis cin)=false := by simpa using hk
              simp only [run,h,Bool.xor_false]
              exact SquareHead.state_ext rfl (by funext q; simp [writeBit])
            simp only [zeroHead,addInPlace,List.append_assoc,run_append]
            have mc : measurementCount (majority a b cin k)=0 := rfl
            simp only [mc,measurementCount,List.take_zero,List.drop_zero]
            rw [first]

def cinHead : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as,b::b'::bs,k::ks,cin =>
      [.CX cin k]++addInPlace (a'::as) (b'::bs) ks k++
        eraseCarry a b cin k++[.CX a b,.CX cin b]
  | xs,ys,carry,cin => addInPlace xs ys carry cin

theorem cinHead_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (cinHead xs ys carry cin)=measurementCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons a' as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons b' bs =>
          cases carry with
          | nil => rfl
          | cons k ks => simp [cinHead,addInPlace,measurementCount_append,majority,measurementCount,Nat.add_assoc]

theorem cinHead_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (s : State) (m : List Bool)
    (hk : carryBit (s.basis (xs.headD 0)) (s.basis (ys.headD 0)) (s.basis cin)=s.basis cin) :
    run (cinHead xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  cases xs with
  | nil => rfl
  | cons a as =>
    cases as with
    | nil => rfl
    | cons a' as =>
      cases ys with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons b' bs =>
          cases carry with
          | nil => rfl
          | cons k ks =>
            have h4 : [a,b,cin,k].Nodup := by
              apply List.nodup_iff_count_le_one.mpr
              intro q
              have h := List.nodup_iff_count_le_one.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have first (r : List Bool) : run [.CX cin k] r s=run (majority a b cin k) r s := by
              rw [majority_correct a b cin k h4]
              simpa [run,List.headD] using congrArg (State.mk s.phase) (show
                writeBit s.basis k (s.basis k ^^ s.basis cin)=
                writeBit s.basis k (s.basis k ^^ carryBit (s.basis a) (s.basis b) (s.basis cin)) by
                  simp_all)
            simp only [cinHead,addInPlace,List.append_assoc,run_append]
            have mc : measurementCount (majority a b cin k)=0 := rfl
            simp only [mc,measurementCount,List.take_zero,List.drop_zero]
            rw [first]


theorem append_eq (p q post : Program) (hm : measurementCount p=measurementCount q)
    (s : State) (he : ∀r,run p r s=run q r s) (m : List Bool) :
    run (p++post) m s=run (q++post) m s := by
  simp only [run_append,hm]
  rw [he]

theorem write_same (s : BasisState) (q : Wire) : writeBit s q (s q)=s := by
  funext w
  by_cases h : w=q <;> simp [writeBit,h]

def zeroTwo : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::a''::as,b::b'::b''::bs,c::c'::cs,ci =>
      zeroHead (a'::a''::as) (b'::b''::bs) (c'::cs) c++eraseCarry a b ci c++[.CX a b,.CX ci b]
  | xs,ys,carry,ci => addInPlace xs ys carry ci

def secondCin : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::a''::as,b::b'::b''::bs,c::c'::cs,ci =>
      majority a b ci c++cinHead (a'::a''::as) (b'::b''::bs) (c'::cs) c++
        eraseCarry a b ci c++[.CX a b,.CX ci b]
  | xs,ys,carry,ci => addInPlace xs ys carry ci

theorem zeroTwo_eq (a a' a'' b b' b'' c c' ci : Wire) (as bs cs : List Wire)
    (hn : (ci::(a::a'::a''::as)++(b::b'::b''::bs)++(c::c'::cs)).Nodup)
    (s : State) (m : List Bool)
    (h0 : carryBit (s.basis a) (s.basis b) (s.basis ci)=false)
    (h1 : s.basis a'=false) (hc : s.basis c=false) :
    run (zeroTwo (a::a'::a''::as) (b::b'::b''::bs) (c::c'::cs) ci) m s=
      run (addInPlace (a::a'::a''::as) (b::b'::b''::bs) (c::c'::cs) ci) m s := by
  have h4 : [a,b,ci,c].Nodup := knd hn (fun q => by
    simp only [List.count_cons,List.count_append,List.count_nil]; omega)
  have ht : (c::(a'::a''::as)++(b'::b''::bs)++(c'::cs)).Nodup := knd hn (fun q => by
    simp only [List.count_cons,List.count_append]; omega)
  have first (r : List Bool) : run (majority a b ci c) r s=s := by
    rw [majority_correct a b ci c h4]
    simp only [h0,Bool.xor_false,write_same]
  have tail (r : List Bool) := zeroHead_eq (a'::a''::as) (b'::b''::bs) (c'::cs) c ht s r
    (by simp [h1,hc,carryBit])
  have hm : measurementCount (zeroHead (a'::a''::as) (b'::b''::bs) (c'::cs) c)=
      measurementCount (majority a b ci c++addInPlace (a'::a''::as) (b'::b''::bs) (c'::cs) c) := by
    rw [zeroHead_measurements,measurementCount_append]
    have z : measurementCount (majority a b ci c)=0 := rfl
    rw [z,Nat.zero_add]
  have hp (r : List Bool) : run (zeroHead (a'::a''::as) (b'::b''::bs) (c'::cs) c) r s=
      run (majority a b ci c++addInPlace (a'::a''::as) (b'::b''::bs) (c'::cs) c) r s := by
    rw [run_append]
    have z : measurementCount (majority a b ci c)=0 := rfl
    simp only [z,List.take_zero,List.drop_zero,first]
    exact tail r
  have e := append_eq _ _ (eraseCarry a b ci c++[.CX a b,.CX ci b]) hm s hp m
  simpa only [zeroTwo,addInPlace,List.append_assoc] using e

theorem secondCin_eq (a a' a'' b b' b'' c c' ci : Wire) (as bs cs : List Wire)
    (hn : (ci::(a::a'::a''::as)++(b::b'::b''::bs)++(c::c'::cs)).Nodup)
    (s : State) (m : List Bool) (hc : s.basis c=false)
    (hk : carryBit (s.basis a') (s.basis b')
      (carryBit (s.basis a) (s.basis b) (s.basis ci))=
      carryBit (s.basis a) (s.basis b) (s.basis ci)) :
    run (secondCin (a::a'::a''::as) (b::b'::b''::bs) (c::c'::cs) ci) m s=
      run (addInPlace (a::a'::a''::as) (b::b'::b''::bs) (c::c'::cs) ci) m s := by
  have h4 : [a,b,ci,c].Nodup := knd hn (fun q => by
    simp only [List.count_cons,List.count_append,List.count_nil]; omega)
  have ht : (c::(a'::a''::as)++(b'::b''::bs)++(c'::cs)).Nodup := knd hn (fun q => by
    simp only [List.count_cons,List.count_append]; omega)
  have ac : a'≠c := by
    intro h
    have z := List.nodup_iff_count_le_one.mp hn c
    simp only [h,List.count_cons,List.count_append,beq_self_eq_true,if_true] at z; omega
  have bc : b'≠c := by
    intro h
    have z := List.nodup_iff_count_le_one.mp hn c
    simp only [h,List.count_cons,List.count_append,beq_self_eq_true,if_true] at z; omega
  let K := carryBit (s.basis a) (s.basis b) (s.basis ci)
  let t : State := ⟨s.phase,writeBit s.basis c K⟩
  have first (r : List Bool) : run (majority a b ci c) r s=t := by
    rw [majority_correct a b ci c h4]
    simp only [hc,Bool.false_xor]; rfl
  have tail (r : List Bool) := cinHead_eq (a'::a''::as) (b'::b''::bs) (c'::cs) c ht t r
    (by simpa [t,writeBit,ac,bc,K] using hk)
  have hp (r : List Bool) :
      run (majority a b ci c++cinHead (a'::a''::as) (b'::b''::bs) (c'::cs) c) r s=
      run (majority a b ci c++addInPlace (a'::a''::as) (b'::b''::bs) (c'::cs) c) r s := by
    simp only [run_append]
    have z : measurementCount (majority a b ci c)=0 := rfl
    simp only [z,List.take_zero,List.drop_zero,first]
    exact tail r
  have hm : measurementCount (majority a b ci c++cinHead (a'::a''::as) (b'::b''::bs) (c'::cs) c)=
      measurementCount (majority a b ci c++addInPlace (a'::a''::as) (b'::b''::bs) (c'::cs) c) := by
    simp only [measurementCount_append,cinHead_measurements]
  have e := append_eq _ _ (eraseCarry a b ci c++[.CX a b,.CX ci b]) hm s hp m
  simpa only [secondCin,addInPlace,List.append_assoc] using e

theorem head_bit (r : List Wire) (s : BasisState) (h : 0<r.length) :
    (s (r.headD 0)).toNat=regValue r s%2 := by
  have e : r.getD 0 0=r.headD 0 := by cases r <;> rfl
  simpa only [Nat.pow_zero,Nat.div_one,e] using regValue_bit r 0 0 s h

theorem bit0_false (r : List Wire) (s : BasisState) (h : 0<r.length)
    (hz : regValue r s%2=0) : s (r.headD 0)=false := by
  have e := head_bit r s h
  rw [hz] at e
  cases hb : s (r.headD 0) <;> simp_all

theorem bit1_false (r : List Wire) (s : BasisState) (h : 1<r.length)
    (hz : regValue r s%4≤1) : s (r.getD 1 0)=false := by
  have e := regValue_bit r 1 0 s h
  norm_num only [Nat.pow_one] at e
  cases hb : s (r.getD 1 0) <;> simp only [hb,Bool.toNat_false,Bool.toNat_true] at e ⊢ <;> omega

theorem square_low (a : Nat) : a^2%4≤1 := by
  rw [Nat.pow_mod]
  have h : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
  rcases h with h|h|h|h <;> rw [h] <;> norm_num

theorem raw_even (n a : Nat) (hn : 0<n) : (a^2+signedDiagValue a n)%2=0 := by
  have en : 2^n%2=0 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simp [Nat.pow_succ,Nat.mul_mod]
  have e : a%2=0 ∨ a%2=1 := by omega
  rcases e with e|e <;> simp [signedDiagValue,show n≠0 by omega,Nat.add_mod,Nat.mul_mod,Nat.pow_mod,en,e]

theorem source_even_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (hx : 0<xs.length)
    (s : State) (m : List Bool) (hi : s.basis cin=false) (he : regValue xs s.basis%2=0) :
    run (zeroHead xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  apply zeroHead_eq xs ys carry cin hn s m
  rw [bit0_false xs s.basis hx he,hi]
  cases s.basis (ys.headD 0) <;> rfl

theorem three (r : List Wire) (h : 3≤r.length) : ∃a b c t,r=a::b::c::t := by
  cases r with
  | nil => simp at h
  | cons a r => cases r with
    | nil => simp at h
    | cons b r => cases r with
      | nil => simp at h
      | cons c t => exact ⟨a,b,c,t,rfl⟩

theorem two (r : List Wire) (h : 2≤r.length) : ∃a b t,r=a::b::t := by
  cases r with
  | nil => simp at h
  | cons a r => cases r with
    | nil => simp at h
    | cons b t => exact ⟨a,b,t,rfl⟩

theorem twoAdd_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hi : s.basis cin=false) (hX : regValue xs s.basis%4≤1) (hY : regValue ys s.basis%2=0) :
    run (zeroTwo xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  have bx := bit1_false xs s.basis (by omega) hX
  have byy := bit0_false ys s.basis (by omega) hY
  obtain ⟨a,a',a'',as,rfl⟩ := three xs hx
  obtain ⟨b,b',b'',bs,rfl⟩ := three ys hy
  obtain ⟨c,c',cs,rfl⟩ := two carry hc
  apply zeroTwo_eq a a' a'' b b' b'' c c' cin as bs cs hn s m
  · simp only [List.headD_cons] at byy
    rw [byy,hi]; cases s.basis a <;> rfl
  · simpa using bx
  · exact hclean c (by simp)

theorem add_second_condition (xs ys : List Wire) (cin : Wire)
    (hx : 1<xs.length) (hy : 1<ys.length) (s : BasisState)
    (hi : s cin=false) (hX : regValue xs s%4≤1) (hS : (regValue xs s+regValue ys s)%4≤1) :
    carryBit (s (xs.getD 1 0)) (s (ys.getD 1 0))
      (carryBit (s (xs.getD 0 0)) (s (ys.getD 0 0)) (s cin))=
      carryBit (s (xs.getD 0 0)) (s (ys.getD 0 0)) (s cin) := by
  have x0 := regValue_bit xs 0 0 s (by omega)
  have y0 := regValue_bit ys 0 0 s (by omega)
  have y1 := regValue_bit ys 1 0 s hy
  have x1 := bit1_false xs s hx hX
  norm_num only [Nat.pow_zero,Nat.div_one,Nat.pow_one] at x0 y0 y1
  rw [x1,hi]
  cases a : s (xs.getD 0 0) <;> cases b : s (ys.getD 0 0) <;> cases c : s (ys.getD 1 0) <;>
    simp only [a,b,c,Bool.toNat_false,Bool.toNat_true] at x0 y0 y1 ⊢ <;>
    norm_num [carryBit] <;> omega

theorem secondAdd_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hi : s.basis cin=false) (hX : regValue xs s.basis%4≤1)
    (hS : (regValue xs s.basis+regValue ys s.basis)%4≤1) :
    run (secondCin xs ys carry cin) m s=run (addInPlace xs ys carry cin) m s := by
  have hk := add_second_condition xs ys cin (by omega) (by omega) s.basis hi hX hS
  obtain ⟨a,a',a'',as,rfl⟩ := three xs hx
  obtain ⟨b,b',b'',bs,rfl⟩ := three ys hy
  obtain ⟨c,c',cs,rfl⟩ := two carry hc
  exact secondCin_eq a a' a'' b b' b'' c c' cin as bs cs hn s m (hclean c (by simp)) (by simpa using hk)

def subZero (xs ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++zeroHead xs ys carry cin++notRegister ys

def subTwo (xs ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++zeroTwo xs ys carry cin++notRegister ys

def subSecond (xs ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++secondCin xs ys carry cin++notRegister ys

theorem zeroTwo_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (zeroTwo xs ys carry cin)=measurementCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => rfl
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => rfl
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => rfl
      | cons a2 xsTail2 =>
        cases ys with
        | nil => rfl
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => rfl
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => rfl
            | cons b2 ysTail2 =>
              cases carry with
              | nil => rfl
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => rfl
                | cons c1 carryTail1 =>
                  simp [zeroTwo,addInPlace,measurementCount_append,zeroHead_measurements,cinHead_measurements,majority,measurementCount,Nat.add_assoc]
theorem secondCin_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (secondCin xs ys carry cin)=measurementCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => rfl
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => rfl
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => rfl
      | cons a2 xsTail2 =>
        cases ys with
        | nil => rfl
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => rfl
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => rfl
            | cons b2 ysTail2 =>
              cases carry with
              | nil => rfl
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => rfl
                | cons c1 carryTail1 =>
                  simp [secondCin,addInPlace,measurementCount_append,zeroHead_measurements,cinHead_measurements,majority,measurementCount,Nat.add_assoc]
theorem zeroHead_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hy : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (zeroHead xs ys carry cin)+1=toffoliCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => simp at hx
  | cons a as => cases as with
    | nil => simp at hx
    | cons a' as => cases ys with
      | nil => simp at hy
      | cons b bs => cases bs with
        | nil => simp at hy
        | cons b' bs => cases carry with
          | nil => simp at hc
          | cons k ks => simp [zeroHead,addInPlace,majority,toffoliCount_append,toffoliCount]; omega

theorem cinHead_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hy : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (cinHead xs ys carry cin)+1=toffoliCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => simp at hx
  | cons a as => cases as with
    | nil => simp at hx
    | cons a' as => cases ys with
      | nil => simp at hy
      | cons b bs => cases bs with
        | nil => simp at hy
        | cons b' bs => cases carry with
          | nil => simp at hc
          | cons k ks => simp [cinHead,addInPlace,majority,toffoliCount_append,toffoliCount]; omega

theorem not_eq (ys : List Wire) (hn : ys.Nodup) (s : State) (r : List Bool) :
    run (notRegister ys) r s=⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩ :=
  notRegister_correct ys hn s r

theorem subZero_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (hx : 0<xs.length)
    (s : State) (m : List Bool) (hi : s.basis cin=false) (he : regValue xs s.basis%2=0) :
    run (subZero xs ys carry cin) m s=run (subInPlace xs ys carry cin) m s := by
  have ny : ys.Nodup := knd hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have out (q : Wire) (hq : q∈cin::xs++carry) : q∉ys := kdis hn
    (fun q => by simp only [List.count_cons,List.count_append]; omega) q hq
  let t : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have ti : t.basis cin=false := by simp [t,out cin (by simp),hi]
  have tx : regValue xs t.basis=regValue xs s.basis := by
    apply regValue_congr; intro q hq; simp [t,out q (by simp [hq])]
  simp only [subZero,subInPlace,List.append_assoc,run_append,zeroHead_measurements,
    (notRegister_counts ys).2,List.take_zero,List.drop_zero]
  rw [show run (notRegister ys) [] s=t from notRegister_correct ys ny s []]
  rw [source_even_eq xs ys carry cin hn hx t _ ti (by rw [tx]; exact he)]

theorem subSecond_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hX : regValue xs s.basis%4≤1) (hY : regValue ys s.basis%4≤1) :
    run (subSecond xs ys carry cin) m s=run (subInPlace xs ys carry cin) m s := by
  have ax := bit1_false xs s.basis (by omega) hX
  have byy := bit1_false ys s.basis (by omega) hY
  have ny : ys.Nodup := knd hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have out (q : Wire) (hq : q∈cin::xs++carry) : q∉ys := kdis hn
    (fun q => by simp only [List.count_cons,List.count_append]; omega) q hq
  let t : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have h (r : List Bool) : run (secondCin xs ys carry cin) r t=run (addInPlace xs ys carry cin) r t := by
    obtain ⟨a,a',a'',as,rfl⟩ := three xs hx
    obtain ⟨b,b',b'',bs,rfl⟩ := three ys hy
    obtain ⟨c,c',cs,rfl⟩ := two carry hc
    apply secondCin_eq a a' a'' b b' b'' c c' cin as bs cs hn t r
    · simp [t,out c (by simp),hclean c (by simp)]
    · have axo := out a' (by simp)
      have aa : s.basis a'=false := by simpa using ax
      have bb : s.basis b'=false := by simpa using byy
      have ta : t.basis a'=false := by simp [t,axo,aa]
      have tb : t.basis b'=true := by simp [t,bb]
      rw [ta,tb]
      cases carryBit (t.basis a) (t.basis b) (t.basis cin) <;> rfl
  simp only [subSecond,subInPlace,List.append_assoc,run_append,secondCin_measurements,
    (notRegister_counts ys).2,List.take_zero,List.drop_zero]
  rw [show run (notRegister ys) [] s=t from notRegister_correct ys ny s []]
  rw [h]

theorem subTwo_eq (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false)
    (hi : s.basis cin=false) (hX : regValue xs s.basis%4≤1)
    (hP : regValue xs s.basis%2=regValue ys s.basis%2) :
    run (subTwo xs ys carry cin) m s=run (subInPlace xs ys carry cin) m s := by
  have ax := bit1_false xs s.basis (by omega) hX
  have x0 := head_bit xs s.basis (by omega)
  have y0 := head_bit ys s.basis (by omega)
  have ny : ys.Nodup := knd hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have out (q : Wire) (hq : q∈cin::xs++carry) : q∉ys := kdis hn
    (fun q => by simp only [List.count_cons,List.count_append]; omega) q hq
  let t : State := ⟨s.phase,fun q => if q∈ys then !s.basis q else s.basis q⟩
  have h (r : List Bool) : run (zeroTwo xs ys carry cin) r t=run (addInPlace xs ys carry cin) r t := by
    obtain ⟨a,a',a'',as,rfl⟩ := three xs hx
    obtain ⟨b,b',b'',bs,rfl⟩ := three ys hy
    obtain ⟨c,c',cs,rfl⟩ := two carry hc
    have ab : s.basis a=s.basis b := by
      simp only [List.headD_cons] at x0 y0
      cases aa : s.basis a <;> cases bb : s.basis b <;>
        simp only [aa,bb,Bool.toNat_false,Bool.toNat_true] at x0 y0 ⊢ <;> omega
    apply zeroTwo_eq a a' a'' b b' b'' c c' cin as bs cs hn t r
    · have ao := out a (by simp)
      have io := out cin (by simp)
      simp only [t,if_neg ao,if_neg io,hi]
      simp only [List.mem_cons,or_true,if_true]
      rw [ab]
      cases s.basis b <;> rfl
    · have axo := out a' (by simp)
      have aa : s.basis a'=false := by simpa using ax
      simp [t,axo,aa]
    · simp [t,out c (by simp),hclean c (by simp)]
  simp only [subTwo,subInPlace,List.append_assoc,run_append,zeroTwo_measurements,
    (notRegister_counts ys).2,List.take_zero,List.drop_zero]
  rw [show run (notRegister ys) [] s=t from notRegister_correct ys ny s []]
  rw [h]

theorem prefix_mod (r z : List Wire) (k : Nat) (hk : k≤r.length) (s : BasisState) :
    regValue (r++z) s%2^k=regValue r s%2^k := by
  have a := CuccaroStreamedSquareWideLayout.regValue_take_mod (r++z) k (by simp; omega) s
  have b := CuccaroStreamedSquareWideLayout.regValue_take_mod r k hk s
  rw [List.take_append_of_le_length hk] at a
  exact a.symm.trans b

def m6N (R : KRegs) : Program := subSecond (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
def m7N (R : KRegs) : Program := subTwo (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
def m8E (R : KRegs) : Program := zeroHead (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
def c8E (R : KRegs) : Program := subZero (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
def c7N (R : KRegs) : Program := zeroTwo (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
def c6N (R : KRegs) : Program := secondCin (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

def m6R (R : KRegs) : Program := subZero (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
def m7R (R : KRegs) : Program := subZero (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
def c7R (R : KRegs) : Program := zeroHead (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
def c6R (R : KRegs) : Program := zeroHead (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m6N_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (a b : Nat) (ha : regValue R.dlo s.basis=a^2) (ht : regValue R.T s.basis=b^2) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    run (m6N R) m s=run R.m6 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dlo R.zA 2 (by omega) s.basis
  norm_num only [Nat.reducePow] at pc
  have low : regValue (R.dlo++R.zA) s.basis%4≤1 := by rw [pc,ha]; exact square_low _
  unfold m6N KRegs.m6
  apply subSecond_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by omega)
    (by simp only [List.length_take]; omega) s m
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)) low
  rw [ht]; exact square_low _
theorem m7N_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (a b : Nat) (ha : regValue R.dhi s.basis=b^2) (ht : regValue R.T s.basis=2*a*b+b^2) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    run (m7N R) m s=run R.m7 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dhi R.zB 2 (by omega) s.basis
  norm_num only [Nat.reducePow] at pc
  have low : regValue (R.dhi++R.zB) s.basis%4≤1 := by rw [pc,ha]; exact square_low _
  unfold m7N KRegs.m7
  apply subTwo_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by omega)
    (by simp only [List.length_take]; omega) s m
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)) hi0 low
  have p2 := prefix_mod R.dhi R.zB 1 (by omega) s.basis
  norm_num only [Nat.pow_one] at p2
  rw [p2,ha,ht]; simp [Nat.add_mod,Nat.mul_mod]
theorem c7N_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (a b : Nat) (ha : regValue R.dhi s.basis=b^2) (ht : regValue R.T s.basis=2*a*b) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    run (c7N R) m s=run R.c7 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dhi R.zB 2 (by omega) s.basis
  norm_num only [Nat.reducePow] at pc
  have low : regValue (R.dhi++R.zB) s.basis%4≤1 := by rw [pc,ha]; exact square_low _
  unfold c7N KRegs.c7
  apply twoAdd_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by omega)
    (by simp only [List.length_take]; omega) s m
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)) hi0 low
  rw [ht]; simp [Nat.mul_mod]
theorem c6N_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (a b : Nat) (ha : regValue R.dlo s.basis=a^2) (ht : regValue R.T s.basis=2*a*b+b^2) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    run (c6N R) m s=run R.c6 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dlo R.zA 2 (by omega) s.basis
  norm_num only [Nat.reducePow] at pc
  have low : regValue (R.dlo++R.zA) s.basis%4≤1 := by rw [pc,ha]; exact square_low _
  unfold c6N KRegs.c6
  apply secondAdd_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by omega)
    (by simp only [List.length_take]; omega) s m
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq)) hi0 low
  rw [Nat.add_mod,pc,ha,ht,←Nat.add_mod]
  rw [show a^2+(2*a*b+b^2)=(a+b)^2 by ring]
  exact square_low _
theorem m8E_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (v : Nat) (ht : regValue R.T s.basis=2*v) (hi0 : s.basis R.cin=false) :
    run (m8E R) m s=run R.m8 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.T R.zM 1 (by omega) s.basis
  norm_num only [Nat.pow_one] at pc
  unfold m8E KRegs.m8
  apply source_even_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by simp only [List.length_append]; omega) s m hi0
  rw [pc,ht]; simp [Nat.mul_mod]
theorem c8E_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (v : Nat) (ht : regValue R.T s.basis=2*v) (hi0 : s.basis R.cin=false) :
    run (c8E R) m s=run R.c8 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.T R.zM 1 (by omega) s.basis
  norm_num only [Nat.pow_one] at pc
  unfold c8E KRegs.c8
  apply subZero_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by simp only [List.length_append]; omega) s m hi0
  rw [pc,ht]; simp [Nat.mul_mod]
theorem m6R_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (he : regValue R.dlo s.basis%2=0) (hi0 : s.basis R.cin=false) :
    run (m6R R) m s=run R.m6 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dlo R.zA 1 (by omega) s.basis
  norm_num only [Nat.pow_one] at pc
  unfold m6R KRegs.m6
  apply subZero_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by simp only [List.length_append]; omega) s m hi0
  rw [pc]; exact he
theorem m7R_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (he : regValue R.dhi s.basis%2=0) (hi0 : s.basis R.cin=false) :
    run (m7R R) m s=run R.m7 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dhi R.zB 1 (by omega) s.basis
  norm_num only [Nat.pow_one] at pc
  unfold m7R KRegs.m7
  apply subZero_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by simp only [List.length_append]; omega) s m hi0
  rw [pc]; exact he
theorem c7R_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (he : regValue R.dhi s.basis%2=0) (hi0 : s.basis R.cin=false) :
    run (c7R R) m s=run R.c7 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dhi R.zB 1 (by omega) s.basis
  norm_num only [Nat.pow_one] at pc
  unfold c7R KRegs.c7
  apply source_even_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by simp only [List.length_append]; omega) s m hi0
  rw [pc]; exact he
theorem c6R_eq (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (he : regValue R.dlo s.basis%2=0) (hi0 : s.basis R.cin=false) :
    run (c6R R) m s=run R.c6 m s := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have pc := prefix_mod R.dlo R.zA 1 (by omega) s.basis
  norm_num only [Nat.pow_one] at pc
  unfold c6R KRegs.c6
  apply source_even_eq _ _ _ R.cin (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by simp only [List.length_append]; omega) s m hi0
  rw [pc]; exact he

theorem zeroHead_sublist (xs ys carry : List Wire) (cin : Wire) :
    (zeroHead xs ys carry cin).Sublist (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact .refl _
  | cons a as => cases as with
    | nil => exact .refl _
    | cons a' as => cases ys with
      | nil => exact .refl _
      | cons b bs => cases bs with
        | nil => exact .refl _
        | cons b' bs => cases carry with
          | nil => exact .refl _
          | cons k ks =>
            have h : ([] : Program).Sublist (majority a b cin k) := List.nil_sublist _
            exact ((h.append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem cinHead_support (xs ys carry : List Wire) (cin : Wire) :
    wires (cinHead xs ys carry cin)⊆wires (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact Finset.Subset.refl _
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact Finset.Subset.refl _
    | cons a1 xsTail1 =>
      cases ys with
      | nil => exact Finset.Subset.refl _
      | cons b ysTail0 =>
        cases ysTail0 with
        | nil => exact Finset.Subset.refl _
        | cons b1 ysTail1 =>
          cases carry with
          | nil => exact Finset.Subset.refl _
          | cons c carryTail0 =>
            have h : wires [Instr.CX cin c]⊆wires (majority a b cin c) := by
              intro q hq
              simp [majority,wires,Instr.wires] at hq ⊢
              tauto
            change wires ([Instr.CX cin c]++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b])⊆_
            change _⊆wires (majority a b cin c++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b])
            simp only [wires_append]
            exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union h (Finset.Subset.refl _)) (Finset.Subset.refl _)) (Finset.Subset.refl _)
theorem cinHead_physical (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) : GatePhysical (cinHead xs ys carry cin) := by
  cases xs with
  | nil => exact addInPlace_physical _ _ _ _ hn
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact addInPlace_physical _ _ _ _ hn
    | cons a1 xsTail1 =>
      cases ys with
      | nil => exact addInPlace_physical _ _ _ _ hn
      | cons b ysTail0 =>
        cases ysTail0 with
        | nil => exact addInPlace_physical _ _ _ _ hn
        | cons b1 ysTail1 =>
          cases carry with
          | nil => exact addInPlace_physical _ _ _ _ hn
          | cons c carryTail0 =>
            have old := addInPlace_physical (a::a1::xsTail1) (b::b1::ysTail1) (c::carryTail0) cin hn
            change GatePhysical (majority a b cin c++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b]) at old
            have nc : cin≠c := by
              intro e
              have t := List.nodup_iff_count_le_one.mp hn c
              simp only [e,List.count_cons,List.count_append,beq_self_eq_true,if_true] at t
              omega
            have cx : GatePhysical [Instr.CX cin c] := by simpa [GatePhysical,PhysicalInstr,ProperGate] using nc
            change GatePhysical ([Instr.CX cin c]++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b])
            simp only [gatePhysical_append,and_assoc] at old ⊢
            exact ⟨cx,old.2.1,old.2.2.1,old.2.2.2⟩
theorem zeroTwo_sublist (xs ys carry : List Wire) (cin : Wire) :
    (zeroTwo xs ys carry cin).Sublist (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact List.Sublist.refl _
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact List.Sublist.refl _
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => exact List.Sublist.refl _
      | cons a2 xsTail2 =>
        cases ys with
        | nil => exact List.Sublist.refl _
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => exact List.Sublist.refl _
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => exact List.Sublist.refl _
            | cons b2 ysTail2 =>
              cases carry with
              | nil => exact List.Sublist.refl _
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => exact List.Sublist.refl _
                | cons c1 carryTail1 =>
                  have t := zeroHead_sublist (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c
                  have h := (List.nil_sublist (majority a b cin c)).append t
                  exact ((h.append (List.Sublist.refl _)).append (List.Sublist.refl _))
theorem secondCin_support (xs ys carry : List Wire) (cin : Wire) :
    wires (secondCin xs ys carry cin)⊆wires (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact Finset.Subset.refl _
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact Finset.Subset.refl _
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => exact Finset.Subset.refl _
      | cons a2 xsTail2 =>
        cases ys with
        | nil => exact Finset.Subset.refl _
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => exact Finset.Subset.refl _
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => exact Finset.Subset.refl _
            | cons b2 ysTail2 =>
              cases carry with
              | nil => exact Finset.Subset.refl _
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => exact Finset.Subset.refl _
                | cons c1 carryTail1 =>
                  have h := cinHead_support (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c
                  change wires (majority a b cin c++cinHead (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])⊆_
                  change _⊆wires (majority a b cin c++addInPlace (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])
                  simp only [wires_append]
                  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)) (Finset.Subset.refl _)
theorem secondCin_physical (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) : GatePhysical (secondCin xs ys carry cin) := by
  cases xs with
  | nil => exact addInPlace_physical _ _ _ _ hn
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact addInPlace_physical _ _ _ _ hn
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => exact addInPlace_physical _ _ _ _ hn
      | cons a2 xsTail2 =>
        cases ys with
        | nil => exact addInPlace_physical _ _ _ _ hn
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => exact addInPlace_physical _ _ _ _ hn
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => exact addInPlace_physical _ _ _ _ hn
            | cons b2 ysTail2 =>
              cases carry with
              | nil => exact addInPlace_physical _ _ _ _ hn
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => exact addInPlace_physical _ _ _ _ hn
                | cons c1 carryTail1 =>
                  have old := addInPlace_physical (a::a1::a2::xsTail2) (b::b1::b2::ysTail2) (c::c1::carryTail1) cin hn
                  change GatePhysical (majority a b cin c++addInPlace (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b]) at old
                  have nt : (c::(a1::a2::xsTail2)++(b1::b2::ysTail2)++(c1::carryTail1)).Nodup := knd hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
                  have tail := cinHead_physical _ _ _ c nt
                  change GatePhysical (majority a b cin c++cinHead (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])
                  simp only [gatePhysical_append,and_assoc] at old ⊢
                  exact ⟨old.1,tail,old.2.2.1,old.2.2.2⟩
theorem zeroHead_slots (xs ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (zeroHead xs ys carry cin)≤Challenge.gateSlots (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact Nat.le_refl _
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact Nat.le_refl _
    | cons a1 xsTail1 =>
      cases ys with
      | nil => exact Nat.le_refl _
      | cons b ysTail0 =>
        cases ysTail0 with
        | nil => exact Nat.le_refl _
        | cons b1 ysTail1 =>
          cases carry with
          | nil => exact Nat.le_refl _
          | cons c carryTail0 =>
            change Challenge.gateSlots (([] : Program)++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b])≤Challenge.gateSlots (majority a b cin c++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b])
            have mg : Challenge.gateSlots (majority a b cin c)=6 := rfl
            simp only [Challenge.gateSlots_append,mg]
            simp only [show Challenge.gateSlots ([] : Program)=0 from rfl]; omega
theorem cinHead_slots (xs ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (cinHead xs ys carry cin)≤Challenge.gateSlots (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact Nat.le_refl _
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact Nat.le_refl _
    | cons a1 xsTail1 =>
      cases ys with
      | nil => exact Nat.le_refl _
      | cons b ysTail0 =>
        cases ysTail0 with
        | nil => exact Nat.le_refl _
        | cons b1 ysTail1 =>
          cases carry with
          | nil => exact Nat.le_refl _
          | cons c carryTail0 =>
            change Challenge.gateSlots ([Instr.CX cin c]++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b])≤Challenge.gateSlots (majority a b cin c++addInPlace (a1::xsTail1) (b1::ysTail1) carryTail0 c++eraseCarry a b cin c++[.CX a b,.CX cin b])
            have mg : Challenge.gateSlots (majority a b cin c)=6 := rfl
            simp only [Challenge.gateSlots_append,mg]
            have one : Challenge.gateSlots [Instr.CX cin c]=1 := rfl
            rw [one]; omega
theorem zeroTwo_slots (xs ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (zeroTwo xs ys carry cin)≤Challenge.gateSlots (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact Nat.le_refl _
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact Nat.le_refl _
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => exact Nat.le_refl _
      | cons a2 xsTail2 =>
        cases ys with
        | nil => exact Nat.le_refl _
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => exact Nat.le_refl _
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => exact Nat.le_refl _
            | cons b2 ysTail2 =>
              cases carry with
              | nil => exact Nat.le_refl _
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => exact Nat.le_refl _
                | cons c1 carryTail1 =>
                  have hh := zeroHead_slots (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c
                  change Challenge.gateSlots (([] : Program)++zeroHead (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])≤Challenge.gateSlots (majority a b cin c++addInPlace (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])
                  have mg : Challenge.gateSlots (majority a b cin c)=6 := rfl
                  simp only [Challenge.gateSlots_append,mg]
                  simp only [show Challenge.gateSlots ([] : Program)=0 from rfl]; omega
theorem secondCin_slots (xs ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (secondCin xs ys carry cin)≤Challenge.gateSlots (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => exact Nat.le_refl _
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => exact Nat.le_refl _
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => exact Nat.le_refl _
      | cons a2 xsTail2 =>
        cases ys with
        | nil => exact Nat.le_refl _
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => exact Nat.le_refl _
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => exact Nat.le_refl _
            | cons b2 ysTail2 =>
              cases carry with
              | nil => exact Nat.le_refl _
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => exact Nat.le_refl _
                | cons c1 carryTail1 =>
                  have hh := cinHead_slots (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c
                  change Challenge.gateSlots (majority a b cin c++cinHead (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])≤Challenge.gateSlots (majority a b cin c++addInPlace (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])
                  have mg : Challenge.gateSlots (majority a b cin c)=6 := rfl
                  simp only [Challenge.gateSlots_append,mg]
                  omega

theorem zeroTwo_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length) :
    toffoliCount (zeroTwo xs ys carry cin)+2=toffoliCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => simp at hx
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => simp at hx
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => simp at hx
      | cons a2 xsTail2 =>
        cases ys with
        | nil => simp at hy
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => simp at hy
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => simp at hy
            | cons b2 ysTail2 =>
              cases carry with
              | nil => simp at hc
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => simp at hc
                | cons c1 carryTail1 =>
                  have h := zeroHead_toffoli (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c (by simp) (by simp) (by simp)
                  change toffoliCount (([] : Program)++zeroHead (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])+2=
                    toffoliCount (majority a b cin c++addInPlace (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])
                  have mg : toffoliCount (majority a b cin c)=1 := rfl
                  simp only [toffoliCount_append,mg]
                  try simp only [show toffoliCount ([] : Program)=0 from rfl]
                  omega
theorem secondCin_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length) :
    toffoliCount (secondCin xs ys carry cin)+1=toffoliCount (addInPlace xs ys carry cin) := by
  cases xs with
  | nil => simp at hx
  | cons a xsTail0 =>
    cases xsTail0 with
    | nil => simp at hx
    | cons a1 xsTail1 =>
      cases xsTail1 with
      | nil => simp at hx
      | cons a2 xsTail2 =>
        cases ys with
        | nil => simp at hy
        | cons b ysTail0 =>
          cases ysTail0 with
          | nil => simp at hy
          | cons b1 ysTail1 =>
            cases ysTail1 with
            | nil => simp at hy
            | cons b2 ysTail2 =>
              cases carry with
              | nil => simp at hc
              | cons c carryTail0 =>
                cases carryTail0 with
                | nil => simp at hc
                | cons c1 carryTail1 =>
                  have h := cinHead_toffoli (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c (by simp) (by simp) (by simp)
                  change toffoliCount (majority a b cin c++cinHead (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])+1=
                    toffoliCount (majority a b cin c++addInPlace (a1::a2::xsTail2) (b1::b2::ysTail2) (c1::carryTail1) c++eraseCarry a b cin c++[.CX a b,.CX cin b])
                  have mg : toffoliCount (majority a b cin c)=1 := rfl
                  simp only [toffoliCount_append,mg]
                  try simp only [show toffoliCount ([] : Program)=0 from rfl]
                  omega
theorem subZero_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (subZero xs ys carry cin)=measurementCount (subInPlace xs ys carry cin) := by
  simp only [subZero,subInPlace,measurementCount_append,zeroHead_measurements]

theorem subZero_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hy : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (subZero xs ys carry cin)+1=toffoliCount (subInPlace xs ys carry cin) := by
  have h := zeroHead_toffoli xs ys carry cin hx hy hc
  simp only [subZero,subInPlace,toffoliCount_append]
  omega

theorem subZero_slots (xs ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subZero xs ys carry cin)≤Challenge.gateSlots (subInPlace xs ys carry cin) := by
  have h := zeroHead_slots xs ys carry cin
  simp only [subZero,subInPlace,Challenge.gateSlots_append]
  omega
theorem subTwo_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (subTwo xs ys carry cin)=measurementCount (subInPlace xs ys carry cin) := by
  simp only [subTwo,subInPlace,measurementCount_append,zeroTwo_measurements]

theorem subTwo_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length) :
    toffoliCount (subTwo xs ys carry cin)+2=toffoliCount (subInPlace xs ys carry cin) := by
  have h := zeroTwo_toffoli xs ys carry cin hx hy hc
  simp only [subTwo,subInPlace,toffoliCount_append]
  omega

theorem subTwo_slots (xs ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subTwo xs ys carry cin)≤Challenge.gateSlots (subInPlace xs ys carry cin) := by
  have h := zeroTwo_slots xs ys carry cin
  simp only [subTwo,subInPlace,Challenge.gateSlots_append]
  omega
theorem subSecond_measurements (xs ys carry : List Wire) (cin : Wire) :
    measurementCount (subSecond xs ys carry cin)=measurementCount (subInPlace xs ys carry cin) := by
  simp only [subSecond,subInPlace,measurementCount_append,secondCin_measurements]

theorem subSecond_toffoli (xs ys carry : List Wire) (cin : Wire)
    (hx : 3≤xs.length) (hy : 3≤ys.length) (hc : 2≤carry.length) :
    toffoliCount (subSecond xs ys carry cin)+1=toffoliCount (subInPlace xs ys carry cin) := by
  have h := secondCin_toffoli xs ys carry cin hx hy hc
  simp only [subSecond,subInPlace,toffoliCount_append]
  omega

theorem subSecond_slots (xs ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subSecond xs ys carry cin)≤Challenge.gateSlots (subInPlace xs ys carry cin) := by
  have h := secondCin_slots xs ys carry cin
  simp only [subSecond,subInPlace,Challenge.gateSlots_append]
  omega
theorem subZero_sublist (xs ys carry : List Wire) (cin : Wire) :
    (subZero xs ys carry cin).Sublist (subInPlace xs ys carry cin) :=
  ((List.Sublist.refl _).append (zeroHead_sublist xs ys carry cin)).append (List.Sublist.refl _)
theorem subTwo_sublist (xs ys carry : List Wire) (cin : Wire) :
    (subTwo xs ys carry cin).Sublist (subInPlace xs ys carry cin) :=
  ((List.Sublist.refl _).append (zeroTwo_sublist xs ys carry cin)).append (List.Sublist.refl _)
theorem subSecond_support (xs ys carry : List Wire) (cin : Wire) :
    wires (subSecond xs ys carry cin)⊆wires (subInPlace xs ys carry cin) := by
  have h := secondCin_support xs ys carry cin
  simp only [subSecond,subInPlace,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)

theorem subSecond_physical (xs ys carry : List Wire) (cin : Wire)
    (hn : (cin::xs++ys++carry).Nodup) : GatePhysical (subSecond xs ys carry cin) := by
  simp only [subSecond,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,secondCin_physical xs ys carry cin hn⟩,notRegister_physical _⟩

theorem m6N_counts (R : KRegs) (w : R.W) :
    toffoliCount (m6N R)+1=toffoliCount R.m6 ∧
    measurementCount (m6N R)=measurementCount R.m6 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold m6N KRegs.m6
  exact ⟨subSecond_toffoli (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    subSecond_measurements _ _ _ _⟩
theorem m7N_counts (R : KRegs) (w : R.W) :
    toffoliCount (m7N R)+2=toffoliCount R.m7 ∧
    measurementCount (m7N R)=measurementCount R.m7 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold m7N KRegs.m7
  exact ⟨subTwo_toffoli (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    subTwo_measurements _ _ _ _⟩
theorem m8E_counts (R : KRegs) (w : R.W) :
    toffoliCount (m8E R)+1=toffoliCount R.m8 ∧
    measurementCount (m8E R)=measurementCount R.m8 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold m8E KRegs.m8
  exact ⟨zeroHead_toffoli (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    zeroHead_measurements _ _ _ _⟩
theorem c8E_counts (R : KRegs) (w : R.W) :
    toffoliCount (c8E R)+1=toffoliCount R.c8 ∧
    measurementCount (c8E R)=measurementCount R.c8 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold c8E KRegs.c8
  exact ⟨subZero_toffoli (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    subZero_measurements _ _ _ _⟩
theorem c7N_counts (R : KRegs) (w : R.W) :
    toffoliCount (c7N R)+2=toffoliCount R.c7 ∧
    measurementCount (c7N R)=measurementCount R.c7 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold c7N KRegs.c7
  exact ⟨zeroTwo_toffoli (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    zeroTwo_measurements _ _ _ _⟩
theorem c6N_counts (R : KRegs) (w : R.W) :
    toffoliCount (c6N R)+1=toffoliCount R.c6 ∧
    measurementCount (c6N R)=measurementCount R.c6 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold c6N KRegs.c6
  exact ⟨secondCin_toffoli (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    secondCin_measurements _ _ _ _⟩
theorem m6R_counts (R : KRegs) (w : R.W) :
    toffoliCount (m6R R)+1=toffoliCount R.m6 ∧
    measurementCount (m6R R)=measurementCount R.m6 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold m6R KRegs.m6
  exact ⟨subZero_toffoli (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    subZero_measurements _ _ _ _⟩
theorem m7R_counts (R : KRegs) (w : R.W) :
    toffoliCount (m7R R)+1=toffoliCount R.m7 ∧
    measurementCount (m7R R)=measurementCount R.m7 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold m7R KRegs.m7
  exact ⟨subZero_toffoli (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    subZero_measurements _ _ _ _⟩
theorem c7R_counts (R : KRegs) (w : R.W) :
    toffoliCount (c7R R)+1=toffoliCount R.c7 ∧
    measurementCount (c7R R)=measurementCount R.c7 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold c7R KRegs.c7
  exact ⟨zeroHead_toffoli (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    zeroHead_measurements _ _ _ _⟩
theorem c6R_counts (R : KRegs) (w : R.W) :
    toffoliCount (c6R R)+1=toffoliCount R.c6 ∧
    measurementCount (c6R R)=measurementCount R.c6 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  unfold c6R KRegs.c6
  exact ⟨zeroHead_toffoli (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by omega) (by simp only [List.length_take]; omega),
    zeroHead_measurements _ _ _ _⟩

end ECDSAAdd.Entrant.SquareBundle

namespace ECDSAAdd.Entrant.SquareBundle
open Arithmetic KG
variable (K : KG)

def makeKG : Program := K.Q1++K.Q2++K.R.smk++K.Q5++m6N K.R++m7N K.R++m8E K.R++K.R.scl0

def clearKG : Program := K.R.smk++c8E K.R++c7N K.R++c6N K.R++K.Q5c++K.R.scl0++K.Q2c++K.Q1c

theorem makeKG_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=0) (hX0 : regValue K.X s.basis=0)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (makeKG K) m s).phase=s.phase ∧
    regValue K.R.dst (run (makeKG K) m s).basis=(regValue K.R.bank s.basis)^2 ∧
    regValue K.R.S (run (makeKG K) m s).basis=0 ∧
    regValue K.R.T (run (makeKG K) m s).basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis ∧
    K.I1 (regValue K.R.lo s.basis) (run (makeKG K) m s).basis ∧
    K.I2 (regValue K.R.hi s.basis) (run (makeKG K) m s).basis ∧
    K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) (run (makeKG K) m s).basis ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (makeKG K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have bv := K.R.bank_value w s.basis
  rw [bv]
  generalize ha : regValue K.R.lo s.basis=a
  generalize hb : regValue K.R.hi s.basis=b
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  obtain ⟨a7,r8,e8⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++(m6N K.R)++(m7N K.R)++(m8E K.R)) K.R.scl0 m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++(m6N K.R)++(m7N K.R)) (m8E K.R) a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++(m6N K.R)) (m7N K.R) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5) (m6N K.R) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.Q1++K.Q2++K.R.smk) K.Q5 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.Q1++K.Q2) K.R.smk a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.Q1 K.Q2 a2 s
  rw [show (makeKG K)=K.Q1++K.Q2++K.R.smk++K.Q5++(m6N K.R)++(m7N K.R)++(m8E K.R)++K.R.scl0 from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- Q1: a^2 into dlo
  have st1 := sp.mk1 s r1 (zero _ _ hd0 (fun q h => mt h)) (zero _ _ hX0 (fun q h => x1 h)) hp0 hc0 hz0 hi0
  rw [ha] at st1
  generalize run K.Q1 r1 s=s1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s1.basis q=s.basis q :=
    fun q h _ _ x => st1.2.2.2 q (fun y => h (mt y)) (fun y => x (x1 y))
  -- Q2: b^2 into dhi
  have dhi1 : regValue K.R.dhi s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hd0 (fun q h => md h))
  have X21 : regValue K.X2 s1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x2 h))
  have hi1 : regValue K.R.hi s1.basis=b := (outV s1 G1 _ (fun q h => Or.inl (md h))).trans hb
  have st2 := sp.mk2 s1 r2 dhi1 X21 ((outV s1 G1 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s1 G1 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s1 G1 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [hi1] at st2
  generalize run K.Q2 r2 s1=s2 at st2 ⊢
  have F2 : ∀q,q∉K.R.dhi → q∉K.X2 → s2.basis q=s1.basis q := st2.2.2.2
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s2.basis q=s.basis q :=
    fun q h hS hT x => (F2 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo s2.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have I12 : K.I1 a s2.basis := sp.lc1 a s1.basis s2.basis (fun q hq => (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st1.2.2.1
  -- sum register
  have S2 : regValue K.R.S s2.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    (F2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (st1.2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)))).trans hS0
  have st3 := K.R.smk_correct w hR s2 r3 S2 ((outV s2 G2 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s2 G2 K.R.carry (by intro q h; simp [h])).trans hc0) ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  have lo2 : regValue K.R.lo s2.basis=a := (outV s2 G2 K.R.lo (fun q h => Or.inl (mt h))).trans ha
  have hi2 : regValue K.R.hi s2.basis=b := (outV s2 G2 K.R.hi (fun q h => Or.inl (md h))).trans hb
  rw [lo2,hi2] at st3
  generalize run K.R.smk r3 s2=s3 at st3 ⊢
  have F3 := st3.2.2
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s3.basis q=s.basis q :=
    fun q h hS hT x => (F3 q hS).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo s3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi s3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st2.2.1
  have I13 : K.I1 a s3.basis := sp.lc1 a s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I12
  have I23 : K.I2 b s3.basis := sp.lc2 b s2.basis s3.basis (fun q hq => (F3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st2.2.2.1
  -- Q5: T = (a+b)^2
  have back3 (q : Wire) (h1 : q∉K.R.dlo) (h2 : q∉K.X1) (h3 : q∉K.R.dhi) (h4 : q∉K.X2) (h5 : q∉K.R.S) :
      s3.basis q=s.basis q :=
    (F3 q h5).trans ((F2 q h3 h4).trans (st1.2.2.2 q h1 h2))
  have T3 : regValue K.R.T s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have X53 : regValue K.X5 s3.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    back3 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans (zero _ _ hX0 (fun q h => x5 h))
  have st5 := sp.mk5 s3 r4 T3 X53 ((outV s3 G3 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV s3 G3 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV s3 G3 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  rw [st3.2.1] at st5
  generalize run K.Q5 r4 s3=s5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → s5.basis q=s3.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G3 q h hS hT x)
  have dlo5 : regValue K.R.dlo s5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi5 : regValue K.R.dhi s5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S5 : regValue K.R.S s5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st3.2.1
  have I15 : K.I1 a s5.basis := sp.lc1 a s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I13
  have I25 : K.I2 b s5.basis := sp.lc2 b s3.basis s5.basis (fun q hq => (F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I23
  have sumLt : a+b<2^K.R.S.length := by
    have hp : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
    omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  -- T -= a^2
  have st6 : (run (m6N K.R) r5 s5).phase=s5.phase ∧ regValue K.R.T (run (m6N K.R) r5 s5).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run (m6N K.R) r5 s5).basis q=s5.basis q := by
    rw [m6N_eq K.R w hR s5 r5 a (a+b) dlo5 st5.2.1 ((outV s5 G5 K.R.carry (by intro q h; simp [h])).trans hc0) ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)]
    unfold KRegs.m6
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.dlo++K.R.zA) K.R.T
      (K.R.carry.take (K.R.T.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) s5 r5
      (fun q hq => (regValue_zero _ _).mp ((outV s5 G5 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo5,outV s5 G5 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st5.2.1,G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [ex]; omega) sqLt,ex]; omega
  generalize run (m6N K.R) r5 s5=s6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hT).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo s6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi s6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  -- T -= b^2
  have st7 : (run (m7N K.R) r6 s6).phase=s6.phase ∧ regValue K.R.T (run (m7N K.R) r6 s6).basis=2*a*b ∧
      ∀q,q∉K.R.T → (run (m7N K.R) r6 s6).basis q=s6.basis q := by
    rw [m7N_eq K.R w hR s6 r6 a b dhi6 st6.2.1 ((outV s6 G6 K.R.carry (by intro q h; simp [h])).trans hc0) ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)]
    unfold KRegs.m7
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.dhi++K.R.zB) K.R.T
      (K.R.carry.take (K.R.T.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) s6 r6
      (fun q hq => (regValue_zero _ _).mp ((outV s6 G6 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      st6.2.1,G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  generalize run (m7N K.R) r6 s6=s7 at st7 ⊢
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s7.basis q=s.basis q :=
    fun q h hS hT x => (st7.2.2 q hT).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo s7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  have dhi7 : regValue K.R.dhi s7.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi6
  have D7 : regValue K.R.dst s7.basis=a^2+2^(2*K.R.h)*b^2 := by rw [K.R.dst_value w,dlo7,dhi7]
  -- dst += 2^h * 2ab
  have st8 : (run (m8E K.R) r7 s7).phase=s7.phase ∧
      regValue K.R.dmid (run (m8E K.R) r7 s7).basis=(2*a*b+(a^2+2^(2*K.R.h)*b^2)/2^K.R.h)%2^(2*K.R.bank.length-K.R.h) ∧
      ∀q,q∉K.R.dmid → (run (m8E K.R) r7 s7).basis q=s7.basis q := by
    rw [m8E_eq K.R w hR s7 r7 (a*b) (by simpa only [Nat.mul_assoc] using st7.2.1) ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)]
    unfold KRegs.m8
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.T++K.R.zM) K.R.dmid (K.R.carry.take (K.R.dmid.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) s7 r7
      (fun q hq => (regValue_zero _ _).mp ((outV s7 G7 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,st7.2.1,outV s7 G7 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      show regValue K.R.dmid s7.basis=regValue K.R.dst s7.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) s7.basis,D7,
      G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,L4]
    simp
  generalize run (m8E K.R) r7 s7=s8 at st8 ⊢
  have G8 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s8.basis q=s.basis q :=
    fun q h hS hT x => (st8.2.2 q (fun y => h (md y))).trans (G7 q h hS hT x)
  have D8 : regValue K.R.dst s8.basis=(a+2^K.R.h*b)^2 := by
    rw [K.R.dst_value_mid w,st8.2.1,kkeep st8.2.2 (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),D7]
    exact KRegs.kfinal a b K.R.h K.R.bank.length aLt bLt (by omega)
  -- facts between s5 and s8: only T and dmid changed
  have back8 (q : Wire) (hT : q∉K.R.T) (hd : q∉K.R.dst) : s8.basis q=s5.basis q :=
    (st8.2.2 q (fun y => hd (md y))).trans ((st7.2.2 q hT).trans (st6.2.2 q hT))
  have S8 : regValue K.R.S s8.basis=a+b := (regValue_congr _ _ _ (fun q hq => back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S5
  have T8 : regValue K.R.T s8.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st8.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1
  have I18 : K.I1 a s8.basis := sp.lc1 a s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I15
  have I28 : K.I2 b s8.basis := sp.lc2 b s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I25
  have I58 : K.I5 (a+b) s8.basis := sp.lc5 (a+b) s5.basis s8.basis (fun q hq => (back8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) st5.2.2.1
  -- clean the sum register
  have st9 := K.R.scl0_correct w hR s8 r8
    (by rw [S8,(outV s8 G8 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV s8 G8 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV s8 G8 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s8 G8 K.R.carry (by intro q h; simp [h])).trans hc0) ((G8 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl0 r8 s8=s9 at st9 ⊢
  refine ⟨st9.1.trans (st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,st9.2.1,?_,?_,?_,?_,?_⟩
  · rw [←D8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · rw [←T8]; exact regValue_congr _ _ _ (fun q hq => st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))
  · exact sp.lc1 a s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I18
  · exact sp.lc2 b s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I28
  · exact sp.lc5 (a+b) s8.basis s9.basis (fun q hq => (st9.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) I58
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · exact ((regValue_zero _ _).mp st9.2.1 q hS).trans ((regValue_zero _ _).mp hS0 q hS).symm
    · exact (st9.2.2 q hS).trans (G8 q hd hS hT hx)

theorem clearKG_correct (sp : K.Spec) (hn : K.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=(regValue K.R.bank s.basis)^2) (hS0 : regValue K.R.S s.basis=0)
    (hT0 : regValue K.R.T s.basis=2*regValue K.R.lo s.basis*regValue K.R.hi s.basis)
    (hI1 : K.I1 (regValue K.R.lo s.basis) s.basis) (hI2 : K.I2 (regValue K.R.hi s.basis) s.basis)
    (hI5 : K.I5 (regValue K.R.lo s.basis+regValue K.R.hi s.basis) s.basis)
    (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    (run (clearKG K) m s).phase=s.phase ∧
    regValue K.R.dst (run (clearKG K) m s).basis=0 ∧
    regValue K.R.S (run (clearKG K) m s).basis=0 ∧
    regValue K.R.T (run (clearKG K) m s).basis=0 ∧
    regValue K.X (run (clearKG K) m s).basis=0 ∧
    ∀q,q∉K.R.dst → q∉K.R.T → q∉K.X → (run (clearKG K) m s).basis q=s.basis q := by
  have w := sp.w
  have hR := K.rnd hn
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := K.R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  rw [K.R.bank_value w s.basis] at hd0
  generalize ha : regValue K.R.lo s.basis=a at hd0 hT0 hI1 hI5
  generalize hb : regValue K.R.hi s.basis=b at hd0 hT0 hI2 hI5
  have aLt : a<2^K.R.h := by rw [←ha,←L0]; exact regValue_lt _ _
  have bLt : b<2^(K.R.bank.length-K.R.h) := by rw [←hb,←L1]; exact regValue_lt _ _
  have mt {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.take k) : q∈l := List.mem_of_mem_take h
  have md {l : List Wire} {k : Nat} {q : Wire} (h : q∈l.drop k) : q∈l := List.mem_of_mem_drop h
  have x1 {q : Wire} (h : q∈K.X1) : q∈K.X := by simp [X,h]
  have x2 {q : Wire} (h : q∈K.X2) : q∈K.X := by simp [X,h]
  have x5 {q : Wire} (h : q∈K.X5) : q∈K.X := by simp [X,h]
  have xo (q : Wire) (h : q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) : q∉K.X := by
    apply K.rX hn q; simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
  have outV (t : State) (G : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t.basis q=s.basis q) (r : List Wire)
      (hr : ∀q∈r,q∈K.R.bank ∨ q∈K.R.z ∨ q∈K.R.pad ∨ q∈K.R.carry ∨ q=K.R.cin) :
      regValue r t.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => let o := K.R.outside hR q (hr q hq); G q o.1 o.2.1 o.2.2 (xo q (hr q hq)))
  have zero (r : List Wire) (big : List Wire) (hz : regValue big s.basis=0) (sub : ∀q∈r,q∈big) :
      regValue r s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hz q (sub q hq))
  have nD : K.R.dst.Nodup := knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have cinO : K.R.cin∉K.R.dst ∧ K.R.cin∉K.R.S ∧ K.R.cin∉K.R.T := K.R.outside hR K.R.cin (by simp)
  have cinX : K.R.cin∉K.X := xo _ (by simp)
  have hp2 : 2^K.R.h≤2^(K.R.bank.length-K.R.h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : 2^K.R.S.length=2*2^(K.R.bank.length-K.R.h) := by rw [hSl,pow_succ]; ring
  have sumLt : a+b<2^K.R.S.length := by omega
  have sqLt : (a+b)^2<2^K.R.T.length := by rw [hTl]; exact square_bound _ _ sumLt
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have hX : (a+2^K.R.h*b)^2=(a^2+2^(2*K.R.h)*b^2)+2^K.R.h*(2*a*b) := by ring
  have hpos : 0<2^K.R.h := Nat.two_pow_pos _
  have XLt : (a+2^K.R.h*b)^2<2^(2*K.R.bank.length) := by
    have hsplit : 2^K.R.bank.length=2^K.R.h*2^(K.R.bank.length-K.R.h) := by rw [←pow_add]; congr 1; omega
    have hm := Nat.mul_le_mul_left (2^K.R.h) (show b+1≤2^(K.R.bank.length-K.R.h) by omega)
    rw [Nat.mul_add,Nat.mul_one,←hsplit] at hm
    exact square_bound _ _ (by omega)
  have aSq : a^2<2^(2*K.R.h) := square_bound _ _ aLt
  obtain ⟨a7,r8,e8⟩ := kseq (K.R.smk++(c8E K.R)++(c7N K.R)++(c6N K.R)++K.Q5c++K.R.scl0++K.Q2c) K.Q1c m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.R.smk++(c8E K.R)++(c7N K.R)++(c6N K.R)++K.Q5c++K.R.scl0) K.Q2c a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.R.smk++(c8E K.R)++(c7N K.R)++(c6N K.R)++K.Q5c) K.R.scl0 a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.R.smk++(c8E K.R)++(c7N K.R)++(c6N K.R)) K.Q5c a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.R.smk++(c8E K.R)++(c7N K.R)) (c6N K.R) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.R.smk++(c8E K.R)) (c7N K.R) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.R.smk (c8E K.R) a2 s
  rw [show (clearKG K)=K.R.smk++(c8E K.R)++(c7N K.R)++(c6N K.R)++K.Q5c++K.R.scl0++K.Q2c++K.Q1c from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- rebuild S
  have st1 := K.R.smk_correct w hR s r1 hS0 hz0 hc0 hi0
  rw [ha,hb] at st1
  generalize run K.R.smk r1 s=t1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t1.basis q=s.basis q := fun q _ h _ _ => st1.2.2 q h
  have T1 : regValue K.R.T t1.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have D1 : regValue K.R.dst t1.basis=(a+2^K.R.h*b)^2 := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hd0
  -- dst -= 2^h * 2ab
  have st2 : (run (c8E K.R) r2 t1).phase=t1.phase ∧
      regValue K.R.dst (run (c8E K.R) r2 t1).basis=a^2+2^(2*K.R.h)*b^2 ∧
      ∀q,q∉K.R.dmid → (run (c8E K.R) r2 t1).basis q=t1.basis q := by
    rw [c8E_eq K.R w hR t1 r2 (a*b) (by simpa only [Nat.mul_assoc] using T1) ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)]
    unfold KRegs.c8
    obtain ⟨p,f,v⟩ := BalancedInverse.subInPlace_any_correct (K.R.T++K.R.zM) K.R.dmid
      (K.R.carry.take (K.R.dmid.length-1)) K.R.cin (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega)
      (by simp only [List.length_take]; omega) t1 r2
      (fun q hq => (regValue_zero _ _).mp ((outV t1 G1 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [K.R.dst_value_mid w,v,kkeep f (by
      intro q hq hx
      have c1 := List.count_pos_iff.mpr hq; have c2 := List.count_pos_iff.mpr hx
      have c3 := (K.R.counts q).2.2.1
      have c4 := List.nodup_iff_count_le_one.mp nD q
      omega),regValue_append,T1,outV t1 G1 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst K.R.h (by omega),
      show regValue K.R.dmid t1.basis=regValue K.R.dst t1.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) t1.basis,D1,L4]
    have hdiv : (a+2^K.R.h*b)^2/2^K.R.h=(a^2+2^(2*K.R.h)*b^2)/2^K.R.h+2*a*b := by
      rw [hX,Nat.add_mul_div_left _ _ hpos]
    have hmod : (a+2^K.R.h*b)^2%2^K.R.h=(a^2+2^(2*K.R.h)*b^2)%2^K.R.h := by
      rw [hX,Nat.add_mul_mod_self_left]
    have hq : (a+2^K.R.h*b)^2/2^K.R.h<2^(2*K.R.bank.length-K.R.h) := by
      rw [Nat.div_lt_iff_lt_mul hpos,←pow_add,show 2*K.R.bank.length-K.R.h+K.R.h=2*K.R.bank.length by omega]
      exact XLt
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod ((a+2^K.R.h*b)^2/2^K.R.h) (2*a*b) _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  generalize run (c8E K.R) r2 t1=t2 at st2 ⊢
  have G2 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t2.basis q=s.basis q :=
    fun q h hS hT x => (st2.2.2 q (fun y => h (md y))).trans (G1 q h hS hT x)
  have dlo2 : regValue K.R.dlo t2.basis=a^2 := by
    rw [show regValue K.R.dlo t2.basis=regValue K.R.dst t2.basis%2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt aSq]
  have dhi2 : regValue K.R.dhi t2.basis=b^2 := by
    rw [show regValue K.R.dhi t2.basis=regValue K.R.dst t2.basis/2^(2*K.R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst (2*K.R.h) (by omega) t2.basis,st2.2.1,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt aSq,Nat.zero_add]
  have S2 : regValue K.R.S t2.basis=a+b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st1.2.1
  have T2 : regValue K.R.T t2.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st2.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans T1
  -- T += b^2
  have st3 : (run (c7N K.R) r3 t2).phase=t2.phase ∧ regValue K.R.T (run (c7N K.R) r3 t2).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run (c7N K.R) r3 t2).basis q=t2.basis q := by
    rw [c7N_eq K.R w hR t2 r3 a b dhi2 T2 ((outV t2 G2 K.R.carry (by intro q h; simp [h])).trans hc0) ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)]
    unfold KRegs.c7
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.dhi++K.R.zB) K.R.T (K.R.carry.take (K.R.T.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t2 r3
      (fun q hq => (regValue_zero _ _).mp ((outV t2 G2 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      T2,G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega)]; ring
  generalize run (c7N K.R) r3 t2=t3 at st3 ⊢
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t3.basis q=s.basis q :=
    fun q h hS hT x => (st3.2.2 q hT).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo t3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi t3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi2
  have S3 : regValue K.R.S t3.basis=a+b := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S2
  -- T += a^2
  have st4 : (run (c6N K.R) r4 t3).phase=t3.phase ∧ regValue K.R.T (run (c6N K.R) r4 t3).basis=(a+b)^2 ∧
      ∀q,q∉K.R.T → (run (c6N K.R) r4 t3).basis q=t3.basis q := by
    rw [c6N_eq K.R w hR t3 r4 a b dlo3 st3.2.1 ((outV t3 G3 K.R.carry (by intro q h; simp [h])).trans hc0) ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)]
    unfold KRegs.c6
    obtain ⟨p,f,v⟩ := addInPlace_correct (K.R.dlo++K.R.zA) K.R.T (K.R.carry.take (K.R.T.length-1)) K.R.cin
      (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t3 r4
      (fun q hq => (regValue_zero _ _).mp ((outV t3 G3 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dlo3,outV t3 G3 K.R.zA (by intro q h; simp [mt h]),zero K.R.zA K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h)),
      st3.2.1,G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega),ex]; ring
  generalize run (c6N K.R) r4 t3=t4 at st4 ⊢
  have G4 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t4.basis q=s.basis q :=
    fun q h hS hT x => (st4.2.2 q hT).trans (G3 q h hS hT x)
  have dlo4 : regValue K.R.dlo t4.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo3
  have dhi4 : regValue K.R.dhi t4.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi3
  have S4 : regValue K.R.S t4.basis=a+b := (regValue_congr _ _ _ (fun q hq => st4.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S3
  have back4 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) : t4.basis q=s.basis q :=
    (st4.2.2 q h3).trans ((st3.2.2 q h3).trans ((st2.2.2 q (fun y => h2 (md y))).trans (st1.2.2 q h1)))
  -- clear T with the S-square cleanup
  have st5 := sp.cl5 t4 r5 (by rw [st4.2.1,S4])
    (by rw [S4]; exact sp.lc5 (a+b) s.basis t4.basis (fun q hq => (back4 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI5)
    ((outV t4 G4 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t4 G4 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t4 G4 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G4 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q5c r5 t4=t5 at st5 ⊢
  have F5 : ∀q,q∉K.R.T → q∉K.X5 → t5.basis q=t4.basis q := st5.2.2.2
  have G5 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t5.basis q=s.basis q :=
    fun q h hS hT x => (F5 q hT (fun y => x (x5 y))).trans (G4 q h hS hT x)
  have dlo5 : regValue K.R.dlo t5.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo4
  have dhi5 : regValue K.R.dhi t5.basis=b^2 := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi4
  have S5 : regValue K.R.S t5.basis=a+b := (regValue_congr _ _ _ (fun q hq => F5 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S4
  -- clean S
  have st6 := K.R.scl0_correct w hR t5 r6
    (by rw [S5,(outV t5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV t5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV t5 G5 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV t5 G5 K.R.carry (by intro q h; simp [h])).trans hc0) ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl0 r6 t5=t6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hS).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo t6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi t6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  have T6 : regValue K.R.T t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.1
  have X56 : regValue K.X5 t6.basis=0 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st5.2.2.1
  have back6 (q : Wire) (h1 : q∉K.R.S) (h2 : q∉K.R.dst) (h3 : q∉K.R.T) (h4 : q∉K.X5) : t6.basis q=s.basis q :=
    (st6.2.2 q h1).trans ((F5 q h3 h4).trans (back4 q h1 h2 h3))
  -- clear b^2
  have st7 := sp.cl2 t6 r7
    (by rw [dhi6,(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    (by rw [(outV t6 G6 K.R.hi (fun q h => Or.inl (md h))).trans hb]
        exact sp.lc2 b s.basis t6.basis (fun q hq => (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).symm) hI2)
    ((outV t6 G6 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t6 G6 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t6 G6 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q2c r7 t6=t7 at st7 ⊢
  have F7 : ∀q,q∉K.R.dhi → q∉K.X2 → t7.basis q=t6.basis q := st7.2.2.2
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t7.basis q=s.basis q :=
    fun q h hS hT x => (F7 q (fun y => h (md y)) (fun y => x (x2 y))).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo t7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  -- clear a^2
  have st8 := sp.cl1 t7 r8
    (by rw [dlo7,(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha])
    (by rw [(outV t7 G7 K.R.lo (fun q h => Or.inl (mt h))).trans ha]
        exact sp.lc1 a s.basis t7.basis (fun q hq => ((F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq)).trans (back6 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).symm) hI1)
    ((outV t7 G7 K.R.pad (by intro q h; simp [h])).trans hp0)
    ((outV t7 G7 K.R.carry (by intro q h; simp [h])).trans hc0) ((outV t7 G7 K.R.z (by intro q h; simp [h])).trans hz0)
    ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.Q1c r8 t7=t8 at st8 ⊢
  have F8 : ∀q,q∉K.R.dlo → q∉K.X1 → t8.basis q=t7.basis q := st8.2.2.2
  have k78 (r : List Wire) (h : ∀q∈r,q∉K.R.dlo ∧ q∉K.X1 ∧ q∉K.R.dhi ∧ q∉K.X2) :
      regValue r t8.basis=regValue r t6.basis :=
    regValue_congr _ _ _ (fun q hq => (F8 q (h q hq).1 (h q hq).2.1).trans (F7 q (h q hq).2.2.1 (h q hq).2.2.2))
  refine ⟨st8.1.trans (st7.1.trans (st6.1.trans (st5.1.trans (st4.1.trans (st3.1.trans
    (st2.1.trans st1.1)))))),?_,?_,?_,?_,?_⟩
  · rw [K.R.dst_value w,st8.2.1,(regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.1]; simp
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact st6.2.1
  · rw [k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩)]; exact T6
  · rw [X,regValue_append,regValue_append,st8.2.2.1,
      (regValue_congr _ _ _ (fun q hq => F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans st7.2.2.1,
      k78 _ (fun q hq => ⟨kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq,kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq⟩),X56]; simp
  · intro q hd hT hx
    by_cases hS : q∈K.R.S
    · have a1 := (regValue_zero _ _).mp st6.2.1 q hS
      have a2 := (regValue_zero _ _).mp hS0 q hS
      rw [F8 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),F7 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS) (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hS),a1,a2]
    · exact (F8 q (fun y => hd (mt y)) (fun y => hx (x1 y))).trans (G7 q hd hS hT hx)

end ECDSAAdd.Entrant.SquareBundle

namespace ECDSAAdd.Entrant.SquareBundle
open Arithmetic RecordedQuantum
theorem m6N_support (R : KRegs) : wires (m6N R)⊆wires R.m6 :=
  subSecond_support (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m6N_slots (R : KRegs) : Challenge.gateSlots (m6N R)≤Challenge.gateSlots R.m6 :=
  subSecond_slots (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m6N_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (m6N R) := by
  have nd : (R.cin::(R.dlo++R.zA)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  exact subSecond_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin nd
theorem m7N_sublist (R : KRegs) : (m7N R).Sublist R.m7 := subTwo_sublist (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m7N_support (R : KRegs) : wires (m7N R)⊆wires R.m7 :=
  SquareHead.wires_sublist (m7N_sublist R)
theorem m7N_slots (R : KRegs) : Challenge.gateSlots (m7N R)≤Challenge.gateSlots R.m7 :=
  subTwo_slots (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m7N_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (m7N R) := by
  have nd : (R.cin::(R.dhi++R.zB)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := subInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin nd
  exact fun i hi => old i ((m7N_sublist R).subset hi)
theorem m8E_sublist (R : KRegs) : (m8E R).Sublist R.m8 := zeroHead_sublist (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem m8E_support (R : KRegs) : wires (m8E R)⊆wires R.m8 :=
  SquareHead.wires_sublist (m8E_sublist R)
theorem m8E_slots (R : KRegs) : Challenge.gateSlots (m8E R)≤Challenge.gateSlots R.m8 :=
  zeroHead_slots (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin

theorem m8E_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (m8E R) := by
  have nd : (R.cin::(R.T++R.zM)++R.dmid++(R.carry.take (R.dmid.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := addInPlace_physical (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin nd
  exact fun i hi => old i ((m8E_sublist R).subset hi)
theorem c8E_sublist (R : KRegs) : (c8E R).Sublist R.c8 := subZero_sublist (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem c8E_support (R : KRegs) : wires (c8E R)⊆wires R.c8 :=
  SquareHead.wires_sublist (c8E_sublist R)
theorem c8E_slots (R : KRegs) : Challenge.gateSlots (c8E R)≤Challenge.gateSlots R.c8 :=
  subZero_slots (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin

theorem c8E_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (c8E R) := by
  have nd : (R.cin::(R.T++R.zM)++R.dmid++(R.carry.take (R.dmid.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := subInPlace_physical (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin nd
  exact fun i hi => old i ((c8E_sublist R).subset hi)
theorem c7N_sublist (R : KRegs) : (c7N R).Sublist R.c7 := zeroTwo_sublist (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c7N_support (R : KRegs) : wires (c7N R)⊆wires R.c7 :=
  SquareHead.wires_sublist (c7N_sublist R)
theorem c7N_slots (R : KRegs) : Challenge.gateSlots (c7N R)≤Challenge.gateSlots R.c7 :=
  zeroTwo_slots (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c7N_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (c7N R) := by
  have nd : (R.cin::(R.dhi++R.zB)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := addInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin nd
  exact fun i hi => old i ((c7N_sublist R).subset hi)
theorem c6N_support (R : KRegs) : wires (c6N R)⊆wires R.c6 :=
  secondCin_support (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c6N_slots (R : KRegs) : Challenge.gateSlots (c6N R)≤Challenge.gateSlots R.c6 :=
  secondCin_slots (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c6N_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (c6N R) := by
  have nd : (R.cin::(R.dlo++R.zA)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  exact secondCin_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin nd
theorem m6R_sublist (R : KRegs) : (m6R R).Sublist R.m6 := subZero_sublist (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m6R_support (R : KRegs) : wires (m6R R)⊆wires R.m6 :=
  SquareHead.wires_sublist (m6R_sublist R)
theorem m6R_slots (R : KRegs) : Challenge.gateSlots (m6R R)≤Challenge.gateSlots R.m6 :=
  subZero_slots (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m6R_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (m6R R) := by
  have nd : (R.cin::(R.dlo++R.zA)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := subInPlace_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin nd
  exact fun i hi => old i ((m6R_sublist R).subset hi)
theorem m7R_sublist (R : KRegs) : (m7R R).Sublist R.m7 := subZero_sublist (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m7R_support (R : KRegs) : wires (m7R R)⊆wires R.m7 :=
  SquareHead.wires_sublist (m7R_sublist R)
theorem m7R_slots (R : KRegs) : Challenge.gateSlots (m7R R)≤Challenge.gateSlots R.m7 :=
  subZero_slots (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m7R_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (m7R R) := by
  have nd : (R.cin::(R.dhi++R.zB)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := subInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin nd
  exact fun i hi => old i ((m7R_sublist R).subset hi)
theorem c7R_sublist (R : KRegs) : (c7R R).Sublist R.c7 := zeroHead_sublist (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c7R_support (R : KRegs) : wires (c7R R)⊆wires R.c7 :=
  SquareHead.wires_sublist (c7R_sublist R)
theorem c7R_slots (R : KRegs) : Challenge.gateSlots (c7R R)≤Challenge.gateSlots R.c7 :=
  zeroHead_slots (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c7R_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (c7R R) := by
  have nd : (R.cin::(R.dhi++R.zB)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := addInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin nd
  exact fun i hi => old i ((c7R_sublist R).subset hi)
theorem c6R_sublist (R : KRegs) : (c6R R).Sublist R.c6 := zeroHead_sublist (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c6R_support (R : KRegs) : wires (c6R R)⊆wires R.c6 :=
  SquareHead.wires_sublist (c6R_sublist R)
theorem c6R_slots (R : KRegs) : Challenge.gateSlots (c6R R)≤Challenge.gateSlots R.c6 :=
  zeroHead_slots (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c6R_physical (R : KRegs) (hn : R.all.Nodup) : GatePhysical (c6R R) := by
  have nd : (R.cin::(R.dlo++R.zA)++R.T++(R.carry.take (R.T.length-1))).Nodup := knd hn
    (fun q => by have h := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at h ⊢; omega)
  have old := addInPlace_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin nd
  exact fun i hi => old i ((c6R_sublist R).subset hi)
theorem makeKG_support (K : KG) : wires (makeKG K)⊆wires (SumKG.make K) := by
  simp only [makeKG,SumKG.make,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (Finset.Subset.refl _)) (Finset.Subset.refl _)) (Finset.Subset.refl _)) (m6N_support K.R)) (m7N_support K.R)) (m8E_support K.R)) (Finset.Subset.refl _)
theorem makeKG_slots (K : KG) : Challenge.gateSlots (makeKG K)≤Challenge.gateSlots (SumKG.make K) := by
  have hm6N := m6N_slots K.R
  have hm7N := m7N_slots K.R
  have hm8E := m8E_slots K.R
  simp only [makeKG,SumKG.make,Challenge.gateSlots_append]
  omega
theorem makeKG_physical (K : KG) (hn : K.all.Nodup) (old : GatePhysical (SumKG.make K)) :
    GatePhysical (makeKG K) := by
  simp only [SumKG.make,gatePhysical_append,and_assoc] at old
  obtain ⟨a,b,c,d,e,f,g,h⟩ := old
  simp only [makeKG,gatePhysical_append,and_assoc]
  exact ⟨a,b,c,d,m6N_physical K.R (K.rnd hn),m7N_physical K.R (K.rnd hn),m8E_physical K.R (K.rnd hn),h⟩
theorem makeKG_counts (K : KG) (w : K.R.W) :
    toffoliCount (makeKG K)+4=toffoliCount (SumKG.make K) ∧
    measurementCount (makeKG K)=measurementCount (SumKG.make K) := by
  have hm6N := m6N_counts K.R w
  have hm7N := m7N_counts K.R w
  have hm8E := m8E_counts K.R w
  simp only [makeKG,SumKG.make,toffoliCount_append,measurementCount_append]
  constructor <;> omega
theorem clearKG_support (K : KG) : wires (clearKG K)⊆wires (SumKG.clear K) := by
  simp only [clearKG,SumKG.clear,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (c8E_support K.R)) (c7N_support K.R)) (c6N_support K.R)) (Finset.Subset.refl _)) (Finset.Subset.refl _)) (Finset.Subset.refl _)) (Finset.Subset.refl _)
theorem clearKG_slots (K : KG) : Challenge.gateSlots (clearKG K)≤Challenge.gateSlots (SumKG.clear K) := by
  have hc8E := c8E_slots K.R
  have hc7N := c7N_slots K.R
  have hc6N := c6N_slots K.R
  simp only [clearKG,SumKG.clear,Challenge.gateSlots_append]
  omega
theorem clearKG_physical (K : KG) (hn : K.all.Nodup) (old : GatePhysical (SumKG.clear K)) :
    GatePhysical (clearKG K) := by
  simp only [SumKG.clear,gatePhysical_append,and_assoc] at old
  obtain ⟨a,b,c,d,e,f,g,h⟩ := old
  simp only [clearKG,gatePhysical_append,and_assoc]
  exact ⟨a,c8E_physical K.R (K.rnd hn),c7N_physical K.R (K.rnd hn),c6N_physical K.R (K.rnd hn),e,f,g,h⟩
theorem clearKG_counts (K : KG) (w : K.R.W) :
    toffoliCount (clearKG K)+4=toffoliCount (SumKG.clear K) ∧
    measurementCount (clearKG K)=measurementCount (SumKG.clear K) := by
  have hc8E := c8E_counts K.R w
  have hc7N := c7N_counts K.R w
  have hc6N := c6N_counts K.R w
  simp only [clearKG,SumKG.clear,toffoliCount_append,measurementCount_append]
  constructor <;> omega

end ECDSAAdd.Entrant.SquareBundle

end SquareLowRungs

section SquareSharedCarry
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.SquareIncrement
open Arithmetic

def one : MappedBit := ⟨none,true⟩
def zero : MappedBit := ⟨none,false⟩

def add (dst carry : List Wire) (cin : Wire) : Program :=
  match dst,carry with
  | [y,y',y''],[c,c'] => [.CX y c]++mappedAdd [zero,zero] [y',y''] [c'] c++
      mappedEraseCarry one y cin c++mappedSum one y cin
  | _,_ => mappedAdd (mappedConstant none 3 1) dst carry cin

def sub (dst carry : List Wire) (cin : Wire) : Program :=
  notRegister dst++add dst carry cin++notRegister dst

theorem measurements (y y' y'' c c' cin : Wire) :
    measurementCount (add [y,y',y''] [c,c'] cin)=2 := by
  simp [add,zero,one,mappedAdd,mappedMajority,mappedEraseCarry,mappedSum,measurementCount]

theorem add_eq (dst carry : List Wire) (cin : Wire) (hd : dst.length=3) (hc : carry.length=2)
    (hn : (cin::dst++carry).Nodup) (s : State) (m : List Bool) (hi : s.basis cin=false) :
    run (add dst carry cin) m s=run (mappedAdd (mappedConstant none 3 1) dst carry cin) m s := by
  obtain ⟨y,y',y'',rfl⟩ : ∃y y' y'',dst=[y,y',y''] := by
    match dst,hd with | [y,y',y''],_ => exact ⟨y,y',y'',rfl⟩
  obtain ⟨c,c',rfl⟩ : ∃c c',carry=[c,c'] := by
    match carry,hc with | [c,c'],_ => exact ⟨c,c',rfl⟩
  have h3 : [y,cin,c].Nodup := knd hn (fun q => by
    simp only [List.count_cons,List.count_append,List.count_nil]; omega)
  have first (r : List Bool) : run [.CX y c] r s=run (mappedMajority one y cin c) r s := by
    rw [mappedMajority_correct one y cin c h3 (by simp [one])]
    simp only [one,MappedBit.value,Option.map_none,Option.getD_none,Bool.xor_false,hi]
    have h : carryBit true (s.basis y) false=s.basis y := by cases s.basis y <;> rfl
    simp only [run,h]
  have old : mappedAdd (mappedConstant none 3 1) [y,y',y''] [c,c'] cin=
      mappedMajority one y cin c++mappedAdd [zero,zero] [y',y''] [c'] c++
        mappedEraseCarry one y cin c++mappedSum one y cin := rfl
  rw [old]
  simp only [add,List.append_assoc,run_append]
  have mz : measurementCount (mappedMajority one y cin c)=0 := rfl
  simp only [mz,measurementCount,List.take_zero,List.drop_zero]
  rw [first]

theorem sub_eq (dst carry : List Wire) (cin : Wire) (hd : dst.length=3) (hc : carry.length=2)
    (hn : (cin::dst++carry).Nodup) (s : State) (m : List Bool) (hi : s.basis cin=false) :
    run (sub dst carry cin) m s=run (mappedSub (mappedConstant none 3 1) dst carry cin) m s := by
  have dn : dst.Nodup := knd hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have co : cin∉dst := (List.nodup_cons.mp hn).1 ∘ (List.mem_append_left carry)
  let t : State := ⟨s.phase,fun q => if q∈dst then !s.basis q else s.basis q⟩
  have ci : t.basis cin=false := by simp [t,co,hi]
  have am : measurementCount (add dst carry cin)=measurementCount (mappedAdd (mappedConstant none 3 1) dst carry cin) := by
    obtain ⟨y,y',y'',rfl⟩ : ∃y y' y'',dst=[y,y',y''] := by match dst,hd with | [y,y',y''],_ => exact ⟨y,y',y'',rfl⟩
    obtain ⟨c,c',rfl⟩ : ∃c c',carry=[c,c'] := by match carry,hc with | [c,c'],_ => exact ⟨c,c',rfl⟩
    rw [measurements]
    rfl
  simp only [sub,mappedSub,List.append_assoc,run_append,am,(notRegister_counts dst).2,List.take_zero,List.drop_zero]
  rw [show run (notRegister dst) [] s=t from notRegister_correct dst dn s []]
  rw [add_eq dst carry cin hd hc hn t _ ci]

theorem add_sublist (dst carry : List Wire) (cin : Wire) :
    (add dst carry cin).Sublist (mappedAdd (mappedConstant none 3 1) dst carry cin) := by
  unfold add
  split
  · rename_i y y' y'' c c'
    have h : ([Instr.CX y c] : Program).Sublist (mappedMajority one y cin c) := by
      simp [mappedMajority,one]
    exact ((h.append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)
  · exact List.Sublist.refl _

theorem sub_sublist (dst carry : List Wire) (cin : Wire) :
    (sub dst carry cin).Sublist (mappedSub (mappedConstant none 3 1) dst carry cin) :=
  ((List.Sublist.refl _).append (add_sublist dst carry cin)).append (List.Sublist.refl _)

theorem counts (dst carry : List Wire) (cin : Wire) (hd : dst.length=3) (hc : carry.length=2) :
    toffoliCount (add dst carry cin)=1 ∧ measurementCount (add dst carry cin)=2 ∧
    toffoliCount (sub dst carry cin)=1 ∧ measurementCount (sub dst carry cin)=2 := by
  obtain ⟨y,y',y'',rfl⟩ : ∃y y' y'',dst=[y,y',y''] := by
    match dst,hd with | [y,y',y''],_ => exact ⟨y,y',y'',rfl⟩
  obtain ⟨c,c',rfl⟩ : ∃c c',carry=[c,c'] := by
    match carry,hc with | [c,c'],_ => exact ⟨c,c',rfl⟩
  simp [add,sub,zero,one,mappedAdd,mappedMajority,mappedEraseCarry,mappedSum,
    toffoliCount_append,measurementCount_append,toffoliCount,measurementCount,
    (notRegister_counts [y,y',y'']).1,(notRegister_counts [y,y',y'']).2]

end ECDSAAdd.Entrant.SquareIncrement

end SquareSharedCarry

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- The unnormalized signed-row square. -/
def rawMakeRef (xs dst pad carry : List Wire) : Program :=
  signedSquareRows xs dst pad carry ++ signedSquareTop xs dst

def rawClearRef (xs dst pad carry : List Wire) : Program :=
  signedSquareTop xs dst ++ signedSquareRowsClear xs dst pad carry

theorem rawMakeRef_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMakeRef xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMakeRef xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMakeRef xs dst pad carry) m s).basis q=s.basis q := by
  let a := m.take (measurementCount (signedSquareRows xs dst pad carry))
  let b := m.drop (measurementCount (signedSquareRows xs dst pad carry))
  have r := signedSquareRows_correct xs dst pad carry hn hd (Or.inr hp) hc s a 0 h0
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq)))
    (by simp [regValue_append,hp0,hc0])
  let u := run (signedSquareRows xs dst pad carry) a s
  have nt : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append] at h ⊢; omega
  have t := signedSquareTop_correct xs dst nt hd u b r.2.2.2.2
  have source (q : Wire) (hq : q∈xs) : u.basis q=s.basis q := r.2.2.1 q (by
    intro bad
    have h := List.nodup_iff_count.mp nt q
    have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
    simp only [List.count_append] at h; omega)
  have topSame : signedTopTerm xs u.basis=signedTopTerm xs s.basis :=
    signedTopTerm_congr xs _ _ source
  simp only [rawMakeRef,run_append]
  refine ⟨t.1.trans r.1,?_,fun q hq => (t.2.2.1 q hq).trans (r.2.2.1 q hq)⟩
  rw [t.2.1,r.2.1,topSame,Nat.zero_add,←signedRawValue_rows_top]
  exact signedRawValue_correct xs s.basis (List.ne_nil_of_length_pos (by omega))

/-- The shared affine correction, expressed in the carry and the sum bits. -/
def sharedWord (h a b : Nat) : Nat :=
  (2^(h-1)-1-(a+b)%2^(h-1))+
    2^(h-1)*((a%2^(h-1)+b%2^(h-1))/2^(h-1))+
    2^h*(1-((a+b)/2^(h-1))%2)

theorem diagonal_identity (h a b : Nat) (hh : h=32 ∨ h=33)
    (ha : a<2^h) (hb : b<2^h) :
    (signedDiagValue (a+b) (h+1) : Int) - signedDiagValue a h - signedDiagValue b h =
      (2^h : Nat)*(sharedWord h a b + 1 : Int) - (2^(2*h-1) : Nat) := by
  rcases hh with rfl|rfl <;>
    norm_num [signedDiagValue,sharedWord] at * <;> omega


theorem sub_congr (x n y : Nat) (hy : y≤n) :
    (((x+n-y)%n : Nat) : Int) ≡ (x : Int)-y [ZMOD (n : Int)] := by
  have h : y≤x+n := by omega
  simp only [Int.ModEq,Int.natCast_mod,Int.natCast_sub h,Int.natCast_add]
  simp [Int.sub_emod,Int.add_emod]

theorem lift_sub_congr (x p n w : Nat) (hw : w+1≤n) :
    ((x%p+p*((x/p+n-w-1)%n) : Nat) : Int) ≡
      (x : Int)-(p : Int)*(w+1) [ZMOD ((p*n : Nat) : Int)] := by
  have hsub : x/p+n-w-1=x/p+n-(w+1) := by omega
  have r := sub_congr (x/p) n (w+1) hw
  rw [←hsub] at r
  have r' := (r.mul_left' (c:=(p : Int))).add_left (x%p : Nat)
  have split : ((x%p : Nat) : Int)+(p : Int)*(x/p)=x := by exact_mod_cast Nat.mod_add_div x p
  push_cast at r' ⊢
  push_cast at split
  convert r' using 1 <;> try rfl
  all_goals nlinarith only [split]

theorem lift_add_congr (x p n k : Nat) :
    ((x%p+p*((x/p+k)%n) : Nat) : Int) ≡
      (x : Int)+(p : Int)*k [ZMOD ((p*n : Nat) : Int)] := by
  have r : (((x/p+k)%n : Nat) : Int) ≡ ((x/p+k : Nat) : Int) [ZMOD (n : Int)] := by
    simp only [Int.natCast_mod]; exact Int.mod_modEq _ _
  have r' := (r.mul_left' (c:=(p : Int))).add_left (x%p : Nat)
  have split : ((x%p : Nat) : Int)+(p : Int)*(x/p)=x := by exact_mod_cast Nat.mod_add_div x p
  push_cast at r' ⊢
  push_cast at split
  convert r' using 1 <;> try rfl
  all_goals nlinarith only [split]

theorem state_ext {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

def recordPad : Program → List Bool → List Bool
  | [], _ => []
  | .measureX _ _ _ :: p, [] => false::recordPad p []
  | .measureX _ _ _ :: p, b::bs => b::recordPad p bs
  | _::p, m => recordPad p m

theorem run_recordPad (p q : Program) (m n : List Bool) (s : State) :
    run (p++q) (recordPad p m++n) s=run q n (run p m s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [recordPad,List.cons_append,run]
    all_goals try exact ih m _
    cases m <;> simp [recordPad,ih]

theorem rawRef_roundtrip (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m n : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    run (rawClearRef xs dst pad carry) n (run (rawMakeRef xs dst pad carry) m s)=s := by
  let rows := signedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let clr := signedSquareRowsClear xs dst pad carry
  have nt : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append] at h ⊢; omega
  have topCancel (u : State) (a b : List Bool) : run top b (run top a u)=u := by
    have r := signedSquareTop_roundtrip xs dst nt u (recordPad top a++b)
    rw [run_recordPad] at r
    simpa only [top] using r
  have rowsCancel (a b : List Bool) : run clr b (run rows a s)=s := by
    have r := signedSquareRows_roundtrip xs dst pad carry hn hd (Or.inr hp) hc s
      (recordPad rows a++b) 0 h0
      ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq)))
      (by simp [regValue_append,hp0,hc0])
    rw [run_recordPad] at r
    exact state_ext r.1 r.2
  simp only [rawClearRef,rawMakeRef,run_append]
  rw [topCancel]
  exact rowsCancel _ _

theorem rawClearRef_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClearRef xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClearRef xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClearRef xs dst pad carry) m s).basis q=s.basis q := by
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
    simp only [List.count_append] at h a; omega
  have keep (r : List Wire) (hr : ∀q∈r,q∈xs++pad++carry) :
      regValue r base.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [base,away q (hr q hq)])
  have d0 : regValue dst base.basis=0 := (regValue_zero _ _).mpr (fun q hq => by simp [base,hq])
  have p0 := (keep pad (fun q h => by simp [h])).trans hp0
  have c0 := (keep carry (fun q h => by simp [h])).trans hc0
  have f := rawMakeRef_correct xs dst pad carry hn hx hd hp hc base [] d0 p0 c0
  have same : run (rawMakeRef xs dst pad carry) [] base=s := by
    apply state_ext (t:=s) (show _=s.phase from f.1)
    funext q
    by_cases hq : q∈dst
    · apply (regValue_eq_iff dst _ _).mp _ q hq
      rw [f.2.1,keep xs (fun q h => by simp [h]),h0]
    · exact (f.2.2 q hq).trans (by simp [base,hq])
  have restore := rawRef_roundtrip xs dst pad carry hn hx hd hp hc base [] m d0 p0 c0
  rw [same] at restore
  rw [restore]
  exact ⟨rfl,d0,fun q hq => by simp [base,hq]⟩

/-- The raw producer with a known first carry. -/
def rawMake (xs dst pad carry : List Wire) : Program :=
  SquareHead.rows xs dst pad carry ++ signedSquareTop xs dst

def rawClear (xs dst pad carry : List Wire) : Program :=
  signedSquareTop xs dst ++ SquareHead.rowsClear xs dst pad carry

theorem rawMake_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMake xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMake xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMake xs dst pad carry) m s).basis q=s.basis q := by
  have h := rawMakeRef_correct xs dst pad carry hn hx hd hp hc s m h0 hp0 hc0
  simpa only [rawMake,rawMakeRef,run_append,(SquareHead.rows_measurements xs dst pad carry).1,
    SquareHead.rows_eq xs dst pad carry hn hd s _ h0] using h
theorem raw_roundtrip (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m n : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    run (rawClear xs dst pad carry) n (run (rawMake xs dst pad carry) m s)=s := by
  let rows := SquareHead.rows xs dst pad carry
  let top := signedSquareTop xs dst
  let clr := SquareHead.rowsClear xs dst pad carry
  have nt : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append] at h ⊢; omega
  have topCancel (u : State) (a b : List Bool) : run top b (run top a u)=u := by
    have r := signedSquareTop_roundtrip xs dst nt u (recordPad top a++b)
    rw [run_recordPad] at r
    simpa only [top] using r
  have rowsCancel (a b : List Bool) : run clr b (run rows a s)=s := by
    exact SquareHead.rows_roundtrip xs dst pad carry hn hd hp hc s a b h0
      (by simp [regValue_append,hp0,hc0])
  simp only [rawClear,rawMake,run_append]
  rw [topCancel]
  exact rowsCancel _ _

theorem rawClear_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClear xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClear xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClear xs dst pad carry) m s).basis q=s.basis q := by
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
    simp only [List.count_append] at h a; omega
  have keep (r : List Wire) (hr : ∀q∈r,q∈xs++pad++carry) :
      regValue r base.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [base,away q (hr q hq)])
  have d0 : regValue dst base.basis=0 := (regValue_zero _ _).mpr (fun q hq => by simp [base,hq])
  have p0 := (keep pad (fun q h => by simp [h])).trans hp0
  have c0 := (keep carry (fun q h => by simp [h])).trans hc0
  have f := rawMake_correct xs dst pad carry hn hx hd hp hc base [] d0 p0 c0
  have same : run (rawMake xs dst pad carry) [] base=s := by
    apply state_ext (t:=s) (show _=s.phase from f.1)
    funext q
    by_cases hq : q∈dst
    · apply (regValue_eq_iff dst _ _).mp _ q hq
      rw [f.2.1,keep xs (fun q h => by simp [h]),h0]
    · exact (f.2.2 q hq).trans (by simp [base,hq])
  have restore := raw_roundtrip xs dst pad carry hn hx hd hp hc base [] m d0 p0 c0
  rw [same] at restore
  rw [restore]
  exact ⟨rfl,d0,fun q hq => by simp [base,hq]⟩

theorem raw_sublist (xs dst pad carry : List Wire) :
    (rawMake xs dst pad carry).Sublist (rawMakeRef xs dst pad carry) ∧
    (rawClear xs dst pad carry).Sublist (rawClearRef xs dst pad carry) :=
  ⟨(SquareHead.rows_sublist xs dst pad carry).1.append (List.Sublist.refl _),
    (List.Sublist.refl _).append (SquareHead.rows_sublist xs dst pad carry).2⟩


def parityLoad (as bs ss : List Wire) (h : Nat) (q : Wire) : Program :=
  [.CX (as.getD (h-1) 0) q,.CX (bs.getD (h-1) 0) q,.CX (ss.getD (h-1) 0) q]

def correctionBits (h : Nat) (ss : List Wire) (q : Wire) : List MappedBit :=
  mappedRead (ss.take (h-1)) true++
    [{wire:=some q,flip:=false},{wire:=some (ss.getD (h-1) 0),flip:=true},
      {wire:=none,flip:=false}]

theorem parity_value (h : Nat) (as bs ss : List Wire) (s : BasisState)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hv : regValue ss s=regValue as s+regValue bs s) :
    (s (as.getD (h-1) 0) ^^ s (bs.getD (h-1) 0) ^^ s (ss.getD (h-1) 0)).toNat =
      (regValue as s%2^(h-1)+regValue bs s%2^(h-1))/2^(h-1) := by
  have ah := regValue_bit as (h-1) 0 s (by rcases hh with rfl|rfl <;> omega)
  have bh := regValue_bit bs (h-1) 0 s (by rcases hh with rfl|rfl <;> omega)
  have sh := regValue_bit ss (h-1) 0 s (by rcases hh with rfl|rfl <;> omega)
  have al := regValue_lt as s; have bl := regValue_lt bs s
  rw [hal] at al; rw [hbl] at bl
  cases a : s (as.getD (h-1) 0) <;> cases b : s (bs.getD (h-1) 0) <;>
    cases c : s (ss.getD (h-1) 0) <;> simp only [a,b,c,Bool.toNat_false,Bool.toNat_true] at * <;>
    rcases hh with rfl|rfl <;> norm_num at * <;> omega


def load (a b c q cin : Wire) : Program := [.CX a q,.CX b q,.CX c q,.X cin]
def unload (a b c q cin : Wire) : Program := [.X cin,.CX a q,.CX b q,.CX c q]

theorem load_effect (a b c q cin : Wire) (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hiq : cin≠q) (s : State) (m : List Bool) :
    run (load a b c q cin) m s=⟨s.phase,
      writeBit (writeBit s.basis q (s.basis q ^^ s.basis a ^^ s.basis b ^^ s.basis c)) cin (!s.basis cin)⟩ := by
  simp only [load,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases wq : w=q <;> by_cases wi : w=cin <;>
    simp [writeBit,Function.update,ha,hb,hc,hiq,Ne.symm hiq,wq,wi,Bool.xor_assoc]

theorem unload_effect (a b c q cin : Wire) (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q) (s : State) (m : List Bool) :
    run (unload a b c q cin) m s=⟨s.phase,
      writeBit (writeBit s.basis cin (!s.basis cin)) q
        (s.basis q ^^ s.basis a ^^ s.basis b ^^ s.basis c)⟩ := by
  simp only [unload,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases wq : w=q <;> by_cases wi : w=cin <;>
    simp [writeBit,Function.update,ha,hb,hc,hia,hib,hic,hiq,Ne.symm hiq,wq,wi,Bool.xor_assoc]

theorem load_sandwich (a b c q cin : Wire) (D : List Wire)
    (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q)
    (ao : a∉D) (bo : b∉D) (co : c∉D) (qo : q∉D) (io : cin∉D)
    (s v : State) (m n : List Bool)
    (hp : v.phase=(run (load a b c q cin) m s).phase)
    (hf : ∀w,w∉D → v.basis w=(run (load a b c q cin) m s).basis w) :
    (run (unload a b c q cin) n v).phase=s.phase ∧
    regValue D (run (unload a b c q cin) n v).basis=regValue D v.basis ∧
    ∀w,w∉D → (run (unload a b c q cin) n v).basis w=s.basis w := by
  rw [load_effect a b c q cin ha hb hc hiq] at hp hf
  rw [unload_effect a b c q cin ha hb hc hia hib hic hiq]
  refine ⟨hp,?_,?_⟩
  · apply regValue_congr
    intro w hw
    have wq : w≠q := fun e => qo (e ▸ hw)
    have wi : w≠cin := fun e => io (e ▸ hw)
    simp [writeBit,wq,wi]
  · intro w hw
    have fa := hf a ao; have fb := hf b bo; have fc := hf c co
    have fq := hf q qo; have fi := hf cin io; have fw := hf w hw
    simp only [writeBit,Function.update] at *
    by_cases wq : w=q
    · subst w
      simp [ha,hb,hc,hia,hib,hic,hiq,Ne.symm hiq] at *
      rw [fq,fa,fb,fc]
      simp [Bool.xor_assoc]
    · by_cases wi : w=cin
      · subst w
        simp [wq,fi]
      · simp [wq,wi,fw]


def Update (dst : List Wire) (delta : Int) (s t : State) : Prop :=
  t.phase=s.phase ∧ (∀q,q∉dst → t.basis q=s.basis q) ∧
    (regValue dst t.basis : Int) ≡ (regValue dst s.basis : Int)+delta [ZMOD (2^dst.length : Nat)]

theorem Update.seq {dst : List Wire} {d e : Int} {s u t : State}
    (hu : Update dst d s u) (ht : Update dst e u t) : Update dst (d+e) s t := by
  refine ⟨ht.1.trans hu.1,fun q hq => (ht.2.1 q hq).trans (hu.2.1 q hq),?_⟩
  convert ht.2.2.trans (hu.2.2.add_right e) using 1 <;> ring

theorem rv_split (dst : List Wire) (k : Nat) (hk : k≤dst.length) (s : BasisState) :
    regValue dst s=regValue (dst.take k) s+2^k*regValue (dst.drop k) s := by
  have e := regValue_append (dst.take k) (dst.drop k) s
  simpa only [List.take_append_drop,List.length_take,Nat.min_eq_left hk] using e

theorem drop_count (dst : List Wire) (k : Nat) (q : Wire) : (dst.drop k).count q≤dst.count q := by
  have e : (dst.take k).count q+(dst.drop k).count q=dst.count q := by
    rw [←List.count_append,List.take_append_drop]
  omega

theorem drop_views (dst carry : List Wire) (cin : Wire) (k : Nat)
    (hn : (cin::dst++carry).Nodup) :
    (cin::dst.drop k++carry).Nodup ∧ List.Disjoint (dst.take k) (dst.drop k) := by
  refine ⟨?_,?_⟩
  · apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q; have d := drop_count dst k q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  · have n : (dst.take k++dst.drop k).Nodup := by
      rw [List.take_append_drop]
      exact (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
    exact List.disjoint_left.mpr (fun q hq ht => (List.nodup_append.mp n).2.2 q hq q ht rfl)

theorem sub_drop (bits : List MappedBit) (dst carry : List Wire) (cin : Wire) (k : Nat)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hc : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    Update dst (-((2^k : Nat) : Int)*(mappedValue bits s.basis+(s.basis cin).toNat)) s
      (run (mappedSub bits (dst.drop k) carry cin) m s) := by
  have views := drop_views dst carry cin k hn
  have r := BalancedInverse.mappedSub_any_correct bits (dst.drop k) carry cin views.1
    (fun q hq bad => hs q hq (by
      simp only [List.mem_cons,List.mem_append] at bad ⊢
      rcases bad with h|h|h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (List.mem_of_mem_drop h))
      · exact Or.inr h))
    (by simpa using hl) (by simpa using hc) s m hclean
  let t := run (mappedSub bits (dst.drop k) carry cin) m s
  have low : regValue (dst.take k) t.basis=regValue (dst.take k) s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.1 q (List.disjoint_left.mp views.2 hq))
  have c : (s.basis cin).toNat≤1 := by cases s.basis cin <;> decide
  have v := mappedValue_lt bits s.basis
  rw [hl] at v
  have sc := sub_congr (regValue (dst.drop k) s.basis) (2^(dst.length-k))
    (mappedValue bits s.basis+(s.basis cin).toNat) (by omega)
  have e : regValue (dst.drop k) t.basis =
      (regValue (dst.drop k) s.basis+2^(dst.length-k)-
        (mappedValue bits s.basis+(s.basis cin).toNat))%2^(dst.length-k) := by
    simpa only [List.length_drop,Nat.sub_sub] using r.2.2
  rw [←e] at sc
  have sc' := (sc.mul_left' (c:=((2^k : Nat) : Int))).add_left
    (regValue (dst.take k) s.basis : Nat)
  have ep : (2^k : Nat)*(2^(dst.length-k))=2^dst.length := by rw [←pow_add]; congr 1; omega
  have epI : ((2^k : Nat) : Int)*((2^(dst.length-k) : Nat) : Int)=((2^dst.length : Nat) : Int) := by
    exact_mod_cast ep
  rw [epI] at sc'
  refine ⟨r.1,fun q hq => r.2.1 q (fun bad => hq (List.mem_of_mem_drop bad)),?_⟩
  rw [rv_split dst k hk t.basis,low]
  push_cast at sc' ⊢
  have split := congrArg (fun x : Nat => (x : Int)) (rv_split dst k hk s.basis)
  push_cast at split
  convert sc' using 1 <;> try rfl
  nlinarith only [split]


theorem add_drop (bits : List MappedBit) (dst carry : List Wire) (cin : Wire) (k : Nat)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hc : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    Update dst (((2^k : Nat) : Int)*(mappedValue bits s.basis+(s.basis cin).toNat)) s
      (run (mappedAdd bits (dst.drop k) carry cin) m s) := by
  have views := drop_views dst carry cin k hn
  have r := mappedAdd_correct bits (dst.drop k) carry cin views.1
    (fun q hq bad => hs q hq (by
      simp only [List.mem_cons,List.mem_append] at bad ⊢
      rcases bad with h|h|h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (List.mem_of_mem_drop h))
      · exact Or.inr h))
    (by simpa using hl) (by simpa using hc) s m hclean
  let t := run (mappedAdd bits (dst.drop k) carry cin) m s
  have low : regValue (dst.take k) t.basis=regValue (dst.take k) s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.1 q (List.disjoint_left.mp views.2 hq))
  have sc : (((mappedValue bits s.basis+regValue (dst.drop k) s.basis+(s.basis cin).toNat)%
      2^(dst.length-k) : Nat) : Int) ≡
      ((mappedValue bits s.basis+regValue (dst.drop k) s.basis+(s.basis cin).toNat : Nat) : Int)
      [ZMOD (2^(dst.length-k) : Nat)] := by
    simp only [Int.natCast_mod]; exact Int.mod_modEq _ _
  have e : regValue (dst.drop k) t.basis =
      (mappedValue bits s.basis+regValue (dst.drop k) s.basis+(s.basis cin).toNat)%2^(dst.length-k) := by
    simpa only [List.length_drop] using r.2.2
  rw [←e] at sc
  have sc' := (sc.mul_left' (c:=((2^k : Nat) : Int))).add_left
    (regValue (dst.take k) s.basis : Nat)
  have ep : (2^k : Nat)*(2^(dst.length-k))=2^dst.length := by rw [←pow_add]; congr 1; omega
  have epI : ((2^k : Nat) : Int)*((2^(dst.length-k) : Nat) : Int)=((2^dst.length : Nat) : Int) := by
    exact_mod_cast ep
  rw [epI] at sc'
  refine ⟨r.1,fun q hq => r.2.1 q (fun bad => hq (List.mem_of_mem_drop bad)),?_⟩
  rw [rv_split dst k hk t.basis,low]
  push_cast at sc' ⊢
  have split := congrArg (fun x : Nat => (x : Int)) (rv_split dst k hk s.basis)
  push_cast at split
  convert sc' using 1 <;> try rfl
  nlinarith only [split]

theorem getD_in (l : List Wire) (k : Nat) (hk : k<l.length) : l.getD k 0∈l := by
  rw [List.getD_eq_getElem l 0 hk]
  exact List.getElem_mem hk

theorem correctionBits_length (h : Nat) (ss : List Wire) (q : Wire)
    (hh : 1≤h) (hl : h≤ss.length) : (correctionBits h ss q).length=h+2 := by
  simp only [correctionBits,List.length_append,mappedRead_length,List.length_take,List.length_cons,List.length_nil]
  omega

theorem correctionBits_value (h a b : Nat) (ss : List Wire) (q : Wire) (s : BasisState)
    (hh : 1≤h) (hsl : ss.length=h+1) (hv : regValue ss s=a+b)
    (hq : (s q).toNat=(a%2^(h-1)+b%2^(h-1))/2^(h-1)) :
    mappedValue (correctionBits h ss q) s=sharedWord h a b := by
  have take : regValue (ss.take (h-1)) s=regValue ss s%2^(h-1) := by
    have e := rv_split ss (h-1) (by omega) s
    rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt]
    simpa only [List.length_take,Nat.min_eq_left (by omega : h-1≤ss.length)] using regValue_lt (ss.take (h-1)) s
  have bit := regValue_bit ss (h-1) 0 s (by omega)
  have neg : (!s (ss.getD (h-1) 0)).toNat=1-(s (ss.getD (h-1) 0)).toNat := by
    cases s (ss.getD (h-1) 0) <;> decide
  simp only [correctionBits,mappedValue_append,mappedRead_complement,mappedRead_length,
    mappedValue,MappedBit.value,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    Bool.false_xor,Bool.true_xor,Bool.xor_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
  rw [take,neg,bit,hv,hq,List.length_take,Nat.min_eq_left (by omega : h-1≤ss.length)]
  have ep : 2^(h-1)*2=2^h := by rw [←pow_succ]; congr 1; omega
  dsimp only [sharedWord]
  rw [←ep]
  ring


def loadedSub (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat) : Program :=
  load a b c q cin ++ (mappedSub bits (dst.drop k) carry cin ++ unload a b c q cin)

theorem loadedSub_correct (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q)
    (ao : a∉dst) (bo : b∉dst) (co : c∉dst) (qo : q∉dst) (io : cin∉dst) (qc : q∉carry)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀w∈mappedWires bits,w∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hcl : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀w∈carry,s.basis w=false) :
    let u := run (load a b c q cin) [] s
    Update dst (-((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (loadedSub a b c q cin bits dst carry k) m s) := by
  let u := run (load a b c q cin) [] s
  let body := mappedSub bits (dst.drop k) carry cin
  let f := m.take (measurementCount body)
  let g := m.drop (measurementCount body)
  let v := run body f u
  have ui : ∀w∈carry,u.basis w=false := by
    intro w hw
    have wi : w≠cin := fun e => (List.nodup_cons.mp hn).1 (by simp [←e,hw])
    have wq : w≠q := fun e => qc (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simpa [writeBit,wi,wq] using hclean w hw
  have r := sub_drop bits dst carry cin k hk hn hs hl hcl u f ui
  have san := load_sandwich a b c q cin dst ha hb hc hia hib hic hiq ao bo co qo io s v [] g r.1 r.2.1
  have ud : regValue dst u.basis=regValue dst s.basis := by
    apply regValue_congr; intro w hw
    have wq : w≠q := fun e => qo (e ▸ hw)
    have wi : w≠cin := fun e => io (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simp [writeBit,wq,wi]
  have out : Update dst (-((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (unload a b c q cin) g v) := by
    refine ⟨san.1,san.2.2,?_⟩
    rw [san.2.1]
    simpa only [ud] using r.2.2
  have lm : measurementCount (load a b c q cin)=0 := rfl
  simpa only [loadedSub,run_append,lm,List.take_zero,List.drop_zero,u,body,f,g,v] using out

def loadedAdd (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat) : Program :=
  load a b c q cin ++ (mappedAdd bits (dst.drop k) carry cin ++ unload a b c q cin)

theorem loadedAdd_correct (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q)
    (ao : a∉dst) (bo : b∉dst) (co : c∉dst) (qo : q∉dst) (io : cin∉dst) (qc : q∉carry)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀w∈mappedWires bits,w∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hcl : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀w∈carry,s.basis w=false) :
    let u := run (load a b c q cin) [] s
    Update dst (((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (loadedAdd a b c q cin bits dst carry k) m s) := by
  let u := run (load a b c q cin) [] s
  let body := mappedAdd bits (dst.drop k) carry cin
  let f := m.take (measurementCount body)
  let g := m.drop (measurementCount body)
  let v := run body f u
  have ui : ∀w∈carry,u.basis w=false := by
    intro w hw
    have wi : w≠cin := fun e => (List.nodup_cons.mp hn).1 (by simp [←e,hw])
    have wq : w≠q := fun e => qc (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simpa [writeBit,wi,wq] using hclean w hw
  have r := add_drop bits dst carry cin k hk hn hs hl hcl u f ui
  have san := load_sandwich a b c q cin dst ha hb hc hia hib hic hiq ao bo co qo io s v [] g r.1 r.2.1
  have ud : regValue dst u.basis=regValue dst s.basis := by
    apply regValue_congr; intro w hw
    have wq : w≠q := fun e => qo (e ▸ hw)
    have wi : w≠cin := fun e => io (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simp [writeBit,wq,wi]
  have out : Update dst (((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (unload a b c q cin) g v) := by
    refine ⟨san.1,san.2.2,?_⟩
    rw [san.2.1]
    simpa only [ud] using r.2.2
  have lm : measurementCount (load a b c q cin)=0 := rfl
  simpa only [loadedAdd,run_append,lm,List.take_zero,List.drop_zero,u,body,f,g,v] using out


theorem nd_count {l L : List Wire} (hn : L.Nodup) (h : ∀q,l.count q≤L.count q) : l.Nodup :=
  List.nodup_iff_count_le_one.mpr (fun q => (h q).trans (List.nodup_iff_count_le_one.mp hn q))

theorem dis_count {L r t : List Wire} (hn : L.Nodup) (h : ∀q,r.count q+t.count q≤L.count q)
    (q : Wire) (hq : q∈r) : q∉t := by
  intro bad
  have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
  have c := List.nodup_iff_count_le_one.mp hn q; have d := h q; omega

theorem correctionBits_wires (h : Nat) (ss : List Wire) (q : Wire) :
    mappedWires (correctionBits h ss q)=ss.take (h-1)++[q,ss.getD (h-1) 0] := by
  simp only [correctionBits,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    Option.toList_some,Option.toList_none,List.nil_append,List.append_nil]
  rw [show List.flatMap (fun b : MappedBit => b.wire.toList) (mappedRead (ss.take (h-1)) true)=
    ss.take (h-1) from mappedRead_wires _ true]
  rfl

theorem sharedSub_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)) s
      (run (loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
        (correctionBits h ss q) dst (carry.take (h+1)) h) m s) := by
  have hpos : 1≤h := by rcases hh with rfl|rfl <;> omega
  have out (w : Wire) (hw : w∈as++bs++ss) : w∉cin::q::dst++carry :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have qo : q∉cin::dst++carry := dis_count (r:=[q]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_singleton,List.count_nil]; omega) q (by simp)
  have io : cin∉dst++carry := dis_count (r:=[cin]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
  let a := as.getD (h-1) 0
  let b := bs.getD (h-1) 0
  let c := ss.getD (h-1) 0
  have am : a∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inl (getD_in as _ (by omega)))
  have bm : b∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inr (getD_in bs _ (by omega)))
  have cm : c∈as++bs++ss := by simp only [List.mem_append]; exact Or.inr (getD_in ss _ (by omega))
  have aq : a≠q := fun e => out a am (by simp [e])
  have bq : b≠q := fun e => out b bm (by simp [e])
  have cq : c≠q := fun e => out c cm (by simp [e])
  have ai : a≠cin := fun e => out a am (by simp [e])
  have bi : b≠cin := fun e => out b bm (by simp [e])
  have ci : c≠cin := fun e => out c cm (by simp [e])
  have iq : cin≠q := fun e => qo (by simp [e])
  have src (w : Wire) (hw : w∈mappedWires (correctionBits h ss q)) : w∉cin::dst++carry := by
    rw [correctionBits_wires] at hw
    rcases List.mem_append.mp hw with hw|hw
    · have o := out w (List.mem_append_right _ (List.mem_of_mem_take hw))
      intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact qo
      · have o := out c cm
        intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
  have tc (w : Wire) (hw : w∈carry.take (h+1)) : w∈carry := List.mem_of_mem_take hw
  have tn : (cin::dst++carry.take (h+1)).Nodup := nd_count hn (fun w => by
    have t := (List.take_sublist (h+1) carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have hs : ∀w∈mappedWires (correctionBits h ss q),w∉cin::dst++carry.take (h+1) := by
    intro w hw bad; apply src w hw
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with (bad|bad)|bad
    · exact Or.inl (Or.inl bad)
    · exact Or.inl (Or.inr bad)
    · exact Or.inr (tc w bad)
  have r := loadedSub_correct a b c q cin (correctionBits h ss q) dst (carry.take (h+1)) h aq bq cq ai bi ci iq
    (fun hm => out a am (by simp [hm])) (fun hm => out b bm (by simp [hm]))
    (fun hm => out c cm (by simp [hm])) (fun hm => qo (by simp [hm]))
    (fun hm => io (by simp [hm])) (fun hm => qo (by simp [tc q hm])) (by omega) tn hs
    (by rw [correctionBits_length h ss q hpos (by omega),hdl]; omega)
    (by simp only [List.length_take]; omega) s m
    (fun w hw => (regValue_zero _ _).mp hc0 w (tc w hw))
  let u := run (load a b c q cin) [] s
  have us : regValue ss u.basis=regValue ss s.basis := by
    apply regValue_congr; intro w hw
    have o := out w (List.mem_append_right _ hw)
    have wi : w≠cin := fun e => o (by simp [e])
    have wq : w≠q := fun e => o (by simp [e])
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,wi,wq]
  have uq : (u.basis q).toNat=(regValue as s.basis%2^(h-1)+regValue bs s.basis%2^(h-1))/2^(h-1) := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp only [writeBit,Function.update,Ne.symm iq,if_false,if_true,hq0,Bool.false_xor]
    exact parity_value h as bs ss s.basis hh hal hbl hsl hv
  have ui : u.basis cin=true := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,hi0]
  have uv := correctionBits_value h (regValue as s.basis) (regValue bs s.basis) ss q u.basis hpos hsl
    (us.trans hv) uq
  simpa only [show run (load a b c q cin) [] s=u from rfl,uv,ui,Bool.toNat_true] using r

theorem sharedAdd_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)) s
      (run (loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
        (correctionBits h ss q) dst (carry.take (h+1)) h) m s) := by
  have hpos : 1≤h := by rcases hh with rfl|rfl <;> omega
  have out (w : Wire) (hw : w∈as++bs++ss) : w∉cin::q::dst++carry :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have qo : q∉cin::dst++carry := dis_count (r:=[q]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_singleton,List.count_nil]; omega) q (by simp)
  have io : cin∉dst++carry := dis_count (r:=[cin]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
  let a := as.getD (h-1) 0
  let b := bs.getD (h-1) 0
  let c := ss.getD (h-1) 0
  have am : a∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inl (getD_in as _ (by omega)))
  have bm : b∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inr (getD_in bs _ (by omega)))
  have cm : c∈as++bs++ss := by simp only [List.mem_append]; exact Or.inr (getD_in ss _ (by omega))
  have aq : a≠q := fun e => out a am (by simp [e])
  have bq : b≠q := fun e => out b bm (by simp [e])
  have cq : c≠q := fun e => out c cm (by simp [e])
  have ai : a≠cin := fun e => out a am (by simp [e])
  have bi : b≠cin := fun e => out b bm (by simp [e])
  have ci : c≠cin := fun e => out c cm (by simp [e])
  have iq : cin≠q := fun e => qo (by simp [e])
  have src (w : Wire) (hw : w∈mappedWires (correctionBits h ss q)) : w∉cin::dst++carry := by
    rw [correctionBits_wires] at hw
    rcases List.mem_append.mp hw with hw|hw
    · have o := out w (List.mem_append_right _ (List.mem_of_mem_take hw))
      intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact qo
      · have o := out c cm
        intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
  have tc (w : Wire) (hw : w∈carry.take (h+1)) : w∈carry := List.mem_of_mem_take hw
  have tn : (cin::dst++carry.take (h+1)).Nodup := nd_count hn (fun w => by
    have t := (List.take_sublist (h+1) carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have hs : ∀w∈mappedWires (correctionBits h ss q),w∉cin::dst++carry.take (h+1) := by
    intro w hw bad; apply src w hw
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with (bad|bad)|bad
    · exact Or.inl (Or.inl bad)
    · exact Or.inl (Or.inr bad)
    · exact Or.inr (tc w bad)
  have r := loadedAdd_correct a b c q cin (correctionBits h ss q) dst (carry.take (h+1)) h aq bq cq ai bi ci iq
    (fun hm => out a am (by simp [hm])) (fun hm => out b bm (by simp [hm]))
    (fun hm => out c cm (by simp [hm])) (fun hm => qo (by simp [hm]))
    (fun hm => io (by simp [hm])) (fun hm => qo (by simp [tc q hm])) (by omega) tn hs
    (by rw [correctionBits_length h ss q hpos (by omega),hdl]; omega)
    (by simp only [List.length_take]; omega) s m
    (fun w hw => (regValue_zero _ _).mp hc0 w (tc w hw))
  let u := run (load a b c q cin) [] s
  have us : regValue ss u.basis=regValue ss s.basis := by
    apply regValue_congr; intro w hw
    have o := out w (List.mem_append_right _ hw)
    have wi : w≠cin := fun e => o (by simp [e])
    have wq : w≠q := fun e => o (by simp [e])
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,wi,wq]
  have uq : (u.basis q).toNat=(regValue as s.basis%2^(h-1)+regValue bs s.basis%2^(h-1))/2^(h-1) := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp only [writeBit,Function.update,Ne.symm iq,if_false,if_true,hq0,Bool.false_xor]
    exact parity_value h as bs ss s.basis hh hal hbl hsl hv
  have ui : u.basis cin=true := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,hi0]
  have uv := correctionBits_value h (regValue as s.basis) (regValue bs s.basis) ss q u.basis hpos hsl
    (us.trans hv) uq
  simpa only [show run (load a b c q cin) [] s=u from rfl,uv,ui,Bool.toNat_true] using r


def correction (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h ++
    SquareIncrement.add (dst.drop (2*h-1)) (carry.take 2) cin

def correctionBack (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  SquareIncrement.sub (dst.drop (2*h-1)) (carry.take 2) cin ++
  loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h

theorem correction_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)+
      (2^(2*h-1) : Nat)) s (run (correction h as bs ss dst carry q cin) m s) := by
  let P := loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h
  let f := m.take (measurementCount P)
  let g := m.drop (measurementCount P)
  let u := run P f s
  have r := sharedSub_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s f hv hq0 hi0 hc0
  have cnd : (cin::dst++carry.take 2).Nodup := nd_count hn (fun w => by
    have c := (List.take_sublist 2 carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have out (w : Wire) (hw : w∈cin::carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have uc : ∀w∈carry.take 2,u.basis w=false := by
    intro w hw
    have hm := List.mem_of_mem_take hw
    exact (r.2.1 w (out w (by simp [hm]))).trans ((regValue_zero _ _).mp hc0 w hm)
  have ui : u.basis cin=false := (r.2.1 cin (out cin (by simp))).trans hi0
  have inc := add_drop (mappedConstant none 3 1) dst (carry.take 2) cin (2*h-1) (by omega) cnd
    (by simp [mappedConstant,mappedConstantBit,mappedWires])
    (by rw [mappedConstant_length,hdl]; rcases hh with rfl|rfl <;> omega)
    (by simp only [List.length_take]; rcases hh with rfl|rfl <;> omega) u g uc
  have inc' : Update dst ((2^(2*h-1) : Nat) : Int) u
      (run (mappedAdd (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin) g u) := by
    simpa only [mappedConstant_value none 3 1 u.basis (by decide),mappedEnabled,
      Option.map_none,Option.getD_none,if_true,ui,Bool.toNat_false,Nat.add_zero,Int.natCast_one,Int.natCast_zero,add_zero,mul_one]
      using inc
  have ie := SquareIncrement.add_eq (dst.drop (2*h-1)) (carry.take 2) cin
    (by rw [List.length_drop,hdl]; rcases hh with rfl|rfl <;> omega)
    (by simp only [List.length_take]; rcases hh with rfl|rfl <;> omega)
    (drop_views dst (carry.take 2) cin (2*h-1) cnd).1 u g ui
  rw [←ie] at inc'
  have total := r.seq inc'
  simpa only [correction,run_append,P,f,g,u] using total

theorem cross_normalize (h a b : Nat) (hh : h=32 ∨ h=33) (ha : a<2^h) (hb : b<2^h) :
    (((a+b)^2+signedDiagValue (a+b) (h+1) : Nat) : Int)-
      ((a^2+signedDiagValue a h : Nat) : Int)-((b^2+signedDiagValue b h : Nat) : Int)-
      ((2^h : Nat) : Int)*(sharedWord h a b+1)+(2^(2*h-1) : Nat)=(2*a*b : Nat) := by
  have dg := diagonal_identity h a b hh ha hb
  push_cast at dg ⊢
  nlinarith only [dg]


theorem correctionBack_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)-
      (2^(2*h-1) : Nat)) s (run (correctionBack h as bs ss dst carry q cin) m s) := by
  let P := mappedSub (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin
  let f := m.take (measurementCount P)
  let g := m.drop (measurementCount P)
  let u := run P f s
  have cnd : (cin::dst++carry.take 2).Nodup := nd_count hn (fun w => by
    have c := (List.take_sublist 2 carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have clean : ∀w∈carry.take 2,s.basis w=false :=
    fun w hw => (regValue_zero _ _).mp hc0 w (List.mem_of_mem_take hw)
  have dec := sub_drop (mappedConstant none 3 1) dst (carry.take 2) cin (2*h-1) (by omega) cnd
    (by simp [mappedConstant,mappedConstantBit,mappedWires])
    (by rw [mappedConstant_length,hdl]; rcases hh with rfl|rfl <;> omega)
    (by simp only [List.length_take]; rcases hh with rfl|rfl <;> omega) s f clean
  have dec' : Update dst (-((2^(2*h-1) : Nat) : Int)) s u := by
    simpa only [mappedConstant_value none 3 1 s.basis (by decide),mappedEnabled,
      Option.map_none,Option.getD_none,if_true,hi0,Bool.toNat_false,Int.natCast_zero,add_zero,
      Int.natCast_one,mul_one] using dec
  have out (w : Wire) (hw : w∈cin::q::as++bs++ss++carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have keep (l : List Wire) (hl : ∀w∈l,w∈cin::q::as++bs++ss++carry) :
      regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun w hw => dec'.2.1 w (out w (hl w hw)))
  have ka := keep as (fun w hw => by simp [hw])
  have kb := keep bs (fun w hw => by simp [hw])
  have ks := keep ss (fun w hw => by simp [hw])
  have kc := keep carry (fun w hw => by simp [hw])
  have r := sharedAdd_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn u g
    (by rw [ks,ka,kb]; exact hv)
    ((dec'.2.1 q (out q (by simp))).trans hq0)
    ((dec'.2.1 cin (out cin (by simp))).trans hi0) (kc.trans hc0)
  rw [ka,kb] at r
  have total := dec'.seq r
  have total' : Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)-
      (2^(2*h-1) : Nat)) s
      (run (loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
        (correctionBits h ss q) dst (carry.take (h+1)) h) g u) := by
    convert total using 1 <;> ring
  have hd3 : (dst.drop (2*h-1)).length=3 := by rw [List.length_drop,hdl]; rcases hh with rfl|rfl <;> omega
  have hc2 : (carry.take 2).length=2 := by simp only [List.length_take]; rcases hh with rfl|rfl <;> omega
  have ee (r : List Bool) := SquareIncrement.sub_eq (dst.drop (2*h-1)) (carry.take 2) cin hd3 hc2
    (drop_views dst (carry.take 2) cin (2*h-1) cnd).1 s r hi0
  have nn := SquareIncrement.counts (dst.drop (2*h-1)) (carry.take 2) cin hd3 hc2
  have oo := mappedSub_counts (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin
    (by rw [mappedConstant_length,hd3]) (by rw [hc2,hd3])
  have mm : measurementCount (SquareIncrement.sub (dst.drop (2*h-1)) (carry.take 2) cin)=measurementCount P := by
    change _=measurementCount (mappedSub (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin)
    rw [nn.2.2.2,oo.2,hd3]
  simpa only [correctionBack,run_append,mm,ee,P,f,g,u] using total'

theorem loaded_counts (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (hl : bits.length=(dst.drop k).length) (hc : carry.length+1=(dst.drop k).length) :
    toffoliCount (loadedSub a b c q cin bits dst carry k)=(dst.drop k).length-1 ∧
    measurementCount (loadedSub a b c q cin bits dst carry k)=(dst.drop k).length-1 ∧
    toffoliCount (loadedAdd a b c q cin bits dst carry k)=(dst.drop k).length-1 ∧
    measurementCount (loadedAdd a b c q cin bits dst carry k)=(dst.drop k).length-1 := by
  have sub := mappedSub_counts bits (dst.drop k) carry cin hl hc
  have add := mappedAdd_counts bits (dst.drop k) carry cin hl hc
  simp only [loadedSub,loadedAdd,toffoliCount_append,measurementCount_append,
    show toffoliCount (load a b c q cin)=0 from rfl,
    show toffoliCount (unload a b c q cin)=0 from rfl,
    show measurementCount (load a b c q cin)=0 from rfl,
    show measurementCount (unload a b c q cin)=0 from rfl,
    sub.1,sub.2,add.1,add.2,Nat.zero_add,Nat.add_zero,and_self]

theorem correction_counts (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : 2≤h) (hsl : ss.length=h+1) (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length) :
    toffoliCount (correction h as bs ss dst carry q cin)=h+2 ∧
    measurementCount (correction h as bs ss dst carry q cin)=h+3 ∧
    toffoliCount (correctionBack h as bs ss dst carry q cin)=h+2 ∧
    measurementCount (correctionBack h as bs ss dst carry q cin)=h+3 := by
  have b := loaded_counts (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h
    (by rw [correctionBits_length h ss q (by omega) (by omega),List.length_drop,hdl]; omega)
    (by simp only [List.length_take,List.length_drop]; omega)
  have a := SquareIncrement.counts (dst.drop (2*h-1)) (carry.take 2) cin
    (by rw [List.length_drop,hdl]; omega) (by simp only [List.length_take]; omega)
  simp only [correction,correctionBack,toffoliCount_append,measurementCount_append,
    b.1,b.2.1,b.2.2.1,b.2.2.2,a.1,a.2.1,a.2.2.1,a.2.2.2,List.length_drop,hdl]
  omega


theorem plain_sub_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hl : xs.length=dst.length) (hc : carry.length+1=dst.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) (hi : s.basis cin=false) :
    Update dst (-(regValue xs s.basis : Int)) s (run (subInPlace xs dst carry cin) m s) := by
  have r := BalancedInverse.subInPlace_any_correct xs dst carry cin hn hl hc s m hclean
  have vl := regValue_lt xs s.basis
  rw [hl] at vl
  refine ⟨r.1,r.2.1,?_⟩
  rw [r.2.2,hi,Bool.toNat_false,Nat.sub_zero]
  simpa only [sub_eq_add_neg] using sub_congr (regValue dst s.basis) (2^dst.length)
    (regValue xs s.basis) (by omega)

theorem plain_add_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hl : xs.length=dst.length) (hc : carry.length+1=dst.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) (hi : s.basis cin=false) :
    Update dst (regValue xs s.basis : Int) s (run (addInPlace xs dst carry cin) m s) := by
  have r := addInPlace_correct xs dst carry cin hn hl hc s m hclean
  refine ⟨r.1,r.2.1,?_⟩
  rw [r.2.2,hi,Bool.toNat_false,Nat.add_zero]
  simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
  rw [Int.add_comm]
  exact Int.emod_emod _ _

theorem diag_sub_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length) (hd : dst.length=2*xs.length)
    (hc : dst.length-1≤carry.length) (s : State) (m : List Bool)
    (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    Update dst (-(signedDiagValue (regValue xs s.basis) xs.length : Int)) s
      (run (mappedDiagSub xs dst carry cin) m s) := by
  have r := mappedDiagSub_correct cin xs dst carry hn hx hd hc s m hclean hi
  have vl : signedDiagValue (regValue xs s.basis) xs.length<2^dst.length := by
    rw [←mappedDiagonal_exact xs s.basis hx]
    simpa only [mappedDiagonal_length xs hx,hd] using mappedValue_lt (mappedDiagonal xs) s.basis
  refine ⟨r.1,r.2.2,?_⟩
  rw [r.2.1]
  simpa only [sub_eq_add_neg] using sub_congr (regValue dst s.basis) (2^dst.length)
    (signedDiagValue (regValue xs s.basis) xs.length) (by omega)

theorem diag_add_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length) (hd : dst.length=2*xs.length)
    (hc : dst.length-1≤carry.length) (s : State) (m : List Bool)
    (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    Update dst (signedDiagValue (regValue xs s.basis) xs.length : Int) s
      (run (mappedDiagAdd xs dst carry cin) m s) := by
  have r := mappedDiagAdd_correct cin xs dst carry hn hx hd hc s m hclean hi
  refine ⟨r.1,r.2.2,?_⟩
  rw [r.2.1]
  simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
  exact Int.emod_emod _ _

end ECDSAAdd.Entrant.DiagSq
end DiagonalSharing
section DiagonalRegisterIntegration
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

def reg (R : KRegs) (i : Fin 4) : List Wire := ![R.dlo,R.dhi,R.S,R.T] i
def vec (a b s t : Int) : Fin 4 → Int := ![a,b,s,t]

theorem vec0 (a b s t x : Int) : Function.update (vec a b s t) 0 x=vec x b s t := by
  funext i; fin_cases i <;> simp [vec,Function.update]
theorem vec1 (a b s t x : Int) : Function.update (vec a b s t) 1 x=vec a x s t := by
  funext i; fin_cases i <;> simp [vec,Function.update]
theorem vec2 (a b s t x : Int) : Function.update (vec a b s t) 2 x=vec a b x t := by
  funext i; fin_cases i <;> simp [vec,Function.update]
theorem vec3 (a b s t x : Int) : Function.update (vec a b s t) 3 x=vec a b s x := by
  funext i; fin_cases i <;> simp [vec,Function.update]

theorem reg_disjoint (R : KRegs) (hn : R.all.Nodup) (i j : Fin 4) (hij : i≠j)
    (q : Wire) (hq : q∈reg R i) : q∉reg R j := by
  fin_cases i <;> fin_cases j <;> simp [reg] at *
  all_goals exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq

theorem reg_member (R : KRegs) (i : Fin 4) (q : Wire) (hq : q∈reg R i) :
    q∈R.dst ∨ q∈R.S ∨ q∈R.T := by
  fin_cases i
  · exact Or.inl (List.mem_of_mem_take hq)
  · exact Or.inl (List.mem_of_mem_drop hq)
  · exact Or.inr (Or.inl hq)
  · exact Or.inr (Or.inr hq)

structure Shape (R : KRegs) (base s : State) (v : Fin 4 → Int) : Prop where
  phase : s.phase=base.phase
  value : ∀i,(regValue (reg R i) s.basis : Int) ≡ v i [ZMOD (2^(reg R i).length : Nat)]
  rest : ∀q,q∉R.dst → q∉R.S → q∉R.T → s.basis q=base.basis q

theorem Shape.step {R : KRegs} (hn : R.all.Nodup) {base s t : State} {v : Fin 4 → Int}
    (h : Shape R base s v) (i : Fin 4) (x : Int)
    (hp : t.phase=s.phase) (hf : ∀q,q∉reg R i → t.basis q=s.basis q)
    (hv : (regValue (reg R i) t.basis : Int) ≡ x [ZMOD (2^(reg R i).length : Nat)]) :
    Shape R base t (Function.update v i x) := by
  refine ⟨hp.trans h.phase,?_,?_⟩
  · intro j
    by_cases ji : j=i
    · subst j; simpa using hv
    · rw [Function.update_of_ne ji,kkeep hf (reg_disjoint R hn j i ji)]
      exact h.value j
  · intro q hd hs ht
    have qi : q∉reg R i := by
      intro bad
      rcases reg_member R i q bad with bad|bad|bad
      · exact hd bad
      · exact hs bad
      · exact ht bad
    exact (hf q qi).trans (h.rest q hd hs ht)

theorem Shape.advance {R : KRegs} (hn : R.all.Nodup) {base s t : State} {v : Fin 4 → Int}
    (h : Shape R base s v) (i : Fin 4) (d : Int) (u : Update (reg R i) d s t) :
    Shape R base t (Function.update v i (v i+d)) := by
  apply h.step hn i (v i+d) u.1 u.2.1
  exact u.2.2.trans ((h.value i).add_right d)

theorem Shape.exact {R : KRegs} {base s : State} {v : Fin 4 → Int} (h : Shape R base s v)
    (i : Fin 4) (x : Nat) (hv : v i=x) (hx : x<2^(reg R i).length) :
    regValue (reg R i) s.basis=x := by
  have r := h.value i
  rw [hv] at r
  have r' := Int.natCast_modEq_iff.mp r
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt (regValue_lt (reg R i) s.basis),Nat.mod_eq_of_lt hx] using r'

theorem Shape.keep {R : KRegs} (hn : R.all.Nodup) {base s : State} {v : Fin 4 → Int}
    (h : Shape R base s v) (l : List Wire)
    (hl : ∀q∈l,q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) :
    regValue l s.basis=regValue l base.basis := by
  apply regValue_congr
  intro q hq
  have o := R.outside hn q (hl q hq)
  exact h.rest q o.1 o.2.1 o.2.2

theorem Shape.cin {R : KRegs} (hn : R.all.Nodup) {base s : State} {v : Fin 4 → Int}
    (h : Shape R base s v) : s.basis R.cin=base.basis R.cin :=
  h.rest R.cin (R.outside hn R.cin (by simp)).1 (R.outside hn R.cin (by simp)).2.1
    (R.outside hn R.cin (by simp)).2.2

def Transition (R : KRegs) (base : State) (v w : Fin 4 → Int) (P : Program) : Prop :=
  ∀s m,Shape R base s v → Shape R base (run P m s) w

theorem Transition.seq {R : KRegs} {base : State} {v w z : Fin 4 → Int} {P Q : Program}
    (hp : Transition R base v w P) (hq : Transition R base w z Q) : Transition R base v z (P++Q) := by
  intro s m hs
  rw [run_append]
  exact hq _ _ (hp _ _ hs)


def rawValue (n x : Nat) : Nat := x^2+signedDiagValue x n

def seeds (R : KRegs) : Program :=
  rawMake R.lo R.dlo R.pad R.carry ++ rawMake R.hi R.dhi R.pad R.carry ++ R.smk ++
    rawMake R.S R.T R.pad R.carry

theorem seeds_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (seeds R) m s)
      (vec (rawValue R.h (regValue R.lo s.basis)) (rawValue R.h (regValue R.hi s.basis))
        (regValue R.lo s.basis+regValue R.hi s.basis)
        (rawValue (R.h+1) (regValue R.lo s.basis+regValue R.hi s.basis))) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hpl := w.pad
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have init : Shape R s s (vec 0 0 0 0) := by
    refine ⟨rfl,?_,fun _ _ _ _ => rfl⟩
    intro i; fin_cases i
    · change (regValue R.dlo s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dlo) hd0 (fun q h => List.mem_of_mem_take h)]; rfl
    · change (regValue R.dhi s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dhi) hd0 (fun q h => List.mem_of_mem_drop h)]; rfl
    · change (regValue R.S s.basis : Int) ≡ 0 [ZMOD _]
      rw [hS0]; rfl
    · change (regValue R.T s.basis : Int) ≡ 0 [ZMOD _]
      rw [hT0]; rfl
  have loStep : Transition R s (vec 0 0 0 0) (vec (rawValue R.h a) 0 0 0)
      (rawMake R.lo R.dlo R.pad R.carry) := by
    intro t rec ht
    have lt := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have r := rawMake_correct R.lo R.dlo R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 0 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 0) (run (rawMake R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h a : Nat) [ZMOD (2^(reg R 0).length : Nat)] := by
      change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,lt,L0]; rfl
    simpa only [vec0] using ht.step hn 0 (rawValue R.h a) r.1 r.2.2 v
  have hiStep : Transition R s (vec (rawValue R.h a) 0 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) 0 0) (rawMake R.hi R.dhi R.pad R.carry) := by
    intro t rec ht
    have ht0 := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := rawMake_correct R.hi R.dhi R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 1 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 1) (run (rawMake R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h b : Nat) [ZMOD (2^(reg R 1).length : Nat)] := by
      change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,ht0,hhi]; rfl
    simpa only [vec1] using ht.step hn 1 (rawValue R.h b) r.1 r.2.2 v
  have sumStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0) R.smk := by
    intro t rec ht
    have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := R.smk_correct w hn t rec (ht.exact 2 0 rfl (by norm_num))
      ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
    have v : (regValue (reg R 2) (run R.smk rec t).basis : Int) ≡ (a+b : Nat) [ZMOD (2^(reg R 2).length : Nat)] := by
      change (regValue R.S _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,al,bl]
    simpa only [vec2] using ht.step hn 2 (a+b : Nat) r.1 r.2.2 v
  have sqStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) (rawValue (R.h+1) (a+b)))
      (rawMake R.S R.T R.pad R.carry) := by
    intro t rec ht
    have av := regValue_lt R.lo s.basis
    have bv := regValue_lt R.hi s.basis
    rw [L0] at av; rw [hhi] at bv
    have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
    have sv := ht.exact 2 (a+b) rfl slt
    change regValue R.S t.basis=a+b at sv
    have r := rawMake_correct R.S R.T R.pad R.carry
      (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      (by omega) hTl hpl (by omega) t rec
      (ht.exact 3 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 3) (run (rawMake R.S R.T R.pad R.carry) rec t).basis : Int) ≡
        (rawValue (R.h+1) (a+b) : Nat) [ZMOD (2^(reg R 3).length : Nat)] := by
      change (regValue R.T _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,sv,hSS]; rfl
    simpa only [vec3] using ht.step hn 3 (rawValue (R.h+1) (a+b)) r.1 r.2.2 v
  exact (((loStep.seq hiStep).seq sumStep).seq sqStep) s m init


theorem rawValue_bound (l : List Wire) (s : BasisState) (hl : 1≤l.length) :
    rawValue l.length (regValue l s)<2^(2*l.length) := by
  rw [rawValue,←signedRawValue_correct l s (List.ne_nil_of_length_pos (by omega))]
  exact signedRawValue_bound l s hl

theorem sublo_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hEven : A%2=0) :
    Transition R base (vec A B S T) (vec A B S (T-A)) (SquareBundle.m6R R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  rw [SquareBundle.m6R_eq R w hn t rec (by rw [xv]; exact hEven) ((ht.cin hn).trans hi0)]
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_sub_update (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addlo_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hEven : A%2=0) :
    Transition R base (vec A B S T) (vec A B S (T+A)) (SquareBundle.c6R R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  rw [SquareBundle.c6R_eq R w hn t rec (by rw [xv]; exact hEven) ((ht.cin hn).trans hi0)]
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_add_update (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem subhi_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hEven : B%2=0) :
    Transition R base (vec A B S T) (vec A B S (T-B)) (SquareBundle.m7R R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  rw [SquareBundle.m7R_eq R w hn t rec (by rw [xv]; exact hEven) ((ht.cin hn).trans hi0)]
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_sub_update (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addhi_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hEven : B%2=0) :
    Transition R base (vec A B S T) (vec A B S (T+B)) (SquareBundle.c7R R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  rw [SquareBundle.c7R_eq R w hn t rec (by rw [xv]; exact hEven) ((ht.cin hn).trans hi0)]
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_add_update (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem diagsublo_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec (A-(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (mappedDiagSub R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.lo.length=R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_sub_update R.lo R.dlo R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 0 (-(signedDiagValue (regValue R.lo base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 0=A from rfl,vec0,sub_eq_add_neg] using act

theorem diagaddlo_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec (A+(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (mappedDiagAdd R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.lo.length=R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_add_update R.lo R.dlo R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 0 ((signedDiagValue (regValue R.lo base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 0=A from rfl,vec0,sub_eq_add_neg] using act

theorem diagsubhi_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec A (B-(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (mappedDiagSub R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.hi.length=R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_sub_update R.hi R.dhi R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 1 (-(signedDiagValue (regValue R.hi base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 1=B from rfl,vec1,sub_eq_add_neg] using act

theorem diagaddhi_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec A (B+(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (mappedDiagAdd R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.hi.length=R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_add_update R.hi R.dhi R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 1 ((signedDiagValue (regValue R.hi base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 1=B from rfl,vec1,sub_eq_add_neg] using act

def parity (R : KRegs) : Wire := R.z.getD 0 0

def corr (R : KRegs) : Program := correction R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
def corrBack (R : KRegs) : Program := correctionBack R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin

theorem corr_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T-((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)+(2^(2*R.h-1) : Nat))) (corr R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correction_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring

theorem corrBack_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T+((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)-(2^(2*R.h-1) : Nat))) (corrBack R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correctionBack_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring


def headBlock (R : KRegs) : Program := seeds R ++ ((SquareBundle.m6R R)++(SquareBundle.m7R R)++corr R++
  mappedDiagSub R.lo R.dlo R.carry R.cin++mappedDiagSub R.hi R.dhi R.carry R.cin)

def make (R : KRegs) : Program := headBlock R++(SquareBundle.m8E R)

def clear (R : KRegs) : Program := (SquareBundle.c8E R)++(mappedDiagAdd R.lo R.dlo R.carry R.cin++
  mappedDiagAdd R.hi R.dhi R.carry R.cin++corrBack R++(SquareBundle.c7R R)++(SquareBundle.c6R R)++
  rawClear R.S R.T R.pad R.carry++R.scl0++rawClear R.hi R.dhi R.pad R.carry++
  rawClear R.lo R.dlo R.pad R.carry)

theorem prefix_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (headBlock R) m s)
      (vec ((regValue R.lo s.basis)^2) ((regValue R.hi s.basis)^2)
        (regValue R.lo s.basis+regValue R.hi s.basis) (2*regValue R.lo s.basis*regValue R.hi s.basis)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  have hhi : R.hi.length=R.h := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have st1 := sublo_transition R w hn s hz0 hc0 hi0 A B S Z hA (by dsimp [A,rawValue]; exact SquareBundle.raw_even R.h a (by omega))
  have st2 := subhi_transition R w hn s hz0 hc0 hi0 A B S ((Z : Int)-A) hB (by dsimp [B,rawValue]; exact SquareBundle.raw_even R.h b (by omega))
  have st3 := corr_transition R w he hh hn s hz0 hc0 hi0 A B ((Z : Int)-A-B)
  have norm := cross_normalize R.h a b hh alo bhi
  change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
    (2*a*b : Nat) at norm
  rw [norm] at st3
  have st4 := diagsublo_transition R w he hn s hc0 hi0 A B S (2*a*b : Nat)
  have st4' : Transition R s (vec A B S (2*a*b : Nat)) (vec (a^2 : Nat) B S (2*a*b : Nat))
      (mappedDiagSub R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add,add_sub_cancel_right] using st4
  have st5 := diagsubhi_transition R w he hn s hc0 hi0 (a^2 : Nat) B S (2*a*b : Nat)
  have st5' : Transition R s (vec (a^2 : Nat) B S (2*a*b : Nat))
      (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (mappedDiagSub R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add,add_sub_cancel_right] using st5
  have tail := (((st1.seq st2).seq st3).seq st4').seq st5'
  have initial := seeds_shape R w he hn s (m.take (measurementCount (seeds R))) hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (seeds R))) initial
  simpa only [headBlock,run_append,A,B,S,Z,a,b,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using result


theorem make_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (make R) m s).phase=s.phase ∧
    regValue R.dst (run (make R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (make R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (make R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (make R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let f := m.take (measurementCount (headBlock R))
  let g := m.drop (measurementCount (headBlock R))
  let u := run (headBlock R) f s
  have h := prefix_shape R w he hh hn s f hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have sq := square_bound (a+b) R.S.length slt
  have tvlt : 2*a*b<2^R.T.length := by rw [hTl]; omega
  have av : regValue R.dlo u.basis=a^2 := h.exact 0 (a^2) (by simp [vec,a,b])
    (by change a^2<2^R.dlo.length; rw [L2]; exact square_bound _ _ al)
  have bv : regValue R.dhi u.basis=b^2 := h.exact 1 (b^2) (by simp [vec,a,b])
    (by change b^2<2^R.dhi.length; rw [L3,show R.bank.length-R.h=R.h by omega]; exact square_bound _ _ bl)
  have sv : regValue R.S u.basis=a+b := h.exact 2 (a+b) (by simp [vec,a,b]) slt
  have tv : regValue R.T u.basis=2*a*b := h.exact 3 (2*a*b) (by simp [vec,a,b]) tvlt
  have dv : regValue R.dst u.basis=a^2+2^(2*R.h)*b^2 := by rw [R.dst_value w,av,bv]
  have cv := (h.keep hn R.carry (by intro q hq; simp [hq])).trans hc0
  have zv := (h.keep hn R.zM (fun q hq => Or.inr (Or.inl (List.mem_of_mem_take hq)))).trans
    (KRegs.xz (r:=R.zM) hz0 (fun q hq => List.mem_of_mem_take hq))
  have ni : (R.cin::(R.T++R.zM)++R.dmid++R.carry.take (R.dmid.length-1)).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := addInPlace_correct (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin ni
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) u g
    (fun q hq => (regValue_zero _ _).mp cv q (List.mem_of_mem_take hq))
  have rv : regValue R.dmid (run R.m8 g u).basis=
      (2*a*b+(a^2+2^(2*R.h)*b^2)/2^R.h)%2^(2*R.bank.length-R.h) := by
    rw [show R.m8=addInPlace (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin from rfl,
      r.2.2,regValue_append,tv,zv,h.cin hn,hi0,
      show regValue R.dmid u.basis=regValue R.dst u.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by have := w.dst; omega) u.basis,dv,L4]
    simp
  have frame : ∀q,q∉R.dmid → (run R.m8 g u).basis q=u.basis q := r.2.1
  have keepLow : regValue (R.dst.take R.h) (run R.m8 g u).basis=regValue (R.dst.take R.h) u.basis :=
    kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have dfin : regValue R.dst (run R.m8 g u).basis=(regValue R.bank s.basis)^2 := by
    rw [R.bank_value w s.basis,R.dst_value_mid w,rv,keepLow,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by have := w.dst; omega),dv]
    exact KRegs.kfinal a b R.h R.bank.length al (by simpa only [show R.bank.length-R.h=R.h by omega] using bl) (by omega)
  have result : (run R.m8 g u).phase=s.phase ∧ regValue R.dst (run R.m8 g u).basis=(regValue R.bank s.basis)^2 ∧
      regValue R.S (run R.m8 g u).basis=a+b ∧ regValue R.T (run R.m8 g u).basis=2*a*b ∧
      ∀q,q∉R.dst → q∉R.S → q∉R.T → (run R.m8 g u).basis q=s.basis q := by
    refine ⟨r.1.trans h.phase,dfin,?_,?_,?_⟩
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans sv
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans tv
    · intro q hd hs ht
      exact (frame q (fun bad => hd (List.mem_of_mem_drop bad))).trans (h.rest q hd hs ht)
  have ee := SquareBundle.m8E_eq R w hn u g (a*b)
    (by simpa only [Nat.mul_assoc] using tv) ((h.cin hn).trans hi0)
  rw [←ee] at result
  simpa only [make,run_append,u,f,g,a,b] using result

theorem rawclearlo_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (B S T : Int) :
    Transition R base (vec (rawValue R.h (regValue R.lo base.basis)) B S T) (vec 0 B S T) (rawClear R.lo R.dlo R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.lo.length=R.h := by omega
  have hdlen : R.dlo.length=2*R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have rb := rawValue_bound R.lo base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 0 (rawValue R.h (regValue R.lo base.basis)) rfl
    (by change _<2^R.dlo.length; rw [hdlen]; exact rb)
  change regValue R.dlo t.basis=_ at dv
  have r := rawClear_correct R.lo R.dlo R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 0) (run (rawClear R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 0).length : Nat)] := by
    change (regValue R.dlo _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec0] using ht.step hn 0 0 r.1 r.2.2 val

theorem rawclearhi_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (A S T : Int) :
    Transition R base (vec A (rawValue R.h (regValue R.hi base.basis)) S T) (vec A 0 S T) (rawClear R.hi R.dhi R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.hi.length=R.h := by omega
  have hdlen : R.dhi.length=2*R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have rb := rawValue_bound R.hi base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 1 (rawValue R.h (regValue R.hi base.basis)) rfl
    (by change _<2^R.dhi.length; rw [hdlen]; exact rb)
  change regValue R.dhi t.basis=_ at dv
  have r := rawClear_correct R.hi R.dhi R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 1) (run (rawClear R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 1).length : Nat)] := by
    change (regValue R.dhi _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec1] using ht.step hn 1 0 r.1 r.2.2 val

theorem rawclearSum_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hp0 : regValue R.pad base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (A B : Int) (S : Nat) (hS : S<2^R.S.length) :
    Transition R base (vec A B S (rawValue R.S.length S)) (vec A B S 0)
      (rawClear R.S R.T R.pad R.carry) := by
  intro t rec ht
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hpl := w.pad
  have sv := ht.exact 2 S rfl hS
  change regValue R.S t.basis=S at sv
  have rb := rawValue_bound R.S t.basis (by omega)
  rw [sv] at rb
  have dv := ht.exact 3 (rawValue R.S.length S) rfl (by change _<2^R.T.length; rw [htl]; exact rb)
  change regValue R.T t.basis=_ at dv
  have r := rawClear_correct R.S R.T R.pad R.carry
    (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by omega) htl hpl (by omega) t rec (by rw [sv]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 3) (run (rawClear R.S R.T R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 3).length : Nat)] := by
    change (regValue R.T _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec3] using ht.step hn 3 0 r.1 r.2.2 val

theorem clearSum_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (base : State) (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B 0 T) R.scl0 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hs := w.S
  have hl : R.hi.length=R.h := by omega
  have av := regValue_lt R.lo base.basis; have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hl] at bv
  have hS : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [show R.S.length=R.h+1 by omega,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) hS
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have r := R.scl0_correct w hn t rec (by rw [sv,al,bl])
    ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
  have val : (regValue (reg R 2) (run R.scl0 rec t).basis : Int) ≡ 0 [ZMOD (2^(reg R 2).length : Nat)] := by
    change (regValue R.S _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec2] using ht.step hn 2 0 r.1 r.2.2 val


theorem clear_start_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (SquareBundle.c8E R) m s) (vec ((regValue R.lo s.basis)^2 : Nat) ((regValue R.hi s.basis)^2 : Nat)
      (regValue R.lo s.basis+regValue R.hi s.basis : Nat) (2*regValue R.lo s.basis*regValue R.hi s.basis : Nat)) := by
  rw [SquareBundle.c8E_eq R w hn s m (regValue R.lo s.basis*regValue R.hi s.basis)
    (by simpa only [Nat.mul_assoc] using hT0) hi0]
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hdl := w.dst
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^(R.bank.length-R.h) := by simpa only [L1] using regValue_lt R.hi s.basis
  have av : a^2<2^(2*R.h) := square_bound _ _ al
  have hd : regValue R.dst s.basis=(a+2^R.h*b)^2 := by
    simpa only [R.bank_value w s.basis] using hd0
  have XLt : (a+2^R.h*b)^2<2^(2*R.bank.length) := by
    rw [←R.bank_value w s.basis]
    exact square_bound _ _ (regValue_lt R.bank s.basis)
  have hX : (a+2^R.h*b)^2=(a^2+2^(2*R.h)*b^2)+2^R.h*(2*a*b) := by ring
  have hdiv : (a+2^R.h*b)^2/2^R.h=(a^2+2^(2*R.h)*b^2)/2^R.h+2*a*b := by
    rw [hX,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have hmod : (a+2^R.h*b)^2%2^R.h=(a^2+2^(2*R.h)*b^2)%2^R.h := by
    rw [hX,Nat.add_mul_mod_self_left]
  have hq : (a+2^R.h*b)^2/2^R.h<2^(2*R.bank.length-R.h) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),←pow_add,
      show 2*R.bank.length-R.h+R.h=2*R.bank.length by omega]
    exact XLt
  have r := BalancedInverse.subInPlace_any_correct (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) s m
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq))
  have frame : ∀q,q∉R.dmid → (run R.c8 m s).basis q=s.basis q := r.2.1
  have low : regValue (R.dst.take R.h) (run R.c8 m s).basis=regValue (R.dst.take R.h) s.basis := kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have dv : regValue R.dst (run R.c8 m s).basis=a^2+2^(2*R.h)*b^2 := by
    rw [R.dst_value_mid w,show regValue R.dmid (run R.c8 m s).basis=
        regValue R.dmid (run (subInPlace (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin) m s).basis from rfl,
      r.2.2,low,regValue_append,hT0,zm,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by omega),
      show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd,L4]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  have dlo : regValue R.dlo (run R.c8 m s).basis=a^2 := by
    rw [show regValue R.dlo (run R.c8 m s).basis=regValue R.dst (run R.c8 m s).basis%2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt av]
  have dhi : regValue R.dhi (run R.c8 m s).basis=b^2 := by
    rw [show regValue R.dhi (run R.c8 m s).basis=regValue R.dst (run R.c8 m s).basis/2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt av,Nat.zero_add]
  have sv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hS0
  have tv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hT0
  refine ⟨r.1,?_,fun q hd _ _ => frame q (fun bad => hd (List.mem_of_mem_drop bad))⟩
  intro i; fin_cases i
  · change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
    rw [dlo]; exact Int.ModEq.rfl
  · change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
    rw [dhi]; exact Int.ModEq.rfl
  · change (regValue R.S _ : Int) ≡ _ [ZMOD _]
    rw [sv]; exact Int.ModEq.rfl
  · change (regValue R.T _ : Int) ≡ _ [ZMOD _]
    rw [tv]; exact Int.ModEq.rfl


theorem clear_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (clear R) m s).phase=s.phase ∧
    regValue R.dst (run (clear R) m s).basis=0 ∧
    regValue R.S (run (clear R) m s).basis=0 ∧
    regValue R.T (run (clear R) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (clear R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  let d : Int := ((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)-(2^(2*R.h-1) : Nat)
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have slt : S<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [S]; omega
  have st1 := diagaddlo_transition R w he hn s hc0 hi0 (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat)
  have st1' : Transition R s (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (vec A (b^2 : Nat) S (2*a*b : Nat)) (mappedDiagAdd R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add] using st1
  have st2 := diagaddhi_transition R w he hn s hc0 hi0 A (b^2 : Nat) S (2*a*b : Nat)
  have st2' : Transition R s (vec A (b^2 : Nat) S (2*a*b : Nat))
      (vec A B S (2*a*b : Nat)) (mappedDiagAdd R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add] using st2
  have st3 := corrBack_transition R w he hh hn s hz0 hc0 hi0 A B (2*a*b : Nat)
  have st4 := addhi_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d) hB (by dsimp [B,rawValue]; exact SquareBundle.raw_even R.h b (by omega))
  have st5 := addlo_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d+B) hA (by dsimp [A,rawValue]; exact SquareBundle.raw_even R.h a (by omega))
  have norm := cross_normalize R.h a b hh alo bhi
  have norm' : ((2*a*b : Nat) : Int)+d+B+A=Z := by
    change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
      (2*a*b : Nat) at norm
    dsimp only [d]
    linarith only [norm]
  rw [norm'] at st5
  have st6 := rawclearSum_transition R w hn s hp0 hc0 A B S slt
  rw [hSS] at st6
  have st7 := clearSum_transition R w he hn s hz0 hc0 hi0 A B 0
  have st8 := rawclearhi_transition R w he hn s hp0 hc0 A 0 0
  have st9 := rawclearlo_transition R w he hn s hp0 hc0 0 0 0
  have st3' : Transition R s (vec A B S (2*a*b : Nat))
      (vec A B S ((2*a*b : Nat)+d)) (corrBack R) := by
    convert st3 using 1 <;> try rfl
    simp only [d]
    congr 1
    ring
  have tail := ((((((((st1'.seq st2').seq st3').seq st4).seq st5).seq st6).seq st7).seq st8).seq st9)
  have initial := clear_start_shape R w he hn s (m.take (measurementCount (SquareBundle.c8E R))) hd0 hS0 hT0 hz0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (SquareBundle.c8E R))) initial
  have final : Shape R s (run (clear R) m s) (vec 0 0 0 0) := by
    simpa only [clear,run_append] using result
  refine ⟨final.phase,?_,final.exact 2 0 rfl (by norm_num),final.exact 3 0 rfl (by norm_num),final.rest⟩
  have zlo : regValue R.dlo (run (clear R) m s).basis=0 := final.exact 0 0 rfl (by norm_num)
  have zhi : regValue R.dhi (run (clear R) m s).basis=0 := final.exact 1 0 rfl (by norm_num)
  rw [R.dst_value w,zlo,zhi]
  simp

end ECDSAAdd.Entrant.DiagSq
end DiagonalRegisterIntegration
section DiagonalSquareInterface
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic
def makeC (R : KRegs) : Program := make R++R.scl0
def clearC (R : KRegs) : Program := R.smk++clear R
end ECDSAAdd.Entrant.DiagSq
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)
theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.make R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := DiagSq.make_correct R w he hh hn s m hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩

theorem diag_sq_full_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.clear R) R.invF := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  have r := DiagSq.clear_correct R w he hh hn s m hd0 (by rw [hI.1,R.lo_mod w,R.hi_div w]) (by rw [hI.2,R.lo_mod w,R.hi_div w])
    (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [regValue_append,r.2.2.1,r.2.2.2.1]; simp

theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (DiagSq.make R))
  let b := m.drop (measurementCount (DiagSq.make R))
  have r := DiagSq.make_correct R w he hh hn s a hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (DiagSq.make R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl0_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (DiagSq.makeC R) m s=run R.scl0 b u := by
    rw [DiagSq.makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

theorem diag_sq_cl_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.clearC R) R.invC := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  let a := m.take (measurementCount R.smk)
  let b := m.drop (measurementCount R.smk)
  have r := R.smk_correct w hn s a hI.1 (xz hz0 hz) hc0 hi0
  generalize hu : run R.smk a s=u at r
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin ∨ q∈R.dst ∨ q∈R.T) : q∉R.S := by
    rcases h with h|h|h|h|h|h|h
    · exact (R.outside hn q (Or.inl h)).2.1
    · exact (R.outside hn q (Or.inr (Or.inl h))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inl h)))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inr h))))).2.1
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.2 q (hl q hq))
  have bk := keep R.bank (fun q h => o q (Or.inl h))
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := DiagSq.clear_correct R w he hh hn u b (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),bk]; exact hd0)
    (by rw [r.2.1,lo,hi])
    (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))),hI.2,lo,hi,R.lo_mod w,R.hi_div w])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inl h))))).trans hp0)
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((r.2.2 _ (o _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hi0)
  have eq : run (DiagSq.clearC R) m s=run (DiagSq.clear R) b u := by
    rw [DiagSq.clearC,run_append,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)

end ECDSAAdd.Entrant.KRegs
end DiagonalSquareInterface


-- DIAGONAL COMPONENT RawBaseline.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant
open Arithmetic
def raw_ksq (k : Nat) : Nat := signedSquareRowsCount k+2*k-1

def raw_kcost (n h : Nat) : Nat :=
  raw_ksq h+raw_ksq (n-h)+(n-h)+raw_ksq (n-h+1)+2*(2*(n-h+1)-1)+(2*n-h-1)

namespace KRegs
variable (R : KRegs)
def raw_m1 : Program := mappedSignedSquare R.lo R.dlo R.pad R.carry R.cin
def raw_m2 : Program := mappedSignedSquare R.hi R.dhi R.pad R.carry R.cin
def raw_m5 : Program := mappedSignedSquare R.S R.T R.pad R.carry R.cin
def raw_c5 : Program := mappedSignedSquareClear R.S R.T R.pad R.carry R.cin
def raw_c2 : Program := mappedSignedSquareClear R.hi R.dhi R.pad R.carry R.cin
def raw_c1 : Program := mappedSignedSquareClear R.lo R.dlo R.pad R.carry R.cin
def raw_make : Program := R.raw_m1++R.raw_m2++R.m3++R.m4++R.raw_m5++R.m6++R.m7++R.m8
def raw_clear : Program := R.c8++R.c7++R.c6++R.raw_c5++R.c4++R.m3++R.raw_c2++R.raw_c1
theorem raw_make_counts (w : R.W) :
    toffoliCount R.raw_make=raw_kcost R.bank.length R.h ∧ measurementCount R.raw_make=raw_kcost R.bank.length R.h := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have q1 := mappedSignedSquare_counts R.lo R.dlo R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q2 := mappedSignedSquare_counts R.hi R.dhi R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q5 := mappedSignedSquare_counts R.S R.T R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q3 := copyRegister_counts none R.lo (R.S.take R.h) (by omega)
  have q4 := addInPlace_counts (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q6 := subInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q7 := subInPlace_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q8 := addInPlace_counts (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,toffoliCount_append,measurementCount_append,
    q1.1.1,q1.1.2,q2.1.1,q2.1.2,q5.1.1,q5.1.2,q3.1,q3.2,q4.1,q4.2,q6.1,q6.2,q7.1,q7.2,q8.1,q8.2]
  simp only [L0,L1,L2,L3,L4,hTl,hSl,raw_kcost,raw_ksq,Option.isSome_none,Bool.false_eq_true,if_false]
  constructor <;> omega

theorem raw_clear_counts (w : R.W) :
    toffoliCount R.raw_clear=raw_kcost R.bank.length R.h ∧ measurementCount R.raw_clear=raw_kcost R.bank.length R.h := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have q1 := mappedSignedSquare_counts R.lo R.dlo R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q2 := mappedSignedSquare_counts R.hi R.dhi R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q5 := mappedSignedSquare_counts R.S R.T R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q3 := copyRegister_counts none R.lo (R.S.take R.h) (by omega)
  have q4 := subInPlace_counts (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q6 := addInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q7 := addInPlace_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q8 := subInPlace_counts (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,toffoliCount_append,measurementCount_append,
    q1.2.1,q1.2.2,q2.2.1,q2.2.2,q5.2.1,q5.2.2,q3.1,q3.2,q4.1,q4.2,q6.1,q6.2,q7.1,q7.2,q8.1,q8.2]
  simp only [L0,L1,L2,L3,L4,hTl,hSl,raw_kcost,raw_ksq,Option.isSome_none,Bool.false_eq_true,if_false]
  constructor <;> omega

theorem raw_steps_support (w : R.W) :
    ECDSAAdd.wires R.raw_make⊆R.all.toFinset ∧ ECDSAAdd.wires R.raw_clear⊆R.all.toFinset := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have g1 := mappedSignedSquare_wires_subset R.lo R.dlo R.pad R.carry R.cin (by omega) hpl (by omega)
  have g2 := mappedSignedSquare_wires_subset R.hi R.dhi R.pad R.carry R.cin (by omega) hpl (by omega)
  have g5 := mappedSignedSquare_wires_subset R.S R.T R.pad R.carry R.cin (by omega) hpl (by omega)
  have g3 := copyRegister_wires_subset none R.lo (R.S.take R.h)
  have g4 := addInPlace_wires (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g6 := addInPlace_wires (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g7 := addInPlace_wires (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g8 := addInPlace_wires (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g4s := subInPlace_wires (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g6s := subInPlace_wires (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g7s := subInPlace_wires (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g8s := subInPlace_wires (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have sb : R.bank ⊆ R.all := fun q h => R.mem_all q (Or.inl h)
  have sd : R.dst ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inl h))
  have sS : R.S ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inl h)))
  have sT : R.T ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have sz : R.z ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have sp : R.pad ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  have sc : R.carry ⊆ R.all := fun q h =>
    R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have si : [R.cin] ⊆ R.all := by
    intro q h; simp only [List.mem_singleton] at h
    exact R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  have tk {l : List Wire} {k : Nat} (h : l ⊆ R.all) : l.take k ⊆ R.all := fun q hq => h (List.mem_of_mem_take hq)
  have dr {l : List Wire} {k : Nat} (h : l ⊆ R.all) : l.drop k ⊆ R.all := fun q hq => h (List.mem_of_mem_drop hq)
  have fs {l : List Wire} (h : l ⊆ R.all) : l.toFinset ⊆ R.all.toFinset :=
    fun q hq => List.mem_toFinset.mpr (h (List.mem_toFinset.mp hq))
  have ap {l1 l2 : List Wire} (h1 : l1 ⊆ R.all) (h2 : l2 ⊆ R.all) : l1++l2 ⊆ R.all :=
    List.append_subset.mpr ⟨h1,h2⟩
  have co {l : List Wire} (h : l ⊆ R.all) : R.cin::l ⊆ R.all := by
    intro q hq; rcases List.mem_cons.mp hq with e|e
    · exact si (by simp [e])
    · exact h e
  have e1 : (R.lo++R.dlo++R.pad++R.carry++[R.cin]).toFinset⊆R.all.toFinset := fs (ap (ap (ap (ap (tk sb) (tk sd)) sp) sc) si)
  have e2 : (R.hi++R.dhi++R.pad++R.carry++[R.cin]).toFinset⊆R.all.toFinset := fs (ap (ap (ap (ap (dr sb) (dr sd)) sp) sc) si)
  have e5 : (R.S++R.T++R.pad++R.carry++[R.cin]).toFinset⊆R.all.toFinset := fs (ap (ap (ap (ap sS sT) sp) sc) si)
  have e3 : ((none : Option Wire).toList++R.lo++R.S.take R.h).toFinset⊆R.all.toFinset := fs (ap (ap (show (none : Option Wire).toList ⊆ R.all by simp) (tk sb)) (tk sS))
  have e4 : (R.cin::(R.hi++R.zS++R.S++R.carry.take (R.S.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap (dr sb) (tk sz)) sS) (tk sc)))
  have e6 : (R.cin::(R.dlo++R.zA++R.T++R.carry.take (R.T.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap (tk sd) (tk sz)) sT) (tk sc)))
  have e7 : (R.cin::(R.dhi++R.zB++R.T++R.carry.take (R.T.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap (dr sd) (tk sz)) sT) (tk sc)))
  have e8 : (R.cin::(R.T++R.zM++R.dmid++R.carry.take (R.dmid.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap sT (tk sz)) (dr sd)) (tk sc)))
  constructor
  · simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨g1.1.trans e1,g2.1.trans e2⟩,g3.trans e3⟩,g4 ▸ e4⟩,g5.1.trans e5⟩,g6s ▸ e6⟩,
      g7s ▸ e7⟩,g8 ▸ e8⟩
  · simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨g8s ▸ e8,g7 ▸ e7⟩,g6 ▸ e6⟩,g5.2.trans e5⟩,g4s ▸ e4⟩,g3.trans e3⟩,
      g2.2.trans e2⟩,g1.2.trans e1⟩

theorem raw_steps_physical (hn : R.all.Nodup) :
    GatePhysical R.raw_make ∧ GatePhysical R.raw_clear := by
  have p1 := mappedSignedSquare_physical R.lo R.dlo R.pad R.carry R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have p2 := mappedSignedSquare_physical R.hi R.dhi R.pad R.carry R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have p5 := mappedSignedSquare_physical R.S R.T R.pad R.carry R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have p3 := copyRegister_physical none R.lo (R.S.take R.h) (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega)) (by intro c hc; simp at hc)
  have a4 := addInPlace_physical (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have a6 := addInPlace_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have a7 := addInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have a8 := addInPlace_physical (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s4 := subInPlace_physical (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s6 := subInPlace_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s7 := subInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s8 := subInPlace_physical (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  constructor
  · simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨p1.1,p2.1⟩,p3⟩,a4⟩,p5.1⟩,s6⟩,s7⟩,a8⟩
  · simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨s8,a7⟩,a6⟩,p5.2⟩,s4⟩,p3⟩,p2.2⟩,p1.2⟩

theorem raw_tiny_slots (w : R.W) (h33 : R.h≤33) (hhi : R.bank.length-R.h≤34) (hb : R.bank.length≤66) :
    Challenge.gateSlots R.raw_make≤150000 ∧ Challenge.gateSlots R.raw_clear≤150000 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z
  have g1 := Baselines.mappedSigned_gateSlots_le R.lo R.dlo R.pad R.carry R.cin
  have g2 := Baselines.mappedSigned_gateSlots_le R.hi R.dhi R.pad R.carry R.cin
  have g5 := Baselines.mappedSigned_gateSlots_le R.S R.T R.pad R.carry R.cin
  have a4 := Baselines.addInPlace_gateSlots_le (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
  have a6 := Baselines.addInPlace_gateSlots_le (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
  have a7 := Baselines.addInPlace_gateSlots_le (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
  have a8 := Baselines.addInPlace_gateSlots_le (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
  have s4 := Baselines.subInPlace_gateSlots_le (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
  have s6 := Baselines.subInPlace_gateSlots_le (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
  have s7 := Baselines.subInPlace_gateSlots_le (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
  have s8 := Baselines.subInPlace_gateSlots_le (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
  have c3 := Baselines.copyRegister_gateSlots none R.lo (R.S.take R.h)
  have x1 : R.lo.length*(12*(R.lo.length+1)+6*R.dlo.length) ≤ 33*(12*34+6*66) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x2 : R.hi.length*(12*(R.hi.length+1)+6*R.dhi.length) ≤ 34*(12*35+6*68) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : R.S.length*(12*(R.S.length+1)+6*R.T.length) ≤ 35*(12*36+6*70) :=
    Nat.mul_le_mul (by omega) (by omega)
  have y4 : (R.hi++R.zS).length ≤ 35 := by simp only [List.length_append]; omega
  have y6 : (R.dlo++R.zA).length ≤ 70 := by simp only [List.length_append]; omega
  have y7 : (R.dhi++R.zB).length ≤ 70 := by simp only [List.length_append]; omega
  have y8 : (R.T++R.zM).length ≤ 102 := by simp only [List.length_append]; omega
  have y9 : R.dmid.length ≤ 102 := by omega
  have yc : min R.lo.length (R.S.take R.h).length ≤ 33 := by omega
  constructor
  · simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,Challenge.gateSlots_append]; omega
  · simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,Challenge.gateSlots_append]; omega

end KRegs
end ECDSAAdd.Entrant


-- DIAGONAL COMPONENT DiagonalResources.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
section DiagonalResources
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

theorem counts_rel (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (make R)+(R.h-2)+7=toffoliCount R.raw_make ∧
    measurementCount (make R)+(R.h-2)=measurementCount R.raw_make ∧
    toffoliCount (clear R)+(R.h-2)+7+R.h=toffoliCount R.raw_clear ∧
    measurementCount (clear R)+(R.h-2)=measurementCount R.raw_clear := by
  have sc:=R.scl0_counts w
  have osT:=(R.piece_counts w).2.2.1
  have osM:=(R.piece_counts w).2.2.2.1
  simp only [KRegs.scl,toffoliCount_append,measurementCount_append] at osT osM
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have cc := correction_counts R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    (by omega) (by omega) (by omega) (by omega)
  have dc := mappedDiag_counts R.S R.T R.carry R.cin (by omega) hTl (by omega)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have a := SquareHead.rows_toffoli R.lo R.dlo R.pad R.carry (by omega) (by omega) w.pad (by omega)
  have b := SquareHead.rows_toffoli R.hi R.dhi R.pad R.carry (by omega) (by omega) w.pad (by omega)
  have c := SquareHead.rows_toffoli R.S R.T R.pad R.carry (by omega) w.T w.pad (by omega)
  have op0 := SquareBundle.m6R_counts R w
  have op1 := SquareBundle.m7R_counts R w
  have op2 := SquareBundle.m8E_counts R w
  have op3 := SquareBundle.c8E_counts R w
  have op4 := SquareBundle.c7R_counts R w
  have op5 := SquareBundle.c6R_counts R w
  simp only [make,headBlock,seeds,clear,corr,corrBack,rawMake,rawClear,
    KRegs.raw_make,KRegs.raw_clear,KRegs.smk,KRegs.scl,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,
    KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquare,mappedSignedSquareClear,
    toffoliCount_append,measurementCount_append,cc.1,cc.2.1,cc.2.2.1,cc.2.2.2,
    dc.1.1,dc.1.2,dc.2.1,dc.2.2,sc.1,sc.2,(SquareHead.rows_measurements R.lo R.dlo R.pad R.carry).1,
    (SquareHead.rows_measurements R.lo R.dlo R.pad R.carry).2,
    (SquareHead.rows_measurements R.hi R.dhi R.pad R.carry).1,
    (SquareHead.rows_measurements R.hi R.dhi R.pad R.carry).2,
    (SquareHead.rows_measurements R.S R.T R.pad R.carry).1,
    (SquareHead.rows_measurements R.S R.T R.pad R.carry).2]
  omega

theorem slots_rel (R : KRegs) :
    Challenge.gateSlots (make R)≤Challenge.gateSlots R.raw_make+Challenge.gateSlots (corr R) ∧
    Challenge.gateSlots (clear R)≤Challenge.gateSlots R.raw_clear+Challenge.gateSlots (corrBack R) := by
  have sc:=R.scl0_slots
  simp only [KRegs.scl,Challenge.gateSlots_append] at sc
  have h0 := SquareHead.slots_sublist (SquareHead.rows_sublist R.lo R.dlo R.pad R.carry).1
  have h1 := SquareHead.slots_sublist (SquareHead.rows_sublist R.hi R.dhi R.pad R.carry).1
  have h2 := SquareHead.slots_sublist (SquareHead.rows_sublist R.S R.T R.pad R.carry).1
  have h3 := SquareHead.slots_sublist (SquareHead.rows_sublist R.lo R.dlo R.pad R.carry).2
  have h4 := SquareHead.slots_sublist (SquareHead.rows_sublist R.hi R.dhi R.pad R.carry).2
  have h5 := SquareHead.slots_sublist (SquareHead.rows_sublist R.S R.T R.pad R.carry).2

  have op0 := SquareBundle.m6R_slots R
  have op1 := SquareBundle.m7R_slots R
  have op2 := SquareBundle.m8E_slots R
  have op3 := SquareBundle.c8E_slots R
  have op4 := SquareBundle.c7R_slots R
  have op5 := SquareBundle.c6R_slots R
  simp only [make,headBlock,seeds,clear,corr,corrBack,rawMake,rawClear,
    KRegs.raw_make,KRegs.raw_clear,KRegs.smk,KRegs.scl,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,
    KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquare,mappedSignedSquareClear,Challenge.gateSlots_append]
  omega

theorem corr_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (corr R)≤800 ∧ Challenge.gateSlots (corrBack R)≤800 := by
  have h4 := w.h4; have hSl := w.S; have hTl := w.T
  have len := correctionBits_length R.h R.S (parity R) (by omega) (by omega)
  have sub := Baselines.mappedSub_gateSlots_le (correctionBits R.h R.S (parity R))
    (R.T.drop R.h) (R.carry.take (R.h+1)) R.cin
  have add := Baselines.mappedAdd_gateSlots_le (correctionBits R.h R.S (parity R))
    (R.T.drop R.h) (R.carry.take (R.h+1)) R.cin
  have inc := Baselines.mappedAdd_gateSlots_le (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  have dec := Baselines.mappedSub_gateSlots_le (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  have ie := SquareHead.slots_sublist (SquareIncrement.add_sublist (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin)
  have de := SquareHead.slots_sublist (SquareIncrement.sub_sublist (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin)
  simp only [len,mappedConstant_length,List.length_drop] at sub add inc dec
  simp only [corr,corrBack,correction,correctionBack,loadedSub,loadedAdd,Challenge.gateSlots_append,
    load,unload,Baselines.gateSlots_cons,Challenge.instructionSlots,Baselines.gateSlots_nil]
  omega


theorem load_support (a b c q cin : Wire) :
    wires (load a b c q cin)⊆[a,b,c,q,cin].toFinset ∧
    wires (unload a b c q cin)⊆[a,b,c,q,cin].toFinset := by
  constructor <;> intro x hx <;>
    simp [load,unload,wires,Instr.wires] at hx ⊢ <;> tauto

theorem mapped_support_to (W : List Wire) (bits : List MappedBit) (dst carry : List Wire) (cin : Wire)
    (hi : cin∈W) (hb : ∀x∈mappedWires bits,x∈W) (hd : ∀x∈dst,x∈W) (hc : ∀x∈carry,x∈W) :
    wires (mappedAdd bits dst carry cin)⊆W.toFinset ∧ wires (mappedSub bits dst carry cin)⊆W.toFinset := by
  have lift {P : Program} (hw : wires P⊆(mappedWires bits++dst++carry++[cin]).toFinset) :
      wires P⊆W.toFinset := by
    intro x hx
    have h := hw hx
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    have b := hb x; have d := hd x; have c := hc x
    rcases h with ((h|h)|h)|h
    · exact b h
    · exact d h
    · exact c h
    · simpa only [h] using hi
  exact ⟨lift (mappedAdd_wires_subset bits dst carry cin),lift (mappedSub_wires_subset bits dst carry cin)⟩

theorem corr_views (R : KRegs) (w : R.W) :
    R.lo.getD (R.h-1) 0∈R.bank ∧ R.hi.getD (R.h-1) 0∈R.bank ∧
    R.S.getD (R.h-1) 0∈R.S ∧ parity R∈R.z ∧
    ∀x∈mappedWires (correctionBits R.h R.S (parity R)),x∈R.S ∨ x∈R.z := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have hzl := w.z
  have a := List.mem_of_mem_take (getD_in R.lo (R.h-1) (by omega))
  have b := List.mem_of_mem_drop (getD_in R.hi (R.h-1) (by omega))
  have c := getD_in R.S (R.h-1) (by omega)
  have q : parity R∈R.z := getD_in R.z 0 (by omega)
  refine ⟨a,b,c,q,?_⟩
  intro x hx
  rw [correctionBits_wires] at hx
  rcases List.mem_append.mp hx with hx|hx
  · exact Or.inl (List.mem_of_mem_take hx)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact Or.inr q
    · exact Or.inl c

theorem corr_support (R : KRegs) (w : R.W) :
    wires (corr R)⊆R.all.toFinset ∧ wires (corrBack R)⊆R.all.toFinset := by
  have v := corr_views R w
  have ci : R.cin∈R.all := by simp [KRegs.all]
  have cp : [R.lo.getD (R.h-1) 0,R.hi.getD (R.h-1) 0,R.S.getD (R.h-1) 0,parity R,R.cin].toFinset⊆R.all.toFinset := by
    intro x hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with rfl|rfl|rfl|rfl|rfl
    · simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
    · simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
    · simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
    · simp [KRegs.all,v.2.2.2.1]
    · exact ci
  have lp := load_support (R.lo.getD (R.h-1) 0) (R.hi.getD (R.h-1) 0) (R.S.getD (R.h-1) 0) (parity R) R.cin
  have l := lp.1.trans cp
  have u := lp.2.trans cp
  have bm := mapped_support_to R.all (correctionBits R.h R.S (parity R)) (R.T.drop R.h) (R.carry.take (R.h+1)) R.cin ci
    (by intro x hx; rcases v.2.2.2.2 x hx with h|h <;> simp [KRegs.all,h])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_drop hx])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_take hx])
  have im := mapped_support_to R.all (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin ci
    (by simp [mappedConstant,mappedConstantBit,mappedWires])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_drop hx])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_take hx])
  have ia := (SquareHead.wires_sublist (SquareIncrement.add_sublist (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin)).trans im.1
  have id := (SquareHead.wires_sublist (SquareIncrement.sub_sublist (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin)).trans im.2
  constructor
  · simp only [corr,correction,loadedSub,wires_append,Finset.union_subset_iff,and_assoc]
    exact ⟨l,bm.2,u,ia⟩
  · simp only [corrBack,correctionBack,loadedAdd,wires_append,Finset.union_subset_iff,and_assoc]
    exact ⟨id,l,bm.1,u⟩

theorem loaded_physical (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (ha : a≠q) (hb : b≠q) (hc : c≠q) (hn : (cin::dst++carry).Nodup)
    (hs : ∀x∈mappedWires bits,x∉cin::dst++carry) :
    GatePhysical (loadedSub a b c q cin bits dst carry k) ∧ GatePhysical (loadedAdd a b c q cin bits dst carry k) := by
  have nd := (drop_views dst carry cin k hn).1
  have src : ∀b∈bits,∀x∈b.wire,x∉cin::dst.drop k++carry := by
    intro b hb x hx bad
    have m : x∈mappedWires bits := List.mem_flatMap.mpr ⟨b,hb,by simpa using hx⟩
    apply hs x m
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with (h|h)|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (List.mem_of_mem_drop h))
    · exact Or.inr h
  have add := mappedAdd_physical bits (dst.drop k) carry cin nd src
  have sub : GatePhysical (mappedSub bits (dst.drop k) carry cin) := by
    simp only [mappedSub,gatePhysical_append]
    exact ⟨⟨notRegister_physical _,add⟩,notRegister_physical _⟩
  have l : GatePhysical (load a b c q cin) := by
    simp [load,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ha,hb,hc]
  have u : GatePhysical (unload a b c q cin) := by
    simp [unload,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ha,hb,hc]
  simp only [loadedSub,loadedAdd,gatePhysical_append]
  tauto

theorem corr_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (corr R) ∧ GatePhysical (corrBack R) := by
  have v := corr_views R w
  have out (x : Wire) (hx : x∈R.bank++R.S) : x∉R.z :=
    kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega) x hx
  have aq : R.lo.getD (R.h-1) 0≠parity R := fun e => out _ (List.mem_append.mpr (Or.inl v.1)) (e ▸ v.2.2.2.1)
  have bq : R.hi.getD (R.h-1) 0≠parity R := fun e => out _ (List.mem_append.mpr (Or.inl v.2.1)) (e ▸ v.2.2.2.1)
  have cq : R.S.getD (R.h-1) 0≠parity R := fun e => out _ (List.mem_append.mpr (Or.inr v.2.2.1)) (e ▸ v.2.2.2.1)
  have nd (n : Nat) : (R.cin::R.T++R.carry.take n).Nodup := knd hn (fun q => by
    have c := (List.take_sublist n R.carry).count_le q
    simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have src (x : Wire) (hx : x∈mappedWires (correctionBits R.h R.S (parity R))) :
      x∉R.cin::R.T++R.carry.take (R.h+1) := by
    have m : x∈R.S++R.z := List.mem_append.mpr (v.2.2.2.2 x hx)
    exact kdis hn (fun q => by have c := (List.take_sublist (R.h+1) R.carry).count_le q; simp only [KRegs.all,List.count_cons,List.count_append]; omega) x m
  have lp := loaded_physical (R.lo.getD (R.h-1) 0) (R.hi.getD (R.h-1) 0) (R.S.getD (R.h-1) 0)
    (parity R) R.cin (correctionBits R.h R.S (parity R)) R.T (R.carry.take (R.h+1)) R.h aq bq cq (nd _) src
  have it := (drop_views R.T (R.carry.take 2) R.cin (2*R.h-1) (nd 2)).1
  have ip := mappedAdd_physical (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin it
    (by simp [mappedConstant,mappedConstantBit])
  have sp : GatePhysical (mappedSub (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin) := by
    simp only [mappedSub,gatePhysical_append]
    exact ⟨⟨notRegister_physical _,ip⟩,notRegister_physical _⟩
  have ia : GatePhysical (SquareIncrement.add (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin) :=
    fun i hi => ip i ((SquareIncrement.add_sublist _ _ _).subset hi)
  have id : GatePhysical (SquareIncrement.sub (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin) :=
    fun i hi => sp i ((SquareIncrement.sub_sublist _ _ _).subset hi)
  simp only [corr,corrBack,correction,correctionBack,gatePhysical_append]
  exact ⟨⟨lp.1,ia⟩,⟨id,lp.2⟩⟩

theorem steps_support (R : KRegs) (w : R.W) : wires (make R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset := by
  have sc:=R.scl0_support w
  have old := R.raw_steps_support w
  have cc := corr_support R w
  have mk := old.1
  have cl := old.2
  simp only [KRegs.raw_make,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,mappedSignedSquare,
    wires_append,Finset.union_subset_iff,and_assoc] at mk
  simp only [KRegs.raw_clear,KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquareClear,
    wires_append,Finset.union_subset_iff,and_assoc] at cl
  obtain ⟨lr,lt,ld,hr,ht,hd,m3,m4,sr,st,sd,m6,m7,m8⟩ := mk
  obtain ⟨c8,c7,c6,sda,stc,src,c4,m3c,hda,htc,hrc,lda,ltc,lrc⟩ := cl
  constructor
  · simp only [make,headBlock,seeds,rawMake,KRegs.smk,wires_append,Finset.union_subset_iff,and_assoc]
    exact ⟨(SquareHead.wires_sublist (SquareHead.rows_sublist R.lo R.dlo R.pad R.carry).1).trans lr,lt,
      (SquareHead.wires_sublist (SquareHead.rows_sublist R.hi R.dhi R.pad R.carry).1).trans hr,ht,m3,m4,
      (SquareHead.wires_sublist (SquareHead.rows_sublist R.S R.T R.pad R.carry).1).trans sr,st,(SquareBundle.m6R_support R).trans m6,(SquareBundle.m7R_support R).trans m7,cc.1,ld,hd,(SquareBundle.m8E_support R).trans m8⟩
  · simp only [clear,rawClear,KRegs.scl,wires_append,Finset.union_subset_iff,and_assoc]
    exact ⟨(SquareBundle.c8E_support R).trans c8,lda,hda,cc.2,(SquareBundle.c7R_support R).trans c7,(SquareBundle.c6R_support R).trans c6,stc,
      (SquareHead.wires_sublist (SquareHead.rows_sublist R.S R.T R.pad R.carry).2).trans src,sc,htc,
      (SquareHead.wires_sublist (SquareHead.rows_sublist R.hi R.dhi R.pad R.carry).2).trans hrc,ltc,
      (SquareHead.wires_sublist (SquareHead.rows_sublist R.lo R.dlo R.pad R.carry).2).trans lrc⟩

theorem steps_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (make R) ∧ GatePhysical (clear R) := by
  have sc:=R.scl0_physical w hn
  have old := R.raw_steps_physical hn
  have cc := corr_physical R w hn
  have mk := old.1
  have cl := old.2
  simp only [KRegs.raw_make,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,mappedSignedSquare,
    gatePhysical_append,and_assoc] at mk
  simp only [KRegs.raw_clear,KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquareClear,
    gatePhysical_append,and_assoc] at cl
  obtain ⟨lr,lt,ld,hr,ht,hd,m3,m4,sr,st,sd,m6,m7,m8⟩ := mk
  obtain ⟨c8,c7,c6,sda,stc,src,c4,m3c,hda,htc,hrc,lda,ltc,lrc⟩ := cl
  constructor
  · simp only [make,headBlock,seeds,rawMake,KRegs.smk,gatePhysical_append,and_assoc]
    exact ⟨(fun i hi => lr i ((SquareHead.rows_sublist R.lo R.dlo R.pad R.carry).1.subset hi)),lt,
      (fun i hi => hr i ((SquareHead.rows_sublist R.hi R.dhi R.pad R.carry).1.subset hi)),ht,m3,m4,
      (fun i hi => sr i ((SquareHead.rows_sublist R.S R.T R.pad R.carry).1.subset hi)),st,SquareBundle.m6R_physical R hn,SquareBundle.m7R_physical R hn,cc.1,ld,hd,SquareBundle.m8E_physical R hn⟩
  · simp only [clear,rawClear,KRegs.scl,gatePhysical_append,and_assoc]
    exact ⟨SquareBundle.c8E_physical R hn,lda,hda,cc.2,SquareBundle.c7R_physical R hn,SquareBundle.c6R_physical R hn,stc,
      (fun i hi => src i ((SquareHead.rows_sublist R.S R.T R.pad R.carry).2.subset hi)),sc,htc,
      (fun i hi => hrc i ((SquareHead.rows_sublist R.hi R.dhi R.pad R.carry).2.subset hi)),ltc,
      (fun i hi => lrc i ((SquareHead.rows_sublist R.lo R.dlo R.pad R.carry).2.subset hi))⟩

def cost (R : KRegs) : Nat := raw_kcost R.bank.length R.h-(R.h-2)

def tCost (R : KRegs) : Nat := cost R-7

theorem make_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (make R)=tCost R ∧ measurementCount (make R)=cost R := by
  have c := counts_rel R w he
  have o := R.raw_make_counts w
  dsimp only [tCost,cost]
  omega

theorem clear_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (clear R)=tCost R-R.h ∧ measurementCount (clear R)=cost R := by
  have c := counts_rel R w he
  have o := R.raw_clear_counts w
  dsimp only [tCost,cost]
  omega

theorem tiny_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (make R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 := by
  have old := R.raw_tiny_slots w hh (by omega) (by omega)
  have c := corr_slots R w he hh
  have r := slots_rel R
  omega

end ECDSAAdd.Entrant.DiagSq
end DiagonalResources


section SquareNormalFirstRows
namespace ECDSAAdd.Entrant.NormalHead
open Arithmetic

def make (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  DiagSq.rawMake xs dst pad carry++
    (notRegister dst++TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++notRegister dst)

def clear (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++DiagSq.rawClear xs dst pad carry

theorem make_eq (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0) :
    run (make xs dst pad carry cin) m s=run (TrimSquare.tsq2 xs dst pad carry cin) m s := by
  simp only [make,DiagSq.rawMake,TrimSquare.tsq2,List.append_assoc,run_append,
    (SquareHead.rows_measurements xs dst pad carry).1]
  rw [SquareHead.rows_eq xs dst pad carry (List.nodup_cons.mp hn).2 hd s _ h0]

theorem make_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    (run (make xs dst pad carry cin) m s).phase=s.phase ∧
    regValue dst (run (make xs dst pad carry cin) m s).basis=(regValue xs s.basis)^2 ∧
    ∀q,q∉dst → (run (make xs dst pad carry cin) m s).basis q=s.basis q := by
  rw [make_eq cin xs dst pad carry hn hd s m h0]
  exact TrimSquare.tsq2_correct cin xs dst pad carry hn hx hd hp hc s m h0 hp0 hc0 hi0

theorem dropAdd_exists (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (m : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) :
    ∃R,run (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) m s=
      run (mappedDiagAdd xs dst carry cin) R s := by
  obtain ⟨x0,b',bits,y,y',ys,c,cs,hx0,hdiag,rfl,hcar,_⟩ := TrimSquare.diag_shape xs dst carry hx hd hc
  obtain ⟨xt,rfl⟩ : ∃xt,xs=x0::xt := by
    match xs,hx0 with | _::xt,rfl => exact ⟨xt,rfl⟩
  obtain ⟨hnd4,hrec,hsrc,hl,hcl,ha,hmem,hcin⟩ :=
    TrimSquare.diag_side cin x0 xt y y' ys pad carry b' bits c cs hn hd hdiag hcar hc
  have sy := TrimSquare.bit0_of_square y x0 (y'::ys) xt s.basis hval
  have clean : ∀q∈carry,s.basis q=false := (regValue_zero _ _).mp hc0
  unfold mappedDiagAdd
  rw [hdiag,hcar]
  exact ⟨_,TrimSquare.drop2_run x0 y y' c cin b' bits ys cs hnd4 hrec hsrc hl hcl ha m s
    (by rw [sy]; simp) (clean c (hmem c List.mem_cons_self))
    (fun q hq => clean q (hmem q (List.mem_cons_of_mem _ hq)))⟩

theorem clear_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (m : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) (hi0 : s.basis cin=false) :
    (run (clear xs dst pad carry cin) m s).phase=s.phase ∧
    regValue dst (run (clear xs dst pad carry cin) m s).basis=0 ∧
    ∀q,q∉dst → (run (clear xs dst pad carry cin) m s).basis q=s.basis q := by
  let P := TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin
  let f := m.take (measurementCount P)
  let g := m.drop (measurementCount P)
  let u := run P f s
  obtain ⟨r,eq⟩ := dropAdd_exists cin xs dst pad carry hn hx hd hc s f hval hc0
  have nd : (cin::xs++dst++carry).Nodup := knd hn (fun q => by
    simp only [List.count_cons,List.count_append]; omega)
  have dc := mappedDiagAdd_correct cin xs dst carry nd (by omega) hd hc s r hc0 hi0
  change u=run (mappedDiagAdd xs dst carry cin) r s at eq
  rw [←eq] at dc
  have away (q : Wire) (hq : q∈cin::xs++pad++carry) : q∉dst :=
    kdis hn (fun q => by simp only [List.count_cons,List.count_append]; omega) q hq
  have src : regValue xs u.basis=regValue xs s.basis :=
    regValue_congr _ _ _ (fun q hq => dc.2.2 q (away q (by simp [hq])))
  have raw : regValue dst u.basis=(regValue xs u.basis)^2+signedDiagValue (regValue xs u.basis) xs.length := by
    rw [dc.2.1,hval,src,hd]
    exact Nat.mod_eq_of_lt (DiagSq.rawValue_bound xs s.basis (by omega))
  have pad0 : regValue pad u.basis=0 := by
    rw [←hp0]; exact regValue_congr _ _ _ (fun q hq => dc.2.2 q (away q (by simp [hq])))
  have car0 : regValue carry u.basis=0 := by
    rw [←hc0]; exact regValue_congr _ _ _ (fun q hq => dc.2.2 q (away q (by simp [hq])))
  have rc := DiagSq.rawClear_correct xs dst pad carry (List.nodup_cons.mp hn).2 hx hd hp (by omega)
    u g raw pad0 car0
  simp only [clear,run_append]
  change (run (DiagSq.rawClear xs dst pad carry) g u).phase=s.phase ∧ _
  exact ⟨rc.1.trans dc.1,rc.2.1,fun q hq => (rc.2.2 q hq).trans (dc.2.2 q hq)⟩

theorem sublist (xs dst pad carry : List Wire) (cin : Wire) :
    (make xs dst pad carry cin).Sublist (TrimSquare.tsq2 xs dst pad carry cin) ∧
    (clear xs dst pad carry cin).Sublist (TrimSquare.tsqc2 xs dst pad carry cin) := by
  have h := SquareHead.rows_sublist xs dst pad carry
  constructor
  · exact (h.1.append (List.Sublist.refl _)).append (List.Sublist.refl _)
  · simpa only [clear,DiagSq.rawClear,TrimSquare.tsqc2,List.append_assoc] using
      (List.Sublist.refl (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)).append
        ((List.Sublist.refl (signedSquareTop xs dst)).append h.2)

theorem counts (xs dst pad carry : List Wire) (cin : Wire) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    (toffoliCount (make xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3 ∧
      measurementCount (make xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-2) ∧
    (toffoliCount (clear xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-3 ∧
      measurementCount (clear xs dst pad carry cin)=signedSquareRowsCount xs.length+dst.length-2) := by
  have t := SquareHead.rows_toffoli xs dst pad carry hx hd hp (by omega)
  have m := SquareHead.rows_measurements xs dst pad carry
  have old := TrimSquare.tsq2_counts xs dst pad carry cin hx hd hp hc
  simp only [make,clear,DiagSq.rawMake,DiagSq.rawClear,TrimSquare.tsq2,TrimSquare.tsqc2,
    toffoliCount_append,measurementCount_append] at *
  omega

theorem support (xs dst pad carry : List Wire) (cin : Wire) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    wires (make xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset ∧
    wires (clear xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
  have old := TrimSquare.tsq2_wires_subset xs dst pad carry cin hd hp hc
  exact ⟨(SquareHead.wires_sublist (sublist xs dst pad carry cin).1).trans old.1,
    (SquareHead.wires_sublist (sublist xs dst pad carry cin).2).trans old.2⟩

theorem physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) :
    GatePhysical (make xs dst pad carry cin) ∧ GatePhysical (clear xs dst pad carry cin) := by
  have old := TrimSquare.tsq2_physical xs dst pad carry cin hn
  exact ⟨fun i hi => old.1 i ((sublist xs dst pad carry cin).1.subset hi),
    fun i hi => old.2 i ((sublist xs dst pad carry cin).2.subset hi)⟩

theorem slots (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (make xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 ∧
    Challenge.gateSlots (clear xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 := by
  have old := TrimSquare.tsq2_gateSlots_le xs dst pad carry cin
  exact ⟨(SquareHead.slots_sublist (sublist xs dst pad carry cin).1).trans old.1,
    (SquareHead.slots_sublist (sublist xs dst pad carry cin).2).trans old.2⟩

theorem sq_make (cin : Wire) (xs dst pad carry z : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqMake xs dst [] pad carry z cin (make xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := make_correct cin xs dst pad carry hn hx hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,trivial,fun q h _ => r.2.2 q h⟩

theorem sq_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (clear xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := clear_correct cin xs dst pad carry hn hx hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩

end ECDSAAdd.Entrant.NormalHead

end SquareNormalFirstRows

section SquareNormalOperators
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)
def norm_m2 : Program := NormalHead.make R.hi R.dhi R.pad R.carry R.cin
def norm_c2 : Program := NormalHead.clear R.hi R.dhi R.pad R.carry R.cin
def norm_m5 : Program := NormalHead.make R.S R.T R.pad R.carry R.cin
def norm_c5 : Program := NormalHead.clear R.S R.T R.pad R.carry R.cin

theorem norm_region (xs dst : List Wire)
    (hx : ∀q∈xs,q∈R.bank ∨ q∈R.S) (hd : ∀q∈dst,q∈R.dst ∨ q∈R.T) :
    (xs++dst++R.pad++R.carry++[R.cin]).toFinset⊆R.all.toFinset := by
  intro q hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
  apply List.mem_toFinset.mpr
  simp only [all,List.mem_cons,List.mem_append,or_assoc]
  rcases hq with h|h|h|h|h
  · have a := hx q h; tauto
  · have a := hd q h; tauto
  · tauto
  · tauto
  · tauto

theorem norm_piece_support (w : R.W) :
    wires R.smk⊆R.all.toFinset ∧ wires R.scl⊆R.all.toFinset ∧
    wires (R.m6++R.m7++R.m8)⊆R.all.toFinset ∧ wires (R.c8++R.c7++R.c6)⊆R.all.toFinset ∧
    wires R.norm_m2⊆R.all.toFinset ∧ wires R.norm_c2⊆R.all.toFinset ∧
    wires R.norm_m5⊆R.all.toFinset ∧ wires R.norm_c5⊆R.all.toFinset := by
  have old := R.piece_support w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hSl := w.S; have hTl := w.T; have hc := w.carry
  have a := NormalHead.support R.hi R.dhi R.pad R.carry R.cin (by omega) w.pad (by omega)
  have b := NormalHead.support R.S R.T R.pad R.carry R.cin w.T w.pad (by omega)
  have ar := R.norm_region R.hi R.dhi (fun q h => Or.inl (List.mem_of_mem_drop h))
    (fun q h => Or.inl (List.mem_of_mem_drop h))
  have br := R.norm_region R.S R.T (fun q h => Or.inr h) (fun q h => Or.inr h)
  exact ⟨old.1,old.2.1,old.2.2.1,old.2.2.2.1,a.1.trans ar,a.2.trans ar,b.1.trans br,b.2.trans br⟩

theorem norm_piece_physical (hn : R.all.Nodup) :
    GatePhysical R.smk ∧ GatePhysical R.scl ∧ GatePhysical (R.m6++R.m7++R.m8) ∧
    GatePhysical (R.c8++R.c7++R.c6) ∧ GatePhysical R.norm_m2 ∧ GatePhysical R.norm_c2 ∧
    GatePhysical R.norm_m5 ∧ GatePhysical R.norm_c5 := by
  have old := R.piece_physical hn
  have a := NormalHead.physical R.hi R.dhi R.pad R.carry R.cin
    (knd hn (fun q => by have h := R.counts q; simp only [all,List.count_cons,List.count_append] at h ⊢; omega))
  have b := NormalHead.physical R.S R.T R.pad R.carry R.cin
    (knd hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega))
  exact ⟨old.1,old.2.1,old.2.2.1,old.2.2.2.1,a.1,a.2,b.1,b.2⟩
end ECDSAAdd.Entrant.KRegs

end SquareNormalOperators

-- DIAGONAL COMPONENT LowK.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
section
namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- Fold-pad tail: untouched by the leaf producer and cleanup, used only for clean-at-rest scratch. -/
def ktmp (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.drop 131

def oregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=64,bank:=L.inputBank.take src.length,dst:=dst,
   S:=((ktmp L).take 66).take (src.length-63),
   T:=(ext.take 132).take (2*(src.length-63)),
   z:=(L.leafCarry.drop 193).take 62,
   pad:=L.leafPad,carry:=L.leafCarry.take 193,cin:=L.core.cin}

def iregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).lo,dst:=(oregs L ext src dst).dlo,
   S:=((ktmp L).drop 66).take 33,T:=(ext.drop 132).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).hi,dst:=(oregs L ext src dst).dhi,
   S:=((ext.drop 198).take 34).take 33,T:=(ext.drop 232).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=33,bank:=(oregs L ext src dst).S,dst:=(oregs L ext src dst).T,
   S:=(ext.drop 198).take 34,T:=(ext.drop 232).take 68,
   z:=(oregs L ext src dst).z.take 31,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

/-- 128-bit leaves: nested split of the low and high halves, cleaned low inner sum. -/
def kgH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=(jregsH L ext src dst).S++(jregsH L ext src dst).T,X5:=[],
   Q1:=DiagSq.makeC (iregs L ext src dst),Q1c:=DiagSq.clearC (iregs L ext src dst),
   Q2:=DiagSq.make (jregsH L ext src dst),Q2c:=DiagSq.clear (jregsH L ext src dst),
   Q5:=(oregs L ext src dst).norm_m5,Q5c:=(oregs L ext src dst).norm_c5,
   I1:=(iregs L ext src dst).invC,I2:=(jregsH L ext src dst).invF,I5:=fun _ _ => True}

/-- 129-bit leaf: nested split of the low half and of the sum square, cleaned low inner sum. -/
def kgS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=[],X5:=(jregsS L ext src dst).S++(jregsS L ext src dst).T,
   Q1:=DiagSq.makeC (iregs L ext src dst),Q1c:=DiagSq.clearC (iregs L ext src dst),
   Q2:=(oregs L ext src dst).norm_m2,Q2c:=(oregs L ext src dst).norm_c2,
   Q5:=DiagSq.make (jregsS L ext src dst),Q5c:=DiagSq.clear (jregsS L ext src dst),
   I1:=(iregs L ext src dst).invC,I2:=fun _ _ => True,I5:=(jregsS L ext src dst).invF}

def kg (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  if src.length=128 then kgH L ext src dst else kgS L ext src dst

theorem ktmp_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (ktmp L).length=123 := by
  simp [ktmp,L.foldPad_length hw]

theorem oregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (oregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem iregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (iregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [iregs,oregs,KRegs.lo,KRegs.dlo,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem jregsH_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : src.length=128) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsH L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsH,oregs,KRegs.hi,KRegs.dhi,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h128] <;> omega

theorem jregsS_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h129 : src.length=129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsS L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsS,oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h129] <;> omega

theorem tmp_count (L : CuccaroStreamedSquareWideLayout) (n : Nat) (q : Wire) :
    (L.inputBank.take n++L.leafPad++L.leafCarry++ktmp L).count q≤
      L.core.work.count q+L.foldPad.count q := by
  have inputBound := (List.take_sublist n L.inputBank).count_le q
  have workSplit := congrArg (List.count q) (List.take_append_drop 129 L.core.work)
  have padSplit := congrArg (List.count q) (List.take_append_drop 1 L.foldPad)
  have tailSplit := congrArg (List.count q) (List.take_append_drop 130 (L.foldPad.drop 1))
  have hdd : (L.foldPad.drop 1).drop 130=L.foldPad.drop 131 := by simp [List.drop_drop]
  rw [hdd] at tailSplit
  simp only [inputBank,leafPad,leafCarry,ktmp,List.count_append] at inputBound workSplit padSplit tailSplit ⊢
  omega

def kbig2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L)++ext

theorem lst_le2 (L : CuccaroStreamedSquareWideLayout) (control : Wire) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (q : Wire) :
    (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L).count q ≤
      (control::L.wires).count q := by
  have a := hs q
  have b := hd q
  have banks := tmp_count L src.length q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_cons,
    List.count_append,List.count_nil] at a banks ⊢
  omega

theorem kbig2_nodup (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (ext : List Wire) (hx : ext.Nodup)
    (hdx : ∀q∈ext,q∉control::L.wires) : (kbig2 L ext control src dst).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have b := List.nodup_iff_count_le_one.mp hx q
  have c := lst_le2 L control src dst hs hd q
  have d := List.nodup_iff_count_le_one.mp hn q
  simp only [kbig2,List.count_append] at c ⊢
  by_cases hq : q∈ext
  · have z : (control::L.wires).count q=0 := List.count_eq_zero.mpr (hdx q hq)
    omega
  · have z : ext.count q=0 := List.count_eq_zero.mpr hq
    omega

theorem ktmp_wires (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q∈ktmp L) : q∈L.wires := by
  have h' : q∈L.foldPad := List.mem_of_mem_drop h
  simp only [foldPad,List.mem_append] at h'
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,List.mem_cons]
  tauto

theorem ext_split4 (ext : List Wire) (a b c : Nat) (q : Wire) :
    ((ext.take 132).take a).count q+((ext.drop 132).take 66).count q+
      (((ext.drop 198).take 34).take b).count q+((ext.drop 232).take c).count q≤ext.count q := by
  have x1 := kcnt_take (ext.take 132) a q
  have x2 := kcnt_take ((ext.drop 198).take 34) b q
  have x3 := kcnt_take (ext.drop 232) c q
  have e1 := kcnt_split ext 132 q
  have e2 := kcnt_split (ext.drop 132) 66 q
  have e3 := kcnt_split (ext.drop 198) 34 q
  have e4 := kcnt_take (ext.drop 132) 66 q
  simp only [List.drop_drop] at e2 e3
  norm_num at e2 e3
  omega

theorem tmp_split2 (L : CuccaroStreamedSquareWideLayout) (a : Nat) (q : Wire) :
    (((ktmp L).take 66).take a).count q+(((ktmp L).drop 66).take 33).count q≤(ktmp L).count q := by
  have x1 := kcnt_take ((ktmp L).take 66) a q
  have x2 := kcnt_take ((ktmp L).drop 66) 33 q
  have e := kcnt_split (ktmp L) 66 q
  omega

theorem carry_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.leafCarry.take 193).count q+((L.leafCarry.drop 193).take 62).count q≤L.leafCarry.count q := by
  have x := kcnt_take (L.leafCarry.drop 193) 62 q
  have e := kcnt_split L.leafCarry 193 q
  omega

end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout




theorem sub_of_count {l l' : List Wire} (h : ∀q,l.count q≤l'.count q) : l.toFinset⊆l'.toFinset := by
  intro q hq
  have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := h q; omega))

section Inst
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hn hs hd hx hdx in
theorem kgH_nodup : (kgH L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c ⊢
    omega)

include hn hs hd hx hdx in
theorem kgS_nodup : (kgS L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c e ⊢
    omega)

theorem kgH_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgH_jall (q : Wire) :
    (jregsH L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,jregsH,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgS,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_jall (q : Wire) :
    (jregsS L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 31 q
  simp only [KG.all,KG.X,kgS,KRegs.all,jregsS,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega

include hw h128 hsmax hlen he in
theorem kgH_spec (h : src.length=128) (hall : (kgH L ext src dst).all.Nodup) : (kgH L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgH_iall L ext src dst)
  have nj : (jregsH L ext src dst).all.Nodup := knd hall (kgH_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have n5 : ((oregs L ext src dst).cin::(oregs L ext src dst).S++(oregs L ext src dst).T++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,(iregs L ext src dst).diag_sq_cl_make wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).diag_sq_cl_clear wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    (jregsH L ext src dst).diag_sq_full_make wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).diag_sq_full_clear wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).invF_local,
    NormalHead.sq_make (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    NormalHead.sq_clear (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain_local⟩

include hw h128 hsmax hlen he in
theorem kgS_spec (h : src.length=129) (hall : (kgS L ext src dst).all.Nodup) : (kgS L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgS_iall L ext src dst)
  have nj : (jregsS L ext src dst).all.Nodup := knd hall (kgS_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have hdl := w.dst
  have n2 : ((oregs L ext src dst).cin::(oregs L ext src dst).hi++(oregs L ext src dst).dhi++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,(iregs L ext src dst).diag_sq_cl_make wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).diag_sq_cl_clear wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    NormalHead.sq_make (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    NormalHead.sq_clear (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain_local,
    (jregsS L ext src dst).diag_sq_full_make wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).diag_sq_full_clear wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).invF_local⟩

end Inst
end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

section Inst3
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (he : 300≤ext.length)

include hw in
theorem oregs_lens (h : 128≤src.length) (h2 : src.length≤129) :
    (oregs L ext src dst).h=64 ∧ (oregs L ext src dst).bank.length=src.length := by
  have sz := L.measured_bank_widths hw
  refine ⟨rfl,?_⟩
  simp only [oregs,List.length_take,sz.1]; omega

include hw h128 hsmax hlen he in
theorem kgH_counts (h : src.length=128) :
    toffoliCount (SumKG.make (kgH L ext src dst))=6582 ∧ measurementCount (SumKG.make (kgH L ext src dst))=6693 ∧
    toffoliCount (SumKG.clear (kgH L ext src dst))=6550 ∧ measurementCount (SumKG.clear (kgH L ext src dst))=6693 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := SumKG.make_counts (kgH L ext src dst) w
  have cl := SumKG.clear_counts (kgH L ext src dst) w
  have i1 := DiagSq.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := DiagSq.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl0_counts wi
  have j1 := DiagSq.make_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have j2 := DiagSq.clear_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have q := NormalHead.counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsH L ext src dst).h=32 := rfl
  simp only [DiagSq.tCost,DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgH L ext src dst).Q1=((raw_kcost 64 32-30)-7) ∧ measurementCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)+32 ∧
      toffoliCount (kgH L ext src dst).Q1c=((raw_kcost 64 32-30)-7) ∧ measurementCount (kgH L ext src dst).Q1c=32+(raw_kcost 64 32-30) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl0)=_; rw [toffoliCount_append,i1.1,ip0.1]; omega
    · show measurementCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl0)=_; rw [measurementCount_append,i1.2,ip0.2]
    · show toffoliCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [measurementCount_append,i2.2,ip.2.1]
  have t2 : toffoliCount (kgH L ext src dst).Q2=((raw_kcost 64 32-30)-7) ∧ measurementCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30) ∧
      toffoliCount (kgH L ext src dst).Q2c=((raw_kcost 64 32-30)-7)-32 ∧ measurementCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30) :=
    ⟨j1.1,j1.2,j2.1,j2.2⟩
  have t5 : toffoliCount (kgH L ext src dst).Q5=(ksq 65-1) ∧ measurementCount (kgH L ext src dst).Q5=ksq 65 ∧
      toffoliCount (kgH L ext src dst).Q5c=(ksq 65-1) ∧ measurementCount (kgH L ext src dst).Q5c=ksq 65 := by
    have e : (oregs L ext src dst).S.length=65 := by omega
    have f : (oregs L ext src dst).T.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (oregs L ext src dst).norm_m5=_; unfold KRegs.norm_m5; rw [q.1.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).norm_m5=_; unfold KRegs.norm_m5; rw [q.1.2,e,f]; rfl
    · show toffoliCount (oregs L ext src dst).norm_c5=_; unfold KRegs.norm_c5; rw [q.2.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).norm_c5=_; unfold KRegs.norm_c5; rw [q.2.2,e,f]; rfl
  have rb : (kgH L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgH L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  exact ⟨mk.1,mk.2,cl.1,cl.2⟩

include hw h128 hsmax hlen he in
theorem kgS_counts (h : src.length=129) :
    toffoliCount (SumKG.make (kgS L ext src dst))=6699 ∧ measurementCount (SumKG.make (kgS L ext src dst))=6811 ∧
    toffoliCount (SumKG.clear (kgS L ext src dst))=6666 ∧ measurementCount (SumKG.clear (kgS L ext src dst))=6811 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := SumKG.make_counts (kgS L ext src dst) w
  have cl := SumKG.clear_counts (kgS L ext src dst) w
  have i1 := DiagSq.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := DiagSq.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl0_counts wi
  have j1 := DiagSq.make_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have j2 := DiagSq.clear_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have q := NormalHead.counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsS L ext src dst).h=33 := rfl
  simp only [DiagSq.tCost,DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgS L ext src dst).Q1=((raw_kcost 64 32-30)-7) ∧ measurementCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)+32 ∧
      toffoliCount (kgS L ext src dst).Q1c=((raw_kcost 64 32-30)-7) ∧ measurementCount (kgS L ext src dst).Q1c=32+(raw_kcost 64 32-30) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl0)=_; rw [toffoliCount_append,i1.1,ip0.1]; omega
    · show measurementCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl0)=_; rw [measurementCount_append,i1.2,ip0.2]
    · show toffoliCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [measurementCount_append,i2.2,ip.2.1]
  have t2 : toffoliCount (kgS L ext src dst).Q2=(ksq 65-1) ∧ measurementCount (kgS L ext src dst).Q2=ksq 65 ∧
      toffoliCount (kgS L ext src dst).Q2c=(ksq 65-1) ∧ measurementCount (kgS L ext src dst).Q2c=ksq 65 := by
    have e : (oregs L ext src dst).hi.length=65 := by omega
    have f : (oregs L ext src dst).dhi.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (oregs L ext src dst).norm_m2=_; unfold KRegs.norm_m2; rw [q.1.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).norm_m2=_; unfold KRegs.norm_m2; rw [q.1.2,e,f]; rfl
    · show toffoliCount (oregs L ext src dst).norm_c2=_; unfold KRegs.norm_c2; rw [q.2.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).norm_c2=_; unfold KRegs.norm_c2; rw [q.2.2,e,f]; rfl
  have t5 : toffoliCount (kgS L ext src dst).Q5=((raw_kcost 66 33-31)-7) ∧ measurementCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31) ∧
      toffoliCount (kgS L ext src dst).Q5c=((raw_kcost 66 33-31)-7)-33 ∧ measurementCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31) :=
    ⟨j1.1,j1.2,j2.1,j2.2⟩
  have rb : (kgS L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgS L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  exact ⟨mk.1,mk.2,cl.1,cl.2⟩

end Inst3
end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

section Inst4
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

theorem kg_R : (kg L ext src dst).R=oregs L ext src dst := by
  unfold kg; split <;> rfl

theorem kg_I1 : (kg L ext src dst).I1=(iregs L ext src dst).invC := by
  unfold kg; split <;> rfl

theorem kg_X (q : Wire) (h : q∈(kg L ext src dst).X) : q∈ext ∨ q∈((ktmp L).drop 66).take 33 := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · rcases List.mem_append.mp h with h|h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take (h : q∈((ext.drop 198).take 34).take 33))))
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 66)))
    · exact absurd h (List.not_mem_nil)
  · rw [kg,if_neg c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · exact absurd h (List.not_mem_nil)
    · rcases List.mem_append.mp h with h|h
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 198).take 34)))
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 68)))

include hn hs hd hx hdx in
theorem kg_nodup : (kg L ext src dst).all.Nodup := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]; exact kgH_nodup L control hn ext src dst hs hd hx hdx
  · rw [kg,if_neg c]; exact kgS_nodup L control hn ext src dst hs hd hx hdx

include hw h128 hsmax hlen he in
theorem kg_spec (hall : (kg L ext src dst).all.Nodup) : (kg L ext src dst).Spec := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at hall ⊢; exact kgH_spec L hw ext src dst h128 hsmax hlen he c hall
  · rw [kg,if_neg c] at hall ⊢; exact kgS_spec L hw ext src dst h128 hsmax hlen he (by omega) hall

def lowkcost2 (n : Nat) : Nat := if n=128 then 6693 else 6811
def lowkcostRefTMake (n : Nat) : Nat := if n=128 then 6582 else 6699
def lowkcostRefTClear (n : Nat) : Nat := if n=128 then 6550 else 6666
def lowkcostTMake (n : Nat) : Nat := if n=128 then 6578 else 6695
def lowkcostTClear (n : Nat) : Nat := if n=128 then 6546 else 6662
def lowkcostTPair (n : Nat) : Nat := lowkcostTMake n+lowkcostTClear n

include hw h128 hsmax hlen he in
theorem kg_counts_ref :
    toffoliCount (SumKG.make (kg L ext src dst))=lowkcostRefTMake src.length ∧
    measurementCount (SumKG.make (kg L ext src dst))=lowkcost2 src.length ∧
    toffoliCount (SumKG.clear (kg L ext src dst))=lowkcostRefTClear src.length ∧
    measurementCount (SumKG.clear (kg L ext src dst))=lowkcost2 src.length := by
  by_cases c : src.length=128
  · simp only [kg,lowkcost2,lowkcostRefTMake,lowkcostRefTClear,if_pos c]; exact kgH_counts L hw ext src dst h128 hsmax hlen he c
  · simp only [kg,lowkcost2,lowkcostRefTMake,lowkcostRefTClear,if_neg c]; exact kgS_counts L hw ext src dst h128 hsmax hlen he (by omega)

include hw h128 hsmax hlen he in
theorem kg_support_ref :
    ECDSAAdd.wires (SumKG.make (kg L ext src dst))⊆(kg L ext src dst).all.toFinset ∧
    ECDSAAdd.wires (SumKG.clear (kg L ext src dst))⊆(kg L ext src dst).all.toFinset := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (oregs L ext src dst).norm_piece_support w
  have ip := (iregs L ext src dst).piece_support wi
  have is := DiagSq.steps_support (iregs L ext src dst) wi
  have isc := (iregs L ext src dst).scl0_support wi
  have tr {P : Program} {A B : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : A⊆B) : ECDSAAdd.wires P⊆B := h1.trans h2
  have ap {P Q : Program} {A : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : ECDSAAdd.wires Q⊆A) :
      ECDSAAdd.wires (P++Q)⊆A := by rw [wires_append]; exact Finset.union_subset h1 h2
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have js := DiagSq.steps_support (jregsH L ext src dst) wj
    have iK := sub_of_count (kgH_iall L ext src dst)
    have jK := sub_of_count (kgH_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgH L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact SumKG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr js.1 jK) (tr js.2 jK) (tr rp.2.2.2.2.2.2.1 rK) (tr rp.2.2.2.2.2.2.2 rK)
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have js := DiagSq.steps_support (jregsS L ext src dst) wj
    have iK := sub_of_count (kgS_iall L ext src dst)
    have jK := sub_of_count (kgS_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgS L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact SumKG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr rp.2.2.2.2.1 rK) (tr rp.2.2.2.2.2.1 rK) (tr js.1 jK) (tr js.2 jK)

include hw h128 hsmax hlen he in
theorem kg_physical_ref (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (SumKG.make (kg L ext src dst)) ∧ GatePhysical (SumKG.clear (kg L ext src dst)) := by
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  by_cases h : src.length=128
  · rw [kg,if_pos h] at hall ⊢
    have wj := jregsH_W L hw ext src dst h hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgH_iall L ext src dst)
    have nj := knd hall (kgH_jall L ext src dst)
    have rp := (oregs L ext src dst).norm_piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := DiagSq.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl0_physical wi ni
    have js := DiagSq.steps_physical (jregsH L ext src dst) wj nj
    exact SumKG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) js.1 js.2 rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2
  · rw [kg,if_neg h] at hall ⊢
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgS_iall L ext src dst)
    have nj := knd hall (kgS_jall L ext src dst)
    have rp := (oregs L ext src dst).norm_piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := DiagSq.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl0_physical wi ni
    have js := DiagSq.steps_physical (jregsS L ext src dst) wj nj
    exact SumKG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) rp.2.2.2.2.1 rp.2.2.2.2.2.1 js.1 js.2

include hw h128 hsmax hlen he in
theorem kg_slots_ref :
    Challenge.gateSlots (SumKG.make (kg L ext src dst))+Challenge.gateSlots (SumKG.clear (kg L ext src dst))≤1200000 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have ol := oregs_lens L hw ext src dst h128 hsmax
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T
  have ad := (oregs L ext src dst).adder_slots w rfl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have it := DiagSq.tiny_slots (iregs L ext src dst) wi (by rw [il,ih]) (by rw [ih]; omega)
  have oldit := (iregs L ext src dst).tiny_slots wi (by rw [ih]; omega) (by rw [il,ih]; omega) (by omega)
  have isb := (iregs L ext src dst).make_sub_slots wi
  have isc := (iregs L ext src dst).scl0_slots
  have g2 := NormalHead.slots (oregs L ext src dst).hi (oregs L ext src dst).dhi
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5 := NormalHead.slots (oregs L ext src dst).S (oregs L ext src dst).T
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have x2 : (oregs L ext src dst).hi.length*(12*((oregs L ext src dst).hi.length+1)+6*(oregs L ext src dst).dhi.length) ≤ 65*(12*66+6*130) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : (oregs L ext src dst).S.length*(12*((oregs L ext src dst).S.length+1)+6*(oregs L ext src dst).T.length) ≤ 66*(12*67+6*132) :=
    Nat.mul_le_mul (by omega) (by omega)
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
    have jh : (jregsH L ext src dst).h=32 := rfl
    have jt := DiagSq.tiny_slots (jregsH L ext src dst) wj (by rw [jl,jh]) (by omega)
    have st := SumKG.steps_slots2 (kgH L ext src dst)
    simp only [kgH,DiagSq.makeC,DiagSq.clearC,KRegs.norm_m5,KRegs.norm_c5,Challenge.gateSlots_append] at st ad ⊢
    omega
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
    have jh : (jregsS L ext src dst).h=33 := rfl
    have jt := DiagSq.tiny_slots (jregsS L ext src dst) wj (by rw [jl,jh]) (by omega)
    have st := SumKG.steps_slots2 (kgS L ext src dst)
    simp only [kgS,DiagSq.makeC,DiagSq.clearC,KRegs.norm_m2,KRegs.norm_c2,Challenge.gateSlots_append] at st ad ⊢
    omega

include hw h128 hsmax hlen he in
theorem kg_counts :
    toffoliCount (SquareBundle.makeKG (kg L ext src dst))=lowkcostTMake src.length ∧
    measurementCount (SquareBundle.makeKG (kg L ext src dst))=lowkcost2 src.length ∧
    toffoliCount (SquareBundle.clearKG (kg L ext src dst))=lowkcostTClear src.length ∧
    measurementCount (SquareBundle.clearKG (kg L ext src dst))=lowkcost2 src.length := by
  have old := kg_counts_ref L hw ext src dst h128 hsmax hlen he
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wk : (kg L ext src dst).R.W := by rw [kg_R L ext src dst]; exact w
  have a := SquareBundle.makeKG_counts (kg L ext src dst) wk
  have b := SquareBundle.clearKG_counts (kg L ext src dst) wk
  by_cases h : src.length=128 <;>
    simp [lowkcostRefTMake,lowkcostRefTClear,lowkcostTMake,lowkcostTClear,lowkcost2,h] at old ⊢ <;> omega

include hw h128 hsmax hlen he in
theorem kg_support :
    wires (SquareBundle.makeKG (kg L ext src dst))⊆(kg L ext src dst).all.toFinset ∧
    wires (SquareBundle.clearKG (kg L ext src dst))⊆(kg L ext src dst).all.toFinset := by
  have old := kg_support_ref L hw ext src dst h128 hsmax hlen he
  exact ⟨(SquareBundle.makeKG_support _).trans old.1,(SquareBundle.clearKG_support _).trans old.2⟩

include hw h128 hsmax hlen he in
theorem kg_physical (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (SquareBundle.makeKG (kg L ext src dst)) ∧ GatePhysical (SquareBundle.clearKG (kg L ext src dst)) := by
  have old := kg_physical_ref L hw ext src dst h128 hsmax hlen he hall
  exact ⟨SquareBundle.makeKG_physical _ hall old.1,SquareBundle.clearKG_physical _ hall old.2⟩

include hw h128 hsmax hlen he in
theorem kg_slots :
    Challenge.gateSlots (SquareBundle.makeKG (kg L ext src dst))+
      Challenge.gateSlots (SquareBundle.clearKG (kg L ext src dst))≤1200000 := by
  have old := kg_slots_ref L hw ext src dst h128 hsmax hlen he
  have a := SquareBundle.makeKG_slots (kg L ext src dst)
  have b := SquareBundle.clearKG_slots (kg L ext src dst)
  omega

end Inst4
end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def withLowK2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body : Program) : Program :=
  copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.makeKG (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.clearKG (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)

private theorem diag3_k2_xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem withLowK2_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (withLowK2 L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2 L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2 L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := kg_R L ext src dst
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(oregs L ext src dst).S,q∈ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(kg L ext src dst).X,q∈ext ∨ q∈ktmp L := fun q h =>
    (kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈ktmp L,q∉L.core.out := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈ktmp L,q∉dst := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈ktmp L,q∉src := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈ktmp L,q∉ext := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉ktmp L) :
      q∉(oregs L ext src dst).dst ∧ q∉(oregs L ext src dst).T ∧ q∉(kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  let P := if s.basis control then regValue src s.basis else 0
  obtain ⟨a6,r7,e7⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.makeKG (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.clearKG (kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) records s
  obtain ⟨a5,r6,e6⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.makeKG (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)) (SquareBundle.clearKG (kg L ext src dst)) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.makeKG (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++body)
    (copyRegister (some control) src (L.inputBank.take src.length)) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.makeKG (kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)) body a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.makeKG (kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)) (SquareBundle.makeKG (kg L ext src dst)) a2 s
  rw [show withLowK2 L ext control src dst body=copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.makeKG (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++body++copyRegister (some control) src (L.inputBank.take src.length)++(SquareBundle.clearKG (kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length) from rfl,e7,e6,e5,e4,e3,e2]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := SquareBundle.makeKG_correct (kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have i1 := mk.2.2.2.2.1
  rw [kg_I1] at i1
  rw [hKR] at mk
  generalize run (SquareBundle.makeKG (kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(oregs L ext src dst).dst → q∉(oregs L ext src dst).T → q∉(kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈ktmp L
    · by_cases hX : q∈(kg L ext src dst).X
      · have hI : q∈((ktmp L).drop 66).take 33 := (kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- erase
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask u1 r3 (by
    rw [bank1,ctl1,src1])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r3 u1=u2 at ep1 ef1 ev1 ⊢
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev1 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · exact (ef1 q hb).trans ((u1z q hq hx).trans (u0s q hb))
  have u2ext : ∀q∈ext,u2.basis q=u1.basis q := fun q h => ef1 q (extB q h)
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact ef1 q (fun h => bD q h hq)
  have cb := callback u2' r4 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r4 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r4 u2'=v' at cb loc
  generalize hv : run body r4 u2=v at loc ⊢
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r4 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r4 u2 q hb,run_preserves_outside body r4 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply diag3_k2_xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  -- second copy
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB v r5
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r5 v=w0 at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := by
    rw [cv2,show regValue (L.inputBank.take src.length) v.basis=0 from (regValue_congr _ _ _ vB).trans banks.1,Nat.zero_xor]
    change (if v.basis control then regValue src v.basis else 0)=P
    rw [show v.basis control=s.basis control from (vFrame _ ctlO).trans (u2s _ ctlD ctlE),regValue_congr _ _ _ vSrc]
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    rw [cf2 q hb,vFrame q ho]
    by_cases hx : q∈ext
    · exact u2ext q hx
    · exact ef1 q hb
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (oregs L ext src dst).lo w0.basis=regValue (oregs L ext src dst).lo u0.basis ∧
      regValue (oregs L ext src dst).hi w0.basis=regValue (oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := SquareBundle.clearKG_correct (kg L ext src dst) sp hall w0 r6
    (by
      rw [hKR,show regValue (oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (oregs L ext src dst).dst w0.basis=regValue (oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  rw [hKR] at cl
  generalize run (SquareBundle.clearKG (kg L ext src dst)) r6 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2 q (srcB q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2 _ ctlB).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r7 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r7 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (cp2.trans (vPhase.trans (ep1.trans (mk.1.trans cp1))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2 q (fun h => bOut q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX,cf2 q hb,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx

end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem kg_cnt (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
    (q : Wire) : (kg L ext src dst).all.count q≤(kbig2 L ext control src dst).count q := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have d := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b d ⊢
    omega
  · rw [kg,if_neg c]
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have d := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b d e ⊢
    omega

theorem withLowK2_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (withLowK2 L ext control src dst body)=
      2*src.length+lowkcostTPair src.length+toffoliCount body ∧
    measurementCount (withLowK2 L ext control src dst body)=
      2*src.length+2*lowkcost2 src.length+measurementCount body := by
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have copy := copyRegister_counts (some control) src (L.inputBank.take src.length) inputLen.symm
  have erase := eraseMask_counts control src (L.inputBank.take src.length) inputLen.symm
  have k := kg_counts L hw ext src dst h128 hsmax hd he
  simp only [withLowK2,toffoliCount_append,measurementCount_append,copy.1,copy.2,erase.1,erase.2,
    k.1,k.2.1,k.2.2.1,k.2.2.2,lowkcostTPair,inputLen,Option.isSome_some,if_true]
  constructor <;> omega

theorem withLowK2_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) (hb : ECDSAAdd.wires body⊆(control::L.wires).toFinset) :
    ECDSAAdd.wires (withLowK2 L ext control src dst body)⊆(control::L.wires++ext).toFinset := by
  have st := kg_support L hw ext src dst h128 hsmax hlen he
  have kin : (kg L ext src dst).all.toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq
    have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
    have b := kg_cnt L ext control src dst q
    have c := lst_le2 L control src dst hs hd q
    simp only [kbig2,List.count_append] at b c
    apply List.mem_toFinset.mpr
    simp only [List.mem_append]
    by_cases hx : q∈ext
    · exact Or.inr hx
    · have z : ext.count q=0 := List.count_eq_zero.mpr hx
      exact Or.inl (List.count_pos_iff.mp (by omega))
  have cin : ∀q∈control::src++L.inputBank.take src.length,q∈control::L.wires := by
    intro q h
    have a := List.count_pos_iff.mpr h
    have c := lst_le L control src dst hs hd q
    simp only [List.count_cons,List.count_append] at a c
    exact List.count_pos_iff.mp (by simp only [List.count_cons] at *; omega)
  have cp : ECDSAAdd.wires (copyRegister (some control) src (L.inputBank.take src.length))⊆
      (control::L.wires++ext).toFinset := by
    intro q hq
    have h := copyRegister_wires_subset (some control) src (L.inputBank.take src.length) hq
    simp only [List.mem_toFinset,Option.toList_some,List.singleton_append] at h
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl (cin q (by simpa using h))
  have er : ECDSAAdd.wires (eraseMask control src (L.inputBank.take src.length))⊆
      (control::L.wires++ext).toFinset := by
    intro q hq
    have h := eraseMask_wires_subset control src (L.inputBank.take src.length) hq
    simp only [List.mem_toFinset] at h
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl (cin q (by simpa using h))
  have bd : ECDSAAdd.wires body⊆(control::L.wires++ext).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (hb hq)
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl h
  simp only [withLowK2,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨cp,st.1.trans kin⟩,er⟩,bd⟩,cp⟩,st.2.trans kin⟩,er⟩

theorem withLowK2_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hb : GatePhysical body) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hall := kg_nodup L control hn ext src dst hs hd hx hdx
  have st := kg_physical L hw ext src dst h128 hsmax hlen he hall
  have ndCopy : (src++L.inputBank.take src.length).Nodup :=
    knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉L.inputBank.take src.length := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e
    exact kdis hbig (r:=[c]) (fun q => by
      simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) c (by simp)
  have cp := copyRegister_physical (some control) src (L.inputBank.take src.length) ndCopy hcB
  have er := eraseMask_physical control src (L.inputBank.take src.length)
  simp only [withLowK2,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨cp,st.1⟩,er⟩,hb⟩,cp⟩,st.2⟩,er⟩

theorem withLowK2_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤1620000+Challenge.gateSlots body := by
  have sizes := L.measured_bank_widths hw
  have st := kg_slots L hw ext src dst h128 hsmax hlen he
  have hcopy := Nat.min_le_right src.length (L.inputBank.take src.length).length
  have hl : (L.inputBank.take src.length).length ≤ 129 := by simp [sizes.1]
  simp only [withLowK2,Challenge.gateSlots_append,Baselines.copyRegister_gateSlots,Baselines.eraseMask_gateSlots]
  omega

end ECDSAAdd.Entrant.OwnDiagLowK

end



-- DIAGONAL COMPONENT All12Primitive.lean

section
-- ===== SquareAccK =====

/-! The accumulated streamed square with all three leaves computed by one
Karatsuba level (`withLowK`), the sum and cross registers borrowed from `ext`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

structure ExtOK (L : CuccaroStreamedSquareWideLayout) (control : Wire) (ext : List Wire) : Prop where
  nodup : ext.Nodup
  away : ∀q∈ext,q∉control::L.wires
  len : 300≤ext.length

theorem ext_out (L : CuccaroStreamedSquareWideLayout) (control : Wire) (ext : List Wire)
    (he : ExtOK L control ext) (q : Wire) (hq : q∈ext) : q∉L.core.out := fun h =>
  he.away q hq (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])

theorem sum_in (L : CuccaroStreamedSquareWideLayout) (control : Wire) (q : Wire) (h : q∈L.core.sum) :
    q∈control::L.wires := by
  simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h
  · simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
      List.mem_of_mem_drop (List.mem_of_mem_take h)]
  · simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]

theorem withMixedK_contribution (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (orientation : Bool) (items : List MixItem)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (O P V : Nat) (hO : O<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O)
    (hp : P=(if s.basis control then regValue src s.basis else 0)^2)
    (whole : ∀t : BasisState,regValue dst t=P → (∀q,q∉dst → t q=s.basis q) → regValue L.core.product t=P)
    (views : ∀t : BasisState,regValue L.core.product t=P → ∀i∈items,MixView L t i)
    (delta : ZMod SquareReduction.p)
    (payload : ∀t : BasisState,regValue L.core.product t=P → mixSignedSum t items=delta)
    (hV : V<SquareReduction.p)
    (target : measuredOrientationCast (mixFinal orientation items) V=
      measuredOrientationCast orientation O+delta)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) (hst : ∀i∈items,MixStatic L i) :
    (run (OwnDiagLowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).phase=s.phase ∧
    regValue L.core.out (run (OwnDiagLowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (OwnDiagLowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (mixFoldsQ L orientation items) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (mixFoldsQ_support L hw nd control orientation items hst hw'))
  apply OwnDiagLowK.withLowK2_correct L hw control hn src dst hs hd hs2 hsmax hlen ext he.nodup he.away he.len
    (mixFoldsQ L orientation items) hbody s records hc hzero hz V
  intro t m dstValue same
  have pv : regValue L.core.product t.basis=P := whole t.basis (by simpa [hp] using dstValue) same
  have clean := L.measured_product_frame_clean nd dst hd s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉dst := by
    intro bad
    have dis := L.product_out_disjoint nd
    have pos := List.count_pos_iff.mpr bad
    have bound := hd q
    have product : q∈L.core.product := List.count_pos_iff.mp (by omega)
    exact List.disjoint_left.mp dis product hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have initial : SquareFrame L.core.out t.basis O t.basis := ⟨outO,fun _ _ => rfl⟩
  have folded := mixFoldsQ_frame L hw nd t.basis clean orientation O hO items (views t.basis pv) t m initial
  have cast := mixValue_cast t.basis orientation O items hO
  rw [payload t.basis pv] at cast
  have result : mixValue t.basis orientation O items=V :=
    measuredOrientationCast_injective _ _ _ (mixValue_lt _ _ _ _ hO) hV (cast.trans target.symm)
  exact ⟨folded.1,folded.2.1.trans result,folded.2.2⟩


/-- Branch C forms `high ← high + low` with the measured in-place adder (n-1
Toffolis) instead of the Cuccaro ripple (2n); the clean work register holds
its carries. The sum is removed by the measured in-place subtractor. -/
def sumSrc (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.low++[L.core.pad.getD 0 0]
def sumBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 128
def gPrep (L : CuccaroStreamedSquareWideLayout) : Program :=
  addInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin
def gClear (L : CuccaroStreamedSquareWideLayout) : Program :=
  subInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin


theorem sum_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (sumSrc L).length=129 ∧ L.core.sum.length=129 ∧ (sumBank L).length=128 := by
  refine ⟨?_,L.core.sum_length hw.core,?_⟩
  · simp [sumSrc,L.core.low_length hw.core]
  · simp [sumBank,hw.core.work]

theorem sumPad_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.core.pad.getD 0 0∈L.core.pad := by
  have h : 0<L.core.pad.length := by rw [hw.core.pad]; omega
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem sum_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.core.cin::(sumSrc L++L.core.sum++sumBank L)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hnd q
  have hlo := (List.take_sublist 128 L.core.y).count_le q
  have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
  have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
  have hsplit := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
  have hbit := (List.singleton_sublist.mpr (sumPad_mem L hw)).count_le q
  have hwk := (List.take_sublist 128 L.core.work).count_le q
  simp only [List.count_cons,List.count_nil,Nat.add_zero] at hbit
  simp only [List.count_append] at hsplit
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,sumSrc,sumBank,
    CuccaroStreamedSquareLayout.low,CuccaroStreamedSquareLayout.high,
    CuccaroStreamedSquareLayout.sum,List.count_append,List.count_cons,
    List.count_nil] at h ⊢
  omega

theorem sumSrc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (base : BasisState) (A : Nat)
    (hA : regValue L.core.low base=A) (hpad : regValue L.core.pad base=0) :
    regValue (sumSrc L) base=A := by
  have bit0 : base (L.core.pad.getD 0 0)=false :=
    (regValue_zero _ _).mp hpad _ (sumPad_mem L hw)
  rw [sumSrc,regValue_append,hA]
  have hz : regValue [L.core.pad.getD 0 0] base=0 := by
    change (if base (L.core.pad.getD 0 0) then 1 else 0)=0
    rw [bit0]
    rfl
  rw [hz,Nat.mul_zero,Nat.add_zero]

theorem sumBank_zero (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (hwork : regValue L.core.work base=0) : regValue (sumBank L) base=0 :=
  (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hwork q (List.mem_of_mem_take hq))

theorem gPrep_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) (hwork : regValue L.core.work base=0) :
    Triple (SquareFrame L.core.sum base B) (gPrep L)
      (SquareFrame L.core.sum base (A+B)) := by
  have lens := sum_lengths L hw
  have add := addInPlace_cin_frame L.core.cin (sumSrc L) L.core.sum (sumBank L)
    (sum_nodup L hw hnd) (lens.1.trans lens.2.1.symm) (by rw [lens.2.2,lens.2.1]) base false hcin
    (sumBank_zero L base hwork) B
  have val : (B+regValue (sumSrc L) base+false.toNat)%2^L.core.sum.length=A+B := by
    rw [sumSrc_value L hw base A hA hpad,lens.2.1]
    simp only [Bool.toNat_false,Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega),Nat.add_comm]
  rw [val] at add
  exact add

theorem gClear_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) (hwork : regValue L.core.work base=0) :
    Triple (SquareFrame L.core.sum base (A+B)) (gClear L)
      (SquareFrame L.core.sum base B) := by
  have lens := sum_lengths L hw
  have nd := sum_nodup L hw hnd
  have dis (w : Wire) (hw' : w∈L.core.cin::(sumSrc L++sumBank L)) : w∉L.core.sum := by
    intro hdw
    have hn := List.nodup_iff_count.mp nd w
    have h1 := List.count_pos_iff.mpr hw'
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  intro s m h
  unfold gClear
  have sv : regValue (sumSrc L) s.basis=A :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans
      (sumSrc_value L hw base A hA hpad)
  have kv : regValue (sumBank L) s.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans (sumBank_zero L base hwork)
  have cv : s.basis L.core.cin=false := (h.2 _ (dis _ (by simp))).trans hcin
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have spec := subInPlace_spec (sumSrc L) L.core.sum (sumBank L) L.core.cin nd hx hc A (A+B) s m
    ⟨⟨⟨sv,h.1⟩,cv⟩,kv⟩
  have hv : regValue L.core.sum (run (subInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin) m s).basis=
      (A+B+2^L.core.sum.length-A)%2^L.core.sum.length := spec.2.1.1.2
  refine ⟨spec.1,?_,?_⟩
  · rw [hv,lens.2.1,show A+B+2^129-A=B+2^129 by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · intro w hw'
    exact (subInPlace_frame (sumSrc L) L.core.sum (sumBank L) L.core.cin nd hx hc s m cv kv w hw').trans
      (h.2 w hw')

theorem gSum_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (toffoliCount (gPrep L)=128 ∧ measurementCount (gPrep L)=128) ∧
    (toffoliCount (gClear L)=128 ∧ measurementCount (gClear L)=128) := by
  have lens := sum_lengths L hw
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have a := addInPlace_counts (sumSrc L) L.core.sum (sumBank L) L.core.cin hx hc
  have b := subInPlace_counts (sumSrc L) L.core.sum (sumBank L) L.core.cin hx hc
  rw [lens.2.1] at a b
  exact ⟨a,b⟩

theorem gSum_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    ECDSAAdd.wires (gPrep L)⊆(control::L.wires).toFinset ∧
    ECDSAAdd.wires (gClear L)⊆(control::L.wires).toFinset := by
  have lens := sum_lengths L hw
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have sub : (L.core.cin::(sumSrc L++L.core.sum++sumBank L)).toFinset⊆(control::L.wires).toFinset := by
    intro q hq
    have pad := sumPad_mem L hw
    have inW : q∈L.wires → q∈(control::L.wires).toFinset := fun h => by simp [h]
    apply inW
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,
      sumSrc,sumBank,CuccaroStreamedSquareLayout.sum] at hq
    rcases hq with h|h|h|h|h|h
    · subst h; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
    · have hy : q∈L.core.y := List.mem_of_mem_take h
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hy]
    · subst h
      simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,
        pad,true_or,or_true]
    · have hy : q∈L.core.y := List.mem_of_mem_drop (List.mem_of_mem_take h)
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hy]
    · subst h; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
    · have hk : q∈L.core.work := List.mem_of_mem_take h
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hk]
  exact ⟨(addInPlace_wires _ _ _ _ hx hc).trans_subset sub,(subInPlace_wires _ _ _ _ hx hc).trans_subset sub⟩

theorem gSum_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    GatePhysical (gPrep L) ∧ GatePhysical (gClear L) := by
  have nd := sum_nodup L hw hnd
  exact ⟨addInPlace_physical _ _ _ _ nd,subInPlace_physical _ _ _ _ nd⟩

theorem gSum_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (gPrep L)≤12*129 ∧ Challenge.gateSlots (gClear L)≤12*129+2*129 := by
  have lens := sum_lengths L hw
  have a := Baselines.addInPlace_gateSlots_le (sumSrc L) L.core.sum (sumBank L) L.core.cin
  have b := Baselines.subInPlace_gateSlots_le (sumSrc L) L.core.sum (sumBank L) L.core.cin
  rw [lens.1] at a b
  rw [lens.2.1] at b
  exact ⟨a,b⟩



/-- Fold schedules ordered so the output orientation flips as often as possible;
every flip uses the comparison-free reflected core of `QFold`. -/
def accAMixQ (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (rot128F L),.inl (negP L),.inr ⟨false,[],earlyHTerms (L.core.product.drop 128),earlyHTerms (L.core.product.drop 128)⟩]
def accBMixQ (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negP L),.inl (rot128F L),.inl (rotC L true 4),.inl (rotC L false 6),
    .inl (rotC L true 10),.inr ⟨false,preW L,termsB L,sortedItems false (accBRaw L)⟩,.inl (rotC L true 32)]

theorem accAMixQ_mem (L : CuccaroStreamedSquareWideLayout) (i : MixItem) (h : i∈accAMixQ L) : i∈accAMix L := by
  simp only [accAMixQ,accAMix,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; tauto
theorem accBMixQ_mem (L : CuccaroStreamedSquareWideLayout) (i : MixItem) (h : i∈accBMixQ L) : i∈accBMix L := by
  simp only [accBMixQ,accBMix,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; tauto
theorem accAMixQ_sum (L : CuccaroStreamedSquareWideLayout) (t : BasisState) :
    mixSignedSum t (accAMixQ L)=mixSignedSum t (accAMix L) := by
  simp only [accAMixQ,accAMix,mixSignedSum]; ring
theorem accBMixQ_sum (L : CuccaroStreamedSquareWideLayout) (t : BasisState) :
    mixSignedSum t (accBMixQ L)=mixSignedSum t (accBMix L) := by
  simp only [accBMixQ,accBMix,mixSignedSum]; ring
theorem accQ_orientations (L : CuccaroStreamedSquareWideLayout) :
    mixFinal true (accAMixQ L)=false ∧ mixFinal false (accBMixQ L)=true ∧
    mixFinal false (accCMix L)=true := by
  simp [mixFinal,mixNeg,accAMixQ,accBMixQ,accCMix,rot128F,negP,negRot,rotC]
theorem accQ_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈accAMixQ L,MixStatic L i) ∧ (∀i∈accBMixQ L,MixStatic L i) :=
  ⟨fun i hi => (acc_static L hw).1 i (accAMixQ_mem L i hi),
    fun i hi => (acc_static L hw).2.1 i (accBMixQ_mem L i hi)⟩
theorem accQ_item_prices (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (mixFoldsQT true (accAMixQ L)=3089 ∧ mixFoldsQM true (accAMixQ L)=3092) ∧
    (mixFoldsQT false (accBMixQ L)=6853 ∧ mixFoldsQM false (accBMixQ L)=6860) ∧
    (mixFoldsQT false (accCMix L)=2646 ∧ mixFoldsQM false (accCMix L)=2647) := by
  norm_num [mixFoldsQT,mixFoldsQM,mixNeg,accAMixQ,accBMixQ,accCMix,rot128F,negP,negRot,rotF,rotC,posTop,
    accARaw,accBRaw,accCRaw,sortedItems,nafMinusOneItems,List.filter_cons,Acc.buildT,Acc.sbuildTNN,Acc.HCase,Acc.hTerms,Acc.sbuildTN,Acc.sbuildT,Acc.WordCase,Acc.wordTerms,topSlice,List.drop_drop,preW,termsB,
    accPrice,accPriceQ,earlyHTerms,Acc.earlyTerm,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,hw.core.product,hiReg]
  all_goals (try rw [if_neg (List.cons_ne_nil _ _)])
  all_goals norm_num

def resAQ (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast true O+((P : ZMod SquareReduction.p)*2^128-P))
def resBQ (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P))

theorem acbQ_complete_exact (enabled : Bool) (A B O : Nat) :
    resBQ ((if enabled then B else 0)^2)
      (resAQ ((if enabled then A else 0)^2) (resC ((if enabled then A+B else 0)^2) O))=
      SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resC PC O
  let OA := resAQ PA OC
  let OB := resBQ PB OA
  have ec : measuredOrientationCast true OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128) :=
    cast_ofCast _ _
  have ea : measuredOrientationCast false OA=measuredOrientationCast true OC+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  have eb : measuredOrientationCast true OB=measuredOrientationCast false OA+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have obBound : OB<SquareReduction.p := ofCast_lt _ _
  have cast : (OB : ZMod SquareReduction.p)=
      -1-(subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [subModValue_cast]
    linear_combination -eb-ec-ea-identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have hp0 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e : ((SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O : Nat) : ZMod SquareReduction.p)=
      -1-(subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]),Nat.cast_one,hp0]
    ring
  have value := congrArg ZMod.val (cast.trans e.symm)
  have lt2 : SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p := by omega
  simpa only [ZMod.val_natCast_of_lt obBound,ZMod.val_natCast_of_lt lt2] using value

/-! Branch C's accumulator is folded positively. A controlled complement
`acc ← acc XOR g·(2^163-1)` turns the negative item `-acc` into the positive item
`2^163-1-acc` plus the constant `g·(2^163-1)`, so both C items switch orientation
(comparison-free `Q` folds) and the square ends in the plain orientation. The
constant is absorbed by the following `3cx` correction. -/
def cFlipK : Nat := 2^163-1

theorem xorConstant_ones (r : List Wire) : xorConstant r (2^r.length-1)=notRegister r := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    have hp : 0<2^ws.length := Nat.two_pow_pos _
    have e : 2^(ws.length+1)=2*2^ws.length := by rw [Nat.pow_succ]; ring
    have h1 : (2^(ws.length+1)-1)%2=1 := by rw [e]; omega
    have h2 : (2^(ws.length+1)-1)/2=2^ws.length-1 := by rw [e]; omega
    simp only [List.length_cons,xorConstant,h1,if_true,h2,ih,notRegister,List.map_cons]
    rfl

theorem accReg_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : (accReg L).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have e1 : (L.core.work.take 163).count q+(L.core.work.drop 163).count q=L.core.work.count q := by
    rw [←List.count_append,List.take_append_drop]
  simp only [accReg]
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  omega

theorem accReg_in (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈accReg L) : q∈L.wires := by
  have w := accReg_work L q hq
  simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,w]

theorem flip_run (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉accReg L) (s : State) (m : List Bool) :
    (run (maskedConstant g (accReg L) cFlipK) m s).phase=s.phase ∧
    (∀q,q∉accReg L → (run (maskedConstant g (accReg L) cFlipK) m s).basis q=s.basis q) ∧
    regValue (accReg L) (run (maskedConstant g (accReg L) cFlipK) m s).basis=
      (if s.basis g then cFlipK-regValue (accReg L) s.basis else regValue (accReg L) s.basis) := by
  have len := (acc_lengths L hw).1
  have nd := accReg_nodup L hn
  rw [maskedConstant_run g _ _ hg]
  cases hs : s.basis g
  · simp
  · have e : cFlipK=2^(accReg L).length-1 := by rw [len]; rfl
    simp only [if_true]
    rw [e,xorConstant_ones,notRegister_correct _ nd]
    refine ⟨rfl,?_,?_⟩
    · intro q hq; simp [hq]
    · change regValue (accReg L) (fun w => if w∈accReg L then !s.basis w else s.basis w)=_
      rw [regValue_congr (accReg L) _ (fun w => !s.basis w) (by intro w hw; simp [hw]),regValue_complement]

def accFoldQF (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) : Program :=
  fillIn L a++(maskedConstant g (accReg L) cFlipK++(qprog L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) cFlipK++fillOut L a)))

theorem accFoldQF_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQF L g a)
      (SquareFrame L.core.out base (((if base g then cFlipK-Acc.accVal base 0 a.spec else Acc.accVal base 0 a.spec)+
        (SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have hAK : A≤cFlipK := by unfold cFlipK; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQF,run_append,run_append,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprog L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correct L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprog L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq

theorem accFoldQF_counts (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) :
    toffoliCount (accFoldQF L g a)=toffoliCount (accFoldQ L a) ∧
    measurementCount (accFoldQF L g a)=measurementCount (accFoldQ L a) := by
  have k := maskedConstant_counts g (accReg L) cFlipK
  simp only [accFoldQF,accFoldQ,toffoliCount_append,measurementCount_append,k.1,k.2]
  constructor <;> omega

theorem accFoldQF_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFoldQF L g a)⊆(g::L.wires).toFinset := by
  have full := accFoldQ_support L hw hn g a cnt ok cntP okP
  simp only [accFoldQ,wires_append,Finset.union_subset_iff] at full
  have mc : ECDSAAdd.wires (maskedConstant g (accReg L) cFlipK)⊆(g::L.wires).toFinset := by
    refine (maskedConstant_wires_subset _ _ _).trans ?_
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (accReg_in L q h)
  simp only [accFoldQF,wires_append,Finset.union_subset_iff]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩

theorem accFoldQF_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQF L g a) := by
  have full := accFoldQ_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQ,gatePhysical_append] at full
  have mc := maskedConstant_physical g (accReg L) cFlipK (fun h => hg (accReg_in L g h))
  simp only [accFoldQF,gatePhysical_append]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩

theorem accFoldQF_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFoldQF L g a)≤
      2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(67*256+41)+7000+2*163 := by
  have full := accFoldQ_gateSlots L hw a ok okP
  have mc := Baselines.maskedConstant_gateSlots_le g (accReg L) cFlipK
  rw [(acc_lengths L hw).1] at mc
  simp only [accFoldQ,Challenge.gateSlots_append] at full
  simp only [accFoldQF,Challenge.gateSlots_append]
  omega

def accCItem (L : CuccaroStreamedSquareWideLayout) : AccItem :=
  ⟨true,[],earlyHTerms (L.core.product.drop 128)++[posTop L],earlyHTerms (L.core.product.drop 128)++[posTop L]⟩

theorem accCMix_eq (L : CuccaroStreamedSquareWideLayout) : accCMix L=[.inl (negRot L),.inr (accCItem L)] := rfl

/-- Branch C body: `negRot` by the switching fold, then the complemented accumulator, also switching. -/
def bodyC (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  mixFoldsQ L false [.inl (negRot L)]++accFoldQF L g (accCItem L)

theorem bodyC_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈[(.inl (negRot L) : MixItem)],MixStatic L i) ∧ MixStatic L (.inr (accCItem L)) := by
  have st := (acc_static L hw).2.2
  rw [accCMix_eq] at st
  exact ⟨fun i hi => st i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; exact Or.inl hi),
    st _ (by simp)⟩

theorem bodyC_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyC L g)=2390 ∧ measurementCount (bodyC L g)=2392 := by
  have st := bodyC_static L hw
  have nR : (negRot L).negative=true := rfl
  have cR : (negRot L).canonical=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have f := mixFoldsQ_counts L hw false _ st.1
  have f1 : mixFoldsQT false [(.inl (negRot L) : MixItem)]=767 := by simp [mixFoldsQT,mixNeg,nR,cR]
  have f2 : mixFoldsQM false [(.inl (negRot L) : MixItem)]=768 := by simp [mixFoldsQM,mixNeg,nR,cR]
  have q := accFoldQ_counts L hw (accCItem L) st.2.2.1 st.2.2.2.2
  have qf := accFoldQF_counts L g (accCItem L)
  have pr := (accQ_item_prices L hw).2.2
  rw [accCMix_eq] at pr
  simp [mixFoldsQT,mixFoldsQM,mixNeg,nR,cR,nC] at pr
  have rel : accPriceQ (accCItem L)+256=accPrice (accCItem L) := by simp only [accPriceQ,accPrice]; omega
  rw [bodyC]
  simp only [toffoliCount_append,measurementCount_append]
  rw [f.1,f.2,qf.1,qf.2,q.1,q.2,f1,f2]
  constructor <;> omega

theorem bodyC_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (g : Wire) :
    ECDSAAdd.wires (bodyC L g)⊆(g::L.wires).toFinset := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_support L hw hn g false _ st.1
  have b := accFoldQF_support L hw hn g (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyC,wires_append,Finset.union_subset_iff]
  exact ⟨a,b⟩

theorem bodyC_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires) : GatePhysical (bodyC L g) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_physical L hw hn false _ st.1
  have b := accFoldQF_physical L hw hn g hg (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyC,gatePhysical_append]
  exact ⟨a,b⟩

theorem bodyC_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Challenge.gateSlots (bodyC L g)≤2*(41000+2*(20*(14*163))+(67*256+41)) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_gateSlots L hw false _ st.1 20 (by intro i hi a e; simp at hi; subst hi; cases e)
  have b := accFoldQF_gateSlots L hw g (accCItem L) st.2.2.1 st.2.2.2.2
  have lt : (accCItem L).terms.length=5 := by simp [accCItem,earlyHTerms]
  have lp : (accCItem L).pre.length=0 := rfl
  rw [lt,lp] at b
  simp only [List.length_singleton] at a
  simp only [bodyC,Challenge.gateSlots_append]
  omega

/-- C contribution with the complemented accumulator: plain orientation, plus `g·(2^163-1)`. -/
def resCF (g : Bool) (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast false O+(-(P : ZMod SquareReduction.p)*2^128)+
    ((if g then cFlipK else 0 : Nat) : ZMod SquareReduction.p))

theorem accC_zero (L : CuccaroStreamedSquareWideLayout) (t : BasisState) (hp : regValue L.core.product t=0) :
    Acc.accVal t 0 (accCItem L).spec=0 := by
  have z := (regValue_zero _ _).mp hp
  have h128 : regValue (L.core.product.drop 128) t=0 :=
    (regValue_zero _ _).mpr (fun q hq => z q (List.mem_of_mem_drop hq))
  have h256 : regValue (L.core.product.drop 256) t=0 :=
    (regValue_zero _ _).mpr (fun q hq => z q (List.mem_of_mem_drop hq))
  simp [accCItem,Acc.accVal,Acc.step,earlyHTerms,Acc.earlyTerm,posTop,h128,h256]

theorem accMiddleCF_body (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (M O : Nat) (hO : O<SquareReduction.p)
    (t : State) (m : List Bool) (pv : regValue L.core.product t.basis=M^2)
    (hM : t.basis control=false → M=0)
    (clean : L.PairClean t.basis) (outO : regValue L.core.out t.basis=O) :
    (run (bodyC L control) m t).phase=t.phase ∧
    regValue L.core.out (run (bodyC L control) m t).basis=resCF (t.basis control) (M^2) O ∧
    ∀q,q∉L.core.out → (run (bodyC L control) m t).basis q=t.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have gW : control∉L.wires := (List.nodup_cons.mp hn).1
  have views := accC_views L hw t.basis M pv
  rw [accCMix_eq] at views
  have v1 : ∀i∈[(.inl (negRot L) : MixItem)],MixView L t.basis i := fun i hi => views i (by simp at hi ⊢; exact Or.inl hi)
  have va : AccView L t.basis (accCItem L) := views (.inr (accCItem L)) (by simp)
  let mm := measurementCount (mixFoldsQ L false [.inl (negRot L)])
  let r1 := run (mixFoldsQ L false [.inl (negRot L)]) (m.take mm) t
  have e1 := mixFoldsQ_frame L hw nd t.basis clean false O hO [.inl (negRot L)] v1 t (m.take mm) ⟨outO,fun _ _ => rfl⟩
  let O1 := mixValue t.basis false O [.inl (negRot L)]
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have e2 := accFoldQF_frame L hw nd control gW t.basis (accCItem L) va clean O1 hO1 r1 (m.drop mm) e1.2
  rw [bodyC,run_append]
  refine ⟨e2.1.trans e1.1,?_,fun q hq => e2.2.2 q hq⟩
  rw [e2.2.1]
  have nR : (negRot L).negative=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have cast1 := mixValue_cast t.basis false O [.inl (negRot L)] hO
  have sum := (accC_mixSum L hw t.basis).trans (L.measuredC_sum hw t.basis (M^2) pv)
  rw [accCMix_eq] at sum
  simp only [mixFinal,mixNeg,nR,nC,mixSignedSum,mixSignedPayload,mixPayload,↓reduceIte,add_zero] at cast1 sum
  simp only [measuredOrientationCast,↓reduceIte,Bool.false_eq_true] at cast1
  have hA : Acc.accVal t.basis 0 (accCItem L).spec<2^163 := Acc.accVal_lt _ 163 _ 0 (by norm_num) va.specValid
  set A := Acc.accVal t.basis 0 (accCItem L).spec with hAdef
  set O1 := mixValue t.basis false O [.inl (negRot L)] with hO1def
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have hp1 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e3 : ((SquareReduction.p-1-O1 : Nat) : ZMod SquareReduction.p)=-1-(O1 : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one,hp1]; ring
  have target : ((((if t.basis control then cFlipK-A else A)+(SquareReduction.p-1-O1)) : Nat) : ZMod SquareReduction.p)=
      measuredOrientationCast false O+(-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)+
        ((if t.basis control then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := by
    simp only [measuredOrientationCast,Bool.false_eq_true,↓reduceIte]
    cases hg : t.basis control
    · have m0 := hM hg
      have a0 : A=0 := by
        have pz : regValue L.core.product t.basis=0 := by rw [pv,m0]; rfl
        exact accC_zero L t.basis pz
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [Nat.cast_add,e3,a0,Nat.cast_zero]
      rw [a0,Nat.cast_zero] at sum
      linear_combination cast1+sum
    · have hAK : A≤cFlipK := by unfold cFlipK; omega
      simp only [↓reduceIte]
      rw [Nat.cast_add,Nat.cast_sub hAK,e3]
      linear_combination cast1+sum
  unfold resCF ofCast
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←target,ZMod.val_natCast]

def accBranchAK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.low (L.core.product.take 256) (mixFoldsQ L true (accAMixQ L))
def accBranchBK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.high (L.core.product.take 256) (mixFoldsQ L false (accBMixQ L))
def accMiddleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.sum L.core.product (bodyC L control)
def accBranchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  gPrep L++accMiddleCK L ext control++gClear L
def accPrefixK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  accBranchCK L ext control++accBranchBK L ext control++accBranchAK L ext control

theorem accBranchAK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchAK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchAK L ext control) records s).basis=
      resAQ ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchAK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) true (accAMixQ L) s records hc dstZero
    O (M^2) (resAQ (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accA_views L hw t M mb hp i (accAMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accAMixQ_sum L t).trans ((accA_mixSum L hw t).trans (L.measuredA_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).1
  exact result

theorem accBranchBK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchBK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchBK L ext control) records s).basis=
      resBQ ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchBK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) false (accBMixQ L) s records hc dstZero
    O (M^2) (resBQ (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accB_views L hw t M mb hp i (accBMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accBMixQ_sum L t).trans ((accB_mixSum L hw t (M^2) hp pb).trans (L.measuredB_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).2.1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).2
  exact result

theorem accMiddleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accMiddleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accMiddleCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accMiddleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (bodyC L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (bodyC_support L hw nd control hw'))
  apply OwnDiagLowK.withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (bodyC L control) hbody
    s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := accMiddleCF_body L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem accBranchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchCK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := accMiddleCK L ext control
  let mp := measurementCount (gPrep L)
  let rest := records.drop mp
  let u := run (gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (gClear L) (rest.drop (measurementCount middle)) v
  have prep := gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (sum_in L control q bad)))).trans hz
  have used := accMiddleCK_correct L hw ext control hn (A+B) O hO u
    (rest.take (measurementCount middle)) prep.2.1 outU productU cleanU he hzU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have workRestore : regValue L.core.work restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hc.work
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [hq])).2
    simp [restoreBase,away]
  have cleared := gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [accBranchCK,middle,u,v,out,rest,mp,run_append] using final

theorem cbaF_complete_exact (enabled : Bool) (A B O : Nat) :
    resAQ ((if enabled then A else 0)^2)
      (resBQ ((if enabled then B else 0)^2) (resCF enabled ((if enabled then A+B else 0)^2) O))=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  have ec : measuredOrientationCast false OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128)+
      ((if enabled then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := cast_ofCast _ _
  have eb : measuredOrientationCast true OB=measuredOrientationCast false OC+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  have ea : measuredOrientationCast false OA=measuredOrientationCast true OB+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have oaBound : OA<SquareReduction.p := ofCast_lt _ _
  have targetBound : (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p<
      SquareReduction.p := Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have cast : (OA : ZMod SquareReduction.p)=
      (((subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p : Nat) :
        ZMod SquareReduction.p) := by
    rw [ZMod.natCast_mod,Nat.cast_add,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt oaBound,ZMod.val_natCast_of_lt targetBound] using value

theorem accPrefixK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accPrefixK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accPrefixK L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then cFlipK else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accPrefixK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  let restC := records.drop (measurementCount (accBranchCK L ext control))
  let restB := restC.drop (measurementCount (accBranchBK L ext control))
  let u := run (accBranchCK L ext control) (records.take (measurementCount (accBranchCK L ext control))) s
  let v := run (accBranchBK L ext control) (restC.take (measurementCount (accBranchBK L ext control))) u
  let w := run (accBranchAK L ext control) restB v
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ec := accBranchCK_correct L hw ext control hn A B O hO s
    (records.take (measurementCount (accBranchCK L ext control))) rfl sumB sumBound ho hp0 hc he hz
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OC ⟨ec.2.1,ec.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ec.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B := regValue_congr _ _ _ (fun q hq => ec.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ec.2.2 control ctrlAway
  have eb := accBranchBK_correct L hw ext control hn B OC (ofCast_lt _ _) u
    (restC.take (measurementCount (accBranchBK L ext control))) highU ec.2.1 productU cleanU he
    ((regValue_congr _ _ _ (fun q hq => ec.2.2 q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ec.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A :=
    regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ea := accBranchAK_correct L hw ext control hn A OB (ofCast_lt _ _) v restB lowV eb.2.1 productV cleanV he
    ((regValue_congr _ _ _ (fun q hq => sameV q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlV] at ea
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ea.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p := by
    have exactResult := cbaF_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    rw [ea.2.1]
    exact exactResult
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ea.1.trans (eb.1.trans ec.1),fullValue,sameW⟩
  simpa [accPrefixK,u,v,w,restB,restC,enabled,run_append,Nat.add_assoc] using final


theorem accPrefixK_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (he : 300≤ext.length) :
    toffoliCount (accPrefixK L ext control)=2*OwnDiagLowK.lowkcostTPair 128+OwnDiagLowK.lowkcostTPair 129+13358 ∧ measurementCount (accPrefixK L ext control)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13370 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_counts L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := OwnDiagLowK.withLowK2_counts L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := OwnDiagLowK.withLowK2_counts L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,su]) he
  have fa := mixFoldsQ_counts L hw true (accAMixQ L) stQ.1
  have fb := mixFoldsQ_counts L hw false (accBMixQ L) stQ.2
  have fc := bodyC_counts L hw control
  have prices := accQ_item_prices L hw
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  have sum := gSum_counts L hw
  rw [lo] at a
  rw [hi] at b
  rw [su] at c
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    sum.1.1,sum.1.2,sum.2.1,sum.2.2]
  constructor <;> omega

theorem accPrefixK_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    ECDSAAdd.wires (accPrefixK L ext control)⊆(control::L.wires++ext).toFinset := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have a := mixFoldsQ_support L hw hn control true (accAMixQ L) stQ.1
  have b := mixFoldsQ_support L hw hn control false (accBMixQ L) stQ.2
  have c := bodyC_support L hw hn control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := OwnDiagLowK.withLowK2_support L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) hl hp (by omega) (by omega) (by omega) he a
  have sb := OwnDiagLowK.withLowK2_support L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) hb hp (by omega) (by omega) (by omega) he b
  have sc := OwnDiagLowK.withLowK2_support L hw ext control L.core.sum L.core.product
    (bodyC L control) hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) he c
  have embed : (control::L.wires).toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  have prep := (gSum_support L hw control).1.trans embed
  have unprep := (gSum_support L hw control).2.trans embed
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨⟨prep,sc⟩,unprep⟩,sb⟩,sa⟩

theorem accPrefixK_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control :: L.wires).Nodup) (he : ExtOK L control ext) :
    GatePhysical (accPrefixK L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hl hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd true (accAMixQ L) stQ.1)
  have b := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hb hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd false (accBMixQ L) stQ.2)
  have c := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) ext he.nodup he.away he.len _
    (bodyC_physical L hw nd control (List.nodup_cons.mp hn).1)
  have prep := (gSum_physical L hw nd).1
  have clear := (gSum_physical L hw nd).2
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,gatePhysical_append]
  exact ⟨⟨⟨⟨prep,c⟩,clear⟩,b⟩,a⟩

theorem accPrefixK_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (accPrefixK L ext control) ≤ 8000000 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have bd (items : List MixItem) (h : items=accAMixQ L ∨ items=accBMixQ L ∨ items=accCMix L) :
      ∀i∈items,∀a,i=.inr a → a.terms.length≤20 ∧ a.pre.length≤4 := by
    intro i hi a e
    subst e
    rcases h with rfl|rfl|rfl <;>
      simp [accAMixQ,accBMixQ,accCMix] at hi <;> rw [hi] <;>
      simp [sortedItems,accARaw,accBRaw,accCRaw,termsB,earlyHTerms,Acc.earlyTerm,preW,nafMinusOneItems,List.filter_cons,posTop]
  have ha := mixFoldsQ_gateSlots L hw true (accAMixQ L) stQ.1 20 (bd _ (Or.inl rfl))
  have hb := mixFoldsQ_gateSlots L hw false (accBMixQ L) stQ.2 20 (bd _ (Or.inr (Or.inl rfl)))
  have hc := bodyC_gateSlots L hw control
  have la : (accAMixQ L).length = 3 := rfl
  have lb : (accBMixQ L).length = 7 := rfl
  have lc : (accCMix L).length = 2 := rfl
  rw [la] at ha
  rw [lb] at hb
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have gs := gSum_gateSlots L hw
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.OwnDiagAll12Square

end

section
-- ===== SquareBF =====

/-! Restructured branch-B fold (on top of the all-reflected-core square `OwnDiagAll12Square`).

With `P = B² = b0 + 2^128·b1`, `W = (c-1)·b1 = W_lo + 2^128·W_hi`, `R = rot128 P`,
`rotW = 2^128·W_lo + W_hi` and `e = b0 - b1 + W_hi`, one has
`(c-2^128)·P ≡ P - R + (c-1)·e + rotW (mod p)`.  Branch B folds `-P, +R, -rotW, +(c-1)·e''`
through four reflected cores, where `e''` is `e` (held as a 130-bit word in
`product[0:128] ++ product[256:258]`) with its low 129 bits complemented under the
control: `e'' = 2^129-1-e`, i.e. a classical offset `control·(c-1)(2^129-1)`.
`W` lives in the accumulator; read rotated it is exactly `rotW`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.DiagSquareBF
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- Classical offset of the restructured B fold. -/
def K : Nat := 4294968272*(2^129-1)

theorem K_lt : K<SquareReduction.p := by
  norm_num [K,SquareReduction.p,SquareReduction.B,SquareReduction.c]

/-- Controlled complement of a register, as a frame transformer. -/
theorem complement_frame (r : List Wire) (hr : r.Nodup) (c : Wire) (hc : c∉r)
    (b : BasisState) (A : Nat) :
    Triple (SquareFrame r b A) (maskedConstant c r (2^r.length-1))
      (SquareFrame r b (if b c then 2^r.length-1-A else A)) := by
  intro s m h
  rw [maskedConstant_run c r _ hc]
  have hcs : s.basis c=b c := h.2 c hc
  cases hb : b c
  · simp only [hcs,hb,Bool.false_eq_true,if_false]
    exact ⟨trivial,h⟩
  · simp only [hcs,hb,if_true]
    rw [OwnDiagAll12Square.xorConstant_ones,notRegister_correct r hr]
    refine ⟨rfl,?_,?_⟩
    · change regValue r (fun w => if w∈r then !s.basis w else s.basis w)=_
      rw [regValue_congr r _ (fun w => !s.basis w) (by intro w hw; simp [hw]),
        regValue_complement,h.1]
    · intro q hq
      change (if q∈r then !s.basis q else s.basis q)=b q
      simp only [hq,if_false]
      exact h.2 q hq

def eReg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.product.take 128++L.core.product.drop 256
def rotWork (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.drop 128++L.core.work.take 128
def rotWCore (L : CuccaroStreamedSquareWideLayout) : MeasuredCanonicalModLayout := {L.measuredCore with src:=rotWork L}
def eBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.take 129
def eZ (L : CuccaroStreamedSquareWideLayout) : List Wire := (L.foldPad.drop 129).take 2
def b1Src (L : CuccaroStreamedSquareWideLayout) : List Wire := hiReg L++eZ L
def whiSrc (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.drop 128++eZ L
def wTerms (L : CuccaroStreamedSquareWideLayout) : List MeasuredSquareFold := earlyHTerms (hiReg L)
def eItem (L : CuccaroStreamedSquareWideLayout) : AccItem := ⟨false,[],earlyHTerms (eReg L),earlyHTerms (eReg L)⟩

def wBuild (L : CuccaroStreamedSquareWideLayout) : Program :=
  Acc.sbuildNN (accReg L) (accZ L) (accBank L) L.core.cin 163 (wTerms L)
def wUnbuild (L : CuccaroStreamedSquareWideLayout) : Program :=
  Acc.sunbuildNN (accReg L) (accZ L) (accBank L) L.core.cin 163 (wTerms L)
def wCore (L : CuccaroStreamedSquareWideLayout) : Program := qprog (rotWCore L) SquareReduction.p
def eSub (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Program :=
  subInPlace src (eReg L) (eBank L) L.core.cin
def eAdd (L : CuccaroStreamedSquareWideLayout) (src : List Wire) : Program :=
  addInPlace src (eReg L) (eBank L) L.core.cin
def eFlip (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  maskedConstant c ((eReg L).take 129) (2^129-1)

/-- `-rotW` through the reflected core, forming `e` meanwhile. -/
def wFold (L : CuccaroStreamedSquareWideLayout) : Program :=
  wBuild L++(wCore L++(eSub L (b1Src L)++(eAdd L (whiSrc L)++wUnbuild L)))
/-- `+(c-1)·e''` through the reflected core. -/
def eFold (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  eFlip L c++(accFoldQ L (eItem L)++eFlip L c)
/-- Rebuild `W` to restore `b0` from `e`. -/
def wRestore (L : CuccaroStreamedSquareWideLayout) : Program :=
  wBuild L++(eSub L (whiSrc L)++(eAdd L (b1Src L)++wUnbuild L))
def bBody (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQ L (negP L)++(measuredFoldQ L (rot128F L)++(wFold L++(eFold L c++wRestore L)))

/-! Register bookkeeping. -/

theorem layoutCount (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) :
    L.core.y.count q+L.core.out.count q+L.core.product.count q+L.foldPad.count q+L.core.work.count q+
      [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag,
        L.core.sumCarry].count q≤1 := by
  have h := List.nodup_iff_count_le_one.mp hn q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
    List.count_append] at h ⊢
  omega

theorem productSplit (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.product.count q=(L.core.product.take 128).count q+(hiReg L).count q+
      (L.core.product.drop 256).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 256 L.core.product)
  have b := congrArg (List.count q) (List.take_append_drop 128 (L.core.product.take 256))
  rw [List.take_take,show min 128 256=128 by decide] at b
  simp only [List.count_append] at a b
  simp only [hiReg]
  omega

theorem workSplit (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.work.count q=(accReg L).count q+(L.core.work.drop 163).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 163 L.core.work)
  simp only [List.count_append] at a
  simp only [accReg]
  omega

theorem work128Split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.work.count q=(L.core.work.take 128).count q+(L.core.work.drop 128).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 128 L.core.work)
  simp only [List.count_append] at a
  omega

theorem padSplit (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.foldPad.count q=(eBank L).count q+(eZ L).count q+((L.foldPad.drop 129).drop 2).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 129 L.foldPad)
  have b := congrArg (List.count q) (List.take_append_drop 2 (L.foldPad.drop 129))
  simp only [List.count_append] at a b
  simp only [eBank,eZ]
  omega

theorem eReg_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (eReg L).count q=(L.core.product.take 128).count q+(L.core.product.drop 256).count q := by
  simp [eReg,List.count_append]

/-- Registers that the B body never changes outside its sub-steps. -/
theorem other_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (h : q∈hiReg L ∨ q∈L.core.work.drop 163 ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∉L.core.out ∧ q∉eReg L ∧ q∉accReg L := by
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ws := workSplit L q
  have ec := eReg_count L q
  have pos : 0<(hiReg L).count q ∨ 0<(L.core.work.drop 163).count q ∨ 0<L.foldPad.count q ∨
      0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
        L.core.modFlag,L.core.sumCarry].count q := by
    rcases h with h|h|h|h
    · exact Or.inl (List.count_pos_iff.mpr h)
    · exact Or.inr (Or.inl (List.count_pos_iff.mpr h))
    · exact Or.inr (Or.inr (Or.inl (List.count_pos_iff.mpr h)))
    · refine Or.inr (Or.inr (Or.inr (List.count_pos_iff.mpr ?_)))
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  refine ⟨fun h1 => ?_,fun h1 => ?_,fun h1 => ?_⟩
  · have a := List.count_pos_iff.mpr h1; omega
  · have a := List.count_pos_iff.mpr h1; omega
  · have a := List.count_pos_iff.mpr h1; omega

theorem eReg_product (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q∈eReg L) : q∈L.core.product := by
  simp only [eReg,List.mem_append] at h
  rcases h with h|h
  · exact List.mem_of_mem_take h
  · exact List.mem_of_mem_drop h

theorem eReg_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (h : q∈eReg L) :
    q∉L.core.out ∧ q∉accReg L ∧ q∉hiReg L := by
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ws := workSplit L q
  have ec := eReg_count L q
  have a := List.count_pos_iff.mpr h
  refine ⟨fun h1 => ?_,fun h1 => ?_,fun h1 => ?_⟩
  · have b := List.count_pos_iff.mpr h1; omega
  · have b := List.count_pos_iff.mpr h1; omega
  · have b := List.count_pos_iff.mpr h1; omega

theorem accReg_out (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire) (h : q∈accReg L) :
    q∉L.core.out := by
  have lc := layoutCount L hn q
  have ws := workSplit L q
  have a := List.count_pos_iff.mpr h
  intro h1
  have b := List.count_pos_iff.mpr h1
  omega

theorem eReg_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (eReg L).length=130 := by
  simp [eReg,hw.core.product]

theorem eReg_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : (eReg L).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ec := eReg_count L q
  omega

theorem eReg_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) (P : Nat)
    (hP : regValue L.core.product t=P) (hb : P<2^256) : regValue (eReg L) t=P%2^128 := by
  rw [eReg,regValue_append,L.product_take_value hw t P hP 128 (by omega),
    L.product_drop_value hw t P hP 256 (by omega),Nat.div_eq_of_lt hb]
  simp

/-! The B-body state: `out`, `e` and the accumulator hold given values, all else is `base`. -/

def BState (L : CuccaroStreamedSquareWideLayout) (base : BasisState) (O E A : Nat) (s : BasisState) : Prop :=
  regValue L.core.out s=O ∧ regValue (eReg L) s=E ∧ regValue (accReg L) s=A ∧
    ∀q,q∉L.core.out → q∉eReg L → q∉accReg L → s q=base q

theorem bstate_other (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A : Nat) (s : BasisState) (h : BState L base O E A s) (q : Wire)
    (hq : q∈hiReg L ∨ q∈L.core.work.drop 163 ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    s q=base q :=
  let a := other_away L hn q hq
  h.2.2.2 q a.1 a.2.1 a.2.2

theorem bstate_clean (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (hc : L.PairClean base) (O E : Nat) (s : BasisState) (h : BState L base O E 0 s) : L.PairClean s := by
  have keep (q : Wire) (hq : q∈L.core.work.drop 163 ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
      s q=base q := bstate_other L hn base O E 0 s h q (Or.inr hq)
  constructor
  · exact (regValue_congr _ _ _ (fun q hq => keep q (Or.inr (Or.inl hq)))).trans hc.pad
  · have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) s
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) s=0 :=
      (regValue_congr _ _ _ (fun q hq => keep q (Or.inl hq))).trans
        ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using h.2.2.1
  · exact (keep _ (by simp)).trans hc.productHigh
  · exact (keep _ (by simp)).trans hc.outHigh
  · exact (keep _ (by simp)).trans hc.workHigh
  · exact (keep _ (by simp)).trans hc.cin
  · exact (keep _ (by simp)).trans hc.normFlag
  · exact (keep _ (by simp)).trans hc.modFlag

/-- Lifting single-register steps to the B-body state. -/
theorem lift_out (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A O' : Nat) (pr : Program)
    (hstep : ∀s : State,∀m : List Bool,BState L base O E A s.basis →
      (run pr m s).phase=s.phase ∧ regValue L.core.out (run pr m s).basis=O' ∧
        ∀q,q∉L.core.out → (run pr m s).basis q=s.basis q) :
    Triple (BState L base O E A) pr (BState L base O' E A) := by
  intro s m h
  obtain ⟨ph,hv,hf⟩ := hstep s m h
  refine ⟨ph,hv,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (eReg_away L hn q hq).1)).trans h.2.1
  · exact (regValue_congr _ _ _ (fun q hq => hf q (accReg_out L hn q hq))).trans h.2.2.1
  · intro q h1 h2 h3
    exact (hf q h1).trans (h.2.2.2 q h1 h2 h3)

theorem lift_e (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A E' : Nat) (pr : Program)
    (hstep : ∀s : State,∀m : List Bool,BState L base O E A s.basis →
      (run pr m s).phase=s.phase ∧ regValue (eReg L) (run pr m s).basis=E' ∧
        ∀q,q∉eReg L → (run pr m s).basis q=s.basis q) :
    Triple (BState L base O E A) pr (BState L base O E' A) := by
  intro s m h
  obtain ⟨ph,hv,hf⟩ := hstep s m h
  refine ⟨ph,?_,hv,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun he => (eReg_away L hn q he).1 hq))).trans h.1
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun he => (eReg_away L hn q he).2.1 hq))).trans h.2.2.1
  · intro q h1 h2 h3
    exact (hf q h2).trans (h.2.2.2 q h1 h2 h3)

theorem lift_acc (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (O E A A' : Nat) (pr : Program)
    (hstep : ∀s : State,∀m : List Bool,BState L base O E A s.basis →
      (run pr m s).phase=s.phase ∧ regValue (accReg L) (run pr m s).basis=A' ∧
        ∀q,q∉accReg L → (run pr m s).basis q=s.basis q) :
    Triple (BState L base O E A) pr (BState L base O E A') := by
  intro s m h
  obtain ⟨ph,hv,hf⟩ := hstep s m h
  refine ⟨ph,?_,?_,hv,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun ha => accReg_out L hn q ha hq))).trans h.1
  · exact (regValue_congr _ _ _ (fun q hq => hf q (fun ha => (eReg_away L hn q hq).2.1 ha))).trans h.2.1
  · intro q h1 h2 h3
    exact (hf q h3).trans (h.2.2.2 q h1 h2 h3)


/-! Source values and static facts. -/

theorem accVal_earlyH (t : BasisState) (src : List Wire) :
    Acc.accVal t 0 (earlyHTerms src)=4294968272*regValue src t := by
  simp only [earlyHTerms,Acc.accVal,Acc.step,Acc.earlyTerm,Bool.false_eq_true,if_false,if_true]
  omega

theorem validH (t : BasisState) (src : List Wire) (hl : src.length≤130) :
    Acc.Valid t 163 0 (earlyHTerms src) := by
  have hT := regValue_lt src t
  have hT' : regValue src t<2^130 := lt_of_lt_of_le hT (Nat.pow_le_pow_right (by norm_num) hl)
  simp [Acc.Valid,Acc.step,earlyHTerms,Acc.earlyTerm]
  generalize regValue src t=T at hT' ⊢
  omega

theorem earlyH_static (L : CuccaroStreamedSquareWideLayout) (src : List Wire)
    (hs : ∀q,src.count q≤L.core.product.count q) (hl0 : 5≤src.length) (hl : src.length≤130) :
    (∀f∈earlyHTerms src,∀q,f.src.count q≤L.core.product.count q) ∧ (∀f∈earlyHTerms src,TermOK f) := by
  constructor
  · intro f hf
    obtain ⟨e,_⟩ := naf_facts false src f ((earlyH_mem _ _).mp hf)
    rw [e]; exact hs
  · intro f hf
    obtain ⟨e,sh⟩ := naf_facts false src f ((earlyH_mem _ _).mp hf)
    simp only [TermOK,e]
    omega

theorem hiReg_count (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (hiReg L).count q≤L.core.product.count q := by
  have := productSplit L q; omega

theorem eReg_count_le (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (eReg L).count q≤L.core.product.count q := by
  have := productSplit L q; have := eReg_count L q; omega

theorem hiReg_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (hiReg L).length=128 :=
  (split_lengths L hw).2.1

theorem wTerms_fits (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ∀f∈wTerms L,Acc.Fits (accReg L) (accZ L) (accBank L) L.core.cin 163 f := by
  have st := earlyH_static L (hiReg L) (hiReg_count L) (by rw [hiReg_length L hw]; omega) (by rw [hiReg_length L hw]; omega)
  intro f hf
  exact fits_of L hw hn f (fun q => by have h := st.1 f hf q; simp only [List.count_append]; omega) (st.2 f hf)

theorem eTerms_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀f∈earlyHTerms (eReg L),∀q,f.src.count q≤L.core.product.count q) ∧
      (∀f∈earlyHTerms (eReg L),TermOK f) :=
  earlyH_static L (eReg L) (eReg_count_le L) (by rw [eReg_length L hw]; omega) (by rw [eReg_length L hw])

theorem eItem_view (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (t : BasisState) :
    AccView L t (eItem L) :=
  plain_view L t false _ (eTerms_static L hw).1 (eTerms_static L hw).2 (validH t (eReg L) (by rw [eReg_length L hw]))

theorem eItem_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : MixStatic L (.inr (eItem L)) := by
  let z : BasisState := fun _ => false
  have h := eItem_view L hw z
  exact ⟨h.count,h.ok,h.preCount,h.preOk⟩

/-! The single steps of the B body. -/

theorem zero_regs (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (base : BasisState)
    (hc : L.PairClean base) (O E A : Nat) (s : BasisState) (h : BState L base O E A s) :
    (∀q∈accZ L,s q=false) ∧ (∀q∈accBank L,s q=false) ∧ s L.core.cin=false ∧
      (∀q∈L.foldPad,s q=false) ∧ (∀q∈L.core.work.drop 163,s q=false) := by
  have padZ : ∀q∈L.foldPad,s q=false := fun q hq =>
    (bstate_other L hn base O E A s h q (Or.inr (Or.inr (Or.inl hq)))).trans ((regValue_zero _ _).mp hc.pad q hq)
  have workZ : ∀q∈L.core.work.drop 163,s q=false := fun q hq =>
    (bstate_other L hn base O E A s h q (Or.inr (Or.inl hq))).trans
      ((regValue_zero _ _).mp hc.work q (List.mem_of_mem_drop hq))
  have dd : (L.core.work.drop 163).drop 33=L.core.work.drop 196 := by simp [List.drop_drop]
  refine ⟨?_,fun q hq => padZ q (List.mem_of_mem_take hq),?_,padZ,workZ⟩
  · intro q hq
    rcases accZ_mem L q hq with h1|h1
    · exact padZ q h1
    · rw [← dd] at h1; exact workZ q (List.mem_of_mem_drop h1)
  · exact (bstate_other L hn base O E A s h _ (Or.inr (Or.inr (Or.inr (by simp))))).trans hc.cin

theorem wBuild_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) :
    Triple (BState L base O E 0) (wBuild L) (BState L base O E (4294968272*regValue (hiReg L) base)) := by
  apply lift_acc L hn base O E 0 _ (wBuild L)
  intro s m h
  obtain ⟨hz,hb,hi,_,_⟩ := zero_regs L hn base hc O E 0 s.basis h
  have tr := Acc.sbuildNN_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    s.basis hz hb hi (wTerms L) (wTerms_fits L hw hn) (validH s.basis (hiReg L) (by rw [hiReg_length L hw]; omega))
    s m ⟨h.2.2.1,fun _ _ => rfl⟩
  have hh : regValue (hiReg L) s.basis=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E 0 s.basis h q (Or.inl hq))
  refine ⟨tr.1,tr.2.1.trans (by rw [wTerms,accVal_earlyH,hh]),tr.2.2⟩

theorem wUnbuild_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) :
    Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (wUnbuild L) (BState L base O E 0) := by
  apply lift_acc L hn base O E _ 0 (wUnbuild L)
  intro s m h
  obtain ⟨hz,hb,hi,_,_⟩ := zero_regs L hn base hc O E _ s.basis h
  have hh : regValue (hiReg L) s.basis=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E _ s.basis h q (Or.inl hq))
  have tr := Acc.sunbuildNN_triple (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    s.basis hz hb hi (wTerms L) (wTerms_fits L hw hn) (validH s.basis (hiReg L) (by rw [hiReg_length L hw]; omega))
    s m ⟨by rw [wTerms,accVal_earlyH,hh]; exact h.2.2.1,fun _ _ => rfl⟩
  exact ⟨tr.1,tr.2.1,tr.2.2⟩

theorem rotWCore_widths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (rotWCore L).Widths 256 := by
  have mc := L.measuredCore_widths hw
  refine ⟨?_,mc.out,mc.carry⟩
  simp [rotWCore,rotWork,hw.core.work]

theorem rotWCore_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : (rotWCore L).wires.Nodup := by
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp coreNd q
  have w := work128Split L q
  simp only [rotWCore,rotWork,measuredCore,MeasuredCanonicalModLayout.wires,List.count_append] at h ⊢
  omega

theorem rotWork_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (s : BasisState) (W : Nat)
    (hA : regValue (accReg L) s=W) (hz : ∀q∈L.core.work.drop 163,s q=false) :
    regValue (rotWork L) s=W/2^128+2^128*(W%2^128) := by
  have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) s
  rw [List.take_append_drop] at sp
  have hi : regValue (L.core.work.drop 163) s=0 := (regValue_zero _ _).mpr hz
  have wv : regValue L.core.work s=W := by
    rw [sp,hi]; simpa [accReg] using hA
  rw [rotWork,regValue_append,regValue_drop_div _ 128 (by rw [hw.core.work]; omega),
    regValue_take_mod _ 128 (by rw [hw.core.work]; omega),wv]
  simp [hw.core.work]

theorem wCore_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E W : Nat) (hO : O<SquareReduction.p) (hW : W<2^163) :
    Triple (BState L base O E W) (wCore L)
      (BState L base ((W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E W) := by
  apply lift_out L hn base O E W _ (wCore L)
  intro s m h
  obtain ⟨_,_,hi,padZ,workZ⟩ := zero_regs L hn base hc O E W s.basis h
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hR : W/2^128+2^128*(W%2^128)<SquareReduction.p := by
    have a : W/2^128<2^35 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc W<2^163 := hW
        _ = 2^35*2^128 := by norm_num
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at a b ⊢
    omega
  have keep (q : Wire) (hq : q=L.core.outHigh ∨ q=L.core.modFlag ∨ q=L.core.productHigh ∨ q=L.core.workHigh) :
      s.basis q=base q :=
    bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl <;> simp))))
  have carryZ : ∀q∈(rotWCore L).carry,s.basis q=false := by
    intro q hq
    simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact padZ q hq
    · exact (keep _ (Or.inr (Or.inr (Or.inl rfl)))).trans hc.productHigh
    · exact (keep _ (Or.inr (Or.inr (Or.inr rfl)))).trans hc.workHigh
  have ek := QCore.qprog_correct (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
    (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hR hO s m
    (rotWork_value L hw s.basis W h.2.2.1 workZ) h.1
    ((keep _ (Or.inl rfl)).trans hc.outHigh) ((keep _ (Or.inr (Or.inl rfl))).trans hc.modFlag) carryZ hi
  exact ⟨ek.1,ek.2.1,ek.2.2⟩

theorem eAdder_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (src : List Wire)
    (hs : src=b1Src L ∨ src=whiSrc L) : (L.core.cin::(src++eReg L++eBank L)).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ws := work128Split L q
  have pd := padSplit L q
  have ec := eReg_count L q
  rcases hs with rfl|rfl <;>
    simp only [b1Src,whiSrc,List.count_cons,List.count_append,List.count_nil] at lc ⊢ <;>
    split <;> split at lc <;> omega

theorem eSrc_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (src : List Wire)
    (hs : src=b1Src L ∨ src=whiSrc L) : src.length=(eReg L).length ∧ (eBank L).length+1=(eReg L).length := by
  have fp : L.foldPad.length=254 := by simp [foldPad,hw.core.pad,hw.overflowPad]
  rcases hs with rfl|rfl <;> simp [b1Src,whiSrc,eZ,eBank,eReg,hiReg,fp,hw.core.product,hw.core.work]

theorem eSub_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L)
    (O E A S : Nat) (hval : ∀t,BState L base O E A t → regValue src t=S) :
    Triple (BState L base O E A) (eSub L src) (BState L base O ((E+2^130-S)%2^130) A) := by
  apply lift_e L hn base O E A _ (eSub L src)
  intro s m h
  obtain ⟨_,_,hi,padZ,_⟩ := zero_regs L hn base hc O E A s.basis h
  have nd := eAdder_nodup L hn src hs
  have lens := eSrc_length L hw src hs
  have bank0 : regValue (eBank L) s.basis=0 := (regValue_zero _ _).mpr (fun q hq => padZ q (List.mem_of_mem_take hq))
  have spec := subInPlace_spec src (eReg L) (eBank L) L.core.cin nd lens.1 lens.2 S E s m
    ⟨⟨⟨hval s.basis h,h.2.1⟩,hi⟩,bank0⟩
  have hv : regValue (eReg L) (run (subInPlace src (eReg L) (eBank L) L.core.cin) m s).basis=
      (E+2^(eReg L).length-S)%2^(eReg L).length := spec.2.1.1.2
  rw [eReg_length L hw] at hv
  exact ⟨spec.1,hv,fun q hq => subInPlace_frame src (eReg L) (eBank L) L.core.cin nd lens.1 lens.2 s m hi bank0 q hq⟩

theorem eAdd_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L)
    (O E A S : Nat) (hval : ∀t,BState L base O E A t → regValue src t=S) :
    Triple (BState L base O E A) (eAdd L src) (BState L base O ((E+S)%2^130) A) := by
  apply lift_e L hn base O E A _ (eAdd L src)
  intro s m h
  obtain ⟨_,_,hi,padZ,_⟩ := zero_regs L hn base hc O E A s.basis h
  have nd := eAdder_nodup L hn src hs
  have lens := eSrc_length L hw src hs
  have bank0 : regValue (eBank L) s.basis=0 := (regValue_zero _ _).mpr (fun q hq => padZ q (List.mem_of_mem_take hq))
  have tr := addInPlace_cin_frame L.core.cin src (eReg L) (eBank L) nd lens.1 lens.2 s.basis false hi bank0 E
    s m ⟨h.2.1,fun _ _ => rfl⟩
  have hv := tr.2.1
  rw [hval s.basis h,eReg_length L hw] at hv
  simp only [Bool.toNat_false,Nat.add_zero] at hv
  exact ⟨tr.1,hv,tr.2.2⟩

def flipE (g : Bool) (E : Nat) : Nat := if g then 2^129*(E/2^129)+(2^129-1-E%2^129) else E

theorem eFlip_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (c : Wire) (hcw : c∉L.wires) (O E A : Nat) :
    Triple (BState L base O E A) (eFlip L c) (BState L base O (flipE (base c) E) A) := by
  apply lift_e L hn base O E A _ (eFlip L c)
  intro s m h
  have nd : ((eReg L).take 129).Nodup := (List.take_sublist _ _).nodup (eReg_nodup L hn)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have cs : s.basis c=base c := h.2.2.2 c
    (fun hm => hcw (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hm]))
    (fun hm => hcw (by have := eReg_product L c hm; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this]))
    (fun hm => hcw (by have := accReg_work L c hm; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this]))
  have lt : ((eReg L).take 129).length=129 := by simp [eReg_length L hw]
  have cmp := complement_frame ((eReg L).take 129) nd c hct s.basis (regValue ((eReg L).take 129) s.basis)
  rw [lt,cs] at cmp
  have tr : (run (eFlip L c) m s).phase=s.phase ∧ SquareFrame ((eReg L).take 129) s.basis
      (if base c then 2^129-1-regValue ((eReg L).take 129) s.basis else regValue ((eReg L).take 129) s.basis)
      (run (eFlip L c) m s).basis := cmp s m ⟨rfl,fun _ _ => rfl⟩
  have el := eReg_length L hw
  have lo : regValue ((eReg L).take 129) s.basis=E%2^129 := by
    rw [regValue_take_mod _ 129 (by omega),h.2.1]
  have hiv : regValue ((eReg L).drop 129) s.basis=E/2^129 := by
    rw [regValue_drop_div _ 129 (by omega),h.2.1]
  have sp := regValue_append ((eReg L).take 129) ((eReg L).drop 129) (run (eFlip L c) m s).basis
  rw [List.take_append_drop,lt] at sp
  have hd : regValue ((eReg L).drop 129) (run (eFlip L c) m s).basis=E/2^129 := by
    rw [← hiv]
    apply regValue_congr
    intro q hq
    apply tr.2.2 q
    intro hm
    have nd2 := eReg_nodup L hn
    rw [← List.take_append_drop 129 (eReg L)] at nd2
    exact List.disjoint_of_nodup_append nd2 hm hq
  refine ⟨tr.1,?_,fun q hq => tr.2.2 q (fun hm => hq (List.mem_of_mem_take hm))⟩
  rw [sp,hd,tr.2.1,lo]
  unfold flipE
  cases base c <;> simp <;> omega

theorem eCore_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E : Nat) (hO : O<SquareReduction.p) :
    Triple (BState L base O E 0) (accFoldQ L (eItem L))
      (BState L base ((4294968272*E+(SquareReduction.p-1-O))%SquareReduction.p) E 0) := by
  apply lift_out L hn base O E 0 _ (accFoldQ L (eItem L))
  intro s m h
  have tr := accFoldQ_frame L hw hn s.basis (eItem L) (eItem_view L hw s.basis)
    (bstate_clean L hn base hc O E s.basis h) O hO s m ⟨h.1,fun _ _ => rfl⟩
  have e : Acc.accVal s.basis 0 (eItem L).spec=4294968272*E := by
    rw [show (eItem L).spec=earlyHTerms (eReg L) from rfl,accVal_earlyH,h.2.1]
  rw [e] at tr
  exact ⟨tr.1,tr.2.1,tr.2.2⟩

/-! Composition of the B body. -/

theorem flipE_flipE (g : Bool) (E : Nat) : flipE g (flipE g E)=E := by
  unfold flipE
  cases g
  · simp
  · simp only [if_true]
    have h1 : (2^129*(E/2^129)+(2^129-1-E%2^129))/2^129=E/2^129 := by omega
    have h2 : (2^129*(E/2^129)+(2^129-1-E%2^129))%2^129=2^129-1-E%2^129 := by omega
    rw [h1,h2]
    omega

def bE1 (P : Nat) : Nat := ((P%2^128+2^130-P/2^128)%2^130+(4294968272*(P/2^128))/2^128)%2^130

def bO4 (P : Nat) (g : Bool) (O : Nat) : Nat :=
  (4294968272*flipE g (bE1 P)+(SquareReduction.p-1-
    (((4294968272*(P/2^128))/2^128+2^128*((4294968272*(P/2^128))%2^128)+(SquareReduction.p-1-
      (((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-
        ((P+(SquareReduction.p-1-O))%SquareReduction.p)))%SquareReduction.p)))%SquareReduction.p)))%SquareReduction.p

theorem b1Src_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E A : Nat) (t : BasisState) (h : BState L base O E A t) :
    regValue (b1Src L) t=regValue (hiReg L) base := by
  have ez : regValue (eZ L) t=0 := (regValue_zero _ _).mpr (fun q hq =>
    (zero_regs L hn base hc O E A t h).2.2.2.1 q (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  rw [b1Src,regValue_append,ez,Nat.mul_zero,Nat.add_zero]
  exact regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E A t h q (Or.inl hq))

theorem whiSrc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O E W : Nat) (t : BasisState) (h : BState L base O E W t) :
    regValue (whiSrc L) t=W/2^128 := by
  have zr := zero_regs L hn base hc O E W t h
  have ez : regValue (eZ L) t=0 := (regValue_zero _ _).mpr (fun q hq =>
    zr.2.2.2.1 q (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) t
  rw [List.take_append_drop] at sp
  have hi : regValue (L.core.work.drop 163) t=0 := (regValue_zero _ _).mpr zr.2.2.2.2
  have wv : regValue L.core.work t=W := by
    rw [sp,hi]; simpa [accReg] using h.2.2.1
  rw [whiSrc,regValue_append,ez,Nat.mul_zero,Nat.add_zero,regValue_drop_div _ 128 (by rw [hw.core.work]; omega),wv]

theorem bBody_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (bBody L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let E1 := bE1 P
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  let O3 := (W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-O2))%SquareReduction.p
  let O4 := (4294968272*flipE g E1+(SquareReduction.p-1-O3))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQ L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frame L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQ L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frame L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0
  -- wFold
  have w1 := wBuild_step L hw hn base hc O2 b0
  rw [hb1] at w1
  have w2 := wCore_step L hw hn base hc O2 b0 W hO2 hWlt
  have w3 := eSub_step L hw hn base hc (b1Src L) (Or.inl rfl) O3 b0 W b1
    (fun t h => (b1Src_value L hw hn base hc O3 b0 W t h).trans hb1)
  have w4 := eAdd_step L hw hn base hc (whiSrc L) (Or.inr rfl) O3 ((b0+2^130-b1)%2^130) W (W/2^128)
    (fun t h => whiSrc_value L hw hn base hc O3 _ W t h)
  have w5 := wUnbuild_step L hw hn base hc O3 (((b0+2^130-b1)%2^130+W/2^128)%2^130)
  rw [hb1] at w5
  have tw : Triple (BState L base O2 b0 0) (wFold L) (BState L base O3 E1 0) :=
    w1.seq (w2.seq (w3.seq (w4.seq w5)))
  -- eFold
  have f1 := eFlip_step L hw hn base c hcw O3 E1 0
  have f2 := eCore_step L hw hn base hc O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn base c hcw O4 (flipE g E1) 0
  rw [flipE_flipE] at f3
  have tf : Triple (BState L base O3 E1 0) (eFold L c) (BState L base O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestore
  have r1 := wBuild_step L hw hn base hc O4 E1
  rw [hb1] at r1
  have r2 := eSub_step L hw hn base hc (whiSrc L) (Or.inr rfl) O4 E1 W (W/2^128)
    (fun t h => whiSrc_value L hw hn base hc O4 E1 W t h)
  have r3 := eAdd_step L hw hn base hc (b1Src L) (Or.inl rfl) O4 ((E1+2^130-W/2^128)%2^130) W b1
    (fun t h => (b1Src_value L hw hn base hc O4 _ W t h).trans hb1)
  have back : ((E1+2^130-W/2^128)%2^130+b1)%2^130=b0 := by
    have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
    have hwh : W/2^128<2^35 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc W<2^163 := hWlt
        _ = 2^35*2^128 := by norm_num
    have e0' : b0=P%2^128 := rfl
    have e1' : b1=P/2^128 := rfl
    have hb0' : P%2^128<2^128 := Nat.mod_lt _ (by positivity)
    show ((bE1 P+2^130-W/2^128)%2^130+b1)%2^130=b0
    unfold bE1
    generalize hx : W/2^128=x at hwh
    norm_num at hb0 hb0' hb1lt hwh ⊢
    omega
  have r4 := wUnbuild_step L hw hn base hc O4 b0
  rw [hb1] at r4
  rw [back] at r3
  have tr : Triple (BState L base O4 E1 0) (wRestore L) (BState L base O4 b0 0) :=
    r1.seq (r2.seq (r3.seq r4))
  have conv2 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv2))
  exact all

/-! Value of the B body. -/

theorem bO4_cast (M O : Nat) (g : Bool) (hM : M<2^128) (hg : g=false → M=0) (hO : O<SquareReduction.p) :
    ((bO4 (M^2) g O : Nat) : ZMod SquareReduction.p)=(O : ZMod SquareReduction.p)+
      (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p)+
        (if g then (K : ZMod SquareReduction.p) else 0)) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  generalize hPdef : M^2=P at hb ⊢
  have hb1lt : P/2^128<2^128 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hb0lt : P%2^128<2^128 := Nat.mod_lt _ (by positivity)
  have hwhi : 4294968272*(P/2^128)/2^128<2^35 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    norm_num at hb1lt ⊢
    omega
  have hEn : g=true → flipE g (bE1 P)+P%2^128+4294968272*(P/2^128)/2^128+1=2^129+P/2^128 := by
    intro hgt
    subst hgt
    unfold flipE bE1
    simp only [if_true]
    generalize 4294968272*(P/2^128)/2^128=x at hwhi ⊢
    norm_num at hb0lt hb1lt hwhi ⊢
    omega
  unfold bO4
  generalize hX1 : (P+(SquareReduction.p-1-O))%SquareReduction.p=X1
  generalize hR : (P/2^128)%2^128+2^128*(P%2^128)=R
  generalize hX2 : (R+(SquareReduction.p-1-X1))%SquareReduction.p=X2
  generalize hW : 4294968272*(P/2^128)=W at hwhi hEn
  generalize hX3 : (W/2^128+2^128*(W%2^128)+(SquareReduction.p-1-X2))%SquareReduction.p=X3
  generalize hE2 : flipE g (bE1 P)=E2 at hEn
  have b1 : X1<SquareReduction.p := by rw [← hX1]; exact Nat.mod_lt _ pmod
  have b2 : X2<SquareReduction.p := by rw [← hX2]; exact Nat.mod_lt _ pmod
  have b3 : X3<SquareReduction.p := by rw [← hX3]; exact Nat.mod_lt _ pmod
  have k1 : (X1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    rw [← hX1,ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod O hO]
  have k2 : (X2 : ZMod SquareReduction.p)=(R : ZMod SquareReduction.p)+(-1-(X1 : ZMod SquareReduction.p)) := by
    rw [← hX2,ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod X1 b1]
  have k3 : (X3 : ZMod SquareReduction.p)=((W/2^128+2^128*(W%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(X2 : ZMod SquareReduction.p)) := by
    rw [← hX3,ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod X2 b2]
  rw [ZMod.natCast_mod,Nat.cast_add,measuredReflection_zmod X3 b3,k3,k2,k1]
  have hc : ((SquareReduction.c : Nat) : ZMod SquareReduction.p)=4294968273 := by norm_num [SquareReduction.c]
  have hK : ((K : Nat) : ZMod SquareReduction.p)=4294968272*(2^129-1) := by norm_num [K,SquareReduction.c]
  have hh : (2 : ZMod SquareReduction.p)^256=4294968273 := by rw [← hc]; exact_mod_cast radix_cast
  have nP : P=P%2^128+2^128*(P/2^128) := (Nat.mod_add_div P (2^128)).symm
  have nR : R=P/2^128+2^128*(P%2^128) := by rw [← hR,Nat.mod_eq_of_lt hb1lt]
  have nW : W=W%2^128+2^128*(W/2^128) := (Nat.mod_add_div W (2^128)).symm
  have zP := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) nP
  have zR := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) nR
  have zW := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) nW
  have zW2 := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) hW
  push_cast at zP zR zW zW2 ⊢
  rw [hc]
  cases hgv : g
  · have M0 := hg hgv
    have P0 : P=0 := by rw [← hPdef,M0]; norm_num
    subst P0
    have W0 : W=0 := by rw [← hW]; simp
    subst W0
    have R0 : R=0 := by rw [← hR]; simp
    subst R0
    have E0 : E2=0 := by rw [← hE2,hgv]; simp [flipE,bE1]
    subst E0
    simp only [Bool.false_eq_true,if_false]
    push_cast
    ring
  · have hE := congrArg (Nat.cast : Nat → ZMod SquareReduction.p) (hEn hgv)
    push_cast at hE
    simp only [if_true]
    rw [hK]
    linear_combination 4294968272*hE+zR+zP*(4294968272-2^128)+2^128*zW2+2^128*zW+((W/2^128 : Nat)-(P/2^128 : Nat) : ZMod SquareReduction.p)*hh

def resBF (P O : Nat) (g : Bool) : Nat :=
  ofCast false (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P+
    (if g then (K : ZMod SquareReduction.p) else 0)))

theorem bO4_eq (M O : Nat) (g : Bool) (hM : M<2^128) (hg : g=false → M=0) (hO : O<SquareReduction.p) :
    bO4 (M^2) g O=resBF (M^2) O g := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have h := bO4_cast M O g hM hg hO
  have lt : bO4 (M^2) g O<SquareReduction.p := Nat.mod_lt _ pmod
  have v := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt lt] at v
  rw [v]
  simp only [resBF,ofCast,Bool.false_eq_true,if_false,measuredOrientationCast]

/-! Branch A from the plain orientation: `-P`, `+rot128`, `-(complemented acc)` (ends reflected). -/

def aAcc (L : CuccaroStreamedSquareWideLayout) : AccItem :=
  ⟨false,[],earlyHTerms (L.core.product.drop 128),earlyHTerms (L.core.product.drop 128)⟩

def aBody (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
  measuredFoldQ L (negP L)++(measuredFoldQ L (rot128F L)++OwnDiagAll12Square.accFoldQF L c (aAcc L))

def resAF (P O : Nat) (g : Bool) : Nat :=
  ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P-
    (if g then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))

theorem aBody_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBody L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQ L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frame L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQ L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frame L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have t3 := OwnDiagAll12Square.accFoldQF_frame L hw hn c hcw base (aAcc L) v3 hc O2 hO2
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  -- value
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

/-! Branch wrappers. -/

def branchBF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.high (L.core.product.take 256) (bBody L control)
def branchAF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.low (L.core.product.take 256) (aBody L control)

theorem wires_in (L : CuccaroStreamedSquareWideLayout) (control q : Wire)
    (h : q∈L.core.out ∨ q∈L.core.product ∨ q∈L.core.work ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∈(control::L.wires).toFinset := by
  simp only [List.mem_toFinset,List.mem_cons,CuccaroStreamedSquareWideLayout.wires,
    CuccaroStreamedSquareLayout.wires,List.mem_append,foldPad,List.not_mem_nil,or_false] at h ⊢
  tauto

theorem bBody_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (bBody L control)⊆(control::L.wires).toFinset := by
  have memP (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) : ∀q∈f.src,q∈L.core.product :=
    fun q hq => List.count_pos_iff.mp (by have := h q; have := List.count_pos_iff.mpr hq; omega)
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have a1 := measuredFoldQ_support L control (negP L) (memP _ sP)
  have a2 := measuredFoldQ_support L control (rot128F L) (memP _ sR)
  have wb := Acc.sbuildNN_support (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_fits L hw hn) (control::L.wires).toFinset (by
      intro f hf q hq
      have st := (earlyH_static L (hiReg L) (hiReg_count L) (by rw [hiReg_length L hw]; omega)
        (by rw [hiReg_length L hw]; omega)).1 f hf
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
      apply wires_in L control q
      rcases hq with rfl|((h|h)|h)|h
      · simp
      · exact Or.inr (Or.inl (memP f st q h))
      · exact Or.inr (Or.inr (Or.inl (accReg_work L q h)))
      · rcases accZ_mem L q h with h1|h1
        · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
        · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h1)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h)))))
  have wc : ECDSAAdd.wires (wCore L)⊆(control::L.wires).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (QCore.qprog_support (rotWCore L) SquareReduction.p hq)
    have hd : q∈L.core.work.drop 128 → q∈L.core.work := List.mem_of_mem_drop
    have ht : q∈L.core.work.take 128 → q∈L.core.work := List.mem_of_mem_take
    apply wires_in L control q
    simp only [rotWCore,rotWork,measuredCore,foldCarry,MeasuredCanonicalModLayout.wires,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have adder (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      (L.core.cin::(src++eReg L++eBank L)).toFinset⊆(control::L.wires).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq
    apply wires_in L control q
    rcases hq with rfl|((h|h)|h)
    · simp
    · rcases hs with rfl|rfl <;> simp only [b1Src,whiSrc,eZ,List.mem_append] at h
      · rcases h with h|h
        · exact Or.inr (Or.inl (hiReg_product L q h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h)))))
      · rcases h with h|h
        · exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take h)))))
    · exact Or.inr (Or.inl (eReg_product L q h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
  have es (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      ECDSAAdd.wires (eSub L src)⊆(control::L.wires).toFinset := by
    have lens := eSrc_length L hw src hs
    rw [eSub,subInPlace_wires _ _ _ _ lens.1 lens.2]; exact adder src hs
  have ea (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      ECDSAAdd.wires (eAdd L src)⊆(control::L.wires).toFinset := by
    have lens := eSrc_length L hw src hs
    rw [eAdd,addInPlace_wires _ _ _ _ lens.1 lens.2]; exact adder src hs
  have fl : ECDSAAdd.wires (eFlip L control)⊆(control::L.wires).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedConstant_wires_subset control ((eReg L).take 129) (2^129-1) hq)
    rcases List.mem_cons.mp h with rfl|h
    · simp
    · exact wires_in L control q (Or.inr (Or.inl (eReg_product L q (List.mem_of_mem_take h))))
  have st := eItem_static L hw
  have ac := accFoldQ_support L hw hn control (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  simp only [bBody,wFold,eFold,wRestore,wBuild,wUnbuild,wires_append,Finset.union_subset_iff]
  exact ⟨a1,a2,⟨wb.1,wc,es _ (Or.inl rfl),ea _ (Or.inr rfl),wb.2⟩,⟨fl,ac,fl⟩,
    ⟨wb.1,es _ (Or.inr rfl),ea _ (Or.inl rfl),wb.2⟩⟩

theorem aBody_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (control : Wire) : ECDSAAdd.wires (aBody L control)⊆(control::L.wires).toFinset := by
  have memP (f : MeasuredSquareFold) (h : ∀q,f.src.count q≤L.core.product.count q) : ∀q∈f.src,q∈L.core.product :=
    fun q hq => List.count_pos_iff.mp (by have := h q; have := List.count_pos_iff.mpr hq; omega)
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have a1 := measuredFoldQ_support L control (negP L) (memP _ sP)
  have a2 := measuredFoldQ_support L control (rot128F L) (memP _ sR)
  have a3 := OwnDiagAll12Square.accFoldQF_support L hw hn control (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [aBody,wires_append,Finset.union_subset_iff]
  exact ⟨a1,a2,a3⟩


/-! Resources of the two bodies. -/

theorem wTerms_okLen (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    ∀f∈wTerms L,Acc.FitsLen (accZ L) (accBank L) 163 f := by
  have st := earlyH_static L (hiReg L) (hiReg_count L) (by rw [hiReg_length L hw]; omega)
    (by rw [hiReg_length L hw]; omega)
  intro f hf
  exact fitsLen_of L hw f (st.2 f hf)

theorem wTerms_price (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : Acc.sbuildTNN 163 (wTerms L)=388 := by
  have hl := hiReg_length L hw
  norm_num [wTerms,earlyHTerms,Acc.earlyTerm,Acc.sbuildTNN,Acc.HCase,Acc.hTerms,Acc.sbuildTN,Acc.WordCase,Acc.wordTerms,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,Acc.buildT,hl]

theorem eItem_price (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQ (eItem L)=1555 := by
  have hl := eReg_length L hw
  norm_num [eItem,accPriceQ,earlyHTerms,Acc.earlyTerm,Acc.sbuildTNN,Acc.HCase,Acc.hTerms,Acc.sbuildTN,Acc.WordCase,Acc.wordTerms,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hl]

theorem aAcc_price (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : accPriceQ (aAcc L)=1555 := by
  norm_num [aAcc,accPriceQ,earlyHTerms,Acc.earlyTerm,Acc.sbuildTNN,Acc.HCase,Acc.hTerms,Acc.sbuildTN,Acc.WordCase,Acc.wordTerms,Acc.sbuildT,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,
    Acc.buildT,hw.core.product]

theorem bBody_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (bBody L c)=5924 ∧ measurementCount (bBody L c)=5928 := by
  have q1 := measuredFoldQ_counts L hw (negP L)
  have q2 := measuredFoldQ_counts L hw (rot128F L)
  have bc := Acc.sbuildNN_counts (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_okLen L hw)
  rw [wTerms_price L hw] at bc
  have wb : toffoliCount (wBuild L)=388 ∧ measurementCount (wBuild L)=388 := bc.1
  have wu : toffoliCount (wUnbuild L)=388 ∧ measurementCount (wUnbuild L)=388 := bc.2
  have core := QCore.qprog_counts (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)
  have wc : toffoliCount (wCore L)=767 ∧ measurementCount (wCore L)=768 :=
    ⟨core.1.trans (by norm_num),core.2.trans (by norm_num)⟩
  have el := eReg_length L hw
  have l1 := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have s1 : toffoliCount (eSub L (b1Src L))=129 ∧ measurementCount (eSub L (b1Src L))=129 := by
    have h := subInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have s2 : toffoliCount (eSub L (whiSrc L))=129 ∧ measurementCount (eSub L (whiSrc L))=129 := by
    have h := subInPlace_counts (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have a1 : toffoliCount (eAdd L (b1Src L))=129 ∧ measurementCount (eAdd L (b1Src L))=129 := by
    have h := addInPlace_counts (b1Src L) (eReg L) (eBank L) L.core.cin l1.1 l1.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have a2 : toffoliCount (eAdd L (whiSrc L))=129 ∧ measurementCount (eAdd L (whiSrc L))=129 := by
    have h := addInPlace_counts (whiSrc L) (eReg L) (eBank L) L.core.cin l2.1 l2.2
    rw [el] at h; exact ⟨h.1.trans (by norm_num),h.2.trans (by norm_num)⟩
  have fl : toffoliCount (eFlip L c)=0 ∧ measurementCount (eFlip L c)=0 :=
    maskedConstant_counts c ((eReg L).take 129) (2^129-1)
  have st := eItem_static L hw
  have ac := accFoldQ_counts L hw (eItem L) st.2.1 st.2.2.2
  rw [eItem_price L hw] at ac
  simp only [bBody,wFold,eFold,wRestore,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,
    wb.1,wb.2,wu.1,wu.2,wc.1,wc.2,s1.1,s1.2,s2.1,s2.2,a1.1,a1.2,a2.1,a2.2,fl.1,fl.2,ac.1,ac.2]
  exact ⟨trivial,trivial⟩

theorem aBody_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    toffoliCount (aBody L c)=3089 ∧ measurementCount (aBody L c)=3092 := by
  have q1 := measuredFoldQ_counts L hw (negP L)
  have q2 := measuredFoldQ_counts L hw (rot128F L)
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have k := OwnDiagAll12Square.accFoldQF_counts L c (aAcc L)
  have a := accFoldQ_counts L hw (aAcc L) sA.2.1 sA.2.2.2
  rw [aAcc_price L hw] at a
  simp only [aBody,toffoliCount_append,measurementCount_append,q1.1,q1.2,q2.1,q2.2,k.1,k.2,a.1,a.2]
  exact ⟨trivial,trivial⟩

theorem bBody_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (bBody L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have p1 := measuredFoldQ_physical L hw nd (negP L) sP
  have p2 := measuredFoldQ_physical L hw nd (rot128F L) sR
  have wb := Acc.sbuildNN_physical (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_fits L hw nd)
  have wc := QCore.qprog_physical (rotWCore L) SquareReduction.p (rotWCore_nodup L nd)
  have adderNd (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) :
      (L.core.cin::src++eReg L++eBank L).Nodup := by
    have h := eAdder_nodup L nd src hs
    simpa only [List.cons_append,List.append_assoc] using h
  have es (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eSub L src) :=
    subInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have ea (src : List Wire) (hs : src=b1Src L ∨ src=whiSrc L) : GatePhysical (eAdd L src) :=
    addInPlace_physical src (eReg L) (eBank L) L.core.cin (adderNd src hs)
  have hct : c∉(eReg L).take 129 := fun hm => hcw (by
    have := eReg_product L c (List.mem_of_mem_take hm)
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,this])
  have fl : GatePhysical (eFlip L c) := maskedConstant_physical c ((eReg L).take 129) (2^129-1) hct
  have st := eItem_static L hw
  have ac := accFoldQ_physical L hw nd (eItem L) st.1 st.2.1 st.2.2.1 st.2.2.2
  simp only [bBody,wFold,eFold,wRestore,gatePhysical_append]
  exact ⟨p1,p2,⟨wb.1,wc,es _ (Or.inl rfl),ea _ (Or.inr rfl),wb.2⟩,⟨fl,ac,fl⟩,
    ⟨wb.1,es _ (Or.inr rfl),ea _ (Or.inl rfl),wb.2⟩⟩

theorem aBody_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (hn : (c::L.wires).Nodup) : GatePhysical (aBody L c) := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw := (List.nodup_cons.mp hn).1
  have sP := (acc_static L hw).1 (.inl (negP L)) (by simp [accAMix])
  have sR := (acc_static L hw).1 (.inl (rot128F L)) (by simp [accAMix])
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have p1 := measuredFoldQ_physical L hw nd (negP L) sP
  have p2 := measuredFoldQ_physical L hw nd (rot128F L) sR
  have p3 := OwnDiagAll12Square.accFoldQF_physical L hw nd c hcw (aAcc L) sA.1 sA.2.1 sA.2.2.1 sA.2.2.2
  simp only [aBody,gatePhysical_append]
  exact ⟨p1,p2,p3⟩

theorem bBody_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Challenge.gateSlots (bBody L c)≤300000 := by
  have q1 := measuredFoldQ_gateSlots L hw (negP L)
  have q2 := measuredFoldQ_gateSlots L hw (rot128F L)
  have bs := Acc.sbuildNN_gateSlots (accReg L) (accZ L) (accBank L) L.core.cin 163 (acc_lengths L hw).1
    (wTerms L) (wTerms_okLen L hw)
  have wl : (wTerms L).length=4 := by simp [wTerms,earlyHTerms]
  rw [wl] at bs
  have wb : Challenge.gateSlots (wBuild L)≤4*(14*163) := bs.1
  have wu : Challenge.gateSlots (wUnbuild L)≤4*(14*163) := bs.2
  have wc : Challenge.gateSlots (wCore L)≤67*256+41 :=
    QCore.qprog_gateSlots (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw)
  have el := eReg_length L hw
  have l1 := eSrc_length L hw (b1Src L) (Or.inl rfl)
  have l2 := eSrc_length L hw (whiSrc L) (Or.inr rfl)
  have s1 : Challenge.gateSlots (eSub L (b1Src L))≤12*130+2*130 := by
    have h := Baselines.subInPlace_gateSlots_le (b1Src L) (eReg L) (eBank L) L.core.cin
    rw [l1.1,el] at h; exact h
  have s2 : Challenge.gateSlots (eSub L (whiSrc L))≤12*130+2*130 := by
    have h := Baselines.subInPlace_gateSlots_le (whiSrc L) (eReg L) (eBank L) L.core.cin
    rw [l2.1,el] at h; exact h
  have a1 : Challenge.gateSlots (eAdd L (b1Src L))≤12*130 := by
    have h := Baselines.addInPlace_gateSlots_le (b1Src L) (eReg L) (eBank L) L.core.cin
    rw [l1.1,el] at h; exact h
  have a2 : Challenge.gateSlots (eAdd L (whiSrc L))≤12*130 := by
    have h := Baselines.addInPlace_gateSlots_le (whiSrc L) (eReg L) (eBank L) L.core.cin
    rw [l2.1,el] at h; exact h
  have fl : Challenge.gateSlots (eFlip L c)≤129 := by
    have h := Baselines.maskedConstant_gateSlots_le c ((eReg L).take 129) (2^129-1)
    have fll : ((eReg L).take 129).length=129 := by simp [el]
    rw [fll] at h; exact h
  have st := eItem_static L hw
  have ac := accFoldQ_gateSlots L hw (eItem L) st.2.1 st.2.2.2
  have tl : (eItem L).terms.length=4 := by simp [eItem,earlyHTerms]
  have pl : (eItem L).pre.length=0 := by simp [eItem]
  rw [tl,pl] at ac
  simp only [bBody,wFold,eFold,wRestore,Challenge.gateSlots_append]
  omega

theorem aBody_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    Challenge.gateSlots (aBody L c)≤150000 := by
  have sA := (acc_static L hw).1 (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have q1 := measuredFoldQ_gateSlots L hw (negP L)
  have q2 := measuredFoldQ_gateSlots L hw (rot128F L)
  have b := OwnDiagAll12Square.accFoldQF_gateSlots L hw c (aAcc L) sA.2.1 sA.2.2.2
  have lt : (aAcc L).terms.length=4 := by simp [aAcc,earlyHTerms]
  have lp : (aAcc L).pre.length=0 := by simp [aAcc]
  rw [lt,lp] at b
  simp only [aBody,Challenge.gateSlots_append]
  omega

/-! The two restructured branches. -/

theorem branchBF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : OwnDiagAll12Square.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchBF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchBF L ext control) records s).basis=
      resBF ((if s.basis control then B else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchBF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (bBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (bBody_support L hw nd control hw'))
  apply OwnDiagLowK.withLowK2_correct L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len
    (bBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have frame := bBody_frame L hw nd control hcw t.basis M mb full clean O hO t m ⟨outO,fun _ _ => rfl⟩
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  rw [bO4_eq M O (t.basis control) mb hg hO,ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

theorem branchAF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : OwnDiagAll12Square.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchAF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchAF L ext control) records s).basis=
      resAF ((if s.basis control then A else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchAF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (aBody L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (aBody_support L hw nd control hw'))
  apply OwnDiagLowK.withLowK2_correct L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len
    (aBody L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [ha] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have frame := aBody_frame L hw nd control hcw t.basis M mb full clean O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

/-! The whole square: B, C, A, then one output reflection. -/

/-- Branch C of `OwnDiagAll12Square` (plain → plain), branch B (restructured fold, plain → plain),
branch A (plain → reflected), then one output reflection: nine reflected cores and the reflection leave
the plain orientation; the complemented accumulators of C and A cancel, the classical offset is `control·K`. -/
def program (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.accBranchCK L ext control++branchBF L ext control++branchAF L ext control++L.reflectOutput

theorem complete_exact (enabled : Bool) (A B O : Nat) :
    SquareReduction.p-1-resAF ((if enabled then A else 0)^2)
      (resBF ((if enabled then B else 0)^2) (OwnDiagAll12Square.resCF enabled ((if enabled then A+B else 0)^2) O) enabled)
        enabled=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then K else 0))%SquareReduction.p := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := resBF PB OC enabled
  let OA := resAF PA OB enabled
  have ec : measuredOrientationCast false OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128)+
      ((if enabled then OwnDiagAll12Square.cFlipK else 0 : Nat) : ZMod SquareReduction.p) := cast_ofCast _ _
  have eb : measuredOrientationCast false OB=measuredOrientationCast false OC+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB+
        (if enabled then (K : ZMod SquareReduction.p) else 0)) := cast_ofCast _ _
  have ea : measuredOrientationCast true OA=measuredOrientationCast false OB+
      ((PA : ZMod SquareReduction.p)*2^128-PA-(if enabled then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)) :=
    cast_ofCast _ _
  rw [Nat.cast_ite,Nat.cast_zero] at ec
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have oaBound : OA<SquareReduction.p := ofCast_lt _ _
  have hrefl := measuredReflection_zmod OA oaBound
  have targetBound : (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then K else 0))%
      SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have ite_cast : (((if enabled then K else 0 : Nat)) : ZMod SquareReduction.p)=
      (if enabled then (K : ZMod SquareReduction.p) else 0) := by
    cases enabled <;> simp
  have cast : ((SquareReduction.p-1-OA : Nat) : ZMod SquareReduction.p)=
      (((subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then K else 0))%
        SquareReduction.p : Nat) : ZMod SquareReduction.p) := by
    rw [hrefl,ZMod.natCast_mod,Nat.cast_add,subModValue_cast,ite_cast]
    linear_combination ea+ec+eb+identity
  have lhsBound : SquareReduction.p-1-OA<SquareReduction.p := by
    have : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
    omega
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt lhsBound,ZMod.val_natCast_of_lt targetBound] using value

theorem correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : OwnDiagAll12Square.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (program L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (program L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (program L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := resBF PB OC enabled
  let OA := resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (OwnDiagAll12Square.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (OwnDiagAll12Square.accBranchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := OwnDiagAll12Square.accBranchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepR : Triple (SquareFrame L.core.out s.basis OA) L.reflectOutput
      (SquareFrame L.core.out s.basis (SquareReduction.p-1-OA)) := by
    intro t m hf
    have h := L.reflectOutput_correct hw nd OA (ofCast_lt _ _) t m hf.1
      (L.squareFrame_clean nd s.basis t.basis OA hf hc)
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := ((stepC.seq stepB).seq stepA).seq stepR
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  exact ⟨phase,value.trans exactResult,frame⟩

theorem counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (he : 300≤ext.length) :
    toffoliCount (program L ext control)=2*OwnDiagLowK.lowkcostTPair 128+OwnDiagLowK.lowkcostTPair 129+12684 ∧
      measurementCount (program L ext control)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+12693 := by
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_counts L hw ext control L.core.low (L.core.product.take 256)
    (aBody L control) (by omega) (by omega) (by omega) he
  have b := OwnDiagLowK.withLowK2_counts L hw ext control L.core.high (L.core.product.take 256)
    (bBody L control) (by omega) (by omega) (by omega) he
  have c := OwnDiagLowK.withLowK2_counts L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,su]) he
  have fa := aBody_counts L hw control
  have fb := bBody_counts L hw control
  have fc := OwnDiagAll12Square.bodyC_counts L hw control
  have sum := OwnDiagAll12Square.gSum_counts L hw
  have r := (L.measured_small_operation_counts hw).2.2
  rw [lo] at a
  rw [hi] at b
  rw [su] at c
  simp only [program,branchAF,branchBF,OwnDiagAll12Square.accBranchCK,OwnDiagAll12Square.accMiddleCK,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    sum.1.1,sum.1.2,sum.2.1,sum.2.2,r.1,r.2]
  constructor <;> omega

theorem reflect_support (L : CuccaroStreamedSquareWideLayout) (control : Wire) :
    ECDSAAdd.wires L.reflectOutput⊆(control::L.wires).toFinset :=
  (L.measured_small_support control).2.2.1

theorem support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    ECDSAAdd.wires (program L ext control)⊆(control::L.wires++ext).toFinset := by
  have a := aBody_support L hw hn control
  have b := bBody_support L hw hn control
  have c := OwnDiagAll12Square.bodyC_support L hw hn control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := OwnDiagLowK.withLowK2_support L hw ext control L.core.low (L.core.product.take 256)
    (aBody L control) hl hp (by omega) (by omega) (by omega) he a
  have sb := OwnDiagLowK.withLowK2_support L hw ext control L.core.high (L.core.product.take 256)
    (bBody L control) hb hp (by omega) (by omega) (by omega) he b
  have sc := OwnDiagLowK.withLowK2_support L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) he c
  have embed : (control::L.wires).toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  have prep := (OwnDiagAll12Square.gSum_support L hw control).1.trans embed
  have unprep := (OwnDiagAll12Square.gSum_support L hw control).2.trans embed
  have rf := (reflect_support L control).trans embed
  simp only [program,branchAF,branchBF,OwnDiagAll12Square.accBranchCK,OwnDiagAll12Square.accMiddleCK,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨prep,sc⟩,unprep⟩,sb⟩,sa⟩,rf⟩

theorem physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control :: L.wires).Nodup) (he : OwnDiagAll12Square.ExtOK L control ext) :
    GatePhysical (program L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hl hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (aBody_physical L hw control hn)
  have b := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hb hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (bBody_physical L hw control hn)
  have c := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) ext he.nodup he.away he.len _ (OwnDiagAll12Square.bodyC_physical L hw nd control (List.nodup_cons.mp hn).1)
  have prep := (OwnDiagAll12Square.gSum_physical L hw nd).1
  have clear := (OwnDiagAll12Square.gSum_physical L hw nd).2
  have rf := L.reflectOutput_physical nd
  simp only [program,branchAF,branchBF,OwnDiagAll12Square.accBranchCK,OwnDiagAll12Square.accMiddleCK,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨prep,c⟩,clear⟩,b⟩,a⟩,rf⟩

theorem gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (program L ext control) ≤ 8000000 := by
  have ha := aBody_gateSlots L hw control
  have hb := bBody_gateSlots L hw control
  have hc := OwnDiagAll12Square.bodyC_gateSlots L hw control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.low (L.core.product.take 256)
    (aBody L control) (by omega) (by omega) (by omega) he
  have b := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.high (L.core.product.take 256)
    (bBody L control) (by omega) (by omega) (by omega) he
  have c := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have gs := OwnDiagAll12Square.gSum_gateSlots L hw
  have rf := (Baselines.streamedFrames_gateSlots_le L hw).2.2
  simp only [program,branchAF,branchBF,OwnDiagAll12Square.accBranchCK,OwnDiagAll12Square.accMiddleCK,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.DiagSquareBF

end

section
-- ===== SquareOffset =====
namespace ECDSAAdd.Entrant.OwnDiagAll12Square

/-- Classical output offset of the square (`DiagSquareBF`): the restructured B fold flips the low
129 bits of `e` under the control (`control·(c-1)(2^129-1)`); the complemented accumulators of
branches C and A cancel. -/
def sqOff : Nat := 4294968272*(2^129-1)

theorem sqOff_eq : DiagSquareBF.K=sqOff := rfl

end ECDSAAdd.Entrant.OwnDiagAll12Square
end


section
-- ===== FastSquare =====

/-! Point-layout binding of the sign-grouped streamed square, with the same
pool relabeling as the Skywalk Step 4 square. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic ControlledPointLayout Secp256k1 CompressedPointSquare

/-- Zero pool sites 978..1028, 1284..1529 and 1533..1535: in the
certified site inventory, outside the square's placed prefix, fixed by its pool permutations. -/
def kext (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 978 51++wireBlock L.core.poolWire 1284 246++wireBlock L.core.poolWire 1533 3

theorem kext_index (L : ControlledPointLayout) (q : Wire) (hq : q∈kext L) :
    ∃i,978 ≤ i ∧ i < 1536 ∧ (i < 1029 ∨ (1284 ≤ i ∧ i < 1530) ∨ 1533 ≤ i) ∧ q=L.core.poolWire i := by
  rcases List.mem_append.mp hq with h|h
  · rcases List.mem_append.mp h with h|h <;> obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h <;>
      simp only [List.mem_range'_1] at hj <;> exact ⟨j,by omega,by omega,by omega,rfl⟩
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    exact ⟨j,by omega,by omega,by omega,rfl⟩

theorem dialogPool_nodup' (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.dialogPool.Nodup :=
  (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.1

theorem kpool_block (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogPool.take 2613=wireBlock L.core.poolWire 0 2613 := by
  simp only [dialogPool,List.take_take,Nat.min_self]
  exact (L.core.pool_prefix hw 2613 (by omega)).symm

theorem kpool_inj (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i j : Nat) (hi : i < 2613) (hj : j < 2613)
    (h : L.core.poolWire i = L.core.poolWire j) : i = j := by
  have nd : (wireBlock L.core.poolWire 0 2613).Nodup := by
    rw [← kpool_block L hw]
    exact (List.take_sublist _ _).nodup (dialogPool_nodup' L hn)
  exact List.inj_on_of_nodup_map nd (x := i) (y := j)
    (by simp [List.mem_range'_1]; omega) (by simp [List.mem_range'_1]; omega) h

theorem kext_mem (L : ControlledPointLayout) (hw : L.Widths) (q : Wire) (hq : q∈kext L) :
    q∈L.dialogPool := by
  obtain ⟨i,h1,h2,h3,rfl⟩ := kext_index L q hq
  have h : L.core.poolWire i∈L.dialogPool.take 2613 := by
    rw [kpool_block L hw]
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  exact List.mem_of_mem_take h

theorem kext_props (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (kext L).Nodup ∧ ∀q∈kext L,q∉L.dialogPool.take 945 := by
  refine ⟨?_,?_⟩
  · have e : kext L=(List.range' 978 51++List.range' 1284 246++List.range' 1533 3).map L.core.poolWire := by
      simp only [kext,wireBlock,List.map_append]
    rw [e]
    apply List.Nodup.map_on
    · intro x hx y hy hxy
      simp only [List.mem_append,List.mem_range'_1] at hx hy
      exact kpool_inj L hw hn x y (by omega) (by omega) hxy
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_append.mpr ⟨List.nodup_range',List.nodup_range',?_⟩,List.nodup_range',?_⟩
      · intro x hx y hy hxy
        simp only [List.mem_range'_1] at hx hy
        omega
      · intro x hx y hy hxy
        simp only [List.mem_append,List.mem_range'_1] at hx hy
        omega
  · intro q hq hm
    obtain ⟨i,h1,h2,h3,rfl⟩ := kext_index L q hq
    have b : L.dialogPool.take 945=wireBlock L.core.poolWire 0 945 := by
      simp only [dialogPool,List.take_take,Nat.min_eq_left (show 945 ≤ 2613 by omega)]
      exact (L.core.pool_prefix hw 945 (by omega)).symm
    rw [b] at hm
    obtain ⟨j,hj,e⟩ := List.mem_map.mp hm
    simp only [List.mem_range'_1] at hj
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega

theorem kext_not_resident (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈kext L) (hr : q∈PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags) :
    False :=
  (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.2 q (by simpa [dialogUsedWires] using hr) q
    (kext_mem L hw q hq) rfl

theorem kext_fixed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈kext L) :
    poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) q=q := by
  obtain ⟨j,hj1,hj2,hj3,rfl⟩ := kext_index L q hq
  apply outside_fixed
  · rintro ⟨i,h1,h2,e⟩
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega
  · rintro ⟨i,h1,h2,e⟩
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega

theorem kext_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ExtOK L.dialogStreamedSquareWide L.core.generic (kext L) := by
  have kp := kext_props L hw hn
  refine ⟨kp.1,?_,by simp [kext,wireBlock_length]⟩
  intro q hq hm
  rw [List.mem_cons,L.streamedSquare_wires_eq hw] at hm
  simp only [List.mem_append] at hm
  rcases hm with h|(h|h)|h
  · subst h
    exact kext_not_resident L hw hn _ hq (by simp [inPlaceFlags])
  · exact kext_not_resident L hw hn q hq (by simp [PointAddLayout.pointWires,h])
  · exact kext_not_resident L hw hn q hq (by simp [PointAddLayout.pointWires,h])
  · apply kp.2 q hq
    have e : (L.dialogPool.take 945).take 775=L.dialogPool.take 775 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←e] at h
    exact List.mem_of_mem_take h

def fastCandidate (L : ControlledPointLayout) : Program :=
  DiagSquareBF.program L.dialogStreamedSquareWide (kext L) L.core.generic

theorem fastCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastCandidate L)=2*OwnDiagLowK.lowkcostTPair 128+OwnDiagLowK.lowkcostTPair 129+12684 ∧ measurementCount (fastCandidate L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+12693 :=
  DiagSquareBF.counts L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
    L.core.generic (by simp [kext,wireBlock_length])

theorem fastCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
  have support := DiagSquareBF.support L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn) (kext L)
    L.core.generic (by simp [kext,wireBlock_length])
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires++kext L).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro q hq
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hq
      exact List.mem_of_mem_take hq
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp : q∈L.dialogPool.take 775 → q∈L.dialogPool.take 776 := fun h => small h
    tauto
  exact support.trans embed

theorem fastCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidate L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then sqOff else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := DiagSquareBF.correct K hwK (kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCandidate,hb,hp,pow_two,sqOff_eq] using kernel

theorem fastCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidate L) := by
  apply DiagSquareBF.physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
  · have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢; omega
  · exact kext_ok L hw hn

/-- Computable relabeled square: the emitted Step 4 program. -/
def fastSquare (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidate L)

noncomputable def fastSquareN (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (fastCandidate L)

theorem fastSquare_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    fastSquare L=fastSquareN L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

private theorem diag4_pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

private theorem diag4_pull_injective' (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

section StateEq
attribute [local irreducible] run wires fastCandidate

theorem fastSquare_state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (fastSquare L) m s=run (fastCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (diag4_pool_away_x' L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidate L) m s) cleanOut
  rw [fastSquare_eq L hw hn,fastSquareN]
  apply diag4_pull_injective' e
  have semantic := run_rename e e.injective (fastCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem fastSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquare L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then sqOff else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastSquare L) m s).basis q=s.basis q := by
  rw [fastSquare_state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc

end StateEq

theorem fastSquare_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact fastCandidate_physical L hw hn

theorem fastSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquare L) ≤ 8000000 := by
  simpa only [fastSquare,Baselines.rename_gateSlots,fastCandidate]
    using DiagSquareBF.gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
      L.core.generic (by simp [kext,wireBlock_length])

end ECDSAAdd.Entrant.OwnDiagAll12Square

end


-- DIAGONAL COMPONENT SquareTriple.lean

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
private theorem diag5_sub_val' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

section SquareStep
attribute [local irreducible] run fastSquare fastCandidate
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

theorem fast_step_square (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (fastSquare L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (sqOff : Fp) else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  have hK : ((sqOff : Nat) : Fp).val=sqOff := ZMod.val_natCast_of_lt (by norm_num [sqOff,p])
  rw [ZMod.val_add,diag5_sub_val']
  cases G
  · simpa using hx
  · simpa [ZMod.val_mul,hK] using hx

end SquareStep
end ECDSAAdd.Entrant.OwnDiagAll12Square


-- DIAGONAL COMPONENT Placement.lean

namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def SquareCorrect (L : ControlledPointLayout) (P : Program) : Prop :=
  ∀ (X Y : Fp) (G : Bool) (origin : BasisState),
    Triple (PointDialogValues L X Y G origin) P
      (PointDialogValues L (X-(if G then Y*Y else 0)+
        (if G then (OwnDiagAll12Square.sqOff : Fp) else 0)) Y G origin)

theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool)
    (hf : ∀q,q∉L.dialogPool → e q=q) (P : Program) (correct : SquareCorrect L P) :
    SquareCorrect L (renameProgram e P) := by
  intro X Y G origin s m v
  have old:=correct X Y G origin s m v
  have eq:=Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean old.2.clean
  simpa only [eq] using old

def initial (L : ControlledPointLayout) : Program :=
  renameProgram (Square5Placement.blockPerm L 202) (OwnDiagAll12Square.fastCandidate L)
def plus (L : ControlledPointLayout) : Program := renameProgram (OwnPlusSquare.swap L) (initial L)
def guard (L : ControlledPointLayout) : Program := renameProgram (OwnGuardSquare.swap L) (plus L)
def minus (L : ControlledPointLayout) : Program := renameProgram (OwnQ4Square.swap L) (guard L)
def program (L : ControlledPointLayout) : Program := renameProgram (OwnQ5Square.swap L) (minus L)

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (OwnDiagAll12Square.fastCandidate L) := by
  intro X Y G origin s m v
  have old:=OwnDiagAll12Square.fast_step_square L hw hn X Y G origin s m v
  rw [OwnDiagAll12Square.fastSquare_state_eq L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean] at old
  exact old

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (program L) := by
  have a:=relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have b:=relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw)
    (OwnPlusSquare.outside L hw) _ a
  have c:=relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw)
    (OwnGuardSquare.outside L hw) _ b
  have d:=relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw)
    (OwnQ4Square.outside L hw) _ c
  exact relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw)
    (OwnQ5Square.outside L hw) _ d

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT Resources.lean

namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=2*OwnDiagLowK.lowkcostTPair 128+OwnDiagLowK.lowkcostTPair 129+12684 ∧
    measurementCount (program L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+12693 := by
  have a:=renameProgram_counts (Square5Placement.blockPerm L 202) (OwnDiagAll12Square.fastCandidate L)
  have b:=renameProgram_counts (OwnPlusSquare.swap L) (initial L)
  have c:=renameProgram_counts (OwnGuardSquare.swap L) (plus L)
  have d:=renameProgram_counts (OwnQ4Square.swap L) (guard L)
  have e:=renameProgram_counts (OwnQ5Square.swap L) (minus L)
  have base:=OwnDiagAll12Square.fastCandidate_counts L hw
  exact ⟨e.1.trans (d.1.trans (c.1.trans (b.1.trans (a.1.trans base.1)))),
    e.2.trans (d.2.trans (c.2.trans (b.2.trans (a.2.trans base.2))))⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202)
    (Square5Placement.blockPerm L 202).injective _ (OwnDiagAll12Square.fastCandidate_physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 := by
  simpa only [program,minus,guard,plus,initial,Baselines.rename_gateSlots,
    OwnDiagAll12Square.fastCandidate] using
      DiagSquareBF.gateSlots_le L.dialogStreamedSquareWide
        (L.dialogStreamedSquareWide_widths hw) (OwnDiagAll12Square.kext L)
        L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT Support.lean
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag8_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem swap_support (P : Program) (a b : Wire) (S : Finset Wire)
    (old : wires P⊆S) (ha : a∈S) (hb : b∈S) :
    wires (renameProgram (Equiv.swap a b) P)⊆S := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=a
  · subst w; simpa only [Equiv.swap_apply_left] using hb
  · by_cases y:w=b
    · subst w; simpa only [Equiv.swap_apply_right] using ha
    · simpa only [Equiv.swap_apply_of_ne_of_ne x y] using old used

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L) ⊆ (OB5Support.sites L).toFinset := by
  have oldGuard : wires (guard L)⊆(OB5Support.sites L).toFinset := by
    have previous : wires (plus L)⊆(OB5Support.sites L).toFinset := by
      have old : wires (initial L)⊆(OB5Support.sites L).toFinset := by
        rw [initial,renameProgram_support]
        intro q hq
        obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
        have support := OwnDiagAll12Square.fastCandidate_support L hw hn used
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at support
        apply List.mem_toFinset.mpr
        rcases support with h | h | h | h | h
        · subst old
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _
            (diag8_resident_away L hn _ (by simp [CompressedPointSquare.residents, inPlaceFlags]))]
          simp [OB5Support.sites]
        · have away := diag8_resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inr h)
        · have away := diag8_resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inl (Or.inr h))
        · rw [pool_block L hw 776 (by omega)] at h
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
          have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
        · obtain ⟨i, h1, h2, h3, rfl⟩ := OwnDiagAll12Square.kext_index L _ h
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
      exact swap_support (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) _ old
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 766 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1530 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    exact swap_support (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) _ previous
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 765 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1531 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
  have oldQ4 := swap_support (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) _ oldGuard
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 767 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1532 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

  exact swap_support (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) _ oldQ4
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 770 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1536 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT Omissions.lean
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag9_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem original_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (n : Nat) (allowed : n∈[1530,1531,1532,1536,1537]) :
    L.core.poolWire n∉wires (initial L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=diag9_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=diag9_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=diag9_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

theorem swap_target_free (P : Program) (a b : Wire) (free : b∉wires P) :
    a∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have back : (Equiv.swap a b) b=a := Equiv.swap_apply_right _ _
  have same : old=b := (Equiv.swap a b).injective (e.trans back.symm)
  exact free (same ▸ used)

private theorem diag9_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613)
    (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)


theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1530 (by simp)
  have p1 : L.core.poolWire 766∉wires (plus L) :=
    swap_target_free (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) p0
  have p2 : L.core.poolWire 766∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 766∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 766∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1531 (by simp)
  have p1 : L.core.poolWire 1531∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1531 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 765∉wires (guard L) :=
    swap_target_free (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) p1
  have p3 : L.core.poolWire 765∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 765∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1532 (by simp)
  have p1 : L.core.poolWire 1532∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1532∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 767∉wires (minus L) :=
    swap_target_free (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) p2
  have p4 : L.core.poolWire 767∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 767 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1536 (by simp)
  have p1 : L.core.poolWire 1536∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1536∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1536∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 770∉wires (program L) :=
    swap_target_free (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) p3
  exact p4

theorem free1537 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1537∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1537 (by simp)
  have p1 : L.core.poolWire 1537∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1537∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1537∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1537∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT PlacementQ6.lean
namespace ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)
def program (L : ControlledPointLayout) : Program :=
  renameProgram (swap L) (OwnDiagAll12Placed.program L)

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 1285
  · subst q; simpa only [swap,Equiv.swap_apply_left] using Square5Placement.pool_member L hw 1537 (by omega)
  · by_cases b:q=L.core.poolWire 1537
    · subst q; simpa only [swap,Equiv.swap_apply_right] using Square5Placement.pool_member L hw 1285 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 1285:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1285 (by omega))
  have b:q≠L.core.poolWire 1537:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1537 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b


theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnDiagAll12Placed.SquareCorrect L (program L) :=
  OwnDiagAll12Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (OwnDiagAll12Placed.correct L hw hn)

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1285∉wires (program L) :=
  OwnDiagAll12Placed.swap_target_free _ _ _ (OwnDiagAll12Placed.free1537 L hw hn)

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=2*OwnDiagLowK.lowkcostTPair 128+OwnDiagLowK.lowkcostTPair 129+12684 ∧
    measurementCount (program L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+12693 := by
  have e:=renameProgram_counts (swap L) (OwnDiagAll12Placed.program L)
  have c:=OwnDiagAll12Placed.counts L hw
  exact ⟨e.1.trans c.1,e.2.trans c.2⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) :=
  gatePhysical_rename (swap L) (swap L).injective _ (OwnDiagAll12Placed.physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (Baselines.rename_gateSlots _ _).le.trans (OwnDiagAll12Placed.slots L hw)

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  OwnDiagAll12Placed.swap_support _ _ _ _ (OwnDiagAll12Placed.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1285
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1537
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

private theorem diag10_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (n : Nat) (hnn : n<2613) (a : n≠1285) (b : n≠1537) : swap L (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact a (pool_inj L hw hn n 1285 hnn (by omega) eq)
  · intro eq;exact b (pool_inj L hw hn n 1537 hnn (by omega) eq)

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 765 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free765 L hw hn)

theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 766 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free766 L hw hn)

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 767 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free767 L hw hn)

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 770 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free770 L hw hn)

end ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6


-- DIAGONAL COMPONENT TailOmissions.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag11_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial1800_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (initial L) := by
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=diag11_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=diag11_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=diag11_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem diag11_fix1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b : Nat) (ha : a<2613) (hb : b<2613) (hna : 1800≠a) (hnb : 1800≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire 1800)=L.core.poolWire 1800 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn 1800 a (by omega) ha eq)
  · intro eq;exact hnb (pool_inj L hw hn 1800 b (by omega) hb eq)

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have p0:=initial1800_free L hw hn
  have p1 : L.core.poolWire 1800∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 766 1530 (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1800∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 765 1531 (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1800∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 767 1532 (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1800∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 770 1536 (by omega) (by omega) (by omega) (by omega)) p3
  exact p4
end ECDSAAdd.Entrant.OwnDiagAll12Placed
namespace ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have same: swap L (L.core.poolWire 1800)=L.core.poolWire 1800 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e
      have :=pool_inj L hw hn 1800 1285 (by omega) (by omega) e
      omega
    · intro e
      have :=pool_inj L hw hn 1800 1537 (by omega) (by omega) e
      omega
  exact OwnPlusHost.rename_avoid _ _ _ same (OwnDiagAll12Placed.free1800 L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) :
    L.core.poolWire k∉wires (program L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact free1800 L hw hn
  · exact free766 L hw hn
  · exact free765 L hw hn
  · exact free767 L hw hn
  · exact free770 L hw hn
  · exact retired_free L hw hn
end ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6


-- DIAGONAL COMPONENT CountsDiag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.DiagEndpointCounts
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
attribute [local irreducible] toffoliCount measurementCount

theorem generic_diff (L : ControlledPointLayout) (hw : L.Widths) (D : Fp→Program) (S Sold P : Program)
 (deltaT deltaM : Nat) (hS : toffoliCount S+deltaT=toffoliCount Sold ∧
   measurementCount S+deltaM=measurementCount Sold) (cx cy : Fp) (ko : Nat) :
 toffoliCount (All12Generic.generic L D S P cx cy ko)+deltaT=
   toffoliCount (All12Generic.generic L D Sold P cx cy) ∧
 measurementCount (All12Generic.generic L D S P cx cy ko)+deltaM=
   measurementCount (All12Generic.generic L D Sold P cx cy) := by
 have a1:=fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(ko : Nat))
 have a2:=fastConstAdd_counts L hw L.point.x (Or.inl rfl) (3*cx-(2^163-1 : Nat))
 simp only [All12Generic.generic,toffoliCount_append,measurementCount_append]
 constructor <;> omega

theorem gen_diff (L : ControlledPointLayout) (hw : L.Widths) (D : Fp→Program) (S Sold P : Program)
 (deltaT deltaM : Nat) (hS : toffoliCount S+deltaT=toffoliCount Sold ∧
   measurementCount S+deltaM=measurementCount Sold) (cx cy : Fp) (ko : Nat) :
 toffoliCount (All12Generic.gen L D S P cx cy ko)+deltaT=
   toffoliCount (All12Generic.gen L D Sold P cx cy) ∧
 measurementCount (All12Generic.gen L D S P cx cy ko)+deltaM=
   measurementCount (All12Generic.gen L D Sold P cx cy) := by
 have h:=generic_diff L hw D S Sold P deltaT deltaM hS cx cy ko
 simp only [All12Generic.gen,All12Generic.mid,toffoliCount_append,measurementCount_append,
   renameProgram_counts]
 constructor <;> omega
end ECDSAAdd.Entrant.DiagEndpointCounts


section SquareSplitLedger
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.SquareBundle
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
attribute [local irreducible] toffoliCount measurementCount

theorem generic_diff (L : ControlledPointLayout) (D : Fp→Program) (S Sold P : Program)
 (deltaT deltaM : Nat) (hS : toffoliCount S+deltaT=toffoliCount Sold ∧
   measurementCount S+deltaM=measurementCount Sold) (cx cy : Fp) :
 toffoliCount (All12Generic.generic L D S P cx cy)+deltaT=
   toffoliCount (All12Generic.generic L D Sold P cx cy) ∧
 measurementCount (All12Generic.generic L D S P cx cy)+deltaM=
   measurementCount (All12Generic.generic L D Sold P cx cy) := by
 simp only [All12Generic.generic,toffoliCount_append,measurementCount_append]
 constructor <;> omega

theorem gen_diff (L : ControlledPointLayout) (D : Fp→Program) (S Sold P : Program)
 (deltaT deltaM : Nat) (hS : toffoliCount S+deltaT=toffoliCount Sold ∧
   measurementCount S+deltaM=measurementCount Sold) (cx cy : Fp) :
 toffoliCount (All12Generic.gen L D S P cx cy)+deltaT=
   toffoliCount (All12Generic.gen L D Sold P cx cy) ∧
 measurementCount (All12Generic.gen L D S P cx cy)+deltaM=
   measurementCount (All12Generic.gen L D Sold P cx cy) := by
 have h:=generic_diff L D S Sold P deltaT deltaM hS cx cy
 simp only [All12Generic.gen,All12Generic.mid,toffoliCount_append,measurementCount_append,
   renameProgram_counts]
 constructor <;> omega
end ECDSAAdd.Entrant.SquareBundle
end SquareSplitLedger

-- DIAGONAL COMPONENT ActualDiag.lean
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OwnDiagEndpointActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run fastConstAdd fastConstNeg fastConstRefl ExitFusionResearch.exitY

def genericE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.generic L (OwnEndpointEntryQ6.fusedDivisionF L) (OwnDiagAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy OwnDiagAll12Square.sqOff

def genE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.gen L (OwnEndpointEntryQ6.fusedDivisionF L) (OwnDiagAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy OwnDiagAll12Square.sqOff



theorem square_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (OwnDiagAll12PlacedQ6.program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (OwnDiagAll12Square.sqOff : Nat) else 0)) Y G origin) := by
  have h:=OwnDiagAll12PlacedQ6.correct L hw hn X Y G origin
  cases G <;> simpa only [Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h

private theorem diag13_square_diff (L : ControlledPointLayout) (hw : L.Widths) :
 toffoliCount (OwnDiagAll12PlacedQ6.program L)+1789=toffoliCount (OwnAll12PlacedQ6.program L) ∧
 measurementCount (OwnDiagAll12PlacedQ6.program L)+1003=measurementCount (OwnAll12PlacedQ6.program L) := by
 have a:=OwnDiagAll12PlacedQ6.counts L hw
 have b:=OwnAll12PlacedQ6.counts L hw
 norm_num [OwnDiagLowK.lowkcost2,OwnDiagLowK.lowkcostTPair,OwnDiagLowK.lowkcostTMake,OwnDiagLowK.lowkcostTClear,lowkcost2] at a b
 constructor <;> omega

theorem genericE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
 toffoliCount (genericE L cx cy)+2299=toffoliCount (OwnQ6Producer.genericE L cx cy) ∧
 measurementCount (genericE L cx cy)+1258=measurementCount (OwnQ6Producer.genericE L cx cy) := by
 have a:=DiagEndpointCounts.generic_diff L hw (OwnEndpointEntryQ6.fusedDivisionF L)
   (OwnDiagAll12PlacedQ6.program L) (OwnAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L)
   1789 1003 (diag13_square_diff L hw) cx cy OwnDiagAll12Square.sqOff
 have b:=OwnEndpointActual.genericE_counts_diff L hw cx cy
 change toffoliCount (genericE L cx cy)+1789=toffoliCount (OwnEndpointActual.genericE L cx cy) ∧
   measurementCount (genericE L cx cy)+1003=measurementCount (OwnEndpointActual.genericE L cx cy) at a
 constructor <;> omega

theorem genE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
 toffoliCount (genE L cx cy)+2299=toffoliCount (OwnQ6Producer.genE L cx cy) ∧
 measurementCount (genE L cx cy)+1258=measurementCount (OwnQ6Producer.genE L cx cy) := by
 have a:=DiagEndpointCounts.gen_diff L hw (OwnEndpointEntryQ6.fusedDivisionF L)
   (OwnDiagAll12PlacedQ6.program L) (OwnAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L)
   1789 1003 (diag13_square_diff L hw) cx cy OwnDiagAll12Square.sqOff
 have b:=OwnEndpointActual.genE_counts_diff L hw cx cy
 change toffoliCount (genE L cx cy)+1789=toffoliCount (OwnEndpointActual.genE L cx cy) ∧
   measurementCount (genE L cx cy)+1003=measurementCount (OwnEndpointActual.genE L cx cy) at a
 constructor <;> omega

theorem genE_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (genE L cx cy)≤49200000 :=
  All12Generic.gen_slots_le L hw _ _ _ (EndpointEntryProperties.division_slots L hw)
    (OwnDiagAll12PlacedQ6.slots L hw) ((OwnExitFuseQ6.arithExit_slots_le L).trans (by decide)) cx cy OwnDiagAll12Square.sqOff


theorem genericE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genericE L cx cy)⊆(OB5Support.sites L).toFinset :=
  All12Generic.generic_sites L hw _ _ _ (EndpointEntryProperties.division_support L hw)
    (OwnDiagAll12PlacedQ6.support L hw hn) (OwnExitFuseQ6.arithExit_support L hw) cx cy OwnDiagAll12Square.sqOff

theorem genE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genE L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [genE,All12Generic.gen_shape (ko := OwnDiagAll12Square.sqOff)]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (genericE_sites L hw hn cx cy)

theorem genE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (genE L cx cy) :=
  All12Generic.gen_physical L hw hn _ _ _ (EndpointEntryProperties.division_physical L hw hn)
    (OwnDiagAll12PlacedQ6.physical L hw hn) (OwnExitFuseQ6.arithExit_physical L hw hn) cx cy OwnDiagAll12Square.sqOff


theorem genericE_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) (cx cy : Fp) :
    L.core.poolWire k∉wires (genericE L cx cy) := by
  have bounds:515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  exact All12Generic.generic_free L hw hn _ _ _ k bounds
    (EndpointEntryProperties.division_free L hw hn k hk)
    (OwnDiagAll12PlacedQ6.square_free L hw hn k hk)
    (Q6FusionOmissions.exit_avoids L hw hn exitFree k hk) cx cy OwnDiagAll12Square.sqOff

theorem genE_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base)) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (genE L cx cy) :=
  All12Generic.genFFused_ok L hw hn _ _ _
    (OwnExitFuseQ6.arithExit_correct exitFree L hw hn)
    (OwnEndpointEntryQ6.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
    (square_step L hw hn) hc
end ECDSAAdd.Entrant.OwnDiagEndpointActual


-- DIAGONAL COMPONENT InventoryDiag.lean
namespace ECDSAAdd.Entrant.OwnDiagEndpointActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

theorem genE_qubits1593
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS) (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (genE layout cx cy))≤1593 := by
  rw [genE,All12Generic.gen_shape (ko := OwnDiagAll12Square.sqOff)]
  apply GenericQ6Geometry.edges_wrapG_qubits _ (genericE_sites layout layout_widths layout_nodup cx cy)
  · intro k hk
    exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with h|h|h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) cx cy
  · exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree 1285 (by simp) cx cy
end ECDSAAdd.Entrant.OwnDiagEndpointActual

