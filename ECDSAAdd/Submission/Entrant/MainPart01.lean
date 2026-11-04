import ECDSAAdd.Arithmetic.MappedSignedSquare
import ECDSAAdd.Arithmetic.MappedSquarePhysical
import ECDSAAdd.Arithmetic.MeasuredGateSupport
import ECDSAAdd.Framework.RecordPadding
import ECDSAAdd.Baselines.SlotSignedSquare
import ECDSAAdd.Baselines.SlotAlgebra
import ECDSAAdd.Arithmetic.PointFixedPrimitivesPhysical
import ECDSAAdd.Submission.Entrant.MainB
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.ExitMerge
import ECDSAAdd.Submission.Entrant.FusedFlags

set_option Elab.async false

-- ===== merged module ECDSAAdd.Submission.Entrant.TrimRow =====
section
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
end

-- ===== merged module ECDSAAdd.Submission.Entrant.TrimMid =====
section

/-! TrimMid: the top ripple carry of the MIDDLE signed row of every odd-width leaf square is a copy.

For an `m = 2k+1`-bit leaf `x`, the signed row at depth `k` adds `X = x >> (k+1)` (`k` bits) into a
window whose value is fixed by the rows below it.  Its top majority computes the carry out of the low
`k` window bits, and that carry always equals the top source bit `x_{m-1}`:
with `u = x mod 2^k`, `v = 2^k-1-u`, `t = x >> k` the window holds
`(u(u+1) + 2^k t (u-v) + 2^m v) / 2^(2k+1)`, and the carry test reduces to the sign of
`(2u+1)·2^k·(2X+1-2^k) + u(u+1)`.  So the majority's Toffoli never fires and the majority/erase pair
is one CX.  -/

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.TrimMid
open ECDSAAdd ECDSAAdd.Arithmetic RecordedQuantum

/-! ### `addTop`: ripple adder whose top majority is a copy -/

def addTop : List Wire → List Wire → List Wire → Wire → Program
  | [a,a'], [b,b'], c::cs, cin => TrimRow.addDrop [a,a'] [b,b'] (c::cs) cin
  | a::a'::a''::as, b::b'::b''::bs, c::cs, cin =>
      majority a b cin c++addTop (a'::a''::as) (b'::b''::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b]
  | x, y, carry, cin => addInPlace x y carry cin

/-- The top majority's carry equals its source bit, read along the ripple. -/
def TopOK : List Wire → List Wire → Bool → BasisState → Prop
  | [a,_], [b,_], ci, st => carryBit (st a) (st b) ci=st a
  | a::a'::a''::as, b::b'::b''::bs, ci, st => TopOK (a'::a''::as) (b'::b''::bs) (carryBit (st a) (st b) ci) st
  | _, _, _, _ => True

theorem TopOK_congr (x y : List Wire) (ci : Bool) (s t : BasisState) (h : ∀q∈x++y,s q=t q) :
    TopOK x y ci s ↔ TopOK x y ci t := by
  induction x generalizing y ci with
  | nil => cases y <;> simp [TopOK]
  | cons a x ih =>
    match x, y with
    | [], _ => simp [TopOK]
    | [a'], [] => simp [TopOK]
    | [a'], [b] => simp [TopOK]
    | [a'], [b,b'] =>
      have ha := h a (by simp); have hb := h b (by simp)
      simp only [TopOK,ha,hb]
    | [a'], b::b'::b''::bs => simp [TopOK]
    | a'::a''::as, [] => simp [TopOK]
    | a'::a''::as, [_] => simp [TopOK]
    | a'::a''::as, [_,_] => simp [TopOK]
    | a'::a''::as, b::b'::b''::bs =>
      have ha := h a (by simp); have hb := h b (by simp)
      simp only [TopOK,ha,hb]
      exact ih (b'::b''::bs) _ (fun q hq => h q (by simp at hq ⊢; tauto))

theorem copy_of_carry (A Y C : Bool) (h : carryBit A Y C=A) : ((Y^^A) && (C^^A))=false := by
  cases A <;> cases Y <;> cases C <;> simp_all [carryBit]

theorem addTop_counts (x y cy : List Wire) (cin : Wire) (hx : x.length=y.length)
    (hc : cy.length+1=y.length) (h2 : 2≤x.length) :
    toffoliCount (addTop x y cy cin)+1=toffoliCount (addInPlace x y cy cin) ∧
    measurementCount (addTop x y cy cin)+1=measurementCount (addInPlace x y cy cin) := by
  induction x generalizing y cy cin with
  | nil => simp at h2
  | cons a x ih =>
    match x, y, cy, hx, hc with
    | [], _, _, _, _ => simp at h2
    | [a'], [b,b'], [c], _, _ =>
      simp [addTop,TrimRow.addDrop,addInPlace,majority,eraseCarry,toffoliCount,measurementCount]
    | a'::a''::as, b::b'::b''::bs, c::cs, hx', hc' =>
      simp only [List.length_cons] at hx' hc'
      have IH := ih (b'::b''::bs) cs c (by simp; omega) (by simp; omega) (by simp)
      simp only [addTop,addInPlace,toffoliCount_append,measurementCount_append]
      omega

theorem addTop_run (x y cy : List Wire) (cin : Wire) (hnd : (cin::(x++y++cy)).Nodup)
    (hx : x.length=y.length) (hc : cy.length+1=y.length) (h2 : 2≤x.length) (rX : List Bool) (s : State)
    (hclean : ∀q∈cy,s.basis q=false) (hok : TopOK x y (s.basis cin) s.basis) :
    run (addTop x y cy cin) rX s=run (addInPlace x y cy cin) (false::rX) s := by
  induction x generalizing y cy cin s rX with
  | nil => simp at h2
  | cons a x ih =>
    match x, y, cy, hx, hc with
    | [], _, _, _, _ => simp at h2
    | [a'], [b,b'], [c], _, _ =>
      have hnd4 : [a,b,cin,c].Nodup := by
        simp at hnd ⊢; tauto
      have hrec : (c::(([a'])++([b'])++[])).Nodup := by simp at hnd ⊢; tauto
      have r := TrimRow.addDrop_run a a' b b' c cin [] [] [] hnd4 hrec rfl rfl
        (by simp at hnd ⊢; tauto) rX s (copy_of_carry _ _ _ hok) (hclean c (by simp)) (by simp)
      simp only [addTop]
      rw [r]
      simp [TrimRow.insF,addInPlace,measurementCount]
    | a'::a''::as, b::b'::b''::bs, c::cs, hx', hc' =>
      simp only [List.length_cons] at hx' hc'
      have hnd4 : [a,b,cin,c].Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hnd w
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        split_ifs at h ⊢ <;> omega
      have m0 : measurementCount (majority a b cin c)=0 := by simp [majority,measurementCount]
      have hmaj := majority_correct a b cin c hnd4 s []
      set u : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ carryBit (s.basis a) (s.basis b) (s.basis cin))⟩
      have hc0 : s.basis c=false := hclean c (by simp)
      have uc : u.basis c=carryBit (s.basis a) (s.basis b) (s.basis cin) := by
        simp [u,writeBit,hc0]
      have uk (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by simp [u,writeBit,Function.update,hq]
      have ndin : (c::((a'::a''::as)++(b'::b''::bs)++cs)).Nodup := by
        apply List.nodup_iff_count.mpr; intro w
        have h := List.nodup_iff_count.mp hnd w
        simp only [List.count_cons,List.count_append] at h ⊢
        split_ifs at h ⊢ <;> omega
      have cn := (List.nodup_cons.mp ndin).1
      have notc (q : Wire) (hq : q∈(a'::a''::as)++(b'::b''::bs)) : q≠c := by
        intro e; subst e; exact cn (List.mem_append_left _ hq)
      have okIn : TopOK (a'::a''::as) (b'::b''::bs) (u.basis c) u.basis := by
        rw [uc]
        rw [TopOK_congr _ _ _ u.basis s.basis (fun q hq => uk q (notc q hq))]
        simpa [TopOK] using hok
      have cleanIn : ∀q∈cs,u.basis q=false := by
        intro q hq
        have : q≠c := by
          intro e; subst e; exact cn (List.mem_append_right _ hq)
        rw [uk q this]; exact hclean q (by simp [hq])
      have IH := ih (b'::b''::bs) cs c ndin (by simp; omega) (by simp; omega) (by simp)
      simp only [addTop,addInPlace]
      rw [List.append_assoc,List.append_assoc,List.append_assoc,List.append_assoc,
        run_append (majority a b cin c),run_append (majority a b cin c),m0,List.take_zero,
        List.drop_zero,List.take_zero,List.drop_zero,hmaj,
        run_append (addTop _ _ _ _),run_append (addInPlace (a'::a''::as) _ _ _)]
      have mc : measurementCount (addInPlace (a'::a''::as) (b'::b''::bs) cs c)=
          measurementCount (addTop (a'::a''::as) (b'::b''::bs) cs c)+1 := by
        have := (addTop_counts (a'::a''::as) (b'::b''::bs) cs c (by simp; omega) (by simp; omega) (by simp)).2
        omega
      rw [mc,List.drop_succ_cons,List.take_succ_cons]
      rw [IH _ u cleanIn okIn]

/-! ### Value-level invariant of the signed rows -/

namespace MidMath

def delta (c : Bool) (R L : Nat) : Nat := if c then R+1 else 2^L-R

/-- Carry out of the low `L` framed window bits equals the top source bit `R / 2^(L-1)`. -/
def RC (c : Bool) (R L W : Nat) : Prop :=
  (R+(if c then W else 2^L-1-W)+c.toNat)/2^L=R/2^(L-1)

def Good : Nat → Nat → Nat → Nat → Prop
  | 0, X, n, A => RC (X%2==1) (X/2) (n-1) (A/2)
  | k+1, X, n, A => Good k (X/2) (n-1) ((A+2*delta (X%2==1) (X/2) (n-1))/4)

def S : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k+1, X, n => 2*delta (X%2==1) (X/2) (n-1)+4*S k (X/2) (n-1)

theorem Good_iff (k X n A : Nat) :
    Good k X n A ↔ RC ((X/2^k)%2==1) (X/2^(k+1)) (n-1-k) ((A+S k X n)/4^k/2) := by
  induction k generalizing X n A with
  | zero => simp [Good,S]
  | succ k ih =>
    rw [Good,ih]
    have e1 : X/2/2^k=X/2^(k+1) := by rw [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm]
    have e2 : X/2/2^(k+1)=X/2^(k+1+1) := by rw [Nat.div_div_eq_div_mul,pow_succ 2 (k+1),Nat.mul_comm]
    have e3 : n-1-1-k=n-1-(k+1) := by omega
    have e4 : ((A+2*delta (X%2==1) (X/2) (n-1))/4+S k (X/2) (n-1))/4^k=(A+S (k+1) X n)/4^(k+1) := by
      rw [S,show (A+2*delta (X%2==1) (X/2) (n-1))/4+S k (X/2) (n-1)=
        (A+(2*delta (X%2==1) (X/2) (n-1)+4*S k (X/2) (n-1)))/4 by omega,
        Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm (4^k) 4]
    rw [e1,e2,e3,e4]

/-- Closed form of the accumulated signed rows below depth `k`. -/
theorem S_closed (k X n : Nat) (hk : k<n) (hX : X<2^n) :
    (S k X n : Int)=(X%2^k : Nat)*((X%2^k : Nat)+1)+2^k*(X/2^k : Nat)*(2*(X%2^k : Nat)-(2^k-1))+
      2^n*((2^k : Int)-1-(X%2^k : Nat)) := by
  induction k generalizing X n with
  | zero => simp [S]
  | succ k ih =>
    obtain ⟨n,rfl⟩ : ∃ n', n=n'+1 := ⟨n-1,by omega⟩
    have hX' : X/2<2^n := by rw [pow_succ] at hX; omega
    have IH := ih (X/2) n (by omega) hX'
    rw [S]
    simp only [Nat.add_sub_cancel]
    have hm : X%2^(k+1)=X%2+2*(X/2%2^k) := by rw [pow_succ,Nat.mul_comm,Nat.mod_mul]
    have ht : X/2^(k+1)=X/2/2^k := by rw [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm]
    have hsplit : X/2=X/2%2^k+2^k*(X/2/2^k) := (Nat.mod_add_div _ _).symm
    have hX2 : X=X%2+2*(X/2) := (Nat.mod_add_div X 2).symm
    rw [hm,ht]
    generalize hu : X/2%2^k=u at IH hsplit ⊢
    generalize ht' : X/2/2^k=t at IH hsplit ⊢
    have hb : X%2<2 := Nat.mod_lt _ (by norm_num)
    have hp : (2:Int)^(n+1)=2*2^n := by ring
    have hq : (2:Int)^(k+1)=2*2^k := by ring
    rcases (show X%2=0 ∨ X%2=1 by omega) with h|h
    · simp only [h,delta,Nat.zero_ne_one,beq_iff_eq,if_false,Bool.false_eq_true]
      have hle : X/2≤2^n := le_of_lt hX'
      rw [Nat.cast_add,Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hle,IH,hsplit]
      push_cast
      rw [hp,hq]; ring
    · simp only [h,delta,beq_self_eq_true,if_true]
      rw [Nat.cast_add,Nat.cast_mul,Nat.cast_mul,IH,hsplit]
      push_cast
      rw [hp,hq]; ring

/-- The middle-row carry identity, as integer inequalities. -/
theorem mid_core (N u R q : Int) (hN : 2≤N) (hu0 : 0≤u) (huN : u<N) (hR0 : 0≤R) (hRN : R<N) (hEv : ∃ M, N=2*M)
    (c : Bool) (Sv : Int)
    (hS : Sv=u*(u+1)+N*(2*R+c.toNat)*(2*u-(N-1))+2*N*N*(N-1-u))
    (hq1 : 2*N*N*q≤Sv) (hq2 : Sv<2*N*N*(q+1)) :
    (c=true → (2*R≥N → N≤R+q+1) ∧ (2*R<N → R+q+1<N)) ∧
    (c=false → (2*R≥N → q+1≤R) ∧ (2*R<N → R≤q)) := by
  have hN0 : 0<N := by omega
  constructor
  · intro hc; subst hc; simp at hS
    have id1 : Sv-2*N*N*(N-1-R)=(2*u+1)*N*(2*R+1-N)+u*(u+1) := by rw [hS]; ring
    constructor
    · intro h
      have : 0≤(2*u+1)*N*(2*R+1-N) := by
        apply mul_nonneg; apply mul_nonneg <;> omega; omega
      have : 2*N*N*(N-1-R)≤Sv := by nlinarith
      by_contra hc
      have : q<N-1-R := by omega
      have : 2*N*N*(q+1)≤2*N*N*(N-1-R) := by apply mul_le_mul_of_nonneg_left <;> nlinarith
      omega
    · intro h
      have h1 : (2*u+1)*N*(2*R+1-N)≤-((2*u+1)*N) := by
        have : 2*R+1-N≤-1 := by omega
        have : 0≤(2*u+1)*N := by apply mul_nonneg <;> omega
        nlinarith
      have h2 : u*(u+1)<(2*u+1)*N := by nlinarith
      have : Sv<2*N*N*(N-1-R) := by linarith
      by_contra hc
      have : N-1-R≤q := by omega
      have : 2*N*N*(N-1-R)≤2*N*N*q := by apply mul_le_mul_of_nonneg_left <;> nlinarith
      omega
  · intro hc; subst hc; simp at hS
    have id2 : 2*N*N*R-Sv=N*(2*N-2*u-1)*(2*R-N)+N*N-u*(u+1) := by rw [hS]; ring
    constructor
    · intro h
      have : 0≤N*(2*N-2*u-1)*(2*R-N) := by
        apply mul_nonneg; apply mul_nonneg <;> omega; omega
      have : u*(u+1)<N*N := by nlinarith
      have : Sv<2*N*N*R := by linarith
      by_contra hc
      have : R≤q := by omega
      have : 2*N*N*R≤2*N*N*q := by apply mul_le_mul_of_nonneg_left <;> nlinarith
      omega
    · intro h
      have hNe : 2*R+2≤N := by
        obtain ⟨M,hM⟩ := hEv; omega
      have : N*(2*N-2*u-1)*(2*R-N)≤-(2*N*(2*N-2*u-1)) := by
        have : 2*R-N≤-2 := by omega
        have : 0≤N*(2*N-2*u-1) := by apply mul_nonneg <;> omega
        nlinarith
      have : 2*N*N*R≤Sv := by nlinarith
      by_contra hc
      have : q<R := by omega
      have : 2*N*N*(q+1)≤2*N*N*R := by apply mul_le_mul_of_nonneg_left <;> nlinarith
      omega

theorem mid_nat (N M u R q Sv : Nat) (c : Bool) (hNM : N=2*M) (hM : 1≤M) (hu : u<N) (hR : R<N)
    (hq : q<N) (hS : (Sv:Int)=u*(u+1)+N*(2*R+c.toNat)*(2*u-(N-1))+2*N*N*(N-1-u))
    (q1 : 2*N*N*q≤Sv) (q2 : Sv<2*N*N*(q+1)) :
    (R+(if c then q else N-1-q)+c.toNat)/N=R/M := by
  have core := mid_core N u R q (by omega) (by omega) (by omega) (by omega) (by omega) ⟨M,by omega⟩ c Sv
    hS (by exact_mod_cast q1) (by exact_mod_cast q2)
  have hRM : R/M=if 2*R≥N then 1 else 0 := by
    split_ifs with h
    · apply Nat.div_eq_of_lt_le <;> omega
    · apply Nat.div_eq_of_lt; omega
  rw [hRM]
  cases c
  · have c2 := core.2 rfl
    simp only [Bool.false_eq_true,if_false,Bool.toNat_false,Nat.add_zero]
    split_ifs with h
    · have := c2.1 (by omega)
      apply Nat.div_eq_of_lt_le <;> omega
    · have := c2.2 (by omega)
      apply Nat.div_eq_of_lt; omega
  · have c1 := core.1 rfl
    simp only [if_true,Bool.toNat_true]
    split_ifs with h
    · have := c1.1 (by omega)
      apply Nat.div_eq_of_lt_le <;> omega
    · have := c1.2 (by omega)
      apply Nat.div_eq_of_lt; omega

theorem mid_RC (k X : Nat) (hk : 1≤k) (hX : X<2^(2*k+1)) (hW : S k X (2*k+1)/4^k/2<2^k) :
    RC ((X/2^k)%2==1) (X/2^(k+1)) k (S k X (2*k+1)/4^k/2) := by
  have hcl := S_closed k X (2*k+1) (by omega) hX
  have h4 : (4:Nat)^k=2^k*2^k := by rw [← Nat.mul_pow]
  have hP : (2:Nat)^(2*k+1)=2*2^k*2^k := by rw [pow_succ,two_mul,pow_add]; ring
  have hk1 : (2:Nat)^k=2*2^(k-1) := by
    rw [← pow_succ']; congr 1; omega
  have hM : 1≤2^(k-1) := Nat.one_le_two_pow
  have hR : X/2^(k+1)=X/2^k/2 := by rw [Nat.div_div_eq_div_mul,pow_succ]
  have ht : X/2^k<2*2^k := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [hP] at hX; linarith
  have hu : X%2^k<2^k := Nat.mod_lt _ (by positivity)
  have htc : X/2^k=2*(X/2^k/2)+(X/2^k%2==1).toNat := by
    rcases Nat.mod_two_eq_zero_or_one (X/2^k) with h|h <;> simp [h] <;> omega
  have hq' : S k X (2*k+1)/4^k/2=S k X (2*k+1)/(2*2^k*2^k) := by
    rw [Nat.div_div_eq_div_mul,h4]; ring_nf
  unfold RC
  rw [hR]
  apply mid_nat (2^k) (2^(k-1)) (X%2^k) (X/2^k/2) _ (S k X (2*k+1)) _ hk1 hM hu (by omega) hW
  · rw [hcl]
    have e : ((X/2^k : Nat) : Int)=2*((X/2^k/2 : Nat) : Int)+((X/2^k%2==1).toNat : Int) := by
      exact_mod_cast htc
    rw [e]; push_cast; ring
  · rw [hq']; exact Nat.mul_div_le _ _
  · rw [hq']; exact Nat.lt_mul_div_succ _ (by positivity)

end MidMath
open MidMath

/-! ### Value form of `TopOK` -/

theorem regValue_cons2 (a : Wire) (r : List Wire) (st : BasisState) :
    regValue (a::r) st=(st a).toNat+2*regValue r st := by
  cases h : st a <;> simp [regValue,h]

theorem carry_toNat (a b c : Bool) : (carryBit a b c).toNat=(a.toNat+b.toNat+c.toNat)/2 := by
  cases a <;> cases b <;> cases c <;> rfl

theorem step_arith (a b ci X Y k : Nat) (ha : a<2) (hb : b<2) :
    ((a+2*X)%2^(k+1)+(b+2*Y)%2^(k+1)+ci)/2^(k+1)=(X%2^k+Y%2^k+(a+b+ci)/2)/2^k := by
  have key : ∀ (a X N : Nat), a<2 → 0<N → (a+2*X)%(2*N)=a+2*(X%N) := by
    intro a X N ha hN
    have hX := Nat.mod_add_div X N
    have hr := Nat.mod_lt X hN
    rw [show a+2*X=(a+2*(X%N))+(2*N)*(X/N) by rw [Nat.mul_assoc]; linarith [hX],
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
  have e1 : (a+2*X)%2^(k+1)=a+2*(X%2^k) := by
    rw [pow_succ,Nat.mul_comm (2^k) 2]; exact key a X (2^k) ha (Nat.two_pow_pos k)
  have e2 : (b+2*Y)%2^(k+1)=b+2*(Y%2^k) := by
    rw [pow_succ,Nat.mul_comm (2^k) 2]; exact key b Y (2^k) hb (Nat.two_pow_pos k)
  rw [e1,e2,pow_succ,Nat.mul_comm (2^k) 2,← Nat.div_div_eq_div_mul]
  congr 1
  omega

theorem TopOK_of_value (x y : List Wire) (ci : Bool) (st : BasisState) (hl : x.length=y.length)
    (h2 : 2≤x.length)
    (h : ((regValue x st%2^(x.length-1))+(regValue y st%2^(x.length-1))+ci.toNat)/2^(x.length-1)=
      regValue x st/2^(x.length-2)%2) : TopOK x y ci st := by
  induction x generalizing y ci with
  | nil => simp at h2
  | cons a x ih =>
    match x, y, hl with
    | [], _, _ => simp at h2
    | [a'], [b,b'], _ =>
      simp only [TopOK]
      simp only [List.length_cons,List.length_nil,regValue_cons2,show (0:Nat)+1+1-1=1 by rfl,
        show (0:Nat)+1+1-2=0 by rfl,pow_one,pow_zero,Nat.div_one] at h
      have := carry_toNat (st a) (st b) ci
      cases hA : st a <;> cases hB : st b <;> cases ci <;> simp_all [carryBit]
    | a'::a''::as, b::b'::b''::bs, hl' =>
      simp only [TopOK]
      apply ih (b'::b''::bs) _ (by simpa using hl') (by simp)
      simp only [List.length_cons] at h ⊢
      rw [regValue_cons2 a,regValue_cons2 b,show as.length+1+1+1-1=(as.length+1)+1 by omega,
        step_arith _ _ _ _ _ _ (by cases st a <;> simp) (by cases st b <;> simp)] at h
      rw [show as.length+1+1-1=as.length+1 by omega,show as.length+1+1-2=as.length by omega,carry_toNat]
      rw [h,show as.length+1+1+1-2=as.length+1 by omega,pow_succ,Nat.mul_comm (2^as.length) 2,
        ← Nat.div_div_eq_div_mul]
      congr 2
      cases st a <;> simp <;> omega

private theorem drop_tail_sublist' (dst : List Wire) (n : Nat) :
    (dst.drop (n+1)).Sublist (dst.drop n) := by
  have h := List.drop_sublist 1 (dst.drop n)
  simpa [List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

/-- Effect of the first signed row, extracted from the library's `signedSquareRows_correct`. -/
theorem row_step (c d : Wire) (tail dst pad carry : List Wire)
    (hnd : ((c::d::tail)++dst++pad++carry).Nodup) (hd : dst.length=2*(c::d::tail).length)
    (hpad : 1≤pad.length) (hc : (c::d::tail).length-1≤carry.length)
    (s : State) (m : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop (c::d::tail).length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) :
    (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) m s).phase=s.phase ∧
    (∀q,q∉(dst.drop 1).take ((d::tail).length+1) →
      (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) m s).basis q=s.basis q) ∧
    regValue ((dst.drop 1).take ((d::tail).length+1))
      (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) m s).basis=
      A/2+signedDeltaValue c (d::tail) s.basis ∧
    regValue (dst.take 2) (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) m s).basis+
      4*regValue (dst.drop 2) (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) m s).basis=
      A+2*signedDeltaValue c (d::tail) s.basis ∧
    regValue ((dst.drop 2).drop (d::tail).length)
      (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) m s).basis=0 ∧
    regValue (pad++carry) (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) m s).basis=0 ∧
    ((d::tail)++dst.drop 2++pad++carry).Nodup ∧ (dst.drop 2).length=2*(d::tail).length := by
  simp only [List.length_cons] at hd hc hhi
  let rest := d::tail
  let n := rest.length+1
  let row := (dst.drop 1).take n
  let dst2 := dst.drop 2
  have hcarry : rest.length≤carry.length := by
    change tail.length+1≤carry.length
    omega
  have hdst : 2≤dst.length := by omega
  have rowLen : row.length=rest.length+1 := by
    have cap : n≤(dst.drop 1).length := by dsimp [n,rest]; simp; omega
    simpa [row,n] using List.length_take_of_le cap
  have dst2Len : dst2.length=2*rest.length := by
    dsimp [dst2,rest]
    simp
    omega
  have rowSub : row.Sublist dst :=
    (List.take_sublist n (dst.drop 1)).trans (List.drop_sublist 1 dst)
  have dst2Sub : dst2.Sublist dst := List.drop_sublist 2 dst
  have ndrow : (c::rest++row++pad++carry).Nodup := by
    have pre := (List.Sublist.refl (c::rest)).append rowSub
    have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
    have sub : (c::rest++row++pad++carry).Sublist
        (c::rest++dst++pad++carry) := by simpa [List.append_assoc] using all
    exact sub.nodup hnd
  have ndrec : (rest++dst2++pad++carry).Nodup := by
    have pre := (List.Sublist.refl rest).append dst2Sub
    have all := (pre.append (List.Sublist.refl pad)).append (List.Sublist.refl carry)
    have sub0 : (rest++dst2++pad++carry).Sublist (rest++dst++pad++carry) := by
      simpa [List.append_assoc] using all
    have htail : (rest++dst++pad++carry).Nodup := by
      simpa [rest,List.append_assoc] using (List.nodup_cons.mp hnd).2
    exact sub0.nodup htail
  have dstN : dst.Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons,List.count_append] at hh ⊢
    omega
  have high0 : regValue (dst.drop n) s.basis=0 := by
    simpa [n,rest] using hhi
  have rowv : regValue row s.basis=A/2 := by
    simpa [row,n] using signed_row_slice_value dst n A (by omega) s.basis hv high0
  have work0 : regValue (pad++carry) s.basis=0 := hw
  have rowBound : A/2<2^row.length := by
    rw [← rowv]
    exact regValue_lt row s.basis
  have rf := signedSquareRow_frame c rest row pad carry ndrow rowLen hpad hcarry
    s.basis (s.basis c) rfl work0 (A/2) rowBound
  let mr := m
  let u := run (signedSquareRow c rest row pad carry) mr s
  have ru := rf s mr ⟨rowv,fun _ _ => rfl⟩
  let D := signedDeltaValue c rest s.basis
  have delta : signedRowValue (s.basis c) (A/2) (regValue rest s.basis) rest.length=A/2+D := by
    have hbA : A/2<2^rest.length := by
      have hnDst : n≤dst.length := by dsimp [n,rest]; omega
      have Ahi : A<2^n := by
        have split := regValue_append (dst.take n) (dst.drop n) s.basis
        rw [List.take_append_drop,List.length_take,Nat.min_eq_left hnDst,
          high0,Nat.mul_zero,Nat.add_zero,hv] at split
        rw [split]
        have b := regValue_lt (dst.take n) s.basis
        simpa [List.length_take,Nat.min_eq_left hnDst] using b
      dsimp [n] at Ahi
      rw [Nat.pow_succ] at Ahi
      omega
    have hbS := regValue_lt rest s.basis
    cases hb : s.basis c
    · simp only [signedRowValue,hb,Bool.false_eq_true,if_false,signedDeltaValue,D]
      have hlt : A/2+2^rest.length-regValue rest s.basis<2^(rest.length+1) := by
        rw [Nat.pow_succ]; omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
    · simp only [signedRowValue,hb,if_true,signedDeltaValue,D]
      have hlt : A/2+regValue rest s.basis+1<2^(rest.length+1) := by
        rw [Nat.pow_succ]; omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
  have rowOut : regValue row u.basis=A/2+D := by
    change regValue row (run (signedSquareRow c rest row pad carry) mr s).basis=_
    rw [ru.2.1,delta]
  have keepRow (q : Wire) (hq : q∉row) : u.basis q=s.basis q := ru.2.2 q hq
  have lift := signed_row_lift_update dst n A D (by omega)
    dstN s.basis u.basis hv rowOut
    (by
      have sub := drop_tail_sublist' dst n
      apply (regValue_zero _ _).mpr; intro q hq
      exact (regValue_zero _ _).mp high0 q (sub.subset hq)) keepRow
  have workU : regValue (pad++carry) u.basis=0 := by
    rw [← hw]
    apply regValue_congr
    intro q hq
    apply keepRow q
    intro hr
    have hnq := List.nodup_iff_count.mp ndrow q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hr
    simp only [List.count_cons,List.count_append] at hnq h1
    omega
  have high2 : regValue (dst2.drop rest.length) u.basis=0 := by
    simpa [dst2,n,List.drop_drop,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using lift.2
  have su := regValue_append (dst.take 2) dst2 u.basis
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at su
  refine ⟨ru.1,keepRow,rowOut,?_,high2,workU,ndrec,dst2Len⟩
  exact su.symm.trans lift.1

/-! ### Rows with the depth-`k` row's top carry copied -/

def rowT (c : Wire) (xs D pad carry : List Wire) : Program :=
  xorWhenFalse c (D.take xs.length)++addTop (xs++pad.take 1) D (carry.take xs.length) c++xorWhenFalse c D

def rowsK : Nat → List Wire → List Wire → List Wire → List Wire → Program
  | 0, c::d::tail, dst, pad, carry =>
      rowT c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry++signedSquareRows (d::tail) (dst.drop 2) pad carry
  | k+1, c::d::tail, dst, pad, carry =>
      signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry++rowsK k (d::tail) (dst.drop 2) pad carry
  | _, xs, dst, pad, carry => signedSquareRows xs dst pad carry

theorem padTake_len (l : List Bool) (K : Nat) : ((l++List.replicate K false).take K).length=K := by simp

theorem good_step (k : Nat) (c d : Wire) (tail dst pad carry : List Wire)
    (hnd : ((c::d::tail)++dst++pad++carry).Nodup) (hd : dst.length=2*(c::d::tail).length)
    (hp : 1≤pad.length) (hc : (c::d::tail).length-1≤carry.length)
    (s : State) (r : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop (c::d::tail).length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) (hg : Good (k+1) (regValue (c::d::tail) s.basis) (c::d::tail).length A) :
    Good k (regValue (d::tail) (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) r s).basis)
      (d::tail).length
      (regValue (dst.drop 2) (run (signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry) r s).basis) := by
  set row := (dst.drop 1).take ((d::tail).length+1)
  obtain ⟨_,keep,_,val,_,_,_,_⟩ := row_step c d tail dst pad carry hnd hd hp hc s r A hv hhi hw
  set u := run (signedSquareRow c (d::tail) row pad carry) r s
  have cnt := fun w => List.nodup_iff_count.mp hnd w
  have rowSub : row.Sublist dst := (List.take_sublist _ (dst.drop 1)).trans (List.drop_sublist 1 dst)
  have restKeep : regValue (d::tail) u.basis=regValue (d::tail) s.basis := by
    apply regValue_congr; intro q hq; apply keep
    intro h; have h1 := cnt q; have h2 := List.count_pos_iff.mpr (rowSub.subset h)
    have h3 := List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,beq_iff_eq] at h1 h3; split_ifs at h1 h3 <;> omega
  have low4 : regValue (dst.take 2) u.basis<4 := by
    have := regValue_lt (dst.take 2) u.basis
    have l2 : (dst.take 2).length≤2 := by simp
    calc regValue (dst.take 2) u.basis<2^(dst.take 2).length := this
      _ ≤ 2^2 := Nat.pow_le_pow_right (by norm_num) l2
      _ = 4 := by norm_num
  simp only [Good] at hg
  have hX : regValue (c::d::tail) s.basis=(s.basis c).toNat+2*regValue (d::tail) s.basis := regValue_cons2 _ _ _
  rw [hX] at hg
  have e2 : ((s.basis c).toNat+2*regValue (d::tail) s.basis)/2=regValue (d::tail) s.basis := by
    cases s.basis c <;> simp <;> omega
  have e3 : (((s.basis c).toNat+2*regValue (d::tail) s.basis)%2==1)=s.basis c := by
    cases h : s.basis c <;> simp [h] <;> omega
  rw [e2,e3,show (c::d::tail).length-1=(d::tail).length by simp] at hg
  rw [restKeep]
  have hdel : delta (s.basis c) (regValue (d::tail) s.basis) (d::tail).length=signedDeltaValue c (d::tail) s.basis := by
    simp [delta,signedDeltaValue]
  rw [hdel] at hg
  rwa [show regValue (dst.drop 2) u.basis=(A+2*signedDeltaValue c (d::tail) s.basis)/4 by omega]

theorem rowsK_exists (k : Nat) (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) (hk : k+2≤xs.length)
    (s : State) (r : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) (hg : Good k (regValue xs s.basis) xs.length A) :
    ∃ R, run (rowsK k xs dst pad carry) r s=run (signedSquareRows xs dst pad carry) R s := by
  induction k generalizing xs dst s r A with
  | zero =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    set rest := d::tail
    set L := rest.length
    set row := (dst.drop 1).take (L+1)
    have rowSub : row.Sublist dst := (List.take_sublist _ (dst.drop 1)).trans (List.drop_sublist 1 dst)
    have rowLen : row.length=L+1 := by simp [row,L,rest] at hd ⊢; omega
    have cnt := fun w => List.nodup_iff_count.mp hnd w
    have rowN : row.Nodup := rowSub.nodup (by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      simp only [List.count_cons,List.count_append] at h; omega)
    have cRow : c∉row := by
      intro h; have h1 := cnt c; have h2 := List.count_pos_iff.mpr (rowSub.subset h)
      simp only [List.count_cons,List.count_append] at h1 h2; simp at h1; omega
    set src := rest++pad.take 1
    set cy := carry.take L
    set Pre := xorWhenFalse c (row.take L)
    set Post := xorWhenFalse c row++signedSquareRows rest (dst.drop 2) pad carry
    have e1 : rowsK 0 (c::rest) dst pad carry=Pre++addTop src row cy c++Post := by
      simp only [rowsK,rowT,Pre,Post,src,cy,row,L,rest,List.append_assoc]
    have e2 : signedSquareRows (c::rest) dst pad carry=Pre++addInPlace src row cy c++Post := by
      simp only [signedSquareRows,signedSquareRow,Pre,Post,src,cy,row,L,rest,List.append_assoc]
    have srcLen : src.length=L+1 := by simp [src,L]; omega
    have cyLen : cy.length=L := by simp [cy]; simp at hc; omega
    have ndadd : (c::(src++row++cy)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w
      have h := cnt w
      have t1 := rowSub.count_le w
      have t2 := (List.take_sublist 1 pad).count_le w
      have t3 := (List.take_sublist L carry).count_le w
      simp only [src,cy,List.count_cons,List.count_append] at h t1 t2 t3 ⊢
      split_ifs at h ⊢ <;> omega
    have cnts := addTop_counts src row cy c (by omega) (by omega) (by simp [srcLen,L,rest])
    rw [e1,e2]
    apply TrimRow.glue _ _ _ _ 0 (Nat.zero_le _) cnts.2.symm
    intro rP rX
    have hu := xorWhenFalse_correct c (row.take L) ((List.take_sublist _ _).nodup rowN)
      (fun h => cRow (List.mem_of_mem_take h)) s rP
    rw [show TrimRow.insF 0 rX=false::rX by simp [TrimRow.insF]]
    apply addTop_run src row cy c ndadd (by omega) (by omega) (by simp [srcLen,L,rest])
    · intro q hq
      rw [hu]
      have qc : q∈carry := List.mem_of_mem_take hq
      have qr : q∉row.take L := by
        intro h; have h1 := cnt q; have h2 := List.count_pos_iff.mpr (rowSub.subset (List.mem_of_mem_take h))
        have h3 := List.count_pos_iff.mpr qc
        simp only [List.count_cons,List.count_append] at h1; omega
      simp only [xorFalseBasis,qr,if_false]
      exact (regValue_zero _ _).mp hw q (by simp [qc])
    · rw [hu]
      set st := xorFalseBasis c (row.take L) s.basis
      have stc : st c=s.basis c := by
        simp only [st,xorFalseBasis]; rw [if_neg (fun h => cRow (List.mem_of_mem_take h))]
      show TopOK src row (st c) st
      rw [stc]
      apply TopOK_of_value src row _ st (by omega) (by simp [srcLen,L,rest])
      rw [srcLen,show L+1-1=L by omega,show L+1-2=L-1 by omega]
      -- the source register reads `rest` and a clean pad bit
      have restDis (q : Wire) (hq : q∈rest) : q∉row.take L := by
        intro h; have h1 := cnt q; have h2 := List.count_pos_iff.mpr (rowSub.subset (List.mem_of_mem_take h))
        have h3 := List.count_pos_iff.mpr hq
        simp only [List.count_cons,List.count_append] at h1 h3; omega
      have hR : regValue rest st=regValue rest s.basis := regValue_congr _ _ _ (fun q hq => by
        simp only [st,xorFalseBasis,restDis q hq,if_false])
      have hP0 : regValue (pad.take 1) st=0 := by
        apply (regValue_zero _ _).mpr; intro q hq
        have qp : q∈pad := List.mem_of_mem_take hq
        have qr : q∉row.take L := by
          intro h; have h1 := cnt q; have h2 := List.count_pos_iff.mpr (rowSub.subset (List.mem_of_mem_take h))
          have h3 := List.count_pos_iff.mpr qp
          simp only [List.count_cons,List.count_append] at h1; omega
        simp only [st,xorFalseBasis,qr,if_false]
        exact (regValue_zero _ _).mp hw q (by simp [qp])
      have hsrc : regValue src st=regValue rest s.basis := by
        simp only [src]; rw [regValue_append,hR,hP0]; simp
      rw [hsrc]
      have hRlt : regValue rest s.basis<2^L := regValue_lt _ _
      rw [Nat.mod_eq_of_lt hRlt]
      -- the framed window
      have hpre := xorWhenFalse_prefix_value c row L rowN cRow (by omega) s rP
      rw [hu] at hpre
      change regValue row st=_ at hpre
      have hV : regValue row s.basis=A/2 := by
        simpa [row] using signed_row_slice_value dst (L+1) A (by simp at hd; omega) s.basis hv (by simpa [L,rest] using hhi)
      have hA : A<2^(L+1) := by
        have split := regValue_append (dst.take (L+1)) (dst.drop (L+1)) s.basis
        rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by simp at hd; omega),
          show regValue (dst.drop (L+1)) s.basis=0 by simpa [L,rest] using hhi,Nat.mul_zero,Nat.add_zero,hv] at split
        have b := regValue_lt (dst.take (L+1)) s.basis
        rw [List.length_take,Nat.min_eq_left (by simp at hd; omega)] at b
        rw [split]; exact b
      have hW : A/2<2^L := by rw [pow_succ] at hA; omega
      have hwin : regValue row st%2^L=if s.basis c then A/2 else 2^L-1-A/2 := by
        rw [hpre,hV,Nat.mod_eq_of_lt hW]
        split_ifs
        · exact Nat.mod_eq_of_lt hW
        · rw [Nat.div_eq_of_lt hW,Nat.mul_zero,Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
      rw [hwin]
      -- the invariant
      have hX : regValue (c::rest) s.basis=(s.basis c).toNat+2*regValue rest s.basis := regValue_cons2 _ _ _
      simp only [Good,RC] at hg
      rw [hX,show (c::rest).length-1=L by simp [L]] at hg
      have e1 : ((s.basis c).toNat+2*regValue rest s.basis)%2==1 ↔ s.basis c=true := by
        cases s.basis c <;> simp <;> omega
      have e2 : ((s.basis c).toNat+2*regValue rest s.basis)/2=regValue rest s.basis := by
        cases s.basis c <;> simp <;> omega
      have e3 : (((s.basis c).toNat+2*regValue rest s.basis)%2==1)=s.basis c := by
        cases h : s.basis c <;> simp [h] <;> omega
      rw [e3,e2] at hg
      have hlt2 : regValue rest s.basis/2^(L-1)<2 := by
        rcases Nat.eq_zero_or_pos L with h0|hpos
        · simp [L,rest] at h0
        · have e : (2:Nat)^L=2*2^(L-1) := by
            rw [← pow_succ']; exact congrArg (fun n => (2:Nat)^n) (by omega)
          rw [Nat.div_lt_iff_lt_mul (by positivity),← e]; exact hRlt
      rw [Nat.mod_eq_of_lt hlt2]
      cases hc' : s.basis c <;> simp only [hc',if_true,if_false,Bool.false_eq_true] at hg ⊢ <;> exact hg
  | succ k ih =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    have hk' : k+2≤(d::tail).length := by simp at hk ⊢; omega
    set row := (dst.drop 1).take ((d::tail).length+1)
    set mr := measurementCount (signedSquareRow c (d::tail) row pad carry)
    obtain ⟨_,_,_,_,hi2,w2,nd2,len2⟩ := row_step c d tail dst pad carry hnd hd hp hc s r A hv hhi hw
    set u := run (signedSquareRow c (d::tail) row pad carry) r s
    have hgood := good_step k c d tail dst pad carry hnd hd hp hc s r A hv hhi hw hg
    have hc2 : (d::tail).length-1≤carry.length := by simp at hc ⊢; omega
    obtain ⟨R',hR'⟩ := ih (d::tail) (dst.drop 2) nd2 len2 hc2 hk' u (r.drop mr) _ rfl hi2 w2 hgood
    refine ⟨(r++List.replicate mr false).take mr++R',?_⟩
    have e1 : rowsK (k+1) (c::d::tail) dst pad carry=
        signedSquareRow c (d::tail) row pad carry++rowsK k (d::tail) (dst.drop 2) pad carry := by
      simp only [rowsK,row]
    have e2 : signedSquareRows (c::d::tail) dst pad carry=
        signedSquareRow c (d::tail) row pad carry++signedSquareRows (d::tail) (dst.drop 2) pad carry := by
      simp only [signedSquareRows,row]
    rw [e1,e2,run_append,run_append,run_take,List.take_left' (padTake_len r mr),
      List.drop_left' (padTake_len r mr),TrimRow.run_padTake _ _ _ _ rfl]
    exact hR'

theorem rowsK_counts (k : Nat) (xs dst pad carry : List Wire) (hk : k+2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (rowsK k xs dst pad carry)+1=toffoliCount (signedSquareRows xs dst pad carry) ∧
    measurementCount (rowsK k xs dst pad carry)+1=measurementCount (signedSquareRows xs dst pad carry) := by
  induction k generalizing xs dst with
  | zero =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    have a := addTop_counts ((d::tail)++pad.take 1) ((dst.drop 1).take ((d::tail).length+1))
      (carry.take (d::tail).length) c (by simp at hd ⊢; omega) (by simp at hd hc ⊢; omega) (by simp; omega)
    simp only [rowsK,rowT,signedSquareRows,signedSquareRow,toffoliCount_append,measurementCount_append]
    omega
  | succ k ih =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    have IH := ih (d::tail) (dst.drop 2) (by simp at hk ⊢; omega) (by simp at hd ⊢; omega) (by simp at hc ⊢; omega)
    simp only [rowsK,signedSquareRows,toffoliCount_append,measurementCount_append]
    omega

/-! ### The TrimRow leaf make with the middle-row top carry copied -/
section MK
open TrimRow

def rows3M (k : Nat) : List Wire → List Wire → List Wire → List Wire → Program
  | c::d::tail, dst, pad, carry =>
      row3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry++rowsK k (d::tail) (dst.drop 2) pad carry
  | xs, dst, pad, carry => signedSquareRows xs dst pad carry

def mkM (k : Nat) (xs dst pad carry : List Wire) : Program :=
  rows3M k xs dst pad carry++signedSquareTop xs dst

theorem mkM_mid (k : Nat) (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hc0 : regValue carry s.basis=0) :
    ∃ R, run (mkM k xs dst pad carry) records s=
      run (rowsK (k+1) xs dst pad carry++signedSquareTop xs dst) R s := by
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
  set Post := xorWhenFalse x0 D++(rowsK k (x1::xt) (dst.drop 2) pad carry++
    signedSquareTop (x0::x1::xt) dst)
  set K := measurementCount (addInPlace (a'::as) (y2::Dt) cs c0)
  have e3 : mkM k (x0::x1::xt) dst pad carry=
      Pre++addDrop ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [mkM,rows3M,row3,Pre,Post,D,List.append_assoc]
  have e2 : rowsK (k+1) (x0::x1::xt) dst pad carry++signedSquareTop (x0::x1::xt) dst=
      Pre++addInPlace ((x1::xt)++pad.take 1) D (carry.take (x1::xt).length) x0++Post := by
    simp only [rowsK,signedSquareRow,Pre,Post,D,List.append_assoc]
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

end MK

theorem exists_append_left (P Q T : Program) (s : State) (r : List Bool)
    (h : ∀ r', ∃ R, run P r' s=run Q R s) : ∃ R, run (P++T) r s=run (Q++T) R s := by
  obtain ⟨R',hR'⟩ := h (r.take (measurementCount P))
  refine ⟨(R'++List.replicate (measurementCount Q) false).take (measurementCount Q)++r.drop (measurementCount P),?_⟩
  rw [run_append,run_append,List.take_left' (padTake_len R' _),List.drop_left' (padTake_len R' _),
    TrimRow.run_padTake _ _ _ _ rfl,hR']

theorem delta_le (c : Bool) (R L : Nat) (h : R<2^L) : delta c R L≤2^L := by
  cases c <;> simp [delta] <;> omega

theorem S_bound (k X n : Nat) (hk : k≤n) (hX : X<2^n) : S k X n+2^n≤2^(k+n) := by
  induction k generalizing X n with
  | zero => simp [S]
  | succ k ih =>
    obtain ⟨n,rfl⟩ : ∃ n', n=n'+1 := ⟨n-1,by omega⟩
    have hX' : X/2<2^n := by rw [pow_succ] at hX; omega
    have IH := ih (X/2) n (by omega) hX'
    have hd := delta_le (X%2==1) (X/2) n hX'
    simp only [S,Nat.add_sub_cancel]
    have e1 : (2:Nat)^(k+1+(n+1))=4*2^(k+n) := by ring_nf
    have e2 : (2:Nat)^(n+1)=2*2^n := by ring
    rw [e1,e2]; omega

theorem good_top (k X : Nat) (hX : X<2^(2*(k+1)+1)) : Good (k+1) X (2*(k+1)+1) 0 := by
  rw [Good_iff,Nat.zero_add,show 2*(k+1)+1-1-(k+1)=k+1 by omega]
  apply mid_RC (k+1) X (by omega) hX
  have hb := S_bound (k+1) X (2*(k+1)+1) (by omega) hX
  have e : (2:Nat)^(k+1)*((4:Nat)^(k+1)*2)=2^(k+1+(2*(k+1)+1)) := by
    rw [show (4:Nat)=2^2 by norm_num,← pow_mul]; ring
  rw [Nat.div_div_eq_div_mul,Nat.div_lt_iff_lt_mul (by positivity),e]
  omega

/-- The middle-row make of an odd `(2k+3)`-bit leaf is a record-renaming of the TrimRow leaf. -/
theorem mkM_exists (k : Nat) (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : xs.length=2*(k+1)+1)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hc0 : regValue carry s.basis=0) (hp0 : regValue pad s.basis=0) :
    ∃ R, run (mkM k xs dst pad carry) records s=
      run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) R s := by
  obtain ⟨R1,h1⟩ := mkM_mid k xs dst pad carry hn (by omega) hd hp hc s records h0 hc0
  have h2 : ∀ r', ∃ R, run (rowsK (k+1) xs dst pad carry) r' s=run (signedSquareRows xs dst pad carry) R s := by
    intro r'
    apply rowsK_exists (k+1) xs dst pad carry hn hd hp hc (by omega) s r' 0 h0
    · apply (regValue_zero _ _).mpr; intro q hq
      exact (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq)
    · rw [regValue_append,hp0,hc0]; simp
    · rw [hx]; apply good_top; rw [← hx]; exact regValue_lt _ _
  obtain ⟨R2,h3⟩ := exists_append_left _ _ (signedSquareTop xs dst) s R1 h2
  exact ⟨R2,h1.trans h3⟩

theorem mkM_counts (k : Nat) (xs dst pad carry : List Wire) (hx : xs.length=2*(k+1)+1)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (mkM k xs dst pad carry)+1=toffoliCount (TrimRow.mk xs dst pad carry) ∧
    measurementCount (mkM k xs dst pad carry)+1=measurementCount (TrimRow.mk xs dst pad carry) := by
  obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
    match xs, hx with
    | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
  have r := rowsK_counts k (d::tail) (dst.drop 2) pad carry (by simp at hx ⊢; omega) (by simp at hd ⊢; omega) hp
    (by simp at hc ⊢; omega)
  simp only [mkM,rows3M,TrimRow.mk,TrimRow.rows3,toffoliCount_append,measurementCount_append]
  omega

/-! ### Clear side: the same carry, recomputed by the measured inverse -/

def rowClearT (c : Wire) (xs D pad carry : List Wire) : Program :=
  xorWhenFalse c D++(notRegister D++(addTop (xs++pad.take 1) D (carry.take xs.length) c++
    (notRegister D++xorWhenFalse c (D.take xs.length))))

def rowsClearK : Nat → List Wire → List Wire → List Wire → List Wire → Program
  | 0, c::d::tail, dst, pad, carry =>
      signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++
        rowClearT c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry
  | k+1, c::d::tail, dst, pad, carry =>
      rowsClearK k (d::tail) (dst.drop 2) pad carry++
        signedSquareRowClear c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry
  | _, xs, dst, pad, carry => signedSquareRowsClear xs dst pad carry

theorem div_one_of (m N : Nat) (h1 : N≤m) (h2 : m<2*N) : m/N=1 :=
  Nat.div_eq_of_lt_le (by simpa using h1) (by omega)

theorem clear_true (W R N : Nat) (hW : W<N) (hR : R<N) :
    (R+(2*N-1-(W+R+1))%N+1)/N=(R+W+1)/N := by
  by_cases h : R+W+1<N
  · rw [show 2*N-1-(W+R+1)=(N-1-(W+R+1))+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt (by omega),Nat.div_eq_of_lt h]
  · rw [Nat.mod_eq_of_lt (by omega),div_one_of _ _ (by omega) (by omega),div_one_of _ _ (by omega) (by omega)]

theorem clear_false (W R N : Nat) (hW : W<N) (hR : R<N) :
    (R+(W+N-R)%N)/N=(R+(N-1-W))/N := by
  by_cases h : R≤W
  · rw [show W+N-R=(W-R)+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt (by omega),Nat.div_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega),div_one_of _ _ (by omega) (by omega),div_one_of _ _ (by omega) (by omega)]

theorem rowsClearK_exists (k : Nat) (xs dst pad carry : List Wire)
    (hnd : (xs++dst++pad++carry).Nodup) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) (hk : k+2≤xs.length)
    (s : State) (m0 r : List Bool) (A : Nat) (hv : regValue dst s.basis=A)
    (hhi : regValue (dst.drop xs.length) s.basis=0)
    (hw : regValue (pad++carry) s.basis=0) (hg : Good k (regValue xs s.basis) xs.length A) :
    ∃ R, run (rowsClearK k xs dst pad carry) r (run (signedSquareRows xs dst pad carry) m0 s)=
      run (signedSquareRowsClear xs dst pad carry) R (run (signedSquareRows xs dst pad carry) m0 s) := by
  induction k generalizing xs dst s m0 r A with
  | succ k ih =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    have hk' : k+2≤(d::tail).length := by simp at hk ⊢; omega
    set row := (dst.drop 1).take ((d::tail).length+1)
    set mr := measurementCount (signedSquareRow c (d::tail) row pad carry)
    obtain ⟨_,_,_,_,hi2,w2,nd2,len2⟩ := row_step c d tail dst pad carry hnd hd hp hc s (m0.take mr) A hv hhi hw
    have hgood := good_step k c d tail dst pad carry hnd hd hp hc s (m0.take mr) A hv hhi hw hg
    set u := run (signedSquareRow c (d::tail) row pad carry) (m0.take mr) s
    have hc2 : (d::tail).length-1≤carry.length := by simp at hc ⊢; omega
    have e0 : run (signedSquareRows (c::d::tail) dst pad carry) m0 s=
        run (signedSquareRows (d::tail) (dst.drop 2) pad carry) (m0.drop mr) u := by
      rw [show signedSquareRows (c::d::tail) dst pad carry=
        signedSquareRow c (d::tail) row pad carry++signedSquareRows (d::tail) (dst.drop 2) pad carry by
        simp only [signedSquareRows,row],run_append]
    rw [e0]
    have e1 : rowsClearK (k+1) (c::d::tail) dst pad carry=
        rowsClearK k (d::tail) (dst.drop 2) pad carry++signedSquareRowClear c (d::tail) row pad carry := by
      simp only [rowsClearK,row]
    have e2 : signedSquareRowsClear (c::d::tail) dst pad carry=
        signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++signedSquareRowClear c (d::tail) row pad carry := by
      simp only [signedSquareRowsClear,row]
    rw [e1,e2]
    apply exists_append_left
    intro r'
    exact ih (d::tail) (dst.drop 2) nd2 len2 hc2 hk' u (m0.drop mr) r' _ rfl hi2 w2 hgood
  | zero =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    set rest := d::tail
    set L := rest.length
    set row := (dst.drop 1).take (L+1)
    set mr := measurementCount (signedSquareRow c rest row pad carry)
    obtain ⟨_,keep,rowOut,_,hi2,w2,nd2,len2⟩ := row_step c d tail dst pad carry hnd hd hp hc s (m0.take mr) A hv hhi hw
    set u := run (signedSquareRow c rest row pad carry) (m0.take mr) s
    have hc2 : rest.length-1≤carry.length := by simp [rest] at hc ⊢; omega
    set S := run (signedSquareRows rest (dst.drop 2) pad carry) (m0.drop mr) u
    have e0 : run (signedSquareRows (c::rest) dst pad carry) m0 s=S := by
      rw [show signedSquareRows (c::rest) dst pad carry=
        signedSquareRow c rest row pad carry++signedSquareRows rest (dst.drop 2) pad carry by
        simp only [signedSquareRows,row,L,rest],run_append]
    rw [e0]
    -- the clear of the deeper rows restores `u`
    have hRT : ∀ r1, run (signedSquareRowsClear rest (dst.drop 2) pad carry) r1 S=u := by
      intro r1
      set mR := measurementCount (signedSquareRows rest (dst.drop 2) pad carry)
      have rt := signedSquareRows_roundtrip rest (dst.drop 2) pad carry nd2 len2 (Or.inr hp) hc2 u
        ((m0.drop mr++List.replicate mR false).take mR++r1) _ rfl hi2 w2
      simp only at rt
      rw [run_append,List.take_left' (padTake_len _ _),List.drop_left' (padTake_len _ _),
        TrimRow.run_padTake _ _ _ _ rfl] at rt
      cases hS : run (signedSquareRowsClear rest (dst.drop 2) pad carry) r1 S
      cases hu : u
      rw [hS,hu] at rt
      simp only at rt
      rw [rt.1,rt.2]
    have rowSub : row.Sublist dst := (List.take_sublist _ (dst.drop 1)).trans (List.drop_sublist 1 dst)
    have rowLen : row.length=L+1 := by simp [row,L,rest] at hd ⊢; omega
    have cnt := fun w => List.nodup_iff_count.mp hnd w
    have rowN : row.Nodup := rowSub.nodup (by
      apply List.nodup_iff_count.mpr; intro w; have h := cnt w
      simp only [List.count_cons,List.count_append] at h; omega)
    have cRow : c∉row := by
      intro h; have h1 := cnt c; have h2 := List.count_pos_iff.mpr (rowSub.subset h)
      simp only [List.count_cons,List.count_append] at h1 h2; simp at h1; omega
    set src := rest++pad.take 1
    set cy := carry.take L
    set Pre := signedSquareRowsClear rest (dst.drop 2) pad carry++(xorWhenFalse c row++notRegister row)
    set Post := notRegister row++xorWhenFalse c (row.take L)
    have e1 : rowsClearK 0 (c::rest) dst pad carry=Pre++addTop src row cy c++Post := by
      simp only [rowsClearK,rowClearT,Pre,Post,src,cy,row,L,rest,List.append_assoc]
    have e2 : signedSquareRowsClear (c::rest) dst pad carry=Pre++addInPlace src row cy c++Post := by
      simp only [signedSquareRowsClear,signedSquareRowClear,Pre,Post,src,cy,row,L,rest,List.append_assoc]
    have srcLen : src.length=L+1 := by simp [src,L]; omega
    have cyLen : cy.length=L := by simp [cy]; simp at hc; omega
    have ndadd : (c::(src++row++cy)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w
      have h := cnt w
      have t1 := rowSub.count_le w
      have t2 := (List.take_sublist 1 pad).count_le w
      have t3 := (List.take_sublist L carry).count_le w
      simp only [src,cy,List.count_cons,List.count_append] at h t1 t2 t3 ⊢
      split_ifs at h ⊢ <;> omega
    have cnts := addTop_counts src row cy c (by omega) (by omega) (by simp [srcLen,L,rest])
    rw [e1,e2]
    apply TrimRow.glue _ _ _ _ 0 (Nat.zero_le _) cnts.2.symm
    intro rP rX
    have m0Pre : measurementCount (xorWhenFalse c row++notRegister row)=0 := by
      rw [measurementCount_append,(notRegister_counts row).2]; simp [measurementCount]
    have hv1 : run Pre rP S=run (xorWhenFalse c row++notRegister row) [] u := by
      simp only [Pre]
      rw [run_append,hRT,← run_take,m0Pre,List.take_zero]
    rw [hv1,run_append,List.take_nil,List.drop_nil,
      xorWhenFalse_correct c row rowN cRow u [],notRegister_correct row rowN _ []]
    rw [show TrimRow.insF 0 rX=false::rX by simp [TrimRow.insF]]
    set st : BasisState := fun w => if w∈row then !xorFalseBasis c row u.basis w else xorFalseBasis c row u.basis w
    have stOut (q : Wire) (hq : q∉row) : st q=u.basis q := by
      simp only [st,xorFalseBasis,hq,if_false]
    have keepS (q : Wire) (hq : q∉row) : u.basis q=s.basis q := keep q hq
    apply addTop_run src row cy c ndadd (by omega) (by omega) (by simp [srcLen,L,rest])
    · intro q hq
      have qc : q∈carry := List.mem_of_mem_take hq
      have qr : q∉row := by
        intro h; have h1 := cnt q; have h2 := List.count_pos_iff.mpr (rowSub.subset h)
        have h3 := List.count_pos_iff.mpr qc
        simp only [List.count_cons,List.count_append] at h1; omega
      change st q=false
      rw [stOut q qr]
      exact (regValue_zero _ _).mp w2 q (by simp [qc])
    · change TopOK src row (st c) st
      have stc : st c=s.basis c := (stOut c cRow).trans (keepS c cRow)
      rw [stc]
      apply TopOK_of_value src row _ st (by omega) (by simp [srcLen,L,rest])
      rw [srcLen,show L+1-1=L by omega,show L+1-2=L-1 by omega]
      have restOut (q : Wire) (hq : q∈rest) : q∉row := by
        intro h; have h1 := cnt q; have h2 := List.count_pos_iff.mpr (rowSub.subset h)
        have h3 := List.count_pos_iff.mpr hq
        simp only [List.count_cons,List.count_append] at h1 h3; omega
      have hR : regValue rest st=regValue rest s.basis := regValue_congr _ _ _ (fun q hq => by
        rw [stOut q (restOut q hq),keepS q (restOut q hq)])
      have hP0 : regValue (pad.take 1) st=0 := by
        apply (regValue_zero _ _).mpr; intro q hq
        have qp : q∈pad := List.mem_of_mem_take hq
        have qr : q∉row := by
          intro h; have h1 := cnt q; have h2 := List.count_pos_iff.mpr (rowSub.subset h)
          have h3 := List.count_pos_iff.mpr qp
          simp only [List.count_cons,List.count_append] at h1; omega
        rw [stOut q qr]
        exact (regValue_zero _ _).mp w2 q (by simp [qp])
      have hsrc : regValue src st=regValue rest s.basis := by
        simp only [src]; rw [regValue_append,hR,hP0]; simp
      rw [hsrc]
      have hRlt : regValue rest s.basis<2^L := regValue_lt _ _
      rw [Nat.mod_eq_of_lt hRlt]
      -- the framed window after the row
      have uc : u.basis c=s.basis c := keepS c cRow
      have hwin : regValue row st=if s.basis c then 2^(L+1)-1-regValue row u.basis else regValue row u.basis := by
        cases hc' : s.basis c
        · simp only [Bool.false_eq_true,if_false]
          apply regValue_congr; intro q hq
          simp only [st,xorFalseBasis,hq,if_true,uc,hc']; simp
        · simp only [if_true]
          rw [← rowLen,← regValue_complement]
          apply regValue_congr; intro q hq
          simp only [st,xorFalseBasis,hq,if_true,uc,hc']; simp
      have hV : regValue row s.basis=A/2 := by
        simpa [row] using signed_row_slice_value dst (L+1) A (by simp at hd; omega) s.basis hv (by simpa [L,rest] using hhi)
      have hA : A<2^(L+1) := by
        have split := regValue_append (dst.take (L+1)) (dst.drop (L+1)) s.basis
        rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by simp at hd; omega),
          show regValue (dst.drop (L+1)) s.basis=0 by simpa [L,rest] using hhi,Nat.mul_zero,Nat.add_zero,hv] at split
        have b := regValue_lt (dst.take (L+1)) s.basis
        rw [List.length_take,Nat.min_eq_left (by simp at hd; omega)] at b
        rw [split]; exact b
      have hW : A/2<2^L := by rw [pow_succ] at hA; omega
      have hX : regValue (c::rest) s.basis=(s.basis c).toNat+2*regValue rest s.basis := regValue_cons2 _ _ _
      simp only [Good,RC] at hg
      rw [hX,show (c::rest).length-1=L by simp [L]] at hg
      have e2 : ((s.basis c).toNat+2*regValue rest s.basis)/2=regValue rest s.basis := by
        cases s.basis c <;> simp <;> omega
      have e3 : (((s.basis c).toNat+2*regValue rest s.basis)%2==1)=s.basis c := by
        cases h : s.basis c <;> simp [h] <;> omega
      rw [e3,e2] at hg
      have hlt2 : regValue rest s.basis/2^(L-1)<2 := by
        rcases Nat.eq_zero_or_pos L with h0|hpos
        · simp [L,rest] at h0
        · have e : (2:Nat)^L=2*2^(L-1) := by
            rw [← pow_succ']; exact congrArg (fun n => (2:Nat)^n) (by omega)
          rw [Nat.div_lt_iff_lt_mul (by positivity),← e]; exact hRlt
      rw [Nat.mod_eq_of_lt hlt2,hwin,rowOut]
      have hN : (2:Nat)^(L+1)=2*2^L := by ring
      rw [hN]
      simp only [signedDeltaValue] at ⊢
      cases hc' : s.basis c
      · simp only [hc',Bool.false_eq_true,if_false,Bool.toNat_false,Nat.add_zero] at hg ⊢
        have e : A/2+(2^(d::tail).length-regValue (d::tail) s.basis)=A/2+2^L-regValue rest s.basis := by
          show A/2+(2^L-regValue rest s.basis)=_; omega
        rw [e,clear_false (A/2) (regValue rest s.basis) (2^L) hW hRlt]; exact hg
      · simp only [hc',if_true,Bool.toNat_true] at hg ⊢
        have e : A/2+(regValue (d::tail) s.basis+1)=A/2+regValue rest s.basis+1 := by
          show A/2+(regValue rest s.basis+1)=_; omega
        rw [e,clear_true (A/2) (regValue rest s.basis) (2^L) hW hRlt]; exact hg

theorem rowsClearK_counts (k : Nat) (xs dst pad carry : List Wire) (hk : k+2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (rowsClearK k xs dst pad carry)+1=toffoliCount (signedSquareRowsClear xs dst pad carry) ∧
    measurementCount (rowsClearK k xs dst pad carry)+1=measurementCount (signedSquareRowsClear xs dst pad carry) := by
  induction k generalizing xs dst with
  | zero =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    have a := addTop_counts ((d::tail)++pad.take 1) ((dst.drop 1).take ((d::tail).length+1))
      (carry.take (d::tail).length) c (by simp at hd ⊢; omega) (by simp at hd hc ⊢; omega) (by simp; omega)
    simp only [rowsClearK,rowClearT,signedSquareRowsClear,signedSquareRowClear,toffoliCount_append,
      measurementCount_append]
    omega
  | succ k ih =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    have IH := ih (d::tail) (dst.drop 2) (by simp at hk ⊢; omega) (by simp at hd ⊢; omega) (by simp at hc ⊢; omega)
    simp only [rowsClearK,signedSquareRowsClear,toffoliCount_append,measurementCount_append]
    omega

theorem cx_twice (x z : Wire) (hxz : x≠z) (t : State) : run [.CX x z] [] (run [.CX x z] [] t)=t := by
  cases t with
  | mk ph b =>
    simp only [run]
    congr 1
    funext w
    by_cases hw : w=z
    · (subst hw; simp [writeBit,Function.update,hxz]) <;> (cases b w <;> cases b x <;> simp)
    · simp [writeBit,Function.update,hw]

theorem top_twice (xs dst : List Wire) (hn : (xs++dst).Nodup) (t : State) :
    run (signedSquareTop xs dst) [] (run (signedSquareTop xs dst) [] t)=t := by
  induction xs generalizing dst with
  | nil => rfl
  | cons x xs ih =>
    match xs, dst with
    | [], [] => rfl
    | [], [_] => rfl
    | [], y::z::rest =>
      simp only [signedSquareTop]
      apply cx_twice
      intro e; subst e
      have h := List.nodup_iff_count.mp hn x
      simp only [List.count_cons,List.count_append,List.count_nil] at h; simp at h <;> split_ifs at h <;> omega
    | x'::xs', [] => simp [signedSquareTop] <;> rfl
    | x'::xs', [_] => simp [signedSquareTop] <;> rfl
    | x'::xs', _::_::dst' =>
      simp only [signedSquareTop]
      apply ih
      apply List.nodup_iff_count.mpr; intro w
      have h := List.nodup_iff_count.mp hn w
      simp only [List.count_cons,List.count_append] at h ⊢
      split_ifs at h ⊢ <;> omega

theorem top_m0 (xs dst : List Wire) : measurementCount (signedSquareTop xs dst)=0 := by
  induction xs generalizing dst with
  | nil => rfl
  | cons x xs ih =>
    match xs, dst with
    | [], [] => rfl
    | [], [_] => rfl
    | [], _::_::_ => rfl
    | _::_, [] => rfl
    | _::_, [_] => rfl
    | x'::xs', _::_::dst' => simp only [signedSquareTop]; exact ih _

/-! ### The TrimRow leaf clear with the middle-row top carry copied -/

def rowsClear3M (k : Nat) : List Wire → List Wire → List Wire → List Wire → Program
  | c::d::tail, dst, pad, carry =>
      rowsClearK k (d::tail) (dst.drop 2) pad carry++
        TrimRow.rowClear3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry
  | xs, dst, pad, carry => signedSquareRowsClear xs dst pad carry

def clM (k : Nat) (xs dst pad carry : List Wire) : Program :=
  signedSquareTop xs dst++rowsClear3M k xs dst pad carry

/-- On the state produced by the plain make from a clean base, the middle-row clear is a record-renaming of
the TrimRow clear. -/
theorem clM_exists (k : Nat) (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : xs.length=2*(k+1)+1)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (base : State) (h0 : regValue dst base.basis=0)
    (hc0 : regValue carry base.basis=0) (hp0 : regValue pad base.basis=0) (records : List Bool) :
    ∃ R, run (clM k xs dst pad carry) records
        (run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) [] base)=
      run (TrimRow.cl xs dst pad carry) R
        (run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) [] base) := by
  obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
    match xs, hx with
    | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
  have hn2 : ((c::d::tail)++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [List.count_append] at h ⊢; omega
  set row := (dst.drop 1).take ((d::tail).length+1)
  set u := run (signedSquareRow c (d::tail) row pad carry) [] base
  have hrows : run (signedSquareRows (c::d::tail) dst pad carry) [] base=
      run (signedSquareRows (d::tail) (dst.drop 2) pad carry) [] u := by
    rw [show signedSquareRows (c::d::tail) dst pad carry=
      signedSquareRow c (d::tail) row pad carry++signedSquareRows (d::tail) (dst.drop 2) pad carry by
      simp only [signedSquareRows,row],run_append]
    simp only [List.take_nil,List.drop_nil]; rfl
  have hhi : regValue (dst.drop (c::d::tail).length) base.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    exact (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq)
  have hw : regValue (pad++carry) base.basis=0 := by rw [regValue_append,hp0,hc0]; simp
  have hg := good_top k (regValue (c::d::tail) base.basis) (by rw [← hx]; exact regValue_lt _ _)
  rw [← hx] at hg
  obtain ⟨_,_,_,_,hi2,w2,nd2,len2⟩ := row_step c d tail dst pad carry hn hd hp hc base [] 0 h0 hhi hw
  have hgood := good_step k c d tail dst pad carry hn hd hp hc base [] 0 h0 hhi hw hg
  have hc2 : (d::tail).length-1≤carry.length := by simp at hc ⊢; omega
  have hk' : k+2≤(d::tail).length := by simp at hx ⊢; omega
  set t := run (signedSquareRows (c::d::tail) dst pad carry++signedSquareTop (c::d::tail) dst) [] base
  have ht : run (signedSquareTop (c::d::tail) dst) [] t=run (signedSquareRows (d::tail) (dst.drop 2) pad carry) [] u := by
    simp only [t]
    rw [run_append]; simp only [List.take_nil,List.drop_nil]
    rw [top_twice _ _ hn2,hrows]
  have split (X : Program) (rr : List Bool) :
      run (signedSquareTop (c::d::tail) dst++X) rr t=run X rr (run (signedSquareTop (c::d::tail) dst) [] t) := by
    rw [run_append,top_m0]; simp only [List.take_zero,List.drop_zero]
  have e1 : clM k (c::d::tail) dst pad carry=signedSquareTop (c::d::tail) dst++
      (rowsClearK k (d::tail) (dst.drop 2) pad carry++TrimRow.rowClear3 c (d::tail) row pad carry) := by
    simp only [clM,rowsClear3M,row]
  have e2 : TrimRow.cl (c::d::tail) dst pad carry=signedSquareTop (c::d::tail) dst++
      (signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++TrimRow.rowClear3 c (d::tail) row pad carry) := by
    simp only [TrimRow.cl,TrimRow.rowsClear3,row]
  rw [e1,e2]
  obtain ⟨R,hR⟩ := exists_append_left (rowsClearK k (d::tail) (dst.drop 2) pad carry)
    (signedSquareRowsClear (d::tail) (dst.drop 2) pad carry) (TrimRow.rowClear3 c (d::tail) row pad carry)
    (run (signedSquareTop (c::d::tail) dst) [] t) records (by
      intro r'; rw [ht]
      exact rowsClearK_exists k (d::tail) (dst.drop 2) pad carry nd2 len2 hp hc2 hk' u [] r' _ rfl hi2 w2 hgood)
  exact ⟨R,by rw [split,split,hR]⟩

theorem clM_counts (k : Nat) (xs dst pad carry : List Wire) (hx : xs.length=2*(k+1)+1)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (clM k xs dst pad carry)+1=toffoliCount (TrimRow.cl xs dst pad carry) ∧
    measurementCount (clM k xs dst pad carry)+1=measurementCount (TrimRow.cl xs dst pad carry) := by
  obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
    match xs, hx with
    | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
  have r := rowsClearK_counts k (d::tail) (dst.drop 2) pad carry (by simp at hx ⊢; omega) (by simp at hd ⊢; omega) hp
    (by simp at hc ⊢; omega)
  simp only [clM,rowsClear3M,TrimRow.cl,TrimRow.rowsClear3,toffoliCount_append,measurementCount_append]
  omega

/-! ### Shape lemmas: exactly one ripple adder is replaced -/

theorem addTop_side (x y cy : List Wire) (cin : Wire) :
    wires (addTop x y cy cin)⊆wires (addInPlace x y cy cin) ∧
    Challenge.gateSlots (addTop x y cy cin)≤Challenge.gateSlots (addInPlace x y cy cin) ∧
    (GatePhysical (addInPlace x y cy cin) → GatePhysical (addTop x y cy cin)) := by
  induction x generalizing y cy cin with
  | nil => simp [addTop]
  | cons a x ih =>
    match x, y, cy with
    | [], _, _ => simp [addTop]
    | [a'], [], _ => simp [addTop]
    | [a'], [b], _ => simp [addTop]
    | [a'], [b,b'], [] => simp [addTop]
    | [a'], [b,b'], c::cs =>
      simp only [addTop]
      exact ⟨TrimRow.addDrop_wires_gen _ _ _ _,TrimRow.addDrop_slots _ _ _ _,TrimRow.addDrop_physical_gen _ _ _ _⟩
    | [a'], b::b'::b''::bs, _ => simp [addTop]
    | a'::a''::as, [], _ => simp [addTop]
    | a'::a''::as, [_], _ => simp [addTop]
    | a'::a''::as, [_,_], _ => simp [addTop]
    | a'::a''::as, b::b'::b''::bs, [] => simp [addTop]
    | a'::a''::as, b::b'::b''::bs, c::cs =>
      obtain ⟨hw,hs,hp⟩ := ih (b'::b''::bs) cs c
      simp only [addTop,addInPlace,wires_append,Challenge.gateSlots_append,gatePhysical_append]
      refine ⟨?_,?_,?_⟩
      · exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (subset_refl _) hw)
          (subset_refl _)) (subset_refl _)
      · omega
      · intro h; exact ⟨⟨⟨h.1.1.1,hp h.1.1.2⟩,h.1.2⟩,h.2⟩

theorem rowsK_form (k : Nat) (xs dst pad carry : List Wire) (hk : k+2≤xs.length) :
    ∃ A B x y cy c, rowsK k xs dst pad carry=A++addTop x y cy c++B ∧
      signedSquareRows xs dst pad carry=A++addInPlace x y cy c++B := by
  induction k generalizing xs dst with
  | zero =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    let D := (dst.drop 1).take ((d::tail).length+1)
    exact ⟨xorWhenFalse c (D.take (d::tail).length),
      xorWhenFalse c D++signedSquareRows (d::tail) (dst.drop 2) pad carry,
      (d::tail)++pad.take 1,D,carry.take (d::tail).length,c,
      by simp only [rowsK,rowT,D,List.append_assoc],
      by simp only [signedSquareRows,signedSquareRow,D,List.append_assoc]⟩
  | succ k ih =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    obtain ⟨A,B,x,y,cy,c',e1,e2⟩ := ih (d::tail) (dst.drop 2) (by simp at hk ⊢; omega)
    exact ⟨signedSquareRow c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry++A,B,x,y,cy,c',
      by simp only [rowsK,e1,List.append_assoc],by simp only [signedSquareRows,e2,List.append_assoc]⟩

theorem rowsClearK_form (k : Nat) (xs dst pad carry : List Wire) (hk : k+2≤xs.length) :
    ∃ A B x y cy c, rowsClearK k xs dst pad carry=A++addTop x y cy c++B ∧
      signedSquareRowsClear xs dst pad carry=A++addInPlace x y cy c++B := by
  induction k generalizing xs dst with
  | zero =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    let D := (dst.drop 1).take ((d::tail).length+1)
    exact ⟨signedSquareRowsClear (d::tail) (dst.drop 2) pad carry++(xorWhenFalse c D++notRegister D),
      notRegister D++xorWhenFalse c (D.take (d::tail).length),
      (d::tail)++pad.take 1,D,carry.take (d::tail).length,c,
      by simp only [rowsClearK,rowClearT,D,List.append_assoc],
      by simp only [signedSquareRowsClear,signedSquareRowClear,D,List.append_assoc]⟩
  | succ k ih =>
    obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
      match xs, hk with
      | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
    obtain ⟨A,B,x,y,cy,c',e1,e2⟩ := ih (d::tail) (dst.drop 2) (by simp at hk ⊢; omega)
    exact ⟨A,B++signedSquareRowClear c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry,x,y,cy,c',
      by simp only [rowsClearK,e1,List.append_assoc],
      by simp only [signedSquareRowsClear,e2,List.append_assoc]⟩

theorem mkM_form (k : Nat) (xs dst pad carry : List Wire) (hx : xs.length=2*(k+1)+1) :
    ∃ A B x y cy c, mkM k xs dst pad carry=A++addTop x y cy c++B ∧
      TrimRow.mk xs dst pad carry=A++addInPlace x y cy c++B := by
  obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
    match xs, hx with
    | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
  obtain ⟨A,B,x,y,cy,c',e1,e2⟩ := rowsK_form k (d::tail) (dst.drop 2) pad carry (by simp at hx ⊢; omega)
  exact ⟨TrimRow.row3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry++A,
    B++signedSquareTop (c::d::tail) dst,x,y,cy,c',
    by simp only [mkM,rows3M,e1,List.append_assoc],
    by simp only [TrimRow.mk,TrimRow.rows3,e2,List.append_assoc]⟩

theorem clM_form (k : Nat) (xs dst pad carry : List Wire) (hx : xs.length=2*(k+1)+1) :
    ∃ A B x y cy c, clM k xs dst pad carry=A++addTop x y cy c++B ∧
      TrimRow.cl xs dst pad carry=A++addInPlace x y cy c++B := by
  obtain ⟨c,d,tail,rfl⟩ : ∃ c d tail, xs=c::d::tail := by
    match xs, hx with
    | c::d::tail, _ => exact ⟨c,d,tail,rfl⟩
  obtain ⟨A,B,x,y,cy,c',e1,e2⟩ := rowsClearK_form k (d::tail) (dst.drop 2) pad carry (by simp at hx ⊢; omega)
  exact ⟨signedSquareTop (c::d::tail) dst++A,
    B++TrimRow.rowClear3 c (d::tail) ((dst.drop 1).take ((d::tail).length+1)) pad carry,x,y,cy,c',
    by simp only [clM,rowsClear3M,e1,List.append_assoc],
    by simp only [TrimRow.cl,TrimRow.rowsClear3,e2,List.append_assoc]⟩

theorem side_of_form (P Q A B : Program) (x y cy : List Wire) (c : Wire)
    (e1 : P=A++addTop x y cy c++B) (e2 : Q=A++addInPlace x y cy c++B) :
    wires P⊆wires Q ∧ Challenge.gateSlots P≤Challenge.gateSlots Q ∧ (GatePhysical Q → GatePhysical P) := by
  obtain ⟨hw,hs,hp⟩ := addTop_side x y cy c
  subst e1 e2
  simp only [wires_append,Challenge.gateSlots_append,gatePhysical_append]
  refine ⟨Finset.union_subset_union (Finset.union_subset_union (subset_refl _) hw) (subset_refl _),by omega,?_⟩
  intro h; exact ⟨⟨h.1.1,hp h.1.2⟩,h.2⟩

/-! ### Parity-adaptive leaf: odd leaves (at least 5 bits) get the middle-row trim -/

def oddLeaf (n : Nat) : Prop := 5≤n ∧ n%2=1

instance (n : Nat) : Decidable (oddLeaf n) := inferInstanceAs (Decidable (5≤n ∧ n%2=1))

def par (n : Nat) : Nat := if oddLeaf n then 1 else 0

def mkP (xs dst pad carry : List Wire) : Program :=
  if oddLeaf xs.length then mkM (xs.length/2-1) xs dst pad carry else TrimRow.mk xs dst pad carry

def clP (xs dst pad carry : List Wire) : Program :=
  if oddLeaf xs.length then clM (xs.length/2-1) xs dst pad carry else TrimRow.cl xs dst pad carry

theorem odd_len (n : Nat) (h : oddLeaf n) : n=2*(n/2-1+1)+1 := by unfold oddLeaf at h; omega

theorem mkP_exists (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    ∃ R, run (mkP xs dst pad carry) records s=
      run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) R s := by
  unfold mkP
  split_ifs with h
  · exact mkM_exists _ xs dst pad carry hn (odd_len _ h) hd hp hc s records h0 hc0 hp0
  · exact TrimRow.mk_exists xs dst pad carry hn hx hd hp hc s records h0 hc0

theorem clP_exists (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (base : State) (h0 : regValue dst base.basis=0)
    (hp0 : regValue pad base.basis=0) (hc0 : regValue carry base.basis=0) (records : List Bool) :
    ∃ R, run (clP xs dst pad carry) records
        (run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) [] base)=
      run (TrimRow.cl xs dst pad carry) R
        (run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) [] base) := by
  unfold clP
  split_ifs with h
  · exact clM_exists _ xs dst pad carry hn (odd_len _ h) hd hp hc base h0 hc0 hp0 records
  · exact ⟨records,rfl⟩

theorem P_counts (xs dst pad carry : List Wire) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    (toffoliCount (mkP xs dst pad carry)+par xs.length=toffoliCount (TrimRow.mk xs dst pad carry) ∧
      measurementCount (mkP xs dst pad carry)+par xs.length=measurementCount (TrimRow.mk xs dst pad carry)) ∧
    (toffoliCount (clP xs dst pad carry)+par xs.length=toffoliCount (TrimRow.cl xs dst pad carry) ∧
      measurementCount (clP xs dst pad carry)+par xs.length=measurementCount (TrimRow.cl xs dst pad carry)) := by
  unfold mkP clP par
  split_ifs with h
  · exact ⟨mkM_counts _ xs dst pad carry (odd_len _ h) hd hp hc,clM_counts _ xs dst pad carry (odd_len _ h) hd hp hc⟩
  · simp

theorem P_side (xs dst pad carry : List Wire) :
    (wires (mkP xs dst pad carry)⊆wires (TrimRow.mk xs dst pad carry) ∧
      Challenge.gateSlots (mkP xs dst pad carry)≤Challenge.gateSlots (TrimRow.mk xs dst pad carry) ∧
      (GatePhysical (TrimRow.mk xs dst pad carry) → GatePhysical (mkP xs dst pad carry))) ∧
    (wires (clP xs dst pad carry)⊆wires (TrimRow.cl xs dst pad carry) ∧
      Challenge.gateSlots (clP xs dst pad carry)≤Challenge.gateSlots (TrimRow.cl xs dst pad carry) ∧
      (GatePhysical (TrimRow.cl xs dst pad carry) → GatePhysical (clP xs dst pad carry))) := by
  unfold mkP clP
  split_ifs with h
  · obtain ⟨A,B,x,y,cy,c,e1,e2⟩ := mkM_form _ xs dst pad carry (odd_len _ h)
    obtain ⟨A',B',x',y',cy',c',e1',e2'⟩ := clM_form _ xs dst pad carry (odd_len _ h)
    exact ⟨side_of_form _ _ _ _ _ _ _ _ e1 e2,side_of_form _ _ _ _ _ _ _ _ e1' e2'⟩
  · exact ⟨⟨subset_refl _,le_refl _,id⟩,⟨subset_refl _,le_refl _,id⟩⟩

theorem par_32 : par 32=0 := by decide
theorem par_33 : par 33=1 := by decide
theorem par_34 : par 34=0 := by decide
theorem par_65 : par 65=1 := by decide

end ECDSAAdd.Entrant.TrimMid

end

-- ===== merged module ECDSAAdd.Submission.Entrant.TrimMid65 =====
section

/-! TrimMid65: the middle-row top-carry trim (`TrimMid`) applied to the odd-width plain
`TrimSquare3.tsq3/tsqc3` leaves (the 65-bit `kg` squares).

`tsqM` is `tsq3` with its signed rows replaced by `TrimMid.mkM` (first-row lowest carry and middle-row
top carry both copies); `tsqcM` is `tsqc3` with `top ++ rowsClear3` replaced by `TrimMid.clM`.
Both fall back to `tsq3/tsqc3` for leaves that are not odd with at least 5 bits. -/

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.TrimMid
open ECDSAAdd ECDSAAdd.Arithmetic RecordedQuantum

/-! ### The two copies of the first-row definitions agree -/

theorem addDrop_eq (x y c : List Wire) (cin : Wire) :
    TrimSquare3.addDrop x y c cin=TrimRow.addDrop x y c cin := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases c with _|⟨c,cs⟩ <;> rfl

theorem rows3_eq (xs dst pad carry : List Wire) :
    TrimSquare3.rows3 xs dst pad carry=TrimRow.rows3 xs dst pad carry := by
  rcases xs with _|⟨c,_|⟨d,tail⟩⟩
  · rfl
  · rfl
  · simp only [TrimSquare3.rows3,TrimRow.rows3,TrimSquare3.row3,TrimRow.row3,addDrop_eq]

theorem rowsClear3_eq (xs dst pad carry : List Wire) :
    TrimSquare3.rowsClear3 xs dst pad carry=TrimRow.rowsClear3 xs dst pad carry := by
  rcases xs with _|⟨c,_|⟨d,tail⟩⟩
  · rfl
  · rfl
  · simp only [TrimSquare3.rowsClear3,TrimRow.rowsClear3,TrimSquare3.rowClear3,TrimRow.rowClear3,addDrop_eq]

/-! ### Definitions -/

/-- The diagonal tail of `tsq2/tsq3`. -/
def dtail (xs dst carry : List Wire) (cin : Wire) : Program :=
  notRegister dst++TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++notRegister dst

def tsqM (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  if oddLeaf xs.length then mkM (xs.length/2-1) xs dst pad carry++dtail xs dst carry cin
  else TrimSquare3.tsq3 xs dst pad carry cin

def tsqcM (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  if oddLeaf xs.length then
    TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++clM (xs.length/2-1) xs dst pad carry
  else TrimSquare3.tsqc3 xs dst pad carry cin

theorem tsq3_split (xs dst pad carry : List Wire) (cin : Wire) :
    TrimSquare3.tsq3 xs dst pad carry cin=TrimRow.mk xs dst pad carry++dtail xs dst carry cin := by
  simp only [TrimSquare3.tsq3,TrimRow.mk,dtail,rows3_eq,List.append_assoc]

theorem tsqc3_split (xs dst pad carry : List Wire) (cin : Wire) :
    TrimSquare3.tsqc3 xs dst pad carry cin=
      TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++TrimRow.cl xs dst pad carry := by
  simp only [TrimSquare3.tsqc3,TrimRow.cl,rowsClear3_eq,List.append_assoc]

theorem tsq2_split (xs dst pad carry : List Wire) (cin : Wire) :
    TrimSquare.tsq2 xs dst pad carry cin=
      (signedSquareRows xs dst pad carry++signedSquareTop xs dst)++dtail xs dst carry cin := by
  simp only [TrimSquare.tsq2,dtail,List.append_assoc]

/-! ### Side conditions, relative to `tsq3/tsqc3` -/

theorem tsqM_rel (xs dst pad carry : List Wire) (cin : Wire) :
    (wires (tsqM xs dst pad carry cin)⊆wires (TrimSquare3.tsq3 xs dst pad carry cin) ∧
      Challenge.gateSlots (tsqM xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare3.tsq3 xs dst pad carry cin) ∧
      (GatePhysical (TrimSquare3.tsq3 xs dst pad carry cin) → GatePhysical (tsqM xs dst pad carry cin))) ∧
    (wires (tsqcM xs dst pad carry cin)⊆wires (TrimSquare3.tsqc3 xs dst pad carry cin) ∧
      Challenge.gateSlots (tsqcM xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare3.tsqc3 xs dst pad carry cin) ∧
      (GatePhysical (TrimSquare3.tsqc3 xs dst pad carry cin) → GatePhysical (tsqcM xs dst pad carry cin))) := by
  unfold tsqM tsqcM
  split_ifs with h
  · obtain ⟨A,B,x,y,cy,c,e1,e2⟩ := mkM_form _ xs dst pad carry (odd_len _ h)
    obtain ⟨A',B',x',y',cy',c',e1',e2'⟩ := clM_form _ xs dst pad carry (odd_len _ h)
    rw [tsq3_split,tsqc3_split,e1,e2,e1',e2']
    have s1 := side_of_form (A++addTop x y cy c++B++dtail xs dst carry cin)
      (A++addInPlace x y cy c++B++dtail xs dst carry cin) A (B++dtail xs dst carry cin) x y cy c
      (by simp only [List.append_assoc]) (by simp only [List.append_assoc])
    have s2 := side_of_form
      (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++(A'++addTop x' y' cy' c'++B'))
      (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++(A'++addInPlace x' y' cy' c'++B'))
      (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++A') B' x' y' cy' c'
      (by simp only [List.append_assoc]) (by simp only [List.append_assoc])
    exact ⟨s1,s2⟩
  · exact ⟨⟨subset_refl _,le_refl _,id⟩,⟨subset_refl _,le_refl _,id⟩⟩

theorem tsqM_wires_le (xs dst pad carry : List Wire) (cin : Wire) :
    wires (tsqM xs dst pad carry cin)⊆wires (TrimSquare.tsq2 xs dst pad carry cin) ∧
    wires (tsqcM xs dst pad carry cin)⊆wires (TrimSquare.tsqc2 xs dst pad carry cin) :=
  ⟨(tsqM_rel xs dst pad carry cin).1.1.trans (TrimSquare3.tsq3_wires_le xs dst pad carry cin).1,
    (tsqM_rel xs dst pad carry cin).2.1.trans (TrimSquare3.tsq3_wires_le xs dst pad carry cin).2⟩

theorem tsqM_physical_of (xs dst pad carry : List Wire) (cin : Wire)
    (h1 : GatePhysical (TrimSquare.tsq2 xs dst pad carry cin))
    (h2 : GatePhysical (TrimSquare.tsqc2 xs dst pad carry cin)) :
    GatePhysical (tsqM xs dst pad carry cin) ∧ GatePhysical (tsqcM xs dst pad carry cin) := by
  have h := TrimSquare3.tsq3_physical_of xs dst pad carry cin h1 h2
  exact ⟨(tsqM_rel xs dst pad carry cin).1.2.2 h.1,(tsqM_rel xs dst pad carry cin).2.2.2 h.2⟩

theorem tsqM_gateSlots_le (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsqM xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 ∧
    Challenge.gateSlots (tsqcM xs dst pad carry cin) ≤
      xs.length*(12*(xs.length+1)+6*dst.length)+34*xs.length+2*dst.length+18 :=
  ⟨(tsqM_rel xs dst pad carry cin).1.2.1.trans (TrimSquare3.tsq3_gateSlots_le xs dst pad carry cin).1,
    (tsqM_rel xs dst pad carry cin).2.2.1.trans (TrimSquare3.tsq3_gateSlots_le xs dst pad carry cin).2⟩

/-! ### Make correctness -/

theorem tsqM_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqM xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqM xs dst pad carry cin) records s).basis=(regValue xs s.basis)^2 ∧
    ∀q,q∉dst → (run (tsqM xs dst pad carry cin) records s).basis q=s.basis q := by
  unfold tsqM
  split_ifs with h
  · have hn' : (xs++dst++pad++carry).Nodup := (List.nodup_cons.mp hn).2
    obtain ⟨R,hR⟩ := exists_append_left (mkM (xs.length/2-1) xs dst pad carry)
      (signedSquareRows xs dst pad carry++signedSquareTop xs dst) (dtail xs dst carry cin) s records
      (fun r' => mkM_exists _ xs dst pad carry hn' (odd_len _ h) hd hp (by omega) s r' h0 hc0 hp0)
    rw [hR,← tsq2_split]
    exact TrimSquare.tsq2_correct cin xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0 hi0
  · exact TrimSquare3.tsq3_correct cin xs dst pad carry hn hx hd hp hc s records h0 hp0 hc0 hi0

/-! ### Clear correctness -/

/-- `rows ++ top` from a clean `dst` (the unnormalized leaf make). -/
theorem rt_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) m s).phase=s.phase ∧
    regValue dst (run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) m s).basis q=s.basis q := by
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
  simp only [run_append]
  refine ⟨t.1.trans r.1,?_,fun q hq => (t.2.2.1 q hq).trans (r.2.2.1 q hq)⟩
  rw [t.2.1,r.2.1,topSame,Nat.zero_add,←signedRawValue_rows_top]
  exact signedRawValue_correct xs s.basis (List.ne_nil_of_length_pos (by omega))

/-- `drop2` may be traded for the plain diagonal add in front of any suffix (as in `tsqc2_exists`). -/
theorem drop2_swap (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) (Post : Program) :
    ∃ R, run (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++Post) records s=
      run (mappedDiagAdd xs dst carry cin++Post) R s := by
  obtain ⟨x0,b',bits,y,y',ys,c,cs,hx0,hdiag,rfl,hcar,_⟩ := TrimSquare.diag_shape xs dst carry hx hd hc
  obtain ⟨xt,rfl⟩ : ∃ xt, xs=x0::xt := by
    match xs, hx0 with
    | _::xt, rfl => exact ⟨xt,rfl⟩
  obtain ⟨hnd4,hrec,hsrc,hl,hcl,ha,hmem,hcin⟩ :=
    TrimSquare.diag_side cin x0 xt y y' ys pad carry b' bits c cs hn hd hdiag hcar hc
  have sy := TrimSquare.bit0_of_square y x0 (y'::ys) xt s.basis hval
  have carry0 : ∀q∈carry,s.basis q=false := (regValue_zero _ _).mp hc0
  unfold mappedDiagAdd
  rw [hdiag,hcar]
  have g := TrimSquare.glue [] (TrimSquare.drop2 ({wire:=some x0,flip:=false}::b'::bits) (y::y'::ys) (c::cs) cin)
    (mappedAdd ({wire:=some x0,flip:=false}::b'::bits) (y::y'::ys) (c::cs) cin) Post
    (measurementCount (mappedAdd (b'::bits) (y'::ys) cs c))
    (by simp only [TrimSquare.drop2,Bool.false_eq_true,if_false,measurementCount_append]; omega)
    (by have cnt := TrimSquare.drop2_counts x0 y y' c cin b' bits ys cs; omega) s
    (fun rP rX => by
      simp only [run]
      exact TrimSquare.drop2_run x0 y y' c cin b' bits ys cs hnd4 hrec hsrc hl hcl ha rX s
        (by rw [sy]; simp) (carry0 c (hmem c List.mem_cons_self))
        (fun q hq => carry0 q (hmem q (List.mem_cons_of_mem _ hq)))) records
  simpa only [List.nil_append,List.append_assoc] using g

theorem run_nil_append (P Q : Program) (s : State) : run (P++Q) [] s=run Q [] (run P [] s) := by
  rw [run_append]; simp

theorem tsqcM_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqcM xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqcM xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (tsqcM xs dst pad carry cin) records s).basis q=s.basis q := by
  unfold tsqcM
  split_ifs with hodd
  swap
  · exact TrimSquare3.tsqc3_correct cin xs dst pad carry hn hx hd hp hc s records hval hp0 hc0 hi0
  have hn' : (xs++dst++pad++carry).Nodup := (List.nodup_cons.mp hn).2
  have hc' : xs.length-1≤carry.length := by omega
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈cin::xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  have regBase (r : List Wire) (hr : r=xs ∨ r=pad ∨ r=carry) :
      regValue r base.basis=regValue r s.basis := by
    apply regValue_congr
    intro q hq
    have ne : q∉dst := away q (by rcases hr with rfl|rfl|rfl <;> simp [hq])
    simp [base,ne]
  have d0 : regValue dst base.basis=0 := (regValue_zero _ _).mpr (fun q hq => by simp [base,hq])
  have p0 : regValue pad base.basis=0 := (regBase pad (Or.inr (Or.inl rfl))).trans hp0
  have c0 : regValue carry base.basis=0 := (regBase carry (Or.inr (Or.inr rfl))).trans hc0
  have i0 : base.basis cin=false := by simp [base,away cin (by simp),hi0]
  have forward := mappedSignedSquare_correct cin xs dst pad carry hn hx hd hp hc base [] d0 p0 c0 i0
  have same : run (mappedSignedSquare xs dst pad carry cin) [] base=s := by
    have phase := forward.1
    have value : regValue dst (run (mappedSignedSquare xs dst pad carry cin) [] base).basis=regValue dst s.basis := by
      rw [forward.2.1,regBase xs (Or.inl rfl),hval]
    cases s with
    | mk ph bs =>
      have basis : (run (mappedSignedSquare xs dst pad carry cin) [] base).basis=bs := by
        funext q
        by_cases inDst : q∈dst
        · exact (regValue_eq_iff dst _ bs).mp value q inDst
        · exact (forward.2.2 q inDst).trans (by simp [base,inDst])
      calc
        _=State.mk (run (mappedSignedSquare xs dst pad carry cin) [] base).phase
            (run (mappedSignedSquare xs dst pad carry cin) [] base).basis := rfl
        _=State.mk ph bs := by rw [phase,basis]
  -- the plain make state `w`, from which `s` is the diagonal subtraction
  set w := run (signedSquareRows xs dst pad carry++signedSquareTop xs dst) [] base with hw
  have hs : s=run (mappedDiagSub xs dst carry cin) [] w := by
    rw [← same,hw]; unfold mappedSignedSquare
    rw [show signedSquareRows xs dst pad carry++signedSquareTop xs dst++mappedDiagSub xs dst carry cin=
      (signedSquareRows xs dst pad carry++signedSquareTop xs dst)++mappedDiagSub xs dst carry cin by
      simp only [List.append_assoc],run_nil_append]
  have rtw := rt_correct xs dst pad carry hn' hx hd hp hc' base [] d0 p0 c0
  have wkeep (q : Wire) (hq : q∉dst) : w.basis q=base.basis q := rtw.2.2 q hq
  have wc0 : regValue carry w.basis=0 := by
    rw [← c0]; apply regValue_congr; intro q hq; exact wkeep q (away q (by simp [hq]))
  have wi0 : w.basis cin=false := by rw [wkeep cin (away cin (by simp)),i0]
  have wval : regValue dst w.basis=(regValue xs w.basis)^2+signedDiagValue (regValue xs w.basis) xs.length := by
    have e : regValue xs w.basis=regValue xs base.basis := by
      apply regValue_congr; intro q hq; exact wkeep q (away q (by simp [hq]))
    rw [e]; exact rtw.2.1
  have hn3 : (cin::xs++dst++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  -- trade drop2 for the plain add, which undoes the subtraction
  obtain ⟨R1,h1⟩ := drop2_swap cin xs dst pad carry hn hx hd hc s records hval hc0
    (clM (xs.length/2-1) xs dst pad carry)
  have hround : run (mappedDiagAdd xs dst carry cin) (R1.take (measurementCount (mappedDiagAdd xs dst carry cin))) s=w := by
    rw [hs]; exact mappedDiag_roundtrip cin xs dst carry hn3 (by omega) hd hc w [] _ wc0 wi0
  rw [h1,run_append,hround]
  -- the middle-row clear is the TrimRow clear, which is the plain clear, which restores `base`
  obtain ⟨R2,h2⟩ := clM_exists _ xs dst pad carry hn' (odd_len _ hodd) hd hp hc' base d0 c0 p0
    (R1.drop (measurementCount (mappedDiagAdd xs dst carry cin)))
  rw [← hw] at h2
  rw [h2]
  obtain ⟨R3,h3⟩ := TrimRow.cl_exists xs dst pad carry hn' hx hd hp hc' w R2 wval wc0
  rw [h3]
  have nt : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn' q
    simp only [List.count_append] at h ⊢; omega
  have hhi : regValue (dst.drop xs.length) base.basis=0 := by
    apply (regValue_zero _ _).mpr; intro q hq
    exact (regValue_zero _ _).mp d0 q (List.mem_of_mem_drop hq)
  have hwz : regValue (pad++carry) base.basis=0 := by rw [regValue_append,p0,c0]; simp
  have back : run (signedSquareTop xs dst++signedSquareRowsClear xs dst pad carry) R3 w=base := by
    have e1 : run (signedSquareTop xs dst) (R3.take (measurementCount (signedSquareTop xs dst))) w=
        run (signedSquareRows xs dst pad carry) [] base := by
      rw [top_m0,List.take_zero,hw,run_nil_append,top_twice _ _ nt]
    rw [run_append,e1,top_m0,List.drop_zero]
    set mR := measurementCount (signedSquareRows xs dst pad carry)
    have rt := signedSquareRows_roundtrip xs dst pad carry hn' hd (Or.inr hp) hc' base
      (([]++List.replicate mR false).take mR++R3) 0 d0 hhi hwz
    simp only at rt
    rw [run_append,List.take_left' (padTake_len _ _),List.drop_left' (padTake_len _ _),
      TrimRow.run_padTake _ _ _ _ rfl] at rt
    cases hS : run (signedSquareRowsClear xs dst pad carry) R3 (run (signedSquareRows xs dst pad carry) [] base)
    rw [hS] at rt
    simp only at rt
    simp only [base] at rt ⊢
    rw [rt.1,rt.2]
  rw [back]
  exact ⟨rfl,d0,fun q hq => by simp [base,hq]⟩

theorem tsqM_counts_rel (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    (toffoliCount (tsqM xs dst pad carry cin)+par xs.length=toffoliCount (TrimSquare3.tsq3 xs dst pad carry cin) ∧
      measurementCount (tsqM xs dst pad carry cin)+par xs.length=measurementCount (TrimSquare3.tsq3 xs dst pad carry cin)) ∧
    (toffoliCount (tsqcM xs dst pad carry cin)+par xs.length=toffoliCount (TrimSquare3.tsqc3 xs dst pad carry cin) ∧
      measurementCount (tsqcM xs dst pad carry cin)+par xs.length=measurementCount (TrimSquare3.tsqc3 xs dst pad carry cin)) := by
  unfold tsqM tsqcM par
  split_ifs with h
  · have m := mkM_counts _ xs dst pad carry (odd_len _ h) hd hp (by omega)
    have c := clM_counts _ xs dst pad carry (odd_len _ h) hd hp (by omega)
    rw [tsq3_split,tsqc3_split]
    simp only [toffoliCount_append,measurementCount_append]
    omega
  · simp

end ECDSAAdd.Entrant.TrimMid

namespace ECDSAAdd.Entrant
open Arithmetic

theorem sq_mid_make (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqMake xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimMid.tsqM xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimMid.tsqM_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,trivial,fun q h _ => r.2.2 q h⟩

theorem sq_mid_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimMid.tsqcM xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimMid.tsqcM_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩

end ECDSAAdd.Entrant

end

-- ===== merged module ECDSAAdd.Submission.Entrant.MeasuredZeroClear =====
section
namespace ECDSAAdd.Entrant.MeasuredZeroClear
open Arithmetic Challenge Baselines RecordedQuantum
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def compute (c a t : Wire) : Program := [.X a, .CCX c a t, .X a]
def erase (c a t : Wire) : Program := [.X a, .measureX t [] [.CZ c a], .X a]

def zeroClear (c target : Wire) : List ZeroBit → Program
  | [] => [.CX c target]
  | [b] => erase c b.input target
  | b::d::bs => compute c b.input b.work ++ zeroClear b.work target (d::bs) ++ erase c b.input b.work

theorem old_cons (c t : Wire) (b : ZeroBit) (bs : List ZeroBit) :
    zeroControlled c t (b::bs) =
      compute c b.input b.work ++ zeroControlled b.work t bs ++ erase c b.input b.work := rfl

theorem compute_run (c a t : Wire) (hca : c≠a) (hat : a≠t) (s : State) (m : List Bool) :
    run (compute c a t) m s =
      ⟨s.phase, writeBit s.basis t (s.basis t ^^ (s.basis c && !s.basis a))⟩ := by
  simp only [compute,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hw : w=a
  · subst w; simp [writeBit,hca,hat]
  · by_cases ht : w=t
    · subst w; simp [writeBit,hca,Ne.symm hat]
    · simp [writeBit,hw,ht,hca]

theorem erase_run (c a t : Wire) (hca : c≠a) (hat : a≠t) (hct : c≠t)
    (s : State) (m : List Bool) (hq : s.basis t = (s.basis c && !s.basis a)) :
    run (erase c a t) m s = ⟨s.phase,writeBit s.basis t false⟩ := by
  simp only [erase,run]
  cases hm : m.headD false <;>
    simp [measureAndCorrect,correct,writeBit,hca,hat,hat.symm,hct,hq]
  all_goals
    funext w
    by_cases hw : w=a
    · subst w; simp [hat]
    · simp [Function.update_apply,hw]

theorem counts (c t : Wire) (bs : List ZeroBit) :
    toffoliCount (zeroClear c t bs)=bs.length-1 ∧
    measurementCount (zeroClear c t bs)=bs.length := by
  induction bs generalizing c with
  | nil => simp [zeroClear,toffoliCount,measurementCount]
  | cons b bs ih =>
    cases bs with
    | nil => simp [zeroClear,erase,toffoliCount,measurementCount]
    | cons d ds =>
      simp only [zeroClear,toffoliCount_append,measurementCount_append,ih]
      simp [compute,erase,toffoliCount,measurementCount]
      omega

theorem support (c t : Wire) (bs : List ZeroBit) :
    wires (zeroClear c t bs) ⊆ wires (zeroControlled c t bs) := by
  induction bs generalizing c with
  | nil => exact Finset.Subset.refl _
  | cons b bs ih =>
    cases bs with
    | nil =>
      rw [zeroControlled_wires]
      intro q h
      simp [zeroClear,erase,wires,Instr.wires,correctionWires,ZeroBit.wires] at h ⊢
      tauto
    | cons d ds =>
      rw [zeroClear,old_cons,wires_append,wires_append,wires_append,wires_append]
      exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (ih _))
        (Finset.Subset.refl _)

theorem slots (c t : Wire) (bs : List ZeroBit) (hne : bs≠[]) :
    gateSlots (zeroClear c t bs)+4=gateSlots (zeroControlled c t bs) := by
  induction bs generalizing c with
  | nil => exact False.elim (hne rfl)
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons d ds =>
      rw [zeroClear,old_cons]
      simp only [gateSlots_append]
      have h := ih b.work (by simp)
      omega

theorem run_eq (c target : Wire) (bs : List ZeroBit)
    (hnd : (c::target::bs.flatMap ZeroBit.wires).Nodup)
    (s : State) (m : List Bool) (hz : ∀b∈bs,s.basis b.work=false)
    (hzero : (run (zeroControlled c target bs) m s).basis target=false) :
    run (zeroClear c target bs) m s=run (zeroControlled c target bs) m s := by
  induction bs generalizing c s m with
  | nil => rfl
  | cons b bs ih =>
    have hnames : (c::target::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hnd
    have hni := hnames
    simp only [List.nodup_cons,List.mem_cons,not_or] at hni
    have hca : c≠b.input := hni.1.2.1
    have hai : b.input≠b.work := hni.2.2.1.1
    have hta : target≠b.input := hni.2.1.1
    have htw : target≠b.work := hni.2.1.2.1
    have hcw : c≠b.work := hni.1.2.2.1
    have hct : c≠target := hni.1.1
    cases bs with
    | nil =>
      have old := zeroControlled_correct c target [b] hnd s m hz
      have ht : s.basis target = (s.basis c && !s.basis b.input) := by
        simpa [old,writeBit] using hzero
      rw [zeroClear,erase_run c b.input target hca hta.symm hct s m ht,old]
      simp [ht]
    | cons d ds =>
      have hchild : (b.work::target::(d::ds).flatMap ZeroBit.wires).Nodup := by
        simp only [List.nodup_cons,List.mem_cons,not_or]
        exact ⟨⟨htw.symm,hni.2.2.2.1⟩,hni.2.1.2.2,hni.2.2.2.2⟩
      let u := run (compute c b.input b.work) m s
      have hu := compute_run c b.input b.work hca hai s m
      have hz' : ∀e∈d::ds,u.basis e.work=false := by
        intro e he
        have ne : e.work≠b.work := by
          intro eq
          exact hni.2.2.2.1 (List.mem_flatMap.mpr ⟨e,he,by simp [ZeroBit.wires,eq]⟩)
        simpa [u,hu,writeBit,ne] using hz e (by simp [he])
      have off : target∉wires (erase c b.input b.work) := by
        simp [erase,wires,Instr.wires,correctionWires,htw,hta,hct.symm]
      have zero : (run (zeroControlled b.work target (d::ds)) m u).basis target=false := by
        have keep := run_preserves_outside (erase c b.input b.work) (m.drop (d::ds).length)
          (run (zeroControlled b.work target (d::ds)) m u) target off
        rw [old_cons,run_append,run_take,run_append,run_take] at hzero
        simp only [measurementCount_append,show measurementCount (compute c b.input b.work)=0 from rfl,
          (zeroControlled_counts b.work target (d::ds)).2,Nat.zero_add,List.drop_zero] at hzero
        exact keep.symm.trans hzero
      rw [zeroClear,old_cons,run_append,run_take,run_append,run_take,
        run_append,run_take,run_append,run_take]
      simp only [measurementCount_append,show measurementCount (compute c b.input b.work)=0 from rfl,
        (counts b.work target (d::ds)).2,(zeroControlled_counts b.work target (d::ds)).2,
        Nat.zero_add,List.drop_zero]
      rw [ih b.work hchild u m hz' zero]

theorem physical (c target : Wire) (bs : List ZeroBit)
    (hn : (c::target::bs.flatMap ZeroBit.wires).Nodup) : GatePhysical (zeroClear c target bs) := by
  induction bs generalizing c with
  | nil => exact zeroControlled_physical c target [] hn
  | cons b bs ih =>
    have names : (c::target::b.input::b.work::bs.flatMap ZeroBit.wires).Nodup := hn
    have h := names
    simp only [List.nodup_cons,List.mem_cons,not_or] at h
    cases bs with
    | nil => simp [zeroClear,erase,GatePhysical,PhysicalInstr,ProperGate]
    | cons d ds =>
      have child : (b.work::target::(d::ds).flatMap ZeroBit.wires).Nodup := by
        simp only [List.nodup_cons,List.mem_cons,not_or]
        exact ⟨⟨Ne.symm h.2.1.2.1,h.2.2.2.1⟩,h.2.1.2.2,h.2.2.2.2⟩
      have old := zeroControlled_physical c target (b::d::ds) hn
      rw [old_cons,gatePhysical_append,gatePhysical_append] at old
      rw [zeroClear,gatePhysical_append,gatePhysical_append]
      exact ⟨⟨old.1.1,ih _ child⟩,old.2⟩

def equalClear (c t : Wire) (bs : List ZeroBit) (k : Nat) : Program :=
  xorConstant (bs.map ZeroBit.input) k ++ zeroClear c t bs ++ xorConstant (bs.map ZeroBit.input) k

theorem equal_counts (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    toffoliCount (equalClear c t bs k)=bs.length-1 ∧
    measurementCount (equalClear c t bs k)=bs.length := by
  simp [equalClear,toffoliCount_append,measurementCount_append,xorConstant_counts,counts]

theorem equal_support (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    wires (equalClear c t bs k) ⊆ wires (equalConstant c t bs k) := by
  simp only [equalClear,equalConstant,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) (support _ _ _))
    (Finset.Subset.refl _)

theorem equal_slots (c t : Wire) (bs : List ZeroBit) (k : Nat) (hne : bs≠[]) :
    gateSlots (equalClear c t bs k)+4=gateSlots (equalConstant c t bs k) := by
  have h := slots c t bs hne
  simp only [equalClear,equalConstant,gateSlots_append]
  omega

theorem equal_physical (c t : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c::t::bs.flatMap ZeroBit.wires).Nodup) : GatePhysical (equalClear c t bs k) := by
  simp only [equalClear,gatePhysical_append]
  exact ⟨⟨xorConstant_physical _ _,physical _ _ _ hn⟩,xorConstant_physical _ _⟩

private theorem split_count (bs : List ZeroBit) (q : Wire) :
    (bs.flatMap ZeroBit.wires).count q=(bs.map ZeroBit.input).count q+(bs.map ZeroBit.work).count q := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons,ZeroBit.wires,List.map_cons,List.count_append,List.count_cons,List.count_nil,ih]
    omega

theorem equal_run_eq (c t : Wire) (bs : List ZeroBit) (k : Nat)
    (hn : (c::t::bs.flatMap ZeroBit.wires).Nodup) (s : State) (m : List Bool)
    (hz : ∀b∈bs,s.basis b.work=false)
    (hzero : (run (equalConstant c t bs k) m s).basis t=false) :
    run (equalClear c t bs k) m s=run (equalConstant c t bs k) m s := by
  let src := bs.map ZeroBit.input
  let P := xorConstant src k
  let u := run P m s
  have off : t∉wires P := by
    intro ht
    have mem := List.mem_toFinset.mp (xorConstant_wires_subset src k ht)
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp mem
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      (List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires,eq]⟩)
  have hz' : ∀b∈bs,u.basis b.work=false := by
    intro b hb
    have away : b.work∉wires P := by
      intro hw
      have mem := List.mem_toFinset.mp (xorConstant_wires_subset src k hw)
      have a := List.count_pos_iff.mpr mem
      have w := List.count_pos_iff.mpr (List.mem_map.mpr ⟨b,hb,rfl⟩ : b.work∈bs.map ZeroBit.work)
      have nd := List.nodup_iff_count.mp hn b.work
      have sp := split_count bs b.work
      simp only [List.count_cons] at nd
      change 0<(bs.map ZeroBit.input).count b.work at a
      omega
    exact (run_preserves_outside P m s b.work away).trans (hz b hb)
  have zero : (run (zeroControlled c t bs) m u).basis t=false := by
    have keep := run_preserves_outside P (m.drop bs.length) (run (zeroControlled c t bs) m u) t off
    rw [equalConstant,run_append,run_take,run_append,run_take] at hzero
    simp only [measurementCount_append,(xorConstant_counts _ _).2,
      (zeroControlled_counts _ _ _).2,Nat.zero_add,List.drop_zero] at hzero
    exact keep.symm.trans hzero
  rw [equalClear,equalConstant,run_append,run_take,run_append,run_take,
    run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(xorConstant_counts _ _).2,(counts c t bs).2,
    (zeroControlled_counts c t bs).2,Nat.zero_add,List.drop_zero]
  rw [run_eq c t bs hn u m hz' zero]

end ECDSAAdd.Entrant.MeasuredZeroClear
end

-- ===== merged module ECDSAAdd.Submission.Entrant.MainC =====
section
-- ===== ECDSAAdd.Submission.Entrant.LowZero =====
section
-- consolidated import: import ECDSAAdd.Arithmetic.InPlaceAdder
-- consolidated import: import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
-- consolidated import: import ECDSAAdd.Arithmetic.Registers
-- consolidated import: import ECDSAAdd.Baselines.SlotMapped
-- consolidated import: import ECDSAAdd.Arithmetic.BalancedFieldInverseArithmetic

/-! LowZero: an in-place addition whose lowest source bit and carry-in are both zero.

Bit 0 of the target is then unchanged and no carry leaves bit 0, so the lowest
majority / measured-erase pair of `addInPlace` (one Toffoli, one measurement) and the
final two CNOTs of that bit are dropped; the remaining bits are added with the original
carry-in wire, which is still zero. -/

set_option maxHeartbeats 1000000

namespace ECDSAAdd.Entrant.LowZero
open ECDSAAdd ECDSAAdd.Arithmetic

/-- `addInPlace` restricted to bits `1..n-1`; the dropped (clean) lowest carry wire is
measured with empty corrections so the measurement count and record layout are kept. -/
def addLow0 (x y carry : List Wire) (cin : Wire) : Program :=
  addInPlace x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []]

theorem foldr_cons_value (w : Wire) (r : List Wire) (st : BasisState) :
    regValue (w :: r) st = (if st w then 1 else 0) + 2 * regValue r st := rfl

theorem measure_zero_id (c : Wire) (m : List Bool) (t : State) (h : t.basis c = false) :
    run [.measureX c [] []] m t = t := by
  obtain ⟨ph, bs⟩ := t
  simp only at h
  have e : writeBit bs c false = bs := by
    funext q; by_cases hq : q = c
    · subst hq; simp [writeBit, h]
    · simp [writeBit, Function.update, hq]
  simp only [run, measureAndCorrect, h, Bool.and_false, Bool.xor_false, e]
  cases m.headD false <;> rfl

theorem low_mod (d A k : Nat) (hd : d < 2) :
    d + 2 * (A % 2^k) = (d + 2 * A) % (2^k * 2) := by
  have hr := Nat.mod_lt A (Nat.two_pow_pos k)
  have e := Nat.div_add_mod A (2^k)
  have key : d + 2 * A = (d + 2 * (A % 2^k)) + (2^k * 2) * (A / 2^k) := by
    conv_lhs => rw [← e]
    ring
  rw [key, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem addLow0_correct (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) (s : State) (m : List Bool)
    (hclean : ∀ w ∈ carry, s.basis w = false)
    (hx0 : s.basis (x.headD 0) = false) (hcin : s.basis cin = false) :
    (run (addLow0 x y carry cin) m s).phase = s.phase ∧
    (∀ w, w ∉ y → (run (addLow0 x y carry cin) m s).basis w = s.basis w) ∧
    regValue y (run (addLow0 x y carry cin) m s).basis =
      (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^y.length := by
  rcases x with _ | ⟨a, as⟩
  · simp at hx h2; omega
  rcases y with _ | ⟨b, bs⟩
  · simp at hx h2
  rcases carry with _ | ⟨c, cs⟩
  · simp only [List.length_cons, List.length_nil] at hc h2; omega
  · simp only [List.headD_cons] at hx0
    simp only [List.length_cons] at hx hc h2
    have hnd' : (cin :: (as ++ bs ++ cs)).Nodup := by
      apply List.Nodup.sublist _ hnd
      apply List.Sublist.cons₂
      simp only [List.cons_append, List.append_assoc]
      apply List.Sublist.cons
      apply List.Sublist.append_left
      apply List.Sublist.cons
      apply List.Sublist.append_left
      exact List.sublist_cons_self c cs
    have hb : b ∉ bs := by
      have h := List.nodup_cons.mp hnd
      have h' := (List.nodup_append.mp (List.nodup_append.mp h.2).1).2.1
      exact (List.nodup_cons.mp h').1
    have hcy : c ∉ bs := by
      intro hc'
      have h := (List.nodup_cons.mp hnd).2
      rw [List.nodup_append] at h
      exact h.2.2 c (List.mem_append_right _ (List.mem_cons_of_mem b hc')) c List.mem_cons_self rfl
    let k := measurementCount (addInPlace as bs cs cin)
    have r := addInPlace_correct as bs cs cin hnd' (by omega) (by omega) s (m.take k)
      (fun w hw => hclean w (List.mem_cons_of_mem c hw))
    have e : run (addLow0 (a :: as) (b :: bs) (c :: cs) cin) m s =
        run (addInPlace as bs cs cin) (m.take k) s := by
      simp only [addLow0, List.tail_cons, List.headD_cons]
      rw [run_append, measure_zero_id]
      rw [r.2.1 c hcy]
      exact hclean c List.mem_cons_self
    rw [e]
    refine ⟨r.1, fun w hw => r.2.1 w (fun h => hw (List.mem_cons_of_mem b h)), ?_⟩
    rw [foldr_cons_value, foldr_cons_value, foldr_cons_value, r.2.1 b hb, r.2.2, hx0, hcin]
    simp only [Bool.false_eq_true, if_false, Bool.toNat_false, Nat.add_zero, Nat.zero_add,
      List.length_cons, pow_succ]
    rw [show 2 * regValue as s.basis + ((if s.basis b = true then 1 else 0) + 2 * regValue bs s.basis) =
        (if s.basis b = true then 1 else 0) + 2 * (regValue as s.basis + regValue bs s.basis) by ring]
    exact low_mod _ _ _ (by split <;> omega)

theorem addLow0_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (addLow0 x y carry cin) = y.length - 2 ∧
    measurementCount (addLow0 x y carry cin) = y.length - 1 := by
  have h := addInPlace_counts x.tail y.tail carry.tail cin
    (by simp only [List.length_tail]; omega) (by simp only [List.length_tail]; omega)
  simp only [List.length_tail] at h
  simp only [addLow0, toffoliCount_append, measurementCount_append, h.1, h.2]
  simp [toffoliCount, measurementCount]; omega

theorem addLow0_wires (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (addLow0 x y carry cin) ⊆ (cin :: (x ++ y ++ carry)).toFinset := by
  unfold addLow0
  rw [wires_append, addInPlace_wires x.tail y.tail carry.tail cin
    (by simp only [List.length_tail]; omega) (by simp only [List.length_tail]; omega)]
  apply Finset.union_subset
  · intro q hq
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append] at hq ⊢
    rcases hq with h | (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl (List.mem_of_mem_tail h)))
    · exact Or.inr (Or.inl (Or.inr (List.mem_of_mem_tail h)))
    · exact Or.inr (Or.inr (List.mem_of_mem_tail h))
  · intro q hq
    rcases carry with _ | ⟨c, cs⟩
    · simp only [List.length_nil] at hc; omega
    · simp [wires, Instr.wires, correctionWires] at hq
      subst hq
      simp

theorem addLow0_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLow0 x y carry cin) := by
  unfold addLow0
  rw [gatePhysical_append]
  refine ⟨?_, ?_⟩
  · apply addInPlace_physical
    apply List.Nodup.sublist _ hn
    simp only [List.cons_append, List.append_assoc]
    apply List.Sublist.cons₂
    exact (List.tail_sublist x).append ((List.tail_sublist y).append (List.tail_sublist carry))
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    trivial

theorem addInPlace_slots_cin (x y cs : List Wire) (c c' : Wire) :
    Challenge.gateSlots (addInPlace x y cs c) = Challenge.gateSlots (addInPlace x y cs c') := by
  match x, y, cs with
  | a :: a' :: as, b :: b' :: bs, d :: ds =>
    simp [addInPlace, Challenge.gateSlots, Challenge.instructionSlots, majority, eraseCarry]
  | [a], [b], _ => simp [addInPlace, Challenge.gateSlots, Challenge.instructionSlots]
  | [], _, _ => simp [addInPlace]
  | [_], [], _ => simp [addInPlace]
  | [_], _ :: _ :: _, _ => simp [addInPlace]
  | _ :: _ :: _, [], _ => simp [addInPlace]
  | _ :: _ :: _, [_], _ => simp [addInPlace]
  | _ :: _ :: _, _ :: _ :: _, [] => simp [addInPlace]

theorem addLow0_slots (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    Challenge.gateSlots (addLow0 x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLow0
  rw [Challenge.gateSlots_append]
  have m1 : Challenge.gateSlots [Instr.measureX (carry.headD 0) [] []] = 1 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  rw [m1]
  rcases x with _ | ⟨a, _ | ⟨a', as⟩⟩
  · simp at hx; omega
  · simp at hx; omega
  rcases y with _ | ⟨b, _ | ⟨b', bs⟩⟩
  · simp at h2
  · simp at h2
  rcases carry with _ | ⟨c, cs⟩
  · simp at hc
  simp only [List.tail_cons, addInPlace, Challenge.gateSlots_append]
  rw [addInPlace_slots_cin (a' :: as) (b' :: bs) cs cin c]
  simp [Challenge.gateSlots, Challenge.instructionSlots, majority, eraseCarry]
  omega

/-- The lowest wire of a register holding an even value is zero. -/
theorem head_false_of_even (r tail : List Wire) (st : BasisState) (k : Nat)
    (h : regValue r st = 2 * k) (hne : r ≠ []) : st ((r ++ tail).headD 0) = false := by
  match r, hne with
  | w :: ws, _ =>
    simp only [List.cons_append, List.headD_cons]
    rw [foldr_cons_value] at h
    by_cases hw : st w = true
    · rw [hw] at h; simp only [if_true] at h; omega
    · simpa using hw

theorem addLow0_wires_sub (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (addLow0 x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  rw [addInPlace_wires x y carry cin hx hc]
  exact addLow0_wires x y carry cin hx hc h2

theorem addLow0_counts_rel (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (addLow0 x y carry cin) + 1 = toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addLow0 x y carry cin) = measurementCount (addInPlace x y carry cin) := by
  have a := addLow0_counts x y carry cin hx hc h2
  have b := addInPlace_counts x y carry cin hx hc
  omega


/-! ### Bit 0 that emits no carry

If `cin = 0` and the two lowest operand bits are not both one, bit 0 produces no carry: only
its sum CNOTs are needed. -/

/-- `addInPlace` whose bit-0 majority/erase pair is replaced by its two sum CNOTs. -/
def addLowNC (x y carry : List Wire) (cin : Wire) : Program :=
  addInPlace x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []] ++
    [.CX (x.headD 0) (y.headD 0), .CX cin (y.headD 0)]

theorem two_cx (a b cin : Wire) (t : State) (hab : a ≠ b) (hcb : cin ≠ b)
    (hc : t.basis cin = false) :
    run [.CX a b, .CX cin b] [] t = ⟨t.phase, writeBit t.basis b (t.basis b ^^ t.basis a)⟩ := by
  simp only [run]
  congr 1
  funext q
  by_cases hq : q = b
  · subst hq; simp [writeBit, Function.update, hcb, hc]
  · simp [writeBit, Function.update, hq]

theorem addLowNC_correct (x y carry : List Wire) (cin : Wire)
    (hnd : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) (s : State) (m : List Bool)
    (hclean : ∀ w ∈ carry, s.basis w = false)
    (hnc : (s.basis (x.headD 0) && s.basis (y.headD 0)) = false) (hcin : s.basis cin = false) :
    (run (addLowNC x y carry cin) m s).phase = s.phase ∧
    (∀ w, w ∉ y → (run (addLowNC x y carry cin) m s).basis w = s.basis w) ∧
    regValue y (run (addLowNC x y carry cin) m s).basis =
      (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^y.length := by
  rcases x with _ | ⟨a, as⟩
  · simp at hx h2; omega
  rcases y with _ | ⟨b, bs⟩
  · simp at hx h2
  rcases carry with _ | ⟨c, cs⟩
  · simp only [List.length_cons, List.length_nil] at hc h2; omega
  · simp only [List.headD_cons] at hnc
    simp only [List.length_cons] at hx hc h2
    have hnd' : (cin :: (as ++ bs ++ cs)).Nodup := by
      apply List.Nodup.sublist _ hnd
      apply List.Sublist.cons₂
      simp only [List.cons_append, List.append_assoc]
      apply List.Sublist.cons
      apply List.Sublist.append_left
      apply List.Sublist.cons
      apply List.Sublist.append_left
      exact List.sublist_cons_self c cs
    have h0 := hnd
    simp only [List.cons_append, List.append_assoc, List.nodup_cons, List.mem_cons, List.mem_append,
      not_or] at h0
    have hca : cin ≠ a := h0.1.1
    have hcb : cin ≠ b := h0.1.2.2.1
    have hcinb : cin ∉ bs := h0.1.2.2.2.1
    have hab : a ≠ b := h0.2.1.2.1
    have ha : a ∉ bs := h0.2.1.2.2.1
    have hb : b ∉ bs := by
      have h := List.nodup_cons.mp hnd
      have h' := (List.nodup_append.mp (List.nodup_append.mp h.2).1).2.1
      exact (List.nodup_cons.mp h').1
    have hcy : c ∉ bs := by
      intro hc'
      have h := (List.nodup_cons.mp hnd).2
      rw [List.nodup_append] at h
      exact h.2.2 c (List.mem_append_right _ (List.mem_cons_of_mem b hc')) c List.mem_cons_self rfl
    have clean' : ∀ w ∈ cs, s.basis w = false := fun w hw => hclean w (List.mem_cons_of_mem c hw)
    have hframe : ∀ m', (run (addInPlace as bs cs cin) m' s).basis c = false := fun m' =>
      ((addInPlace_correct as bs cs cin hnd' (by omega) (by omega) s m' clean').2.1 c hcy).trans
        (hclean c List.mem_cons_self)
    have e : ∃ m1, run (addLowNC (a :: as) (b :: bs) (c :: cs) cin) m s =
        run [.CX a b, .CX cin b] [] (run (addInPlace as bs cs cin) m1 s) := by
      refine ⟨(m.take (measurementCount (addInPlace as bs cs cin ++ [.measureX c [] []]))).take
        (measurementCount (addInPlace as bs cs cin)), ?_⟩
      simp only [addLowNC, List.tail_cons, List.headD_cons]
      rw [run_append, run_append, measure_zero_id _ _ _ (hframe _)]
      rfl
    obtain ⟨m1, e⟩ := e
    have r := addInPlace_correct as bs cs cin hnd' (by omega) (by omega) s m1 clean'
    generalize ht : run (addInPlace as bs cs cin) m1 s = t at r e
    have ta : t.basis a = s.basis a := r.2.1 a ha
    have tb : t.basis b = s.basis b := r.2.1 b hb
    have tcin : t.basis cin = s.basis cin := r.2.1 cin hcinb
    rw [e, two_cx a b cin t hab hcb (tcin.trans hcin)]
    refine ⟨r.1, ?_, ?_⟩
    · intro w hw
      have wb : w ≠ b := fun e => hw (e ▸ List.mem_cons_self)
      simp only [writeBit, Function.update, wb, dite_false]
      exact r.2.1 w (fun h => hw (List.mem_cons_of_mem b h))
    · rw [foldr_cons_value, foldr_cons_value, foldr_cons_value]
      have rest : regValue bs (writeBit t.basis b (t.basis b ^^ t.basis a)) = regValue bs t.basis := by
        apply regValue_congr
        intro q hq
        have qb : q ≠ b := fun e => hb (e ▸ hq)
        simp [writeBit, Function.update, qb]
      rw [rest, r.2.2, ta, tb, hcin]
      simp only [writeBit, Function.update_self, Bool.toNat_false, Nat.add_zero, List.length_cons, pow_succ]
      have key : ∀ (u v : Bool) (A B : Nat), (u && v) = false →
          (if (v ^^ u) = true then 1 else 0) + 2 * ((A + B) % 2 ^ bs.length) =
            ((if u = true then 1 else 0) + 2 * A + ((if v = true then 1 else 0) + 2 * B)) % (2 ^ bs.length * 2) := by
        intro u v A B huv
        have hl := low_mod (if (v ^^ u) = true then 1 else 0) (A + B) bs.length (by split <;> omega)
        rw [hl]
        congr 1
        cases u <;> cases v <;> simp at huv ⊢ <;> ring
      exact key _ _ _ _ hnc

theorem addLowNC_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (addLowNC x y carry cin) + 1 = toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addLowNC x y carry cin) = measurementCount (addInPlace x y carry cin) := by
  have h := addInPlace_counts x.tail y.tail carry.tail cin
    (by simp only [List.length_tail]; omega) (by simp only [List.length_tail]; omega)
  have b := addInPlace_counts x y carry cin hx hc
  simp only [List.length_tail] at h
  simp only [addLowNC, toffoliCount_append, measurementCount_append, h.1, h.2, b.1, b.2]
  simp [toffoliCount, measurementCount]; omega

theorem addLowNC_wires_sub (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (addLowNC x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  rw [addInPlace_wires x y carry cin hx hc]
  have base := addLow0_wires x y carry cin hx hc h2
  unfold addLow0 at base
  unfold addLowNC
  rw [wires_append]
  apply Finset.union_subset base
  rcases x with _ | ⟨a, as⟩
  · simp at hx; omega
  rcases y with _ | ⟨b, bs⟩
  · simp at hx h2
  intro q hq
  simp [wires, Instr.wires] at hq ⊢
  rcases hq with h | h | h <;> simp [h]

theorem addLowNC_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hx : 1 ≤ x.length) (hy : 1 ≤ y.length) :
    GatePhysical (addLowNC x y carry cin) := by
  have base := addLow0_physical x y carry cin hn
  unfold addLow0 at base
  unfold addLowNC
  rw [gatePhysical_append]
  refine ⟨base, ?_⟩
  rcases x with _ | ⟨a, as⟩
  · simp at hx
  rcases y with _ | ⟨b, bs⟩
  · simp at hy
  have h0 := hn
  simp only [List.cons_append, List.append_assoc, List.nodup_cons, List.mem_cons, List.mem_append,
    not_or] at h0
  intro i hi
  simp only [List.headD_cons, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h0.2.1.2.1
  · exact h0.1.2.2.1

theorem addLowNC_slots (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    Challenge.gateSlots (addLowNC x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLowNC
  rw [Challenge.gateSlots_append, Challenge.gateSlots_append]
  have m1 : Challenge.gateSlots [Instr.measureX (carry.headD 0) [] []] = 1 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  have m2 : Challenge.gateSlots [Instr.CX (x.headD 0) (y.headD 0), Instr.CX cin (y.headD 0)] = 2 := by
    simp [Challenge.gateSlots, Challenge.instructionSlots]
  rw [m1, m2]
  rcases x with _ | ⟨a, _ | ⟨a', as⟩⟩
  · simp at hx; omega
  · simp at hx; omega
  rcases y with _ | ⟨b, _ | ⟨b', bs⟩⟩
  · simp at h2
  · simp at h2
  rcases carry with _ | ⟨c, cs⟩
  · simp at hc
  simp only [List.tail_cons, addInPlace, Challenge.gateSlots_append]
  rw [addInPlace_slots_cin (a' :: as) (b' :: bs) cs cin c]
  simp [Challenge.gateSlots, Challenge.instructionSlots, majority, eraseCarry]
  omega


/-- `subInPlace` with the bit-0 carry pair replaced: valid when `x₀ ∧ ¬y₀` is false. -/
def subLowNC (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addLowNC x y carry cin ++ notRegister y

theorem subLowNC_correct (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) (s : State) (m : List Bool)
    (hclean : ∀ q ∈ carry, s.basis q = false)
    (hnc : (s.basis (x.headD 0) && !s.basis (y.headD 0)) = false) (hcin : s.basis cin = false) :
    (run (subLowNC x y carry cin) m s).phase = s.phase ∧
    (∀ q, q ∉ y → (run (subLowNC x y carry cin) m s).basis q = s.basis q) ∧
    regValue y (run (subLowNC x y carry cin) m s).basis =
      (regValue y s.basis + 2^y.length - regValue x s.basis - (s.basis cin).toNat) % 2^y.length := by
  have words := List.nodup_cons.mp hn
  have split := List.nodup_append'.mp (show (x++(y++carry)).Nodup from by simpa only [List.append_assoc] using words.2)
  have nd := List.nodup_append'.mp split.2.1
  let u : State := ⟨s.phase, fun q => if q ∈ y then !s.basis q else s.basis q⟩
  have ci : cin ∉ y := fun h => words.1 (by simp [h])
  have clean : ∀ q ∈ carry, u.basis q = false := by
    intro q hq; have away : q ∉ y := fun h => List.disjoint_left.mp nd.2.2 h hq
    simp only [show u.basis q = s.basis q from by simp [u, away], hclean q hq]
  have source : regValue x u.basis = regValue x s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u, show q ∉ y from fun h => List.disjoint_left.mp split.2.2 hq (by simp [h])])
  have input : regValue y u.basis = 2^y.length - 1 - regValue y s.basis := by
    rw [regValue_congr y _ (fun q => !s.basis q) (by intro q hq; simp [u, hq]), regValue_complement]
  have hx0 : u.basis (x.headD 0) = s.basis (x.headD 0) := by
    rcases x with _ | ⟨a, as⟩
    · simp at hx; omega
    · have : a ∉ y := fun h => List.disjoint_left.mp split.2.2 List.mem_cons_self (by simp [h])
      simp [u, this]
  have hy0 : u.basis (y.headD 0) = !s.basis (y.headD 0) := by
    rcases y with _ | ⟨b, bs⟩
    · simp at h2
    · simp [u]
  have add := addLowNC_correct x y carry cin hn hx hc h2 u m clean
    (by rw [hx0, hy0]; exact hnc) (by simp [u, ci, hcin])
  have sw := BalancedInverse.complement_sandwich y nd.1 (addLowNC x y carry cin)
    (regValue x s.basis) (s.basis cin).toNat s m
    (by simpa only [hx] using regValue_lt x s.basis) (by cases s.basis cin <;> decide)
    (by simpa only [source, input, show u.basis cin = s.basis cin from by simp [u, ci]] using add)
  simpa only [subLowNC, List.append_assoc] using sw

theorem subLowNC_counts (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    toffoliCount (subLowNC x y carry cin) + 1 = toffoliCount (subInPlace x y carry cin) ∧
    measurementCount (subLowNC x y carry cin) = measurementCount (subInPlace x y carry cin) := by
  have h := addLowNC_counts x y carry cin hx hc h2
  simp only [subLowNC, subInPlace, toffoliCount_append, measurementCount_append,
    (notRegister_counts y).1, (notRegister_counts y).2]
  omega

theorem subLowNC_wires_sub (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    wires (subLowNC x y carry cin) ⊆ wires (subInPlace x y carry cin) := by
  have h := addLowNC_wires_sub x y carry cin hx hc h2
  simp only [subLowNC, subInPlace, wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with (h1 | h1) | h1
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (h h1))
  · exact Or.inr h1

theorem subLowNC_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hx : 1 ≤ x.length) (hy : 1 ≤ y.length) :
    GatePhysical (subLowNC x y carry cin) := by
  simp only [subLowNC, gatePhysical_append]
  exact ⟨⟨notRegister_physical _, addLowNC_physical x y carry cin hn hx hy⟩, notRegister_physical _⟩

theorem subLowNC_slots (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    Challenge.gateSlots (subLowNC x y carry cin) ≤ Challenge.gateSlots (subInPlace x y carry cin) := by
  have h := addLowNC_slots x y carry cin hx hc h2
  simp only [subLowNC, subInPlace, Challenge.gateSlots_append]
  omega


/-- The lowest wire of a nonempty register is its value's parity. -/
theorem head_bit (r tail : List Wire) (st : BasisState) (hne : r ≠ []) :
    st ((r ++ tail).headD 0) = decide (regValue r st % 2 = 1) := by
  match r, hne with
  | w :: ws, _ =>
    simp only [List.cons_append, List.headD_cons]
    rw [foldr_cons_value]
    by_cases hw : st w = true
    · rw [hw]; simp only [if_true]; simp
    · simp only [Bool.not_eq_true] at hw; rw [hw]; simp

end ECDSAAdd.Entrant.LowZero
end -- original module boundary


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
