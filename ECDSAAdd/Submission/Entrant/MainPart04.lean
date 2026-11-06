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
import ECDSAAdd.Submission.Entrant.TerminalGraph


-- Consolidated source module: MainPart04
section

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


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.LowZero18KRegs =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.DiagSquare
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero

/-! The LowZero wrappers from accepted606afa1e, with the checked old KRegs layout. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)

/-- `m8` with the dead lowest carry dropped: its source `T = 2ab` is even and `cin` is clean. -/
def m8z : Program := LowZero.addLow0 (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin

theorem m8z_lens (w : R.W) : (R.T++R.zM).length=R.dmid.length ∧
    (R.carry.take (R.dmid.length-1)).length+1=R.dmid.length ∧ 2≤R.dmid.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega

theorem m8z_counts (w : R.W) : toffoliCount R.m8z+1=toffoliCount R.m8 ∧
    measurementCount R.m8z=measurementCount R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_counts_rel _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_wires (w : R.W) : wires R.m8z⊆wires R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_wires_sub _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_slots (w : R.W) : Challenge.gateSlots R.m8z≤Challenge.gateSlots R.m8 := by
  have l := R.m8z_lens w
  exact LowZero.addLow0_slots _ _ _ _ l.1 l.2.1 l.2.2

theorem m8z_physical (hn : R.all.Nodup) : GatePhysical R.m8z :=
  LowZero.addLow0_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))

theorem m8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (k : Nat)
    (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hT : regValue R.T s.basis=2*k) (hi : s.basis R.cin=false) :
    (run R.m8z m s).phase=s.phase ∧
    (∀q,q∉R.dmid → (run R.m8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.m8z m s).basis=
      (regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis+(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  have hTl := w.T; have hSl := w.S
  have ne : R.T≠[] := by
    intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
  exact LowZero.addLow0_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl (LowZero.head_false_of_even R.T R.zM s.basis k hT ne) hi

/-- `m7` (`T -= b²`) with its dead lowest carry dropped: bit 0 of `T = 2ab+b²` equals bit 0 of `b²`. -/
def m7z : Program := LowZero.subLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
/-- `c8` (`dmid -= T`) with its dead lowest carry dropped: `T = 2ab` is even. -/
def c8z : Program := LowZero.subLowNC (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
/-- `c7` (`T += b²`) with its dead lowest carry dropped: `T = 2ab` is even. -/
def c7z : Program := LowZero.addLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin

theorem t_lens (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dhi++R.zB).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega

theorem T_ne (w : R.W) : R.T≠[] := by
  have hTl := w.T; have hSl := w.S
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega

theorem dhi_ne (w : R.W) : R.dhi≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega

theorem m7z_counts (w : R.W) : toffoliCount R.m7z+1=toffoliCount R.m7 ∧
    measurementCount R.m7z=measurementCount R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_counts (w : R.W) : toffoliCount R.c7z+1=toffoliCount R.c7 ∧
    measurementCount R.c7z=measurementCount R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_counts (w : R.W) : toffoliCount R.c8z+1=toffoliCount R.c8 ∧
    measurementCount R.c8z=measurementCount R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_wires (w : R.W) : wires R.m7z⊆wires R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_wires (w : R.W) : wires R.c7z⊆wires R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_wires (w : R.W) : wires R.c8z⊆wires R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_wires_sub _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_slots (w : R.W) : Challenge.gateSlots R.m7z≤Challenge.gateSlots R.m7 := by
  have l := R.t_lens w
  exact LowZero.subLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7z_slots (w : R.W) : Challenge.gateSlots R.c7z≤Challenge.gateSlots R.c7 := by
  have l := R.t_lens w
  exact LowZero.addLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c8z_slots (w : R.W) : Challenge.gateSlots R.c8z≤Challenge.gateSlots R.c8 := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_slots _ _ _ _ l.1 l.2.1 l.2.2

theorem m7z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.m7z := by
  have l := R.t_lens w
  exact LowZero.subLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) l.2.2.2 (by omega)
theorem c7z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.c7z := by
  have l := R.t_lens w
  exact LowZero.addLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) l.2.2.2 (by omega)
theorem c8z_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.c8z := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) (by omega) (by omega)

theorem m7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7z m s).basis=
      (regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi
theorem c8z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hnc : (s.basis ((R.T++R.zM).headD 0) && !s.basis (R.dmid.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c8z m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.c8z m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.c8z m s).basis=
      (regValue R.dmid s.basis+2^R.dmid.length-regValue (R.T++R.zM) s.basis-(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8z_lens w
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl hnc hi
theorem c7z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c7z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7z m s).basis=
      (regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lens w
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi


end ECDSAAdd.Entrant.KRegs
end -- original module boundary


section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero
open ECDSAAdd ECDSAAdd.Arithmetic
/-! ### Guarded forms

The guarded programs fall back to the untrimmed adder when the register lengths are
degenerate, so their slot bound holds without any width hypothesis. -/

def addLow0G (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then addLow0 x y carry cin
  else addInPlace x y carry cin
def addLowNCG (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then addLowNC x y carry cin
  else addInPlace x y carry cin
def subLowNCG (x y carry : List Wire) (cin : Wire) : Program :=
  if x.length = y.length ∧ carry.length + 1 = y.length ∧ 2 ≤ y.length then subLowNC x y carry cin
  else subInPlace x y carry cin

theorem addLow0G_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    addLow0G x y carry cin = addLow0 x y carry cin := if_pos ⟨hx, hc, h2⟩
theorem addLowNCG_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    addLowNCG x y carry cin = addLowNC x y carry cin := if_pos ⟨hx, hc, h2⟩
theorem subLowNCG_eq (x y carry : List Wire) (cin : Wire) (hx : x.length = y.length)
    (hc : carry.length + 1 = y.length) (h2 : 2 ≤ y.length) :
    subLowNCG x y carry cin = subLowNC x y carry cin := if_pos ⟨hx, hc, h2⟩

theorem addLow0G_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLow0G x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLow0G; split
  · next h => exact addLow0_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _
theorem addLowNCG_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLowNCG x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _
theorem subLowNCG_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subLowNCG x y carry cin) ≤ Challenge.gateSlots (subInPlace x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_slots x y carry cin h.1 h.2.1 h.2.2
  · exact le_refl _

theorem addLow0G_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (addLow0G x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  unfold addLow0G; split
  · next h => exact addLow0_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _
theorem addLowNCG_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (addLowNCG x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _
theorem subLowNCG_wires_sub (x y carry : List Wire) (cin : Wire) :
    wires (subLowNCG x y carry cin) ⊆ wires (subInPlace x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_wires_sub x y carry cin h.1 h.2.1 h.2.2
  · exact subset_refl _

theorem nodup_assoc (cin : Wire) (x y carry : List Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup) :
    (cin :: x ++ y ++ carry).Nodup := by
  simpa only [List.cons_append, List.append_assoc] using hn

theorem addLow0G_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLow0G x y carry cin) := by
  unfold addLow0G; split
  · exact addLow0_physical x y carry cin hn
  · exact addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)
theorem addLowNCG_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (addLowNCG x y carry cin) := by
  unfold addLowNCG; split
  · next h => exact addLowNC_physical x y carry cin hn (by omega) (by omega)
  · exact addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)
theorem subLowNCG_physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) : GatePhysical (subLowNCG x y carry cin) := by
  unfold subLowNCG; split
  · next h => exact subLowNC_physical x y carry cin hn (by omega) (by omega)
  · simp only [subInPlace, gatePhysical_append]
    exact ⟨⟨notRegister_physical _, addInPlace_physical x y carry cin (nodup_assoc cin x y carry hn)⟩,
      notRegister_physical _⟩

end ECDSAAdd.Entrant.LowZero

namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)
/-! Low-bit carry trims (LowZero): each `*z` program drops the dead bit-0 carry of the
corresponding Karatsuba combination adder. -/
theorem m8g_lens (w : R.W) : (R.T++R.zM).length=R.dmid.length ∧
    (R.carry.take (R.dmid.length-1)).length+1=R.dmid.length ∧ 2≤R.dmid.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
theorem t_lensg (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dhi++R.zB).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem lo_lens (w : R.W) : (R.dlo++R.zA).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length ∧ 1≤(R.dlo++R.zA).length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.length_append]; omega
  · simp only [List.length_take]; omega
  · omega
  · simp only [List.length_append]; omega
theorem T_neg (w : R.W) : R.T≠[] := by
  have hTl := w.T; have hSl := w.S
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dhi_neg (w : R.W) : R.dhi≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
theorem dlo_ne (w : R.W) : R.dlo≠[] := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  intro e; have e' := congrArg List.length e; simp only [List.length_nil] at e'; omega
def m8g : Program := LowZero.addLow0G (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem m8g_counts (w : R.W) : toffoliCount R.m8g+1=toffoliCount R.m8 ∧
    measurementCount R.m8g=measurementCount R.m8 := by
  have l := R.m8g_lens w
  unfold m8g; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_counts_rel _ _ _ _ l.1 l.2.1 l.2.2
theorem m8g_wires : wires R.m8g⊆wires R.m8 := LowZero.addLow0G_wires_sub _ _ _ _
theorem m8g_slots : Challenge.gateSlots R.m8g≤Challenge.gateSlots R.m8 := LowZero.addLow0G_slots _ _ _ _
theorem m8g_physical (hn : R.all.Nodup) : GatePhysical R.m8g :=
  LowZero.addLow0G_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m8g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (k : Nat) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hT : regValue R.T s.basis=2*k) (hi : s.basis R.cin=false) :
    (run R.m8g m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.m8g m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.m8g m s).basis=(regValue (R.T++R.zM) s.basis+regValue R.dmid s.basis+(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8g_lens w
  unfold m8g; rw [LowZero.addLow0G_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.addLow0_correct _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl (LowZero.head_false_of_even R.T R.zM s.basis k hT (R.T_neg w)) hi

def m7g : Program := LowZero.subLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m7g_counts (w : R.W) : toffoliCount R.m7g+1=toffoliCount R.m7 ∧
    measurementCount R.m7g=measurementCount R.m7 := by
  have l := R.t_lensg w
  unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m7g_wires : wires R.m7g⊆wires R.m7 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m7g_slots : Challenge.gateSlots R.m7g≤Challenge.gateSlots R.m7 := LowZero.subLowNCG_slots _ _ _ _
theorem m7g_physical (hn : R.all.Nodup) : GatePhysical R.m7g :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m7g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m7g m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7g m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7g m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c8g : Program := LowZero.subLowNCG (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
theorem c8g_counts (w : R.W) : toffoliCount R.c8g+1=toffoliCount R.c8 ∧
    measurementCount R.c8g=measurementCount R.c8 := by
  have l := R.m8g_lens w
  unfold c8g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2
theorem c8g_wires : wires R.c8g⊆wires R.c8 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem c8g_slots : Challenge.gateSlots R.c8g≤Challenge.gateSlots R.c8 := LowZero.subLowNCG_slots _ _ _ _
theorem c8g_physical (hn : R.all.Nodup) : GatePhysical R.c8g :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c8g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.dmid.length-1),s.basis q=false)
    (hnc : (s.basis ((R.T++R.zM).headD 0) && !s.basis (R.dmid.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c8g m s).phase=s.phase ∧ (∀q,q∉R.dmid → (run R.c8g m s).basis q=s.basis q) ∧
    regValue R.dmid (run R.c8g m s).basis=(regValue R.dmid s.basis+2^R.dmid.length-regValue (R.T++R.zM) s.basis-(s.basis R.cin).toNat)%2^R.dmid.length := by
  have l := R.m8g_lens w
  unfold c8g; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2 s m hcl hnc hi

def c7g : Program := LowZero.addLowNCG (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c7g_counts (w : R.W) : toffoliCount R.c7g+1=toffoliCount R.c7 ∧
    measurementCount R.c7g=measurementCount R.c7 := by
  have l := R.t_lensg w
  unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c7g_wires : wires R.c7g⊆wires R.c7 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c7g_slots : Challenge.gateSlots R.c7g≤Challenge.gateSlots R.c7 := LowZero.addLowNCG_slots _ _ _ _
theorem c7g_physical (hn : R.all.Nodup) : GatePhysical R.c7g :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c7g_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c7g m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7g m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7g m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def m6z : Program := LowZero.subLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem m6z_counts (w : R.W) : toffoliCount R.m6z+1=toffoliCount R.m6 ∧
    measurementCount R.m6z=measurementCount R.m6 := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem m6z_wires : wires R.m6z⊆wires R.m6 := LowZero.subLowNCG_wires_sub _ _ _ _
theorem m6z_slots : Challenge.gateSlots R.m6z≤Challenge.gateSlots R.m6 := LowZero.subLowNCG_slots _ _ _ _
theorem m6z_physical (hn : R.all.Nodup) : GatePhysical R.m6z :=
  LowZero.subLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem m6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.m6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.m6z m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dlo++R.zA) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.subLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

def c6z : Program := LowZero.addLowNCG (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
theorem c6z_counts (w : R.W) : toffoliCount R.c6z+1=toffoliCount R.c6 ∧
    measurementCount R.c6z=measurementCount R.c6 := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_counts _ _ _ _ l.1 l.2.1 l.2.2.1
theorem c6z_wires : wires R.c6z⊆wires R.c6 := LowZero.addLowNCG_wires_sub _ _ _ _
theorem c6z_slots : Challenge.gateSlots R.c6z≤Challenge.gateSlots R.c6 := LowZero.addLowNCG_slots _ _ _ _
theorem c6z_physical (hn : R.all.Nodup) : GatePhysical R.c6z :=
  LowZero.addLowNCG_physical _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
theorem c6z_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false) :
    (run R.c6z m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c6z m s).basis q=s.basis q) ∧
    regValue R.T (run R.c6z m s).basis=(regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.lo_lens w
  unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
  exact LowZero.addLowNC_correct _ _ _ _ (knd hn (fun q => by
    have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    l.1 l.2.1 l.2.2.1 s m hcl hnc hi

end ECDSAAdd.Entrant.KRegs

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- `rawMake` with the dead lowest carry of the first signed row copied (TrimRow), and, for odd leaves,
the dead top carry of the middle signed row copied too (TrimMid). -/
def rawMakeT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimMid.mkP xs dst pad carry

/-- `rawClear` with the same dead carries copied. -/
def rawClearT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimMid.clP xs dst pad carry

/-- Number of odd leaves (each saves one more Toffoli) among the three leaf squares of `R`. -/
def parR (R : KRegs) : Nat :=
  ECDSAAdd.Entrant.TrimMid.par R.lo.length+ECDSAAdd.Entrant.TrimMid.par R.hi.length+
    ECDSAAdd.Entrant.TrimMid.par R.S.length

theorem parR_eq (R : KRegs) (w : R.W) :
    parR R=ECDSAAdd.Entrant.TrimMid.par R.h+ECDSAAdd.Entrant.TrimMid.par (R.bank.length-R.h)+
      ECDSAAdd.Entrant.TrimMid.par (R.bank.length-R.h+1) := by
  obtain ⟨L0,L1,-⟩ := R.lens w
  rw [parR,L0,L1,w.S]

theorem rawMakeT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMakeT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMakeT xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMakeT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimMid.mkP_exists xs dst pad carry hn hx hd hp hc s m h0 hp0 hc0
  rw [rawMakeT,hR]
  exact rawMake_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawClearT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClearT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClearT xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClearT xs dst pad carry) m s).basis q=s.basis q := by
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
  obtain ⟨R1,h1⟩ := ECDSAAdd.Entrant.TrimMid.clP_exists xs dst pad carry hn hx hd hp hc base d0 p0 c0 m
  have h1' : run (rawClearT xs dst pad carry) m s=run (ECDSAAdd.Entrant.TrimRow.cl xs dst pad carry) R1 s := by
    rw [← same]; exact h1
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.cl_exists xs dst pad carry hn hx hd hp hc s R1 h0 hc0
  rw [h1',hR]
  exact rawClear_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (rawMakeT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=toffoliCount (rawMake xs dst pad carry) ∧
      measurementCount (rawMakeT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=measurementCount (rawMake xs dst pad carry)) ∧
    (toffoliCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=measurementCount (rawClear xs dst pad carry)) := by
  have a := ECDSAAdd.Entrant.TrimRow.counts xs dst pad carry hx hd hp hc
  have b := ECDSAAdd.Entrant.TrimMid.P_counts xs dst pad carry hx hd hp hc
  simp only [rawMakeT,rawClearT,rawMake,rawClear] at a b ⊢
  exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

theorem rawT_slots (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawMakeT xs dst pad carry)≤Challenge.gateSlots (rawMake xs dst pad carry) ∧
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) :=
  ⟨(ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).1.2.1.trans (ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry).1,
    (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).2.2.1.trans (ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry).2⟩

theorem rawT_wires (xs dst pad carry : List Wire) (X : Finset Wire)
    (h1 : wires (signedSquareRows xs dst pad carry)⊆X) (h2 : wires (signedSquareTop xs dst)⊆X)
    (h3 : wires (signedSquareRowsClear xs dst pad carry)⊆X) :
    wires (rawMakeT xs dst pad carry)⊆X ∧ wires (rawClearT xs dst pad carry)⊆X := by
  have w := ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry
  have p := ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry
  simp only [wires_append] at w
  exact ⟨p.1.1.trans (w.1.trans (Finset.union_subset h1 h2)),p.2.1.trans (w.2.trans (Finset.union_subset h2 h3))⟩

theorem rawT_physical (xs dst pad carry : List Wire)
    (h1 : GatePhysical (signedSquareRows xs dst pad carry)) (h2 : GatePhysical (signedSquareTop xs dst))
    (h3 : GatePhysical (signedSquareRowsClear xs dst pad carry)) :
    GatePhysical (rawMakeT xs dst pad carry) ∧ GatePhysical (rawClearT xs dst pad carry) := by
  have t := ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,h3⟩)
  have p := ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry
  exact ⟨p.1.2.2 t.1,p.2.2.2 t.2⟩


def seedsT (R : KRegs) : Program :=
  rawMakeT R.lo R.dlo R.pad R.carry ++ rawMakeT R.hi R.dhi R.pad R.carry ++ R.smk ++
    rawMakeT R.S R.T R.pad R.carry

theorem seedsT_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (seedsT R) m s)
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
      (rawMakeT R.lo R.dlo R.pad R.carry) := by
    intro t rec ht
    have lt := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have r := rawMakeT_correct R.lo R.dlo R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 0 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 0) (run (rawMakeT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h a : Nat) [ZMOD (2^(reg R 0).length : Nat)] := by
      change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,lt,L0]; rfl
    simpa only [vec0] using ht.step hn 0 (rawValue R.h a) r.1 r.2.2 v
  have hiStep : Transition R s (vec (rawValue R.h a) 0 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) 0 0) (rawMakeT R.hi R.dhi R.pad R.carry) := by
    intro t rec ht
    have ht0 := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := rawMakeT_correct R.hi R.dhi R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 1 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 1) (run (rawMakeT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡
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
      (rawMakeT R.S R.T R.pad R.carry) := by
    intro t rec ht
    have av := regValue_lt R.lo s.basis
    have bv := regValue_lt R.hi s.basis
    rw [L0] at av; rw [hhi] at bv
    have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
    have sv := ht.exact 2 (a+b) rfl slt
    change regValue R.S t.basis=a+b at sv
    have r := rawMakeT_correct R.S R.T R.pad R.carry
      (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      (by omega) hTl hpl (by omega) t rec
      (ht.exact 3 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 3) (run (rawMakeT R.S R.T R.pad R.carry) rec t).basis : Int) ≡
        (rawValue (R.h+1) (a+b) : Nat) [ZMOD (2^(reg R 3).length : Nat)] := by
      change (regValue R.T _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,sv,hSS]; rfl
    simpa only [vec3] using ht.step hn 3 (rawValue (R.h+1) (a+b)) r.1 r.2.2 v
  exact (((loStep.seq hiStep).seq sumStep).seq sqStep) s m init



theorem rawClearT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawClearT xs dst pad carry)⊆wires (rawClear xs dst pad carry) := by
  unfold rawClearT rawClear
  exact (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).2.1.trans (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).2
theorem rawClearT_slots_le (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) := by
  exact (rawT_slots xs dst pad carry).2
theorem rawClearT_physical_of (xs dst pad carry : List Wire) (hm : GatePhysical (rawMake xs dst pad carry))
    (hc : GatePhysical (rawClear xs dst pad carry)) : GatePhysical (rawClearT xs dst pad carry) := by
  unfold rawClearT; exact (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).2.2.2 (ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry hm hc).2
theorem rawClearT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length) :
    toffoliCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1+ECDSAAdd.Entrant.TrimMid.par xs.length=measurementCount (rawClear xs dst pad carry) :=
  (rawT_counts xs dst pad carry hx hd hp hc).2

theorem rawclearlo_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (B S T : Int) :
    Transition R base (vec (rawValue R.h (regValue R.lo base.basis)) B S T) (vec 0 B S T) (rawClearT R.lo R.dlo R.pad R.carry) := by
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
  have r := rawClearT_correct R.lo R.dlo R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 0) (run (rawClearT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 0).length : Nat)] := by
    change (regValue R.dlo _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec0] using ht.step hn 0 0 r.1 r.2.2 val

theorem rawclearhi_transitionT (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (A S T : Int) :
    Transition R base (vec A (rawValue R.h (regValue R.hi base.basis)) S T) (vec A 0 S T) (rawClearT R.hi R.dhi R.pad R.carry) := by
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
  have r := rawClearT_correct R.hi R.dhi R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 1) (run (rawClearT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 1).length : Nat)] := by
    change (regValue R.dhi _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec1] using ht.step hn 1 0 r.1 r.2.2 val

theorem rawclearSum_transitionT (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hp0 : regValue R.pad base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (A B : Int) (S : Nat) (hS : S<2^R.S.length) :
    Transition R base (vec A B S (rawValue R.S.length S)) (vec A B S 0)
      (rawClearT R.S R.T R.pad R.carry) := by
  intro t rec ht
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hpl := w.pad
  have sv := ht.exact 2 S rfl hS
  change regValue R.S t.basis=S at sv
  have rb := rawValue_bound R.S t.basis (by omega)
  rw [sv] at rb
  have dv := ht.exact 3 (rawValue R.S.length S) rfl (by change _<2^R.T.length; rw [htl]; exact rb)
  change regValue R.T t.basis=_ at dv
  have r := rawClearT_correct R.S R.T R.pad R.carry
    (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by omega) htl hpl (by omega) t rec (by rw [sv]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 3) (run (rawClearT R.S R.T R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 3).length : Nat)] := by
    change (regValue R.T _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec3] using ht.step hn 3 0 r.1 r.2.2 val

end ECDSAAdd.Entrant.DiagSq

section
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Constant `+1` on the top three bits with a clean carry-in: the bit-0 majority of a
constant-one bit is `[CX y c, CX cin c, CCX y cin c]`, and its Toffoli is the identity
while `cin = 0`. `incr1` drops it. -/

theorem ccx_noop (a b t : Wire) (p : Program) (m : List Bool) (s : State) (h : s.basis b=false) :
    run (.CCX a b t :: p) m s=run p m s := by
  have e : (⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩ : State)=s := by
    obtain ⟨ph,bs⟩ := s
    simp only at h
    congr 1
    funext q
    by_cases hq : q=t
    · subst hq; simp [writeBit,h]
    · simp [writeBit,Function.update,hq]
  simp only [run]
  rw [e]

theorem run_cx_cx_ccx (y cin c : Wire) (X : Program) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hcc : cin≠c) :
    run (.CX y c :: .CX cin c :: .CCX y cin c :: X) m s=run (.CX y c :: .CX cin c :: X) m s := by
  let t1 : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis y)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis c (t1.basis c ^^ t1.basis cin)⟩
  have ht2 : t2.basis cin=false := by
    simp [t2,t1,writeBit,Function.update,hcc,hi]
  calc run (.CX y c :: .CX cin c :: .CCX y cin c :: X) m s=run (.CCX y cin c :: X) m t2 := rfl
    _=run X m t2 := ccx_noop _ _ _ _ _ _ ht2
    _=run (.CX y c :: .CX cin c :: X) m s := rfl

def incr1 (ys carry : List Wire) (cin : Wire) : Program :=
  match ys, carry with
  | y::y'::ys', c::cs => [.CX y c,.CX cin c]++mappedAdd (mappedConstant none 2 0) (y'::ys') cs c++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin
  | _, _ => mappedAdd (mappedConstant none 3 1) ys carry cin

theorem incr1_split (y y' c cin : Wire) (ys cs : List Wire) :
    mappedAdd (mappedConstant none 3 1) (y::y'::ys) (c::cs) cin=
      [.CX y c,.CX cin c,.CCX y cin c]++(mappedAdd (mappedConstant none 2 0) (y'::ys) cs c++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin) := by
  simp [mappedConstant,mappedAdd,mappedMajority,mappedConstantBit,List.append_assoc]

theorem incr1_run (ys carry : List Wire) (cin : Wire) (s : State) (m : List Bool)
    (hi : s.basis cin=false) (hc : ∀c∈carry.take 1,cin≠c) :
    run (incr1 ys carry cin) m s=run (mappedAdd (mappedConstant none 3 1) ys carry cin) m s := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  have hcc : cin≠c := hc c (by simp)
  rw [incr1_split]
  simp only [incr1,List.append_assoc,List.cons_append,List.nil_append]
  exact (run_cx_cx_ccx y cin c _ m s hi hcc).symm

theorem incr1_mc (ys carry : List Wire) (cin : Wire) :
    measurementCount (incr1 ys carry cin)=measurementCount (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

def decr1 (ys carry : List Wire) (cin : Wire) : Program :=
  notRegister ys++incr1 ys carry cin++notRegister ys

theorem decr1_run (ys carry : List Wire) (cin : Wire) (s : State) (m : List Bool)
    (hi : s.basis cin=false) (hc : ∀c∈carry.take 1,cin≠c) (hy : cin∉ys) (hyn : ys.Nodup) :
    run (decr1 ys carry cin) m s=run (mappedSub (mappedConstant none 3 1) ys carry cin) m s := by
  have hm : measurementCount (notRegister ys)=0 := (notRegister_counts ys).2
  have nr := notRegister_correct ys hyn s []
  simp only [decr1,mappedSub,List.append_assoc]
  rw [run_append (notRegister ys),run_append (notRegister ys),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (incr1 ys carry cin),run_append (mappedAdd (mappedConstant none 3 1) ys carry cin),incr1_mc,
    incr1_run ys carry cin _ _ (by rw [nr]; simp [hy,hi]) hc]

theorem incr1_mem (ys carry : List Wire) (cin : Wire) :
    ∀i∈incr1 ys carry cin,i∈mappedAdd (mappedConstant none 3 1) ys carry cin := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try (intro i h; exact h)
  rw [incr1_split]
  intro i h
  simp only [incr1,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem incr1_counts (ys carry : List Wire) (cin : Wire) (h2 : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (incr1 ys carry cin)+1=toffoliCount (mappedAdd (mappedConstant none 3 1) ys carry cin) ∧
    measurementCount (incr1 ys carry cin)=measurementCount (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> simp at h2 hc
  rw [incr1_split]
  simp only [incr1,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem incr1_slots (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (incr1 ys carry cin)≤Challenge.gateSlots (mappedAdd (mappedConstant none 3 1) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try exact le_refl _
  rw [incr1_split]
  simp only [incr1,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]
  omega

theorem wires_of_mem {p q : Program} (h : ∀i∈p,i∈q) : wires p⊆wires q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [wires]
    apply Finset.union_subset
    · intro w hw
      have hq := h i (by simp)
      clear h ih
      induction q with
      | nil => simp at hq
      | cons j q ihq =>
        simp only [wires,Finset.mem_union]
        rcases List.mem_cons.mp hq with e|e
        · subst e; exact Or.inl hw
        · exact Or.inr (ihq e)
    · exact ih (fun j hj => h j (by simp [hj]))

def correctionZ (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h ++
    incr1 (dst.drop (2*h-1)) (carry.take 2) cin

def correctionBackZ (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  decr1 (dst.drop (2*h-1)) (carry.take 2) cin ++
  loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h

theorem correctionZ_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)+
      (2^(2*h-1) : Nat)) s (run (correctionZ h as bs ss dst carry q cin) m s) := by
  let P := loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h
  have r := sharedSub_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s
    (m.take (measurementCount P)) hv hq0 hi0 hc0
  have out (w : Wire) (hw : w∈cin::carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have ui : (run P (m.take (measurementCount P)) s).basis cin=false := (r.2.1 cin (out cin (by simp))).trans hi0
  have hc : ∀c∈(carry.take 2).take 1,cin≠c := by
    intro c hc e; subst e
    have := List.mem_of_mem_take (List.mem_of_mem_take hc)
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [this])
  have e : run (correctionZ h as bs ss dst carry q cin) m s=run (correction h as bs ss dst carry q cin) m s := by
    simp only [correctionZ,correction,run_append]
    exact incr1_run _ _ _ _ _ ui hc
  rw [e]
  exact correction_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s m hv hq0 hi0 hc0

theorem correctionBackZ_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)-
      (2^(2*h-1) : Nat)) s (run (correctionBackZ h as bs ss dst carry q cin) m s) := by
  have hc : ∀c∈(carry.take 2).take 1,cin≠c := by
    intro c hc e; subst e
    have := List.mem_of_mem_take (List.mem_of_mem_take hc)
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [this])
  have hy : cin∉dst.drop (2*h-1) := by
    intro hy
    have h0 := (List.nodup_cons.mp hn).1
    exact h0 (by simp [List.mem_of_mem_drop hy])
  have hyn : (dst.drop (2*h-1)).Nodup := by
    apply List.Nodup.sublist (List.drop_sublist _ _)
    exact nd_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega)
  have e : run (correctionBackZ h as bs ss dst carry q cin) m s=run (correctionBack h as bs ss dst carry q cin) m s := by
    simp only [correctionBackZ,correctionBack,run_append]
    have mc : measurementCount (decr1 (dst.drop (2*h-1)) (carry.take 2) cin)=
        measurementCount (mappedSub (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin) := by
      have a := incr1_counts (dst.drop (2*h-1)) (carry.take 2) cin
        (by simp only [List.length_drop]; rcases hh with rfl|rfl <;> omega)
        (by simp only [List.length_take]; omega)
      simp only [decr1,mappedSub,measurementCount_append,a.2]
    rw [mc,decr1_run _ _ _ _ _ hi0 hc hy hyn]
  rw [e]
  exact correctionBack_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s m hv hq0 hi0 hc0

def corrZ (R : KRegs) : Program := correctionZ R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
def corrBackZ (R : KRegs) : Program := correctionBackZ R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin

theorem corrZ_mem (R : KRegs) : ∀i∈corrZ R,i∈corr R := by
  intro i h
  simp only [corrZ,corr,correctionZ,correction,List.mem_append] at h ⊢
  rcases h with h|h
  · exact Or.inl h
  · exact Or.inr (incr1_mem _ _ _ i h)
theorem corrBackZ_mem (R : KRegs) : ∀i∈corrBackZ R,i∈corrBack R := by
  intro i h
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,List.mem_append] at h ⊢
  rcases h with ((h|h)|h)|h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (incr1_mem _ _ _ i h)))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem corrZ_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrZ R)+1=toffoliCount (corr R) ∧ measurementCount (corrZ R)=measurementCount (corr R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr1_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrZ,corr,correctionZ,correction,toffoliCount_append,measurementCount_append]
  omega
theorem corrBackZ_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrBackZ R)+1=toffoliCount (corrBack R) ∧ measurementCount (corrBackZ R)=measurementCount (corrBack R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr1_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,toffoliCount_append,measurementCount_append]
  omega
theorem corrZ_slots (R : KRegs) : Challenge.gateSlots (corrZ R)≤Challenge.gateSlots (corr R) := by
  have a := incr1_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrZ,corr,correctionZ,correction,Challenge.gateSlots_append]
  omega
theorem corrBackZ_slots (R : KRegs) : Challenge.gateSlots (corrBackZ R)≤Challenge.gateSlots (corrBack R) := by
  have a := incr1_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrBackZ,corrBack,correctionBackZ,correctionBack,decr1,mappedSub,Challenge.gateSlots_append]
  omega

theorem corrZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T-((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)+(2^(2*R.h-1) : Nat))) (corrZ R) := by
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
  have r := correctionZ_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring

theorem corrBackZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T+((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)-(2^(2*R.h-1) : Nat))) (corrBackZ R) := by
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
  have r := correctionBackZ_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring


end ECDSAAdd.Entrant.DiagSq
end

section
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Diagonal add/subtract whose lowest target bit is known. The bit-0 majority of
`mappedAdd (mappedDiagonal xs)` is `majority x₀ y₀ cin c`; with `cin = 0` its Toffoli
fires on `(y₀ ⊕ x₀) ∧ x₀`, which is zero whenever `x₀ → y₀`. For the subtraction
(complemented target) this holds when the target is even, for the addition when the
target's bit 0 equals `x₀`. `addHead0` drops that Toffoli (its carry is then just `x₀`). -/

theorem ccx_noop2 (a b t : Wire) (p : Program) (m : List Bool) (s : State)
    (h : (s.basis a && s.basis b)=false) : run (.CCX a b t :: p) m s=run p m s := by
  have e : (⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis a && s.basis b))⟩ : State)=s := by
    obtain ⟨ph,bs⟩ := s
    simp only at h
    congr 1
    funext q
    by_cases hq : q=t
    · subst hq; simp [writeBit,h]
    · simp [writeBit,Function.update,hq]
  simp only [run]
  rw [e]

theorem run_maj_idle (a y cin c : Wire) (X : Program) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hay : s.basis a=true → s.basis y=true)
    (h1 : a≠y) (h3 : y≠cin) :
    run (.CX a y :: .CX a cin :: .CCX y cin c :: X) m s=run (.CX a y :: .CX a cin :: X) m s := by
  let t1 : State := ⟨s.phase,writeBit s.basis y (s.basis y ^^ s.basis a)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis cin (t1.basis cin ^^ t1.basis a)⟩
  have ht2 : (t2.basis y && t2.basis cin)=false := by
    have e1 : t2.basis y=(s.basis y ^^ s.basis a) := by
      simp [t2,t1,writeBit,Function.update,h3]
    have e2 : t2.basis cin=s.basis a := by
      simp [t2,t1,writeBit,Function.update,h3.symm,h1,hi]
    rw [e1,e2]
    cases ha : s.basis a <;> cases hy : s.basis y <;> simp_all
  calc run (.CX a y :: .CX a cin :: .CCX y cin c :: X) m s=run (.CCX y cin c :: X) m t2 := rfl
    _=run X m t2 := ccx_noop2 _ _ _ _ _ _ ht2
    _=run (.CX a y :: .CX a cin :: X) m s := rfl

def maj0 (a y cin c : Wire) : Program := [.CX a y,.CX a cin,.CX a c,.CX a cin,.CX a y]

def addHead0 (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  match bits, ys, carry with
  | ⟨some a,false⟩::b'::bits', y::y'::ys', c::cs =>
      maj0 a y cin c++(mappedAdd (b'::bits') (y'::ys') cs c++
        mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin)
  | bits, ys, carry => mappedAdd bits ys carry cin

theorem addHead0_split (a y y' c cin : Wire) (b' : MappedBit) (bits : List MappedBit) (ys cs : List Wire) :
    mappedAdd (⟨some a,false⟩::b'::bits) (y::y'::ys) (c::cs) cin=
      majority a y cin c++(mappedAdd (b'::bits) (y'::ys) cs c++
        mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin) := by
  simp [mappedAdd,mappedMajority,List.append_assoc]

theorem addHead0_run (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (hay : ∀y ys',ys=y::ys' → s.basis a=true → s.basis y=true)
    (h1 : a∉ys) (h3 : cin∉ys) :
    run (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin) m s=
      run (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) m s := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,List.cons_append,List.nil_append]
  exact (run_maj_idle a y cin c _ m s hi (hay y _ rfl) (fun e => h1 (by simp [e]))
    (fun e => h3 (by simp [e]))).symm

theorem addHead0_mem (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    ∀i∈addHead0 (⟨some a,false⟩::b'::bits) ys carry cin,i∈mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try (intro i h; exact h)
  rw [addHead0_split]
  intro i h
  simp only [addHead0,maj0,majority,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem addHead0_mc (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    measurementCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)=
      measurementCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

theorem addHead0_counts (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (h2 : 2≤ys.length) (hc : 1≤carry.length) :
    toffoliCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)+1=
      toffoliCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) ∧
    measurementCount (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)=
      measurementCount (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> simp at h2 hc
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem addHead0_slots (a : Wire) (b' : MappedBit) (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHead0 (⟨some a,false⟩::b'::bits) ys carry cin)≤
      Challenge.gateSlots (mappedAdd (⟨some a,false⟩::b'::bits) ys carry cin) := by
  rcases ys with _|⟨y,_|⟨y',ys⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try exact le_refl _
  rw [addHead0_split]
  simp only [addHead0,maj0,majority,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]

theorem diag_cons (x : Wire) (xs : List Wire) :
    ∃ b' bits,mappedDiagonal (x::xs)=⟨some x,false⟩::b'::bits := by
  cases xs with
  | nil => exact ⟨_,_,rfl⟩
  | cons x' xs => exact ⟨_,_,rfl⟩

def dAddZ (xs dst carry : List Wire) (cin : Wire) : Program :=
  addHead0 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

def dSubZ (xs dst carry : List Wire) (cin : Wire) : Program :=
  notRegister dst++dAddZ xs dst carry cin++notRegister dst

theorem dAddZ_mem (xs dst carry : List Wire) (cin : Wire) :
    ∀i∈dAddZ xs dst carry cin,i∈mappedDiagAdd xs dst carry cin := by
  rcases xs with _|⟨x,xs⟩
  · intro i h; exact h
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_mem _ _ _ _ _ _

theorem dSubZ_mem (xs dst carry : List Wire) (cin : Wire) :
    ∀i∈dSubZ xs dst carry cin,i∈mappedDiagSub xs dst carry cin := by
  intro i h
  simp only [dSubZ,mappedDiagSub,mappedSub,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (dAddZ_mem xs dst carry cin i h))
  · exact Or.inr h

theorem dAddZ_counts (xs dst carry : List Wire) (cin : Wire) (hx : 0<xs.length)
    (hd : 2≤dst.length) (hc : 1≤carry.length) :
    toffoliCount (dAddZ xs dst carry cin)+1=toffoliCount (mappedDiagAdd xs dst carry cin) ∧
    measurementCount (dAddZ xs dst carry cin)=measurementCount (mappedDiagAdd xs dst carry cin) := by
  rcases xs with _|⟨x,xs⟩
  · simp at hx
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_counts _ _ _ _ _ _ hd (by simp only [List.length_take]; omega)

theorem dSubZ_counts (xs dst carry : List Wire) (cin : Wire) (hx : 0<xs.length)
    (hd : 2≤dst.length) (hc : 1≤carry.length) :
    toffoliCount (dSubZ xs dst carry cin)+1=toffoliCount (mappedDiagSub xs dst carry cin) ∧
    measurementCount (dSubZ xs dst carry cin)=measurementCount (mappedDiagSub xs dst carry cin) := by
  have a := dAddZ_counts xs dst carry cin hx hd hc
  simp only [dAddZ,mappedDiagAdd] at a
  simp only [dSubZ,dAddZ,mappedDiagSub,mappedSub,toffoliCount_append,measurementCount_append]
  omega

theorem dAddZ_slots (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dAddZ xs dst carry cin)≤Challenge.gateSlots (mappedDiagAdd xs dst carry cin) := by
  rcases xs with _|⟨x,xs⟩
  · exact le_refl _
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    exact addHead0_slots _ _ _ _ _ _

theorem dSubZ_slots (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dSubZ xs dst carry cin)≤Challenge.gateSlots (mappedDiagSub xs dst carry cin) := by
  have a := dAddZ_slots xs dst carry cin
  simp only [dAddZ,mappedDiagAdd] at a
  simp only [dSubZ,dAddZ,mappedDiagSub,mappedSub,Challenge.gateSlots_append]
  omega

theorem dAddZ_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hi : s.basis cin=false)
    (hay : ∀y ys',dst=y::ys' → s.basis (xs.headD 0)=true → s.basis y=true) :
    run (dAddZ xs dst carry cin) m s=run (mappedDiagAdd xs dst carry cin) m s := by
  rcases xs with _|⟨x,xs⟩
  · rfl
  · obtain ⟨b',bits,e⟩ := diag_cons x xs
    simp only [dAddZ,mappedDiagAdd,e]
    have hx : x∉dst := dis_count (r:=x::xs) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append]; omega) x (by simp)
    have hc : cin∉dst := dis_count (r:=[cin]) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
    exact addHead0_run x b' bits dst _ cin m s hi (by simpa using hay) hx hc

theorem dSubZ_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hi : s.basis cin=false)
    (hy : s.basis (dst.headD 0)=false) :
    run (dSubZ xs dst carry cin) m s=run (mappedDiagSub xs dst carry cin) m s := by
  have hm : measurementCount (notRegister dst)=0 := (notRegister_counts dst).2
  have hdn : dst.Nodup := nd_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct dst hdn s []
  have hc : cin∉dst := dis_count (r:=[cin]) (t:=dst) hn (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
  have mc : measurementCount (dAddZ xs dst carry cin)=measurementCount (mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) := by
    rcases xs with _|⟨x,xs⟩
    · rfl
    · obtain ⟨b',bits,e⟩ := diag_cons x xs
      simp only [dAddZ,e]
      exact addHead0_mc _ _ _ _ _ _
  simp only [dSubZ,mappedDiagSub,mappedSub,List.append_assoc]
  rw [run_append (notRegister dst),run_append (notRegister dst),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (dAddZ xs dst carry cin),run_append (mappedAdd (mappedDiagonal xs) dst _ cin),mc]
  have e := dAddZ_run xs dst carry cin (m.take (measurementCount (mappedAdd (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)))
    (run (notRegister dst) [] s) hn (by rw [nr]; simp [hc,hi]) (by
      intro y ys' e _
      subst e
      rw [nr]
      simp at hy ⊢; simp [hy])
  simp only [dAddZ,mappedDiagAdd] at e
  simp only [dAddZ]
  rw [e]

end ECDSAAdd.Entrant.DiagSq
end

section
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

/-! Bit 1 of a square is always zero (`b² mod 4 ∈ {0,1}`). In `m7g : T −= b²` and
`c7g : T += b²` the bit-0 carry is already dropped (its carry-in for bit 1 is the clean
`cin`), so the bit-1 majority has source bit `0` and carry-in `0`: its Toffoli is idle.
`addHeadI` drops the Toffoli of the first majority of an in-place adder whose first
source bit is zero. -/

def addHeadI : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::as, b::b'::bs, c::cs, cin =>
      DiagSq.maj0 a b cin c++(addInPlace (a'::as) (b'::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b])
  | x, y, c, cin => addInPlace x y c cin

theorem addHeadI_split (a a' b b' c cin : Wire) (as bs cs : List Wire) :
    addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin=
      majority a b cin c++(addInPlace (a'::as) (b'::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b]) := by
  simp [addInPlace,List.append_assoc]

theorem addHeadI_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hi : s.basis cin=false) (h0 : ∀a as,x=a::as → s.basis a=false)
    (hd : ∀a as b bs,x=a::as → y=b::bs → a≠b ∧ a≠cin ∧ b≠cin) :
    run (addHeadI x y carry cin) m s=run (addInPlace x y carry cin) m s := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> try rfl
  rw [addHeadI_split]
  obtain ⟨h1,-,h3⟩ := hd a _ b _ rfl rfl
  simp only [addHeadI,DiagSq.maj0,majority,List.cons_append,List.nil_append]
  exact (DiagSq.run_maj_idle a b cin c _ m s hi (by intro h; rw [h0 a _ rfl] at h; cases h) h1 h3).symm

theorem addHeadI_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈addHeadI x y carry cin,i∈addInPlace x y carry cin := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    try (intro i h; exact h)
  rw [addHeadI_split]
  intro i h
  simp only [addHeadI,DiagSq.maj0,majority,List.mem_append,List.mem_cons] at h ⊢
  tauto

theorem addHeadI_counts (x y carry : List Wire) (cin : Wire) (hx : 2≤x.length) (hy : 2≤y.length)
    (hc : 1≤carry.length) :
    toffoliCount (addHeadI x y carry cin)+1=toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addHeadI x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    simp at hx hy hc
  rw [addHeadI_split]
  simp only [addHeadI,DiagSq.maj0,majority,toffoliCount_append,measurementCount_append]
  simp [toffoliCount,measurementCount]
  omega

theorem addHeadI_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHeadI x y carry cin)≤Challenge.gateSlots (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;>
    try exact le_refl _
  rw [addHeadI_split]
  simp only [addHeadI,DiagSq.maj0,majority,Challenge.gateSlots_append]
  simp [Challenge.gateSlots,Challenge.instructionSlots]

theorem addHeadI_mc (x y carry : List Wire) (cin : Wire) :
    measurementCount (addHeadI x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',as⟩⟩ <;> rcases y with _|⟨b,_|⟨b',bs⟩⟩ <;> rcases carry with _|⟨c,cs⟩ <;> rfl

/-- `addLowNC` with the bit-1 Toffoli also dropped. -/
def addLowNC1 (x y carry : List Wire) (cin : Wire) : Program :=
  addHeadI x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []] ++
    [.CX (x.headD 0) (y.headD 0), .CX cin (y.headD 0)]

def subLowNC1 (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addLowNC1 x y carry cin ++ notRegister y

theorem addLowNC1_mc (x y carry : List Wire) (cin : Wire) :
    measurementCount (addLowNC1 x y carry cin)=measurementCount (LowZero.addLowNC x y carry cin) := by
  simp only [addLowNC1,LowZero.addLowNC,measurementCount_append,addHeadI_mc]

theorem addLowNC1_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hi : s.basis cin=false)
    (h1 : s.basis (x.tail.headD 0)=false) :
    run (addLowNC1 x y carry cin) m s=run (LowZero.addLowNC x y carry cin) m s := by
  have hd : ∀a as b bs,x.tail=a::as → y.tail=b::bs → a≠b ∧ a≠cin ∧ b≠cin := by
    intro a as b bs ha hb
    have ax : a∈x := List.mem_of_mem_tail (by rw [ha]; simp)
    have bx : b∈y := List.mem_of_mem_tail (by rw [hb]; simp)
    have hc := (List.nodup_cons.mp hn).1
    refine ⟨fun e => ?_,fun e => hc (by rw [← e]; simp [ax]),fun e => hc (by rw [← e]; simp [bx])⟩
    rw [e] at ax
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) b ax bx
  have h0 : ∀a as,x.tail=a::as → s.basis a=false := by
    intro a as h; have := h1; rw [h] at this; simpa using this
  have e := addHeadI_run x.tail y.tail carry.tail cin
    (m.take (measurementCount (addInPlace x.tail y.tail carry.tail cin))) s hi h0 hd
  simp only [addLowNC1,LowZero.addLowNC,List.append_assoc]
  rw [run_append (addHeadI _ _ _ _),run_append (addInPlace _ _ _ _),addHeadI_mc,e]

theorem subLowNC1_run (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hi : s.basis cin=false)
    (h1 : s.basis (x.tail.headD 0)=false) (hx : 2≤x.length) :
    run (subLowNC1 x y carry cin) m s=run (LowZero.subLowNC x y carry cin) m s := by
  have hm : measurementCount (notRegister y)=0 := (notRegister_counts y).2
  have hyn : y.Nodup := DiagSq.nd_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct y hyn s []
  have hc : cin∉y := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hx1 : x.tail.headD 0∈x := by rcases x with _|⟨a,_|⟨b,xs⟩⟩ <;> simp at hx ⊢
  have hx2 : x.tail.headD 0∉y :=
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ hx1
  simp only [subLowNC1,LowZero.subLowNC,List.append_assoc]
  rw [run_append (notRegister y),run_append (notRegister y),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (addLowNC1 x y carry cin),
    run_append (LowZero.addLowNC x y carry cin),addLowNC1_mc,
    addLowNC1_run x y carry cin _ _ hn (by rw [nr]; simp [hc,hi]) (by rw [nr]; dsimp only; rw [if_neg hx2]; exact h1)]

theorem addLowNC1_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈addLowNC1 x y carry cin,i∈LowZero.addLowNC x y carry cin := by
  intro i h
  simp only [addLowNC1,LowZero.addLowNC,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl (addHeadI_mem _ _ _ _ i h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem subLowNC1_mem (x y carry : List Wire) (cin : Wire) :
    ∀i∈subLowNC1 x y carry cin,i∈LowZero.subLowNC x y carry cin := by
  intro i h
  simp only [subLowNC1,LowZero.subLowNC,List.mem_append] at h ⊢
  rcases h with (h|h)|h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (addLowNC1_mem _ _ _ _ i h))
  · exact Or.inr h

theorem addLowNC1_counts (x y carry : List Wire) (cin : Wire) (hx : 3≤x.length) (hy : 3≤y.length)
    (hc : 2≤carry.length) :
    toffoliCount (addLowNC1 x y carry cin)+1=toffoliCount (LowZero.addLowNC x y carry cin) := by
  have a := addHeadI_counts x.tail y.tail carry.tail cin (by simp; omega) (by simp; omega) (by simp; omega)
  simp only [addLowNC1,LowZero.addLowNC,toffoliCount_append]
  omega

theorem subLowNC1_counts (x y carry : List Wire) (cin : Wire) (hx : 3≤x.length) (hy : 3≤y.length)
    (hc : 2≤carry.length) :
    toffoliCount (subLowNC1 x y carry cin)+1=toffoliCount (LowZero.subLowNC x y carry cin) := by
  have a := addLowNC1_counts x y carry cin hx hy hc
  simp only [subLowNC1,LowZero.subLowNC,toffoliCount_append]
  omega

theorem addLowNC1_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addLowNC1 x y carry cin)≤Challenge.gateSlots (LowZero.addLowNC x y carry cin) := by
  have a := addHeadI_slots x.tail y.tail carry.tail cin
  simp only [addLowNC1,LowZero.addLowNC,Challenge.gateSlots_append]
  omega

theorem subLowNC1_slots (x y carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (subLowNC1 x y carry cin)≤Challenge.gateSlots (LowZero.subLowNC x y carry cin) := by
  have a := addLowNC1_slots x y carry cin
  simp only [subLowNC1,LowZero.subLowNC,Challenge.gateSlots_append]
  omega

theorem bit1 (r tail : List Wire) (st : BasisState) (hl : 2≤r.length) :
    st ((r++tail).tail.headD 0)=decide (regValue r st/2%2=1) := by
  match r, hl with
  | w::ws, hl2 =>
    have hne : ws≠[] := by intro e; subst e; simp at hl2
    simp only [List.cons_append,List.tail_cons]
    rw [LowZero.head_bit ws tail st hne,LowZero.foldr_cons_value]
    have : ((if st w then 1 else 0)+2*regValue ws st)/2=regValue ws st := by split <;> omega
    rw [this]

theorem sq_bit1 (b : Nat) : b^2/2%2=0 := by
  have h : b^2%4=0 ∨ b^2%4=1 := by
    rw [Nat.pow_mod]
    have : b%4<4 := Nat.mod_lt _ (by norm_num)
    interval_cases (b%4) <;> simp
  omega

variable (R : KRegs)

theorem dhi_two (w : R.W) : 2≤R.dhi.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  omega

def m7y : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length then
    subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.m7g
def c7y : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 2≤R.T.length then
    addLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.c7g

theorem m7y_mem : ∀i∈R.m7y,i∈R.m7g := by
  unfold m7y
  split_ifs with h
  · unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact subLowNC1_mem _ _ _ _
  · exact fun i hi => hi
theorem c7y_mem : ∀i∈R.c7y,i∈R.c7g := by
  unfold c7y
  split_ifs with h
  · unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact addLowNC1_mem _ _ _ _
  · exact fun i hi => hi

theorem m7y_wires : wires R.m7y⊆wires R.m7 := (DiagSq.wires_of_mem R.m7y_mem).trans R.m7g_wires
theorem c7y_wires : wires R.c7y⊆wires R.c7 := (DiagSq.wires_of_mem R.c7y_mem).trans R.c7g_wires
theorem m7y_physical (hn : R.all.Nodup) : GatePhysical R.m7y := fun i hi => R.m7g_physical hn i (R.m7y_mem i hi)
theorem c7y_physical (hn : R.all.Nodup) : GatePhysical R.c7y := fun i hi => R.c7g_physical hn i (R.c7y_mem i hi)

theorem m7y_slots : Challenge.gateSlots R.m7y≤Challenge.gateSlots R.m7 := by
  refine le_trans ?_ R.m7g_slots
  unfold m7y
  split_ifs with h
  · unfold m7g; rw [LowZero.subLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact subLowNC1_slots _ _ _ _
  · exact le_refl _
theorem c7y_slots : Challenge.gateSlots R.c7y≤Challenge.gateSlots R.c7 := by
  refine le_trans ?_ R.c7g_slots
  unfold c7y
  split_ifs with h
  · unfold c7g; rw [LowZero.addLowNCG_eq _ _ _ _ h.1 h.2.1 h.2.2]; exact addLowNC1_slots _ _ _ _
  · exact le_refl _

theorem m7y_counts (w : R.W) : toffoliCount R.m7y+2=toffoliCount R.m7 ∧
    measurementCount R.m7y=measurementCount R.m7 := by
  have l := R.t_lensg w
  have z := R.m7g_counts w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have c := subLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by rw [l.1]; omega) (by omega) (by simp only [List.length_take]; omega)
  have mc : measurementCount R.m7y=measurementCount R.m7g := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    simp only [subLowNC1,LowZero.subLowNC,measurementCount_append,addLowNC1_mc]
  have tc : toffoliCount R.m7y+1=toffoliCount R.m7g := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]; exact c
  constructor <;> omega
theorem c7y_counts (w : R.W) : toffoliCount R.c7y+2=toffoliCount R.c7 ∧
    measurementCount R.c7y=measurementCount R.c7 := by
  have l := R.t_lensg w
  have z := R.c7g_counts w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have c := addLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by rw [l.1]; omega) (by omega) (by simp only [List.length_take]; omega)
  have mc : measurementCount R.c7y=measurementCount R.c7g := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact addLowNC1_mc _ _ _ _
  have tc : toffoliCount R.c7y+1=toffoliCount R.c7g := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]; exact c
  constructor <;> omega

theorem m7y_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false) :
    (run R.m7y m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7y m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7y m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  have e : run R.m7y m s=run R.m7g m s := by
    unfold m7y m7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.subLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact subLowNC1_run _ _ _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hi h1 (by rw [l.1]; exact l.2.2.1)
  rw [e]; exact R.m7g_correct w hn s m hcl hnc hi
theorem c7y_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false) :
    (run R.c7y m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7y m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7y m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  have l := R.t_lensg w
  have e : run R.c7y m s=run R.c7g m s := by
    unfold c7y c7g; rw [if_pos ⟨l.1,l.2.1,l.2.2.1⟩,LowZero.addLowNCG_eq _ _ _ _ l.1 l.2.1 l.2.2.1]
    exact addLowNC1_run _ _ _ _ _ _ (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hi h1
  rw [e]; exact R.c7g_correct w hn s m hcl hnc hi

end ECDSAAdd.Entrant.KRegs
end

section
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

/-! Inner `T −= A` / `T += A` with a bounded low part. In every inner leaf the subtracted
value `A = rawValue h a < 2^{2h}` never exceeds the low `2h+1` bits of `T = rawValue (h+1) S`,
so the borrow out of bit `2h` is always zero and the 66/68-bit adder can run on the low
`2h+1` bits only (one majority/erase pair fewer). -/

theorem add_take_sublist (n : Nat) : ∀ (x y c : List Wire) (cin : Wire), x.length=n+2 → y.length=n+2 →
    c.length=n+1 →
    (addInPlace (x.take (n+1)) (y.take (n+1)) (c.take n) cin).Sublist (addInPlace x y c cin) := by
  induction n with
  | zero =>
    intro x y c cin hx hy hc
    match x, y, c, hx, hy, hc with
    | [a,a'], [b,b'], [c0], _, _, _ =>
      simp only [List.take, addInPlace]
      exact List.sublist_append_right _ _
  | succ n ih =>
    intro x y c cin hx hy hc
    match x, y, c, hx, hy, hc with
    | a::a'::x', b::b'::y', c0::c', hx, hy, hc =>
      have hx' : (a'::x').length=n+2 := by simpa using hx
      have hy' : (b'::y').length=n+2 := by simpa using hy
      have hc' : c'.length=n+1 := by simpa using hc
      have r := ih (a'::x') (b'::y') c' c0 hx' hy' hc'
      simp only [List.take_succ_cons] at r ⊢
      simp only [addInPlace]
      exact ((((List.Sublist.refl _).append r).append (List.Sublist.refl _)).append (List.Sublist.refl _))

theorem slots_sublist {p q : Program} (h : p.Sublist q) : Challenge.gateSlots p≤Challenge.gateSlots q := by
  unfold Challenge.gateSlots
  exact (h.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem notRegister_take_sublist (y : List Wire) (k : Nat) : (notRegister (y.take k)).Sublist (notRegister y) := by
  unfold notRegister
  rw [List.map_take]
  exact List.take_sublist _ _

/-- `addLowNC` on the low `k+2` bits is a sublist of `addLowNC` on all bits. -/
theorem addLowNC_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3) (hy : y.length=n+3)
    (hc : c.length=n+2) :
    (LowZero.addLowNC (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (LowZero.addLowNC x y c cin) := by
  match x, y, c, hx, hy, hc with
  | a::x', b::y', c0::c', hx, hy, hc =>
    have r := add_take_sublist n x' y' c' cin (by simpa using hx) (by simpa using hy) (by simpa using hc)
    simp only [LowZero.addLowNC,List.take_succ_cons,List.tail_cons,List.headD_cons]
    exact (r.append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem subLowNC_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3) (hy : y.length=n+3)
    (hc : c.length=n+2) :
    (LowZero.subLowNC (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (LowZero.subLowNC x y c cin) := by
  simp only [LowZero.subLowNC]
  exact ((notRegister_take_sublist y (n+2)).append (addLowNC_take_sublist n x y c cin hx hy hc)).append
    (notRegister_take_sublist y (n+2))

variable (R : KRegs)

def lowOK : Prop := (R.dlo++R.zA).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 3≤R.T.length

instance : Decidable R.lowOK := by unfold lowOK; infer_instance

def m6w : Program := if R.lowOK then
  LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.m6z
def c6w : Program := if R.lowOK then
  LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.c6z

theorem lowOK_of (w : R.W) : R.lowOK := by
  have l := R.lo_lens w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hcl := w.carry
  exact ⟨l.1,l.2.1,by omega⟩

theorem m6w_sub : R.m6w.Sublist R.m6z := by
  unfold m6w
  split_ifs with h
  · obtain ⟨h1,h2,h3⟩ := h
    unfold m6z; rw [LowZero.subLowNCG_eq _ _ _ _ h1 h2 (by omega)]
    have e1 : R.T.length-1=(R.T.length-3)+2 := by omega
    have e2 : R.T.length-2=(R.T.length-3)+1 := by omega
    rw [e1,e2]
    exact subLowNC_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _
theorem c6w_sub : R.c6w.Sublist R.c6z := by
  unfold c6w
  split_ifs with h
  · obtain ⟨h1,h2,h3⟩ := h
    unfold c6z; rw [LowZero.addLowNCG_eq _ _ _ _ h1 h2 (by omega)]
    have e1 : R.T.length-1=(R.T.length-3)+2 := by omega
    have e2 : R.T.length-2=(R.T.length-3)+1 := by omega
    rw [e1,e2]
    exact addLowNC_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _

theorem m6w_wires : wires R.m6w⊆wires R.m6 :=
  (DiagSq.wires_of_mem (fun _ h => (R.m6w_sub).subset h)).trans R.m6z_wires
theorem c6w_wires : wires R.c6w⊆wires R.c6 :=
  (DiagSq.wires_of_mem (fun _ h => (R.c6w_sub).subset h)).trans R.c6z_wires
theorem m6w_slots : Challenge.gateSlots R.m6w≤Challenge.gateSlots R.m6 :=
  (slots_sublist R.m6w_sub).trans R.m6z_slots
theorem c6w_slots : Challenge.gateSlots R.c6w≤Challenge.gateSlots R.c6 :=
  (slots_sublist R.c6w_sub).trans R.c6z_slots
theorem m6w_physical (hn : R.all.Nodup) : GatePhysical R.m6w :=
  fun i h => R.m6z_physical hn i ((R.m6w_sub).subset h)
theorem c6w_physical (hn : R.all.Nodup) : GatePhysical R.c6w :=
  fun i h => R.c6z_physical hn i ((R.c6w_sub).subset h)

theorem m6w_counts (w : R.W) : toffoliCount R.m6w+2=toffoliCount R.m6 ∧
    measurementCount R.m6w+1=measurementCount R.m6 := by
  have z := R.m6z_counts w
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have a := LowZero.subLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
  have b := subInPlace_counts ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin lx lc
  have c := LowZero.subLowNC_counts _ _ _ R.cin h1 h2 (by omega)
  have d := subInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin h1 h2
  have em : R.m6w=LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have ez : R.m6z=LowZero.subLowNC (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin := by
    unfold m6z; exact LowZero.subLowNCG_eq _ _ _ _ h1 h2 (by omega)
  rw [em]; rw [ez] at z
  simp only [List.length_take] at a b
  constructor <;> omega

theorem c6w_counts (w : R.W) : toffoliCount R.c6w+2=toffoliCount R.c6 ∧
    measurementCount R.c6w+1=measurementCount R.c6 := by
  have z := R.c6z_counts w
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have a := LowZero.addLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
  have b := addInPlace_counts ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin lx lc
  have c := LowZero.addLowNC_counts _ _ _ R.cin h1 h2 (by omega)
  have d := addInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin h1 h2
  have em : R.c6w=LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have ez : R.c6z=LowZero.addLowNC (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin := by
    unfold c6z; exact LowZero.addLowNCG_eq _ _ _ _ h1 h2 (by omega)
  rw [em]; rw [ez] at z
  simp only [List.length_take] at a b
  constructor <;> omega

theorem take_headD (l : List Wire) (k : Nat) (hk : 1≤k) : (l.take k).headD 0=l.headD 0 := by
  rcases l with _|⟨a,l⟩
  · simp
  · obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩
    simp

theorem low_nodup (hn : R.all.Nodup) :
    (R.cin::(((R.dlo++R.zA).take (R.T.length-1))++(R.T.take (R.T.length-1))++
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)))).Nodup := by
  have full : (R.cin::((R.dlo++R.zA)++R.T++(R.carry.take (R.T.length-1)))).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  exact full.sublist ((((List.take_sublist _ _).append (List.take_sublist _ _)).append
    (List.take_sublist _ _)).cons₂ _)

theorem m6w_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (hA : regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1))
    (hb : regValue (R.dlo++R.zA) s.basis≤regValue R.T s.basis%2^(R.T.length-1)) :
    (run R.m6w m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m6w m s).basis q=s.basis q) ∧
    regValue R.T (run R.m6w m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dlo++R.zA) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have em : R.m6w=LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := LowZero.subLowNC_correct _ _ _ R.cin (R.low_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.subLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dlo++R.zA).take (R.T.length-1)) s.basis=regValue (R.dlo++R.zA) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    have := List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
    exact this
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue R.T s.basis%P-regValue (R.dlo++R.zA) s.basis := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.sub_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    rw [show regValue R.T s.basis%P+P-regValue (R.dlo++R.zA) s.basis=
      (regValue R.T s.basis%P-regValue (R.dlo++R.zA) s.basis)+P by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := Nat.mod_lt (regValue R.T s.basis) Ppos; omega)]
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.sub_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dlo++R.zA) s.basis=AV at *
  have dq : P*D=TV-M := by omega
  rw [dq,show TV+2*P-AV=(TV-AV)+2*P by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  omega

theorem c6w_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool) (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dlo++R.zA).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (hA : regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1))
    (hb : regValue R.T s.basis%2^(R.T.length-1)+regValue (R.dlo++R.zA) s.basis<2^(R.T.length-1)) :
    (run R.c6w m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c6w m s).basis q=s.basis q) ∧
    regValue R.T (run R.c6w m s).basis=(regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  obtain ⟨h1,h2,h3⟩ := R.lowOK_of w
  have em : R.c6w=LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos ⟨h1,h2,h3⟩
  have lx : ((R.dlo++R.zA).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := LowZero.addLowNC_correct _ _ _ R.cin (R.low_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.addLowNC ((R.dlo++R.zA).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dlo++R.zA).take (R.T.length-1)) s.basis=regValue (R.dlo++R.zA) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    exact List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue (R.dlo++R.zA) s.basis+regValue R.T s.basis%P := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.add_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    exact Nat.mod_eq_of_lt (by omega)
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.add_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  have dle : regValue R.T s.basis/P≤1 := by
    have := Nat.div_lt_of_lt_mul (show regValue R.T s.basis<P*2 by omega); omega
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dlo++R.zA) s.basis=AV at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp dle with e|e
  · subst e; simp only [Nat.mul_zero,Nat.add_zero] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · subst e; simp only [Nat.mul_one] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem pow_two_mul_split (h : Nat) (hh : 1≤h) : 2^h=2*2^(h-1) := by
  rw [← pow_succ']; congr 1; omega

theorem raw_lo_le (h a : Nat) (hh : 1≤h) (ha : a<2^h) : DiagSq.rawValue h a+2^h≤2^(2*h) := by
  unfold DiagSq.rawValue signedDiagValue
  rw [if_neg (by omega)]
  have hP : 2^h=2*2^(h-1) := pow_two_mul_split h hh
  have hPP : 2^(2*h)=2^h*2^h := by rw [two_mul,pow_add]
  rw [hPP,hP]; rw [hP] at ha
  generalize 2^(h-1)=Q at *
  have Qpos : 0<Q := by omega
  have vlt : a%Q<Q := Nat.mod_lt _ Qpos
  have adiv := Nat.mod_add_div a Q
  obtain ⟨k,hk⟩ : ∃k,Q=a%Q+1+k := ⟨Q-1-a%Q,by omega⟩
  have e1 : Q-1-a%Q=k := by omega
  rw [e1]
  have t1 : a/Q≤1 := by have := Nat.div_lt_of_lt_mul (show a<Q*2 by omega); omega
  generalize a%Q=v at *
  subst hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp t1 with e|e
  · have av : a=v := by rw [e] at adiv; omega
    subst av
    nlinarith [Nat.zero_le (a*k),Nat.zero_le (k*k),Nat.zero_le (a*a)]
  · have av : a=v+(v+1+k) := by rw [e] at adiv; omega
    subst av
    nlinarith [Nat.zero_le (v*k),Nat.zero_le (k*k),Nat.zero_le (v*v)]

theorem raw_hi_ge (h S : Nat) (hh : 1≤h) (hS : S<2^(h+1)) :
    2^(2*h)≤DiagSq.rawValue (h+1) S%2^(2*h+1)+2^h := by
  unfold DiagSq.rawValue signedDiagValue
  rw [if_neg (by omega),show h+1-1=h by omega]
  have h1 : 2^(h+1)=2*2^h := by rw [pow_succ]; ring
  have hPP : 2^(2*h)=2^h*2^h := by rw [two_mul,pow_add]
  have hM : 2^(2*h+1)=2*(2^h*2^h) := by rw [pow_succ,hPP]; ring
  rw [h1] at hS ⊢; rw [hPP,hM]
  generalize 2^h=P at *
  have Ppos : 0<P := by omega
  have ult : S%P<P := Nat.mod_lt _ Ppos
  have sdiv := Nat.mod_add_div S P
  obtain ⟨k,hk⟩ : ∃k,P=S%P+1+k := ⟨P-1-S%P,by omega⟩
  have e1 : P-1-S%P=k := by omega
  rw [e1]
  have t1 : S/P≤1 := by have := Nat.div_lt_of_lt_mul (show S<P*2 by omega); omega
  generalize S%P=u at *
  subst hk
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp t1 with e|e
  · have sv : S=u := by rw [e] at sdiv; omega
    subst sv
    have lt : S^2+(S+k*(2*(S+1+k)))<2*((S+1+k)*(S+1+k)) := by
      nlinarith [Nat.zero_le (S*k),Nat.zero_le (k*k),Nat.zero_le (S*S)]
    rw [Nat.mod_eq_of_lt lt]
    nlinarith [Nat.zero_le (S*k),Nat.zero_le (k*k),Nat.zero_le (S*S)]
  · have sv : S=u+(u+1+k) := by rw [e] at sdiv; omega
    subst sv
    have ge : 2*((u+1+k)*(u+1+k))≤(u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k))) := by
      nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
    have lt : (u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))-2*((u+1+k)*(u+1+k))<2*((u+1+k)*(u+1+k)) := by
      have : (u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))<2*((u+1+k)*(u+1+k))+2*((u+1+k)*(u+1+k)) := by
        nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
      omega
    rw [Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt lt]
    have : (u+1+k)*(u+1+k)+2*((u+1+k)*(u+1+k))≤(u+(u+1+k))^2+(u+(u+1+k)+k*(2*(u+1+k)))+(u+1+k) := by
      nlinarith [Nat.zero_le (u*k),Nat.zero_le (k*k),Nat.zero_le (u*u)]
    omega

/-- The bound used by `m6w`/`c6w`: the subtracted diagonal seed never exceeds the low
`2h+1` bits of the sum-square seed. -/
theorem raw_low_bound (h a b : Nat) (hh : 1≤h) (ha : a<2^h) (hb : b<2^h) :
    DiagSq.rawValue h a≤DiagSq.rawValue (h+1) (a+b)%2^(2*h+1) ∧ DiagSq.rawValue h a<2^(2*h) := by
  have x := raw_lo_le h a hh ha
  have y := raw_hi_ge h (a+b) hh (by rw [pow_succ]; omega)
  have p : 0<2^h := by positivity
  constructor <;> omega

end ECDSAAdd.Entrant.KRegs
end

section
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

theorem subloW_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S TN : Nat) (hX : A<2^R.dlo.length) (hAe : 2∣A) (hT : TN<2^R.T.length)
    (hb : A≤TN%2^(R.T.length-1)) (hA' : A<2^(R.T.length-1)) :
    Transition R base (vec A B S (TN : Int)) (vec A B S ((TN : Int)-A)) R.m6w := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have tv := ht.exact 3 TN rfl hT
  change regValue R.T t.basis=TN at tv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have av : regValue (R.dlo++R.zA) t.basis=A := by rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero]
  have l := R.lo_lens w
  have c := R.m6w_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0) (by rw [av]; exact hA') (by rw [av,tv]; exact hb)
  have r : Update R.T (-(regValue (R.dlo++R.zA) t.basis : Int)) t (run R.m6w rec t) := by
    have vl := regValue_lt (R.dlo++R.zA) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dlo++R.zA) t.basis) (by omega)
  rw [av] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S (TN : Int)) 3=(TN : Int) from rfl,vec3,sub_eq_add_neg] using act

theorem addloW_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (Z : Nat) (hX : A<2^R.dlo.length) (hAe : 2∣A) (hZ : T+A=Z)
    (hZlt : Z<2^R.T.length) (hb : A≤Z%2^(R.T.length-1)) (hA' : A<2^(R.T.length-1)) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6w := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have AZ : A≤Z := le_trans hb (Nat.mod_le _ _)
  have tv := ht.exact 3 (Z-A) (by simp only [vec]; push_cast [AZ]; omega) (by change Z-A<2^R.T.length; omega)
  change regValue R.T t.basis=Z-A at tv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have av : regValue (R.dlo++R.zA) t.basis=A := by rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero]
  have Ppos : 0<2^(R.T.length-1) := by positivity
  have low : (Z-A)%2^(R.T.length-1)+A<2^(R.T.length-1) := by
    have md := Nat.mod_add_div Z (2^(R.T.length-1))
    have ml := Nat.mod_lt Z Ppos
    generalize 2^(R.T.length-1)=P at *
    generalize Z%P=M at *
    generalize Z/P=D at *
    have e : Z-A=(M-A)+P*D := by omega
    rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega)]
    omega
  have c := R.c6w_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0) (by rw [av]; exact hA') (by rw [av,tv]; exact low)
  have r : Update R.T (regValue (R.dlo++R.zA) t.basis : Int) t (run R.c6w rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [av] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

end ECDSAAdd.Entrant.DiagSq
end

namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- A register whose value is congruent to an even integer modulo `2^len` (`len ≥ 1`) has
its lowest wire clear. -/
theorem head_false_of_modEq (r : List Wire) (st : BasisState) (T : Int) (hl : 1≤r.length)
    (hv : (regValue r st : Int) ≡ T [ZMOD (2^r.length : Nat)]) (hT : (2:Int)∣T) :
    st (r.headD 0)=false := by
  have h2 : (2:Int)∣((2^r.length : Nat) : Int) := by
    push_cast; exact dvd_pow_self 2 (by omega)
  have hd : (2:Int)∣(regValue r st : Int) := by
    have m := (Int.ModEq.dvd hv.symm)
    have := dvd_trans h2 m
    have e : (regValue r st : Int)=T+((regValue r st : Int)-T) := by ring
    rw [e]; exact dvd_add hT this
  obtain ⟨k,hk⟩ := hd
  have hk' : regValue r st=2*k.toNat := by omega
  have ne : r≠[] := by intro e; rw [e] at hl; simp at hl
  have := LowZero.head_false_of_even r [] st k.toNat hk' ne
  simpa using this

theorem addhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hTe : (2:Int)∣T) :
    Transition R base (vec A B S T) (vec A B S (T+B)) R.c7g := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have t0 : t.basis (R.T.headD 0)=false :=
    head_false_of_modEq R.T t.basis T (by omega) (ht.value 3) hTe
  have c := R.c7g_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [t0]; exact Bool.and_false _) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dhi++R.zB) t.basis : Int) t (run R.c7g rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem rawValue_even (n x : Nat) (hn : 1≤n) : 2∣rawValue n x := by
  unfold rawValue signedDiagValue
  rw [if_neg (by omega)]
  have h1 : 2∣x^2+x := by
    rw [show x^2+x=x*(x+1) by ring]; exact (Nat.even_mul_succ_self x).two_dvd
  have h2 : 2∣(2^(n-1)-1-x%2^(n-1))*2^n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
  rw [show x^2+(x+(2^(n-1)-1-x%2^(n-1))*2^n)=(x^2+x)+(2^(n-1)-1-x%2^(n-1))*2^n by ring]
  exact dvd_add h1 h2

theorem subloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T-A)) R.m6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have l := R.lo_lens w
  have c := R.m6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dlo++R.zA) t.basis : Int)) t (run R.m6z rec t) := by
    have vl := regValue_lt (R.dlo++R.zA) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dlo++R.zA) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem subhiZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) (hBe : 2∣B) :
    Transition R base (vec A B S T) (vec A B S (T-B)) R.m7g := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dhi++R.zB).headD 0)=false := by
    obtain ⟨k,hk⟩ := hBe
    exact LowZero.head_false_of_even R.dhi R.zB t.basis k (by rw [xv,hk]) (R.dhi_neg w)
  have l := R.t_lensg w
  have c := R.m7g_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (-(regValue (R.dhi++R.zB) t.basis : Int)) t (run R.m7g rec t) := by
    have vl := regValue_lt (R.dhi++R.zB) t.basis
    rw [l.1] at vl
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.sub_zero]
    simpa only [sub_eq_add_neg] using sub_congr (regValue R.T t.basis) (2^R.T.length)
      (regValue (R.dhi++R.zB) t.basis) (by omega)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addloZ_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) (hAe : 2∣A) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6z := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have x0 : t.basis ((R.dlo++R.zA).headD 0)=false := by
    obtain ⟨k,hk⟩ := hAe
    exact LowZero.head_false_of_even R.dlo R.zA t.basis k (by rw [xv,hk]) (R.dlo_ne w)
  have c := R.c6z_correct w hn t rec (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h))
    (by rw [x0]; rfl) ((ht.cin hn).trans hi0)
  have r : Update R.T (regValue (R.dlo++R.zA) t.basis : Int) t (run R.c6z rec t) := by
    refine ⟨c.1,c.2.1,?_⟩
    rw [c.2.2,(ht.cin hn).trans hi0,Bool.toNat_false,Nat.add_zero]
    simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
    rw [Int.add_comm]
    exact Int.emod_emod _ _
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act


theorem head_eq_of_modEq (r r' : List Wire) (st : BasisState) (T : Int) (hl : 1≤r.length) (hl' : 1≤r'.length)
    (hv : (regValue r st : Int) ≡ T [ZMOD (2^r.length : Nat)]) (hT : (2:Int)∣T-regValue r' st) :
    st (r.headD 0)=st (r'.headD 0) := by
  have h2 : (2:Int)∣((2^r.length : Nat) : Int) := by
    push_cast; exact dvd_pow_self 2 (by omega)
  have d1 : (2:Int)∣(regValue r st : Int)-T := dvd_trans h2 (Int.ModEq.dvd hv.symm)
  have d : (2:Int)∣(regValue r st : Int)-regValue r' st := by
    have e : (regValue r st : Int)-regValue r' st=((regValue r st : Int)-T)+(T-regValue r' st) := by ring
    rw [e]; exact dvd_add d1 hT
  have ne : r≠[] := by intro e; rw [e] at hl; simp at hl
  have ne' : r'≠[] := by intro e; rw [e] at hl'; simp at hl'
  have a := LowZero.head_bit r [] st ne
  have b := LowZero.head_bit r' [] st ne'
  simp only [List.append_nil] at a b
  rw [a,b]
  have : regValue r st%2=regValue r' st%2 := by omega
  rw [this]

theorem sq_sub_even (a : Nat) : (2:Int)∣((a^2 : Nat) : Int)-(a : Int) := by
  have h : 2∣a^2+a := by
    rw [show a^2+a=a*(a+1) by ring]; exact (Nat.even_mul_succ_self a).two_dvd
  have h' : (2:Int)∣((a^2+a : Nat) : Int) := by exact_mod_cast h
  push_cast at h' ⊢
  have e : (a:Int)^2-a=((a:Int)^2+a)-2*a := by ring
  rw [e]; exact dvd_sub h' (dvd_mul_right 2 _)

theorem dsubloZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAe : (2:Int)∣A) :
    Transition R base (vec A B S T) (vec (A-(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dSubZ R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have e := dSubZ_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (head_false_of_modEq R.dlo t.basis A (by omega) (ht.value 0) hAe)
  rw [e]
  exact diagsublo_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem dsubhiZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hBe : (2:Int)∣B) :
    Transition R base (vec A B S T) (vec A (B-(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dSubZ R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have e := dSubZ_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (head_false_of_modEq R.dhi t.basis B (by omega) (ht.value 1) hBe)
  rw [e]
  exact diagsubhi_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem daddloZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAp : (2:Int)∣A-regValue R.lo base.basis) :
    Transition R base (vec A B S T) (vec (A+(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dAddZ R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have hb := head_eq_of_modEq R.dlo R.lo t.basis A (by omega) (by omega) (ht.value 0) (by rw [xv]; exact hAp)
  have e := dAddZ_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (by
      intro y ys' ey hx
      have h1 : t.basis (R.dlo.headD 0)=true := by rw [hb]; exact hx
      rw [ey] at h1; simpa using h1)
  rw [e]
  exact diagaddlo_transition R w he hn base hc0 hi0 A B S T t rec ht

theorem daddhiZ_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hBp : (2:Int)∣B-regValue R.hi base.basis) :
    Transition R base (vec A B S T) (vec A (B+(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dAddZ R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have hb := head_eq_of_modEq R.dhi R.hi t.basis B (by omega) (by omega) (ht.value 1) (by rw [xv]; exact hBp)
  have e := dAddZ_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    ((ht.cin hn).trans hi0) (by
      intro y ys' ey hx
      have h1 : t.basis (R.dhi.headD 0)=true := by rw [hb]; exact hx
      rw [ey] at h1; simpa using h1)
  rw [e]
  exact diagaddhi_transition R w he hn base hc0 hi0 A B S T t rec ht

section TopBit
set_option maxHeartbeats 1000000

theorem ccx_as_cx_top (a b t y : Wire) (p : Program) (m : List Bool) (s : State)
    (h : (s.basis a && s.basis b)=s.basis y) : run (.CCX a b t::p) m s=run (.CX y t::p) m s := by
  simp only [run,h]

/-- `incr1` with its second-bit carry Toffoli `CCX y' c c'` replaced by a CNOT. On the 3-bit top field that
`correctionZ` increments (the only width it is used at), the copy is `CX y'' c'`: valid when the field
`y + 2 y' + 4 y''` plus one has a clear top bit, so that `y AND y' = y''` (`incr2_run`). The wider arm is never
instantiated; it uses `CX y' c'` only so that the resource lemmas need no width hypothesis. -/
def incr2 (ys carry : List Wire) (cin : Wire) : Program :=
  match ys, carry with
  | [y,y',y''], c::c'::cs => [.CX y c,.CX cin c]++(.CX y'' c'::
      (mappedAdd [⟨none,false⟩] [y''] cs c'++mappedEraseCarry ⟨none,false⟩ y' c c'++
        mappedSum ⟨none,false⟩ y' c))++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin
  | y::y'::y''::y3::ys', c::c'::cs => [.CX y c,.CX cin c]++(.CX y' c'::
      (mappedAdd [⟨none,false⟩] (y''::y3::ys') cs c'++mappedEraseCarry ⟨none,false⟩ y' c c'++
        mappedSum ⟨none,false⟩ y' c))++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin
  | ys, carry => incr1 ys carry cin

theorem incr2_split (y y' y'' c c' cin : Wire) (ys cs : List Wire) :
    incr1 (y::y'::y''::ys) (c::c'::cs) cin=[.CX y c,.CX cin c]++(.CCX y' c c'::
      (mappedAdd [⟨none,false⟩] (y''::ys) cs c'++mappedEraseCarry ⟨none,false⟩ y' c c'++
        mappedSum ⟨none,false⟩ y' c))++
      mappedEraseCarry (mappedConstantBit none true) y cin c++mappedSum (mappedConstantBit none true) y cin := by
  simp [incr1,mappedConstant,mappedAdd,mappedMajority,mappedConstantBit,List.append_assoc]

theorem incr2_run (y y' y'' c c' cin : Wire) (cs : List Wire) (s : State) (m : List Bool)
    (h1 : y'≠c) (h2 : y''≠c) (h3 : cin≠c) (hc : s.basis c=false) (hi : s.basis cin=false)
    (hv : (s.basis y && s.basis y')=s.basis y'') :
    run (incr2 [y,y',y''] (c::c'::cs) cin) m s=run (incr1 [y,y',y''] (c::c'::cs) cin) m s := by
  rw [incr2_split]
  simp only [incr2,List.append_assoc,List.cons_append,List.nil_append]
  let t1 : State := ⟨s.phase,writeBit s.basis c (s.basis c ^^ s.basis y)⟩
  let t2 : State := ⟨t1.phase,writeBit t1.basis c (t1.basis c ^^ t1.basis cin)⟩
  have e : (t2.basis y' && t2.basis c)=t2.basis y'' := by
    simp only [t2,t1,writeBit,Function.update,h1,h2,h3,dif_neg,if_false,dite_false,ne_eq,not_false_eq_true,
      if_true,dite_true,hc,hi]
    simp only [Bool.false_xor,Bool.xor_false]
    rw [← hv, Bool.and_comm]
  exact (ccx_as_cx_top y' c c' y'' _ m t2 e).symm

theorem incr2_mem (ys carry : List Wire) (cin : Wire) :
    ∀i∈incr2 ys carry cin,i∈incr1 ys carry cin∨∃ a b,i=.CX a b ∧ a∈ys ∧ b∈carry := by
  match ys, carry with
  | [y,y',y''], c::c'::cs =>
    rw [incr2_split]
    intro i h
    simp only [incr2,List.mem_append,List.mem_cons] at h ⊢
    rcases h with ((h|h|h)|h)|h
    · tauto
    · right; exact ⟨y'',c',h,by simp,by simp⟩
    · tauto
    · tauto
    · tauto
  | y::y'::y''::y3::ys', c::c'::cs =>
    rw [incr2_split]
    intro i h
    simp only [incr2,List.mem_append,List.mem_cons] at h ⊢
    rcases h with ((h|h|h)|h)|h
    · tauto
    · right; exact ⟨y',c',h,by simp,by simp⟩
    · tauto
    · tauto
    · tauto
  | [], _ => intro i h; exact Or.inl h
  | [_], _ => intro i h; exact Or.inl h
  | [_,_], _ => intro i h; exact Or.inl h
  | [_,_,_], [] => intro i h; exact Or.inl h
  | _::_::_::_::_, [] => intro i h; exact Or.inl h
  | [_,_,_], [_] => intro i h; exact Or.inl h
  | _::_::_::_::_, [_] => intro i h; exact Or.inl h

theorem incr2_counts (ys carry : List Wire) (cin : Wire) (h3 : 3≤ys.length) (hc : 2≤carry.length) :
    toffoliCount (incr2 ys carry cin)+1=toffoliCount (incr1 ys carry cin) ∧
    measurementCount (incr2 ys carry cin)=measurementCount (incr1 ys carry cin) := by
  match ys, carry, h3, hc with
  | [y,y',y''], c::c'::cs, _, _ =>
    rw [incr2_split]
    simp only [incr2,toffoliCount_append,measurementCount_append]
    simp [toffoliCount,measurementCount]
    omega
  | y::y'::y''::y3::ys', c::c'::cs, _, _ =>
    rw [incr2_split]
    simp only [incr2,toffoliCount_append,measurementCount_append]
    simp [toffoliCount,measurementCount]
    omega

theorem incr2_slots (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (incr2 ys carry cin)=Challenge.gateSlots (incr1 ys carry cin) := by
  match ys, carry with
  | [y,y',y''], c::c'::cs =>
    rw [incr2_split]
    simp only [incr2,Challenge.gateSlots_append]
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  | y::y'::y''::y3::ys', c::c'::cs =>
    rw [incr2_split]
    simp only [incr2,Challenge.gateSlots_append]
    simp [Challenge.gateSlots,Challenge.instructionSlots]
  | [], _ => rfl
  | [_], _ => rfl
  | [_,_], _ => rfl
  | [_,_,_], [] => rfl
  | _::_::_::_::_, [] => rfl
  | [_,_,_], [_] => rfl
  | _::_::_::_::_, [_] => rfl

/-- If `L + P*(F+1) ≡ n (mod 8P)` with `L < P`, `n < 4P` and `F` the 3-bit field `b0 + 2 b1 + 4 b2`, then
`b0 AND b1 = b2`. -/
theorem top_field (P L n : Nat) (b0 b1 b2 : Bool) (hL : L<P) (hn : n<4*P)
    (hm : ((8*P : Nat) : Int)∣(n : Int)-(((L+P*((if b0 then 1 else 0)+2*((if b1 then 1 else 0)+
      2*((if b2 then 1 else 0)+2*0))) : Nat) : Int)+((P : Nat) : Int))) :
    (b0 && b1)=b2 := by
  obtain ⟨k,hk⟩ := hm
  have hP : (0 : Int)<P := by exact_mod_cast (show 0<P by omega)
  have hL' : (L : Int)<P := by exact_mod_cast hL
  have hn' : (n : Int)<4*P := by exact_mod_cast hn
  have hn0 : (0 : Int)≤n := by positivity
  have hL0 : (0 : Int)≤L := by positivity
  cases b0 <;> cases b1 <;> cases b2 <;> simp at hk ⊢ <;>
    (rcases le_or_gt 0 k with h|h <;> nlinarith)

def correctionZ2 (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h ++
    incr2 (dst.drop (2*h-1)) (carry.take 2) cin

theorem correctionZ2_run (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0)
    (n : Nat) (hnl : n<2^(2*h+1))
    (hT : (regValue dst s.basis : Int)-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)+
      (2^(2*h-1) : Nat) ≡ n [ZMOD (2^dst.length : Nat)]) :
    run (correctionZ2 h as bs ss dst carry q cin) m s=run (correctionZ h as bs ss dst carry q cin) m s := by
  have r := sharedSub_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s
    (m.take (measurementCount (loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
      (correctionBits h ss q) dst (carry.take (h+1)) h))) hv hq0 hi0 hc0
  have out (w : Wire) (hw : w∈cin::carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have h1 : 1≤h := by rcases hh with rfl|rfl <;> omega
  have hd3 : (dst.drop (2*h-1)).length=3 := by simp only [List.length_drop]; omega
  have hc2 : (carry.take 2).length=2 := by simp only [List.length_take]; omega
  obtain ⟨y,y',y'',ey⟩ := List.length_eq_three.mp hd3
  obtain ⟨c,c',ec⟩ := List.length_eq_two.mp hc2
  have ym : ∀w∈[y,y',y''],w∈dst := fun w hw => List.mem_of_mem_drop (by rw [ey]; exact hw)
  have cm : c∈carry := List.mem_of_mem_take (by rw [ec]; simp)
  have cnd : c∉dst := out c (by simp [cm])
  have cind : cin≠c := fun e => (List.nodup_cons.mp hn).1 (by rw [e]; simp [cm])
  have e8 : 2^dst.length=8*2^(2*h-1) := by
    rw [hdl,show 2*h+2=(2*h-1)+3 by omega,pow_add]; ring
  have e4 : 2^(2*h+1)=4*2^(2*h-1) := by
    rw [show 2*h+1=(2*h-1)+2 by omega,pow_add]; ring
  have key : ∀u : State,Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)) s u →
      ∀m',run (incr2 (dst.drop (2*h-1)) (carry.take 2) cin) m' u=run (incr1 (dst.drop (2*h-1)) (carry.take 2) cin) m' u := by
    intro u hu m'
    have comb := (hu.2.2.add_right ((2^(2*h-1) : Nat) : Int)).trans (by convert hT using 1; ring)
    have dv := comb.dvd
    have sp := rv_split dst (2*h-1) (by omega) u.basis
    rw [ey] at sp
    have lt := regValue_lt (dst.take (2*h-1)) u.basis
    rw [List.length_take,Nat.min_eq_left (by omega)] at lt
    rw [sp,e8] at dv
    have tf := top_field (2^(2*h-1)) (regValue (dst.take (2*h-1)) u.basis) n (u.basis y) (u.basis y') (u.basis y'')
      lt (by omega) dv
    rw [ey,ec]
    apply incr2_run _ _ _ _ _ _ []
    · intro e; exact cnd (e ▸ ym y' (by simp))
    · intro e; exact cnd (e ▸ ym y'' (by simp))
    · exact cind
    · exact (hu.2.1 c cnd).trans ((regValue_zero _ _).mp hc0 c cm)
    · exact (hu.2.1 cin (out cin (by simp))).trans hi0
    · exact tf
  simp only [correctionZ2,correctionZ,run_append]
  exact key _ r _

def corrZ2 (R : KRegs) : Program := correctionZ2 R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin

theorem corrZ2_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) (n : Nat)
    (hnl : n<2^(2*R.h+1))
    (hb : T-((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)+
      (2^(2*R.h-1) : Nat)=n) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) n) (corrZ2 R) := by
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
  have tv := ht.value 3
  change (regValue R.T t.basis : Int) ≡ T [ZMOD (2^R.T.length : Nat)] at tv
  have e : run (corrZ2 R) rec t=run (corrZ R) rec t :=
    correctionZ2_run R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin hh L0 hhi hs (by omega) (by omega) cn t rec
      (by rw [sv,al,bl]) ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv n hnl
      (by rw [al,bl,← hb]; exact (tv.sub_right _).add_right _)
  rw [e]
  have := corrZ_transition R w he hh hn base hz0 hc0 hi0 A B T t rec ht
  rwa [hb] at this

theorem corrZ2_mem (R : KRegs) :
    ∀i∈corrZ2 R,i∈corr R∨∃ a b,i=.CX a b ∧ a∈R.T ∧ b∈R.carry := by
  intro i h
  simp only [corrZ2,correctionZ2,List.mem_append] at h
  rcases h with h|h
  · exact Or.inl (corrZ_mem R i (by simp only [corrZ,correctionZ,List.mem_append]; exact Or.inl h))
  · rcases incr2_mem _ _ _ i h with h|⟨a,b,e,ha,hb⟩
    · exact Or.inl (corrZ_mem R i (by simp only [corrZ,correctionZ,List.mem_append]; exact Or.inr h))
    · exact Or.inr ⟨a,b,e,List.mem_of_mem_drop ha,List.mem_of_mem_take hb⟩

theorem corrZ2_counts (R : KRegs) (w : R.W) :
    toffoliCount (corrZ2 R)+1=toffoliCount (corrZ R) ∧ measurementCount (corrZ2 R)=measurementCount (corrZ R) := by
  have hTl := w.T; have hSl := w.S; have hcl := w.carry; have hh2 := w.hh; have h5 := w.h5
  have a := incr2_counts (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
    (by simp only [List.length_drop]; have h4 := w.h4; omega)
    (by simp only [List.length_take]; omega)
  simp only [corrZ2,corrZ,correctionZ2,correctionZ,toffoliCount_append,measurementCount_append]
  omega

theorem corrZ2_slots (R : KRegs) : Challenge.gateSlots (corrZ2 R)=Challenge.gateSlots (corrZ R) := by
  have a := incr2_slots (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [corrZ2,corrZ,correctionZ2,correctionZ,Challenge.gateSlots_append]
  omega

theorem wires_sub_of {p q : Program} (h : ∀i∈p,i.wires⊆wires q) : wires p⊆wires q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    simp only [wires]
    exact Finset.union_subset (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem instr_wires_sub {i : Instr} {q : Program} (h : i∈q) : i.wires⊆wires q := by
  induction q with
  | nil => simp at h
  | cons j q ih =>
    simp only [wires]
    rcases List.mem_cons.mp h with e|h
    · subst e; exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

theorem incr2_wires_le (ys carry : List Wire) (cin : Wire) :
    wires (incr2 ys carry cin)⊆wires (incr1 ys carry cin) := by
  apply wires_sub_of
  intro i hi
  match ys, carry with
  | [y,y',y''], c::c'::cs =>
    have hm : Instr.CX c' y''∈incr1 [y,y',y''] (c::c'::cs) cin := by
      rw [incr2_split]; simp [mappedAdd,mappedSum]
    rw [incr2_split] at hm ⊢
    simp only [incr2,List.mem_append,List.mem_cons] at hi
    rcases hi with ((h|h|h)|h)|h
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · subst h
      show ({y'',c'} : Finset Wire)⊆_
      rw [Finset.pair_comm]
      exact instr_wires_sub hm
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
  | y::y'::y''::y3::ys', c::c'::cs =>
    have hm : Instr.CCX y' c c'∈incr1 (y::y'::y''::y3::ys') (c::c'::cs) cin := by
      rw [incr2_split]; simp
    rw [incr2_split] at hm ⊢
    simp only [incr2,List.mem_append,List.mem_cons] at hi
    rcases hi with ((h|h|h)|h)|h
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · subst h
      refine Finset.Subset.trans ?_ (instr_wires_sub hm)
      intro q hq
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq ⊢
      tauto
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
    · exact instr_wires_sub (by simp only [List.mem_append,List.mem_cons]; tauto)
  | [], _ => exact instr_wires_sub hi
  | [_], _ => exact instr_wires_sub hi
  | [_,_], _ => exact instr_wires_sub hi
  | [_,_,_], [] => exact instr_wires_sub hi
  | _::_::_::_::_, [] => exact instr_wires_sub hi
  | [_,_,_], [_] => exact instr_wires_sub hi
  | _::_::_::_::_, [_] => exact instr_wires_sub hi

theorem corrZ2_wires (R : KRegs) : wires (corrZ2 R)⊆wires (corrZ R) := by
  simp only [corrZ2,corrZ,correctionZ2,correctionZ,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (incr2_wires_le _ _ _)

theorem corrZ2_physical (R : KRegs) (hn : R.all.Nodup) (h : GatePhysical (corr R)) : GatePhysical (corrZ2 R) := by
  intro i hi
  rcases corrZ2_mem R i hi with hi|⟨a,b,rfl,ha,hb⟩
  · exact h i hi
  · show a≠b
    intro e; subst e
    exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) a ha hb

end TopBit

def headBlockZ (R : KRegs) : Program := seedsT R ++ (R.m6w++R.m7g++corrZ2 R++
  dSubZ R.lo R.dlo R.carry R.cin++dSubZ R.hi R.dhi R.carry R.cin)

/-- `make` with the dead lowest carries of `m6`, `m7`, `m8` dropped. -/
def makeZ (R : KRegs) : Program := headBlockZ R++R.m8g

theorem makeZ_counts_rel (R : KRegs) (w : R.W) :
    toffoliCount (makeZ R)+11+parR R=toffoliCount (make R) ∧ measurementCount (makeZ R)+4+parR R=measurementCount (make R) := by
  have a := R.m6w_counts w; have b := R.m7g_counts w; have c := R.m8g_counts w
  have cz := corrZ_counts R w
  have cz2 := corrZ2_counts R w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have ds1 := dSubZ_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have ds2 := dSubZ_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  have t1 := rawT_counts R.lo R.dlo R.pad R.carry (by simp only [KRegs.lo,List.length_take]; omega)
    (by simp only [KRegs.lo,KRegs.dlo,List.length_take]; omega) hpl
    (by simp only [KRegs.lo,List.length_take]; omega)
  have t2 := rawT_counts R.hi R.dhi R.pad R.carry (by simp only [KRegs.hi,List.length_drop]; omega)
    (by simp only [KRegs.hi,KRegs.dhi,List.length_drop]; omega) hpl
    (by simp only [KRegs.hi,List.length_drop]; omega)
  have t5 := rawT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,toffoliCount_append,measurementCount_append,parR]
  constructor <;> omega

theorem makeZ_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (makeZ R)+11+parR R=cost R ∧ measurementCount (makeZ R)+4+parR R=cost R := by
  have a := makeZ_counts_rel R w
  have b := make_counts R w he
  constructor <;> omega

theorem rawMakeT_wires_sub (xs dst pad carry : List Wire) :
    wires (rawMakeT xs dst pad carry)⊆wires (rawMake xs dst pad carry) := by
  unfold rawMakeT rawMake
  exact (ECDSAAdd.Entrant.TrimMid.P_side xs dst pad carry).1.1.trans (ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry).1

theorem seedsT_wires (R : KRegs) : wires (seedsT R)⊆wires (seeds R) := by
  simp only [seedsT,seeds,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
    (rawMakeT_wires_sub _ _ _ _) (rawMakeT_wires_sub _ _ _ _)) (subset_refl _)) (rawMakeT_wires_sub _ _ _ _)

theorem makeZ_support (R : KRegs) (w : R.W) : wires (makeZ R)⊆R.all.toFinset := by
  have old := (steps_support R w).1
  have a := R.m6w_wires; have b := R.m7g_wires; have c := R.m8g_wires
  have d := seedsT_wires R
  simp only [make,headBlock,wires_append,Finset.union_subset_iff] at old
  simp only [makeZ,headBlockZ,wires_append,Finset.union_subset_iff]
  obtain ⟨⟨o1,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  exact ⟨⟨d.trans o1,⟨⟨⟨⟨a.trans o2,b.trans o3⟩,((corrZ2_wires R).trans (wires_of_mem (corrZ_mem R))).trans o4⟩,(wires_of_mem (dSubZ_mem _ _ _ _)).trans o5⟩,(wires_of_mem (dSubZ_mem _ _ _ _)).trans o6⟩⟩,c.trans o7⟩

theorem makeZ_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeZ R) := by
  have old := (steps_physical R w hn).1
  have oldc := (steps_physical R w hn).2
  simp only [make,headBlock,seeds,rawMake,gatePhysical_append] at old
  simp only [clear,rawClear,gatePhysical_append] at oldc
  simp only [makeZ,headBlockZ,seedsT,gatePhysical_append]
  obtain ⟨⟨⟨⟨⟨⟨l1,l2⟩,⟨h1,h2⟩⟩,sm⟩,⟨s1,s2⟩⟩,⟨⟨⟨⟨o2,o3⟩,o4⟩,o5⟩,o6⟩⟩,o7⟩ := old
  have pl := ECDSAAdd.Entrant.TrimRow.physical R.lo R.dlo R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨l1,l2⟩) (by rw [gatePhysical_append]; exact ⟨l2,by tauto⟩)
  have ph := ECDSAAdd.Entrant.TrimRow.physical R.hi R.dhi R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,by tauto⟩)
  have ps := ECDSAAdd.Entrant.TrimRow.physical R.S R.T R.pad R.carry
    (by rw [gatePhysical_append]; exact ⟨s1,s2⟩) (by rw [gatePhysical_append]; exact ⟨s2,by tauto⟩)
  exact ⟨⟨⟨⟨⟨(ECDSAAdd.Entrant.TrimMid.P_side _ _ _ _).1.2.2 pl.1,(ECDSAAdd.Entrant.TrimMid.P_side _ _ _ _).1.2.2 ph.1⟩,sm⟩,
    (ECDSAAdd.Entrant.TrimMid.P_side _ _ _ _).1.2.2 ps.1⟩,⟨⟨⟨⟨R.m6w_physical hn,R.m7g_physical hn⟩,(corrZ2_physical R hn o4)⟩,(fun i hi => o5 i (dSubZ_mem _ _ _ _ i hi))⟩,(fun i hi => o6 i (dSubZ_mem _ _ _ _ i hi))⟩⟩,R.m8g_physical hn⟩

theorem makeZ_slots (R : KRegs) : Challenge.gateSlots (makeZ R)≤Challenge.gateSlots (make R) := by
  have a := R.m6w_slots; have b := R.m7g_slots; have c := R.m8g_slots; have cz := corrZ_slots R
  have cz2 := corrZ2_slots R
  have ds1 := dSubZ_slots R.lo R.dlo R.carry R.cin; have ds2 := dSubZ_slots R.hi R.dhi R.carry R.cin
  have t1 := (rawT_slots R.lo R.dlo R.pad R.carry).1
  have t2 := (rawT_slots R.hi R.dhi R.pad R.carry).1
  have t5 := (rawT_slots R.S R.T R.pad R.carry).1
  simp only [makeZ,make,headBlockZ,headBlock,seedsT,seeds,rawMakeT,rawMake,Challenge.gateSlots_append] at t1 t2 t5 ⊢
  omega

theorem prefixZ_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (headBlockZ R) m s)
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
  have bnd := KRegs.raw_low_bound R.h a b (by omega) alo bhi
  have hT1 : R.T.length=2*R.h+2 := by have := w.T; have := w.S; omega
  have zlt : Z<2^(2*R.h+2) := by
    have x := KRegs.raw_lo_le (R.h+1) S (by omega) (by rw [pow_succ]; dsimp only [S]; omega)
    rw [show 2*(R.h+1)=2*R.h+2 by ring] at x
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by positivity)) x
  have p2 : 2^(2*R.h)≤2^(2*R.h+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1 : A≤Z%2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact bnd.1
  have hA1 : A<2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact lt_of_lt_of_le bnd.2 p2
  have hZ1 : Z<2^R.T.length := by rw [hT1]; exact zlt
  have st1 := subloW_transition R w hn s hz0 hc0 hi0 A B S Z hA (rawValue_even _ _ (by omega)) hZ1 hb1 hA1
  have st2 := subhiZ_transition R w hn s hz0 hc0 hi0 A B S ((Z : Int)-A) hB (rawValue_even _ _ (by omega))
  have norm := cross_normalize R.h a b hh alo bhi
  change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
    (2*a*b : Nat) at norm
  have ab2 : 2*a*b<2^(2*R.h+1) := by
    have := Nat.mul_lt_mul'' alo bhi
    rw [show 2*R.h+1=R.h+R.h+1 by omega,pow_succ,pow_add]; nlinarith
  have st3 := corrZ2_transition R w he hh hn s hz0 hc0 hi0 A B ((Z : Int)-A-B) (2*a*b) ab2 norm
  have st4 := dsubloZ_transition R w he hn s hc0 hi0 A B S (2*a*b : Nat) (by exact_mod_cast rawValue_even _ _ (by omega))
  have st4' : Transition R s (vec A B S (2*a*b : Nat)) (vec (a^2 : Nat) B S (2*a*b : Nat))
      (dSubZ R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add,add_sub_cancel_right] using st4
  have st5 := dsubhiZ_transition R w he hn s hc0 hi0 (a^2 : Nat) B S (2*a*b : Nat) (by exact_mod_cast rawValue_even _ _ (by omega))
  have st5' : Transition R s (vec (a^2 : Nat) B S (2*a*b : Nat))
      (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (dSubZ R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add,add_sub_cancel_right] using st5
  have tail := (((st1.seq st2).seq st3).seq st4').seq st5'
  have initial := seedsT_shape R w he hn s (m.take (measurementCount (seedsT R))) hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (seedsT R))) initial
  simpa only [headBlockZ,run_append,A,B,S,Z,a,b,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using result


theorem makeZ_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (makeZ R) m s).phase=s.phase ∧
    regValue R.dst (run (makeZ R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (makeZ R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (makeZ R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (makeZ R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let f := m.take (measurementCount (headBlockZ R))
  let g := m.drop (measurementCount (headBlockZ R))
  let u := run (headBlockZ R) f s
  have h := prefixZ_shape R w he hh hn s f hd0 hS0 hT0 hz0 hp0 hc0 hi0
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
  have r := R.m8g_correct w hn u g (a*b) (fun q hq => (regValue_zero _ _).mp cv q (List.mem_of_mem_take hq))
    (by rw [tv]; ring) ((h.cin hn).trans hi0)
  have rv : regValue R.dmid (run R.m8g g u).basis=
      (2*a*b+(a^2+2^(2*R.h)*b^2)/2^R.h)%2^(2*R.bank.length-R.h) := by
    rw [r.2.2,regValue_append,tv,zv,h.cin hn,hi0,
      show regValue R.dmid u.basis=regValue R.dst u.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by have := w.dst; omega) u.basis,dv,L4]
    simp
  have frame : ∀q,q∉R.dmid → (run R.m8g g u).basis q=u.basis q := r.2.1
  have keepLow : regValue (R.dst.take R.h) (run R.m8g g u).basis=regValue (R.dst.take R.h) u.basis :=
    kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have dfin : regValue R.dst (run R.m8g g u).basis=(regValue R.bank s.basis)^2 := by
    rw [R.bank_value w s.basis,R.dst_value_mid w,rv,keepLow,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by have := w.dst; omega),dv]
    exact KRegs.kfinal a b R.h R.bank.length al (by simpa only [show R.bank.length-R.h=R.h by omega] using bl) (by omega)
  have result : (run R.m8g g u).phase=s.phase ∧ regValue R.dst (run R.m8g g u).basis=(regValue R.bank s.basis)^2 ∧
      regValue R.S (run R.m8g g u).basis=a+b ∧ regValue R.T (run R.m8g g u).basis=2*a*b ∧
      ∀q,q∉R.dst → q∉R.S → q∉R.T → (run R.m8g g u).basis q=s.basis q := by
    refine ⟨r.1.trans h.phase,dfin,?_,?_,?_⟩
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans sv
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans tv
    · intro q hd hs ht
      exact (frame q (fun bad => hd (List.mem_of_mem_drop bad))).trans (h.rest q hd hs ht)
  simpa only [makeZ,run_append,u,f,g,a,b] using result

theorem clearZ_start_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run R.c8g m s) (vec ((regValue R.lo s.basis)^2 : Nat) ((regValue R.hi s.basis)^2 : Nat)
      (regValue R.lo s.basis+regValue R.hi s.basis : Nat) (2*regValue R.lo s.basis*regValue R.hi s.basis : Nat)) := by
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
  have r := R.c8g_correct w hn s m (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq))
    (by rw [LowZero.head_false_of_even R.T R.zM s.basis (a*b) (by rw [hT0]; ring) (R.T_neg w)]; rfl) hi0
  have frame : ∀q,q∉R.dmid → (run R.c8g m s).basis q=s.basis q := r.2.1
  have low : regValue (R.dst.take R.h) (run R.c8g m s).basis=regValue (R.dst.take R.h) s.basis := kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have dv : regValue R.dst (run R.c8g m s).basis=a^2+2^(2*R.h)*b^2 := by
    rw [R.dst_value_mid w,
      r.2.2,low,regValue_append,hT0,zm,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by omega),
      show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd,L4]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  have dlo : regValue R.dlo (run R.c8g m s).basis=a^2 := by
    rw [show regValue R.dlo (run R.c8g m s).basis=regValue R.dst (run R.c8g m s).basis%2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt av]
  have dhi : regValue R.dhi (run R.c8g m s).basis=b^2 := by
    rw [show regValue R.dhi (run R.c8g m s).basis=regValue R.dst (run R.c8g m s).basis/2^(2*R.h) from
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


end ECDSAAdd.Entrant.DiagSq


section
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-! Bit 1 of the clear-side diagonal add. In `dAddZ xs dst` with `dst ≡ X² (mod 8)` the bit-0
carry is `x₀` (already a copy in `addHead0`) and the bit-1 majority fires on
`(y₁ ⊕ x₁) ∧ (x₀ ⊕ x₁) = x₁ ∧ ¬x₀ = y₂`: its Toffoli is the CNOT `y₂ → c₁`. -/

def head1Pre (a y cin c a1 y1 : Wire) : Program :=
  [.CX a y,.CX a cin,.CX a c,.CX a cin,.CX a y,.CX a1 y1,.CX a1 c]

def head1Post (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) : Program :=
  [.CX a1 c1,.CX a1 c,.CX a1 y1]++(mappedAdd (b''::bits) (y2::ys) cs c1++
    mappedEraseCarry ⟨some a1,false⟩ y1 c c1++mappedSum ⟨some a1,false⟩ y1 c)++
    mappedEraseCarry ⟨some a,false⟩ y cin c++mappedSum ⟨some a,false⟩ y cin

def addHead1 (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  match bits, ys, carry with
  | ⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits', y::y1::y2::y3::ys', c::c1::c2::cs =>
      head1Pre a y cin c a1 y1++(.CX y2 c1::head1Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs))
  | bits, ys, carry => addHead0 bits ys carry cin

theorem addHead0_split1 (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) :
    addHead0 (⟨some a,false⟩::⟨some a1,false⟩::b''::bits) (y::y1::y2::ys) (c::c1::cs) cin=
      head1Pre a y cin c a1 y1++(.CCX y1 c c1::head1Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  simp [addHead0,maj0,mappedAdd,mappedMajority,majority,head1Pre,head1Post,List.append_assoc]

theorem ccx_as_cx (a b t y : Wire) (p : Program) (m : List Bool) (s : State)
    (h : (s.basis a && s.basis b)=s.basis y) : run (.CCX a b t::p) m s=run (.CX y t::p) m s := by
  simp only [run,h]

theorem addHead1_run (a a1 y y1 y2 y3 c c1 c2 cin : Wire) (b'' b3 : MappedBit) (bits : List MappedBit)
    (ys cs : List Wire) (m : List Bool) (s : State)
    (hd : [a,a1,y,y1,y2,c,cin].Nodup)
    (hcopy : ((s.basis y1 ^^ s.basis a1) && (s.basis c ^^ s.basis a ^^ s.basis a1))=s.basis y2) :
    run (addHead1 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s=
      run (addHead0 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s := by
  rw [addHead0_split1]
  simp only [addHead1]
  have m0 : measurementCount (head1Pre a y cin c a1 y1)=0 := rfl
  rw [run_append,run_append,m0,List.take_zero,List.drop_zero]
  symm
  apply ccx_as_cx
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,or_false,
    not_false_eq_true,and_true] at hd
  obtain ⟨⟨h1,h2,h3,h4,h5,h6⟩,⟨h7,h8,h9,h10,h11⟩,⟨h12,h13,h14,h15⟩,⟨h16,h17,h18⟩,⟨h19,h20⟩,h21⟩ := hd
  simp only [head1Pre,run,writeBit,Function.update]
  simp [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,
    Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5,Ne.symm h6,Ne.symm h7,Ne.symm h8,Ne.symm h9,
    Ne.symm h10,Ne.symm h11,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h15,Ne.symm h16,Ne.symm h17,
    Ne.symm h18,Ne.symm h19,Ne.symm h20,Ne.symm h21] at hcopy ⊢
  try (rw [← hcopy])

theorem diag_cons2 (x x' : Wire) (xs : List Wire) :
    ∃ b'' bits,mappedDiagonal (x::x'::xs)=⟨some x,false⟩::⟨some x',false⟩::b''::bits := by
  cases xs with
  | nil => exact ⟨_,_,rfl⟩
  | cons x'' xs => exact ⟨_,_,rfl⟩

theorem diag_cons3 (x x' : Wire) (xs : List Wire) :
    ∃ b'' b3 bits,mappedDiagonal (x::x'::xs)=⟨some x,false⟩::⟨some x',false⟩::b''::b3::bits := by
  cases xs with
  | nil => exact ⟨_,_,_,rfl⟩
  | cons x'' xs =>
    cases xs with
    | nil => exact ⟨_,_,_,rfl⟩
    | cons x3 xs => exact ⟨_,_,_,rfl⟩

def dAddZ2 (xs dst carry : List Wire) (cin : Wire) : Program :=
  addHead1 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin

/-- The low three bits of `X²`: bit 1 is clear and bit 2 is `x₁ ∧ ¬x₀`. -/
theorem bits_of_sq8 (y0 y1 y2 x0 x1 : Wire) (ys xt : List Wire) (st : BasisState) (A : Int)
    (hv : (regValue (y0::y1::y2::ys) st : Int) ≡ A [ZMOD (2^(y0::y1::y2::ys).length : Nat)])
    (h8 : (8:Int)∣A-((regValue (x0::x1::xt) st : Nat) : Int)^2) :
    ((st y1 ^^ st x1) && (st x0 ^^ st x1))=st y2 := by
  have ey : regValue (y0::y1::y2::ys) st=(if st y0 then 1 else 0)+2*((if st y1 then 1 else 0)+
      2*((if st y2 then 1 else 0)+2*regValue ys st)) := rfl
  have ex : regValue (x0::x1::xt) st=(if st x0 then 1 else 0)+2*((if st x1 then 1 else 0)+
      2*regValue xt st) := rfl
  have d8 : (8:Int)∣((2^(y0::y1::y2::ys).length : Nat) : Int) := by
    have : 2^(y0::y1::y2::ys).length=8*2^ys.length := by
      simp only [List.length_cons,pow_succ]; ring
    rw [this]; push_cast; exact Dvd.intro _ rfl
  have d1 : (8:Int)∣(regValue (y0::y1::y2::ys) st : Int)-A := dvd_trans d8 (Int.ModEq.dvd hv.symm)
  have d2 : (8:Int)∣(regValue (y0::y1::y2::ys) st : Int)-((regValue (x0::x1::xt) st : Nat) : Int)^2 := by
    have e : (regValue (y0::y1::y2::ys) st : Int)-((regValue (x0::x1::xt) st : Nat) : Int)^2=
        ((regValue (y0::y1::y2::ys) st : Int)-A)+(A-((regValue (x0::x1::xt) st : Nat) : Int)^2) := by ring
    rw [e]; exact dvd_add d1 h8
  have hX : ((regValue (x0::x1::xt) st : Nat) : Int)=((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)+
      4*(regValue xt st : Int) := by rw [ex]; push_cast; ring
  have hY : ((regValue (y0::y1::y2::ys) st : Nat) : Int)=((if st y0 then 1 else 0)+2*(if st y1 then 1 else 0)+
      4*(if st y2 then 1 else 0) : Int)+8*(regValue ys st : Int) := by rw [ey]; push_cast; ring
  have d4 : (8:Int)∣((if st y0 then 1 else 0)+2*(if st y1 then 1 else 0)+4*(if st y2 then 1 else 0) : Int)-
      ((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)^2 := by
    have e : ((if st y0 then 1 else 0)+2*(if st y1 then 1 else 0)+4*(if st y2 then 1 else 0) : Int)-
        ((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)^2=
        ((regValue (y0::y1::y2::ys) st : Int)-((regValue (x0::x1::xt) st : Nat) : Int)^2)+
        8*(((if st x0 then 1 else 0)+2*(if st x1 then 1 else 0) : Int)*(regValue xt st : Int)+
          2*(regValue xt st : Int)^2-(regValue ys st : Int)) := by
      rw [hX,hY]; ring
    rw [e]; exact dvd_add d2 (dvd_mul_right 8 _)
  revert d4
  generalize st y0=b0; generalize st y1=b1; generalize st y2=b2; generalize st x0=b3; generalize st x1=b4
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

theorem dAddZ2_run (xs dst carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length)
    (hcopy : ∀x0 x1 xt y0 y1 y2 ys c cs,xs=x0::x1::xt → dst=y0::y1::y2::ys →
      carry.take (dst.length-1)=c::cs →
      ((s.basis y1 ^^ s.basis x1) && (s.basis c ^^ s.basis x0 ^^ s.basis x1))=s.basis y2) :
    run (dAddZ2 xs dst carry cin) m s=run (dAddZ xs dst carry cin) m s := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt,xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,y3,ys,rfl⟩ : ∃ y0 y1 y2 y3 ys,dst=y0::y1::y2::y3::ys := by
    match dst, hd with
    | y0::y1::y2::y3::ys, _ => exact ⟨y0,y1,y2,y3,ys,rfl⟩
  obtain ⟨c,c1,c2,cs,hct⟩ : ∃ c c1 c2 cs,carry.take ((y0::y1::y2::y3::ys).length-1)=c::c1::c2::cs := by
    have hl : 3≤(carry.take ((y0::y1::y2::y3::ys).length-1)).length := by
      rw [List.length_take]; simp only [List.length_cons]; omega
    match carry.take ((y0::y1::y2::y3::ys).length-1), hl with
    | c::c1::c2::cs, _ => exact ⟨c,c1,c2,cs,rfl⟩
  obtain ⟨b'',b3,bits,e⟩ := diag_cons3 x0 x1 xt
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  have cnt := fun w => List.nodup_iff_count.mp hn w
  have nd : [x0,x1,y0,y1,y2,c,cin].Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have tc : [c].count w≤carry.count w := by
      by_cases hw : w=c
      · subst hw; simpa using List.count_pos_iff.mpr (hcm w (by simp))
      · rw [List.count_eq_zero.mpr (by simpa using hw)]; exact Nat.zero_le _
    simp only [List.count_cons,List.count_append,List.count_nil] at h tc ⊢
    omega
  simp only [dAddZ2,dAddZ,e,hct]
  exact addHead1_run x0 x1 y0 y1 y2 y3 c c1 c2 cin b'' b3 bits ys cs m s nd
    (hcopy x0 x1 xt y0 y1 y2 (y3::ys) c (c1::c2::cs) rfl rfl hct)

theorem daddloZ2_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAp : (2:Int)∣A-regValue R.lo base.basis)
    (h8 : (8:Int)∣A-((regValue R.lo base.basis : Nat) : Int)^2) :
    Transition R base (vec A B S T) (vec (A+(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (dAddZ2 R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have cv := ht.keep hn R.carry (fun q h => Or.inr (Or.inr (Or.inr (Or.inl h))))
  have cz : ∀q∈R.carry,t.basis q=false := (regValue_zero _ _).mp (cv.trans hc0)
  have e := dAddZ2_run R.lo R.dlo R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) (by
      intro x0 x1 xt y0 y1 y2 ys c cs hx hy hcc
      have hcm : c∈R.carry := List.mem_of_mem_take (by rw [hcc]; exact List.mem_cons_self)
      rw [cz c hcm,Bool.false_xor]
      have hv := ht.value 0
      change (regValue R.dlo t.basis : Int) ≡ A [ZMOD (2^R.dlo.length : Nat)] at hv
      rw [hy] at hv
      apply bits_of_sq8 y0 y1 y2 x0 x1 ys xt t.basis A hv
      rw [← hx,xv]; exact h8)
  rw [e]
  exact daddloZ_transition R w he hn base hc0 hi0 A B S T hAp t rec ht

theorem daddhiZ2_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) (hAp : (2:Int)∣B-regValue R.hi base.basis)
    (h8 : (8:Int)∣B-((regValue R.hi base.basis : Nat) : Int)^2) :
    Transition R base (vec A B S T) (vec A (B+(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (dAddZ2 R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := ht.keep hn R.carry (fun q h => Or.inr (Or.inr (Or.inr (Or.inl h))))
  have cz : ∀q∈R.carry,t.basis q=false := (regValue_zero _ _).mp (cv.trans hc0)
  have e := dAddZ2_run R.hi R.dhi R.carry R.cin rec t
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) (by
      intro x0 x1 xt y0 y1 y2 ys c cs hx hy hcc
      have hcm : c∈R.carry := List.mem_of_mem_take (by rw [hcc]; exact List.mem_cons_self)
      rw [cz c hcm,Bool.false_xor]
      have hv := ht.value 1
      change (regValue R.dhi t.basis : Int) ≡ B [ZMOD (2^R.dhi.length : Nat)] at hv
      rw [hy] at hv
      apply bits_of_sq8 y0 y1 y2 x0 x1 ys xt t.basis B hv
      rw [← hx,xv]; exact h8)
  rw [e]
  exact daddhiZ_transition R w he hn base hc0 hi0 A B S T hAp t rec ht

theorem dAddZ2_shape (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) :
    ∃ a a1 y y1 y2 c c1 b'' bits ys cs,y2∈dst ∧ c1∈carry ∧
      dAddZ2 xs dst carry cin=head1Pre a y cin c a1 y1++(.CX y2 c1::head1Post a y cin c a1 y1 c1 b'' bits y2 ys cs) ∧
      dAddZ xs dst carry cin=head1Pre a y cin c a1 y1++(.CCX y1 c c1::head1Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt,xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,y3,ys,rfl⟩ : ∃ y0 y1 y2 y3 ys,dst=y0::y1::y2::y3::ys := by
    match dst, hd with
    | y0::y1::y2::y3::ys, _ => exact ⟨y0,y1,y2,y3,ys,rfl⟩
  obtain ⟨c,c1,c2,cs,hct⟩ : ∃ c c1 c2 cs,carry.take ((y0::y1::y2::y3::ys).length-1)=c::c1::c2::cs := by
    have hl : 3≤(carry.take ((y0::y1::y2::y3::ys).length-1)).length := by
      rw [List.length_take]; simp only [List.length_cons]; omega
    match carry.take ((y0::y1::y2::y3::ys).length-1), hl with
    | c::c1::c2::cs, _ => exact ⟨c,c1,c2,cs,rfl⟩
  obtain ⟨b'',b3,bits,e⟩ := diag_cons3 x0 x1 xt
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  refine ⟨x0,x1,y0,y1,y2,c,c1,b'',b3::bits,y3::ys,c2::cs,by simp,hcm c1 (by simp),?_,?_⟩
  · simp only [dAddZ2,e,hct,addHead1]
  · simp only [dAddZ,e,hct]; exact addHead0_split1 _ _ _ _ _ _ _ _ _ _ _ _

theorem dAddZ2_counts (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) :
    toffoliCount (dAddZ2 xs dst carry cin)+1=toffoliCount (dAddZ xs dst carry cin) ∧
    measurementCount (dAddZ2 xs dst carry cin)=measurementCount (dAddZ xs dst carry cin) := by
  obtain ⟨a,a1,y,y1,y2,c,c1,b'',bits,ys,cs,-,-,e2,e1⟩ := dAddZ2_shape xs dst carry cin hx hd hc
  rw [e2,e1]
  have t1 : ∀ (u v : Wire) (p : Program),toffoliCount (.CX u v::p)=toffoliCount p := fun _ _ _ => rfl
  have t2 : ∀ (u v w : Wire) (p : Program),toffoliCount (.CCX u v w::p)=1+toffoliCount p := fun _ _ _ _ => rfl
  simp only [toffoliCount_append,measurementCount_append,t1,t2]
  exact ⟨by omega,rfl⟩

theorem addHead1_slots (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (addHead1 bits ys carry cin)=Challenge.gateSlots (addHead0 bits ys carry cin) := by
  unfold addHead1
  split
  · rw [addHead0_split1]
    simp [Challenge.gateSlots_append,Challenge.gateSlots,Challenge.instructionSlots]
  · rfl

theorem dAddZ2_slots_eq (xs dst carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (dAddZ2 xs dst carry cin)=Challenge.gateSlots (dAddZ xs dst carry cin) :=
  addHead1_slots _ _ _ _

theorem y_mem_mappedMajority (b : MappedBit) (y cin t : Wire) : y∈wires (mappedMajority b y cin t) := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp [mappedMajority,hw,hf,majority,borrowMajority,wires,Instr.wires]

theorem addHead1_wires_le (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (addHead1 bits ys carry cin)⊆wires (addHead0 bits ys carry cin) := by
  unfold addHead1
  split
  · rename_i a a1 b'' b3 bits' y y1 y2 y3 ys' c c1 c2 cs
    rw [addHead0_split1]
    have hy2 : y2∈wires (head1Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs)) := by
      have h := y_mem_mappedMajority b'' y2 c1 c2
      simp only [head1Post,mappedAdd,wires_append,Finset.mem_union] at h ⊢
      tauto
    simp only [wires_append,wires,Instr.wires]
    apply Finset.union_subset_union (Finset.Subset.refl _)
    intro q hq
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq ⊢
    rcases hq with (rfl|rfl)|h
    · exact Or.inr hy2
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr h
  · exact Finset.Subset.refl _

theorem dAddZ2_wires_le (xs dst carry : List Wire) (cin : Wire) :
    wires (dAddZ2 xs dst carry cin)⊆wires (dAddZ xs dst carry cin) :=
  addHead1_wires_le _ _ _ _

theorem dAddZ2_mem (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) :
    ∀i∈dAddZ2 xs dst carry cin,i∈dAddZ xs dst carry cin ∨ ∃ y c,y∈dst ∧ c∈carry ∧ i=.CX y c := by
  obtain ⟨a,a1,y,y1,y2,c,c1,b'',bits,ys,cs,hy2,hc1,e2,e1⟩ := dAddZ2_shape xs dst carry cin hx hd hc
  rw [e2,e1]
  intro i hi
  simp only [List.mem_append,List.mem_cons] at hi ⊢
  rcases hi with hi|hi|hi
  · exact Or.inl (Or.inl hi)
  · exact Or.inr ⟨y2,c1,hy2,hc1,hi⟩
  · exact Or.inl (Or.inr (Or.inr hi))

theorem dAddZ2_wires (xs dst carry : List Wire) (cin : Wire) :
    wires (dAddZ2 xs dst carry cin)⊆wires (dAddZ xs dst carry cin)∪dst.toFinset∪carry.toFinset :=
  (dAddZ2_wires_le xs dst carry cin).trans
    (Finset.subset_union_left.trans Finset.subset_union_left)

theorem dAddZ2_physical (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : 4≤carry.length) (hdc : ∀q∈dst,q∉carry) (h : GatePhysical (dAddZ xs dst carry cin)) :
    GatePhysical (dAddZ2 xs dst carry cin) := by
  intro i hi
  rcases dAddZ2_mem xs dst carry cin hx hd hc i hi with h'|⟨y,c,hy,hcm,rfl⟩
  · exact h i h'
  · show y≠c
    intro e; exact hdc y hy (e ▸ hcm)

end ECDSAAdd.Entrant.DiagSq
end

namespace ECDSAAdd.Entrant.Z5Diagonal
open Arithmetic DiagSq KRegs

def clear (R : KRegs) : Program := R.c8g++(dAddZ2 R.lo R.dlo R.carry R.cin++
  dAddZ2 R.hi R.dhi R.carry R.cin++corrBackZ R++R.c7g++R.c6w++
  rawClearT R.S R.T R.pad R.carry++R.scl1591++rawClearT R.hi R.dhi R.pad R.carry++
  rawClearT R.lo R.dlo R.pad R.carry)

def makeC (R : KRegs) : Program := DiagSq.makeZ R++R.scl1591
def clearC (R : KRegs) : Program := R.smk++clear R

theorem clearSum_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (base : State) (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B 0 T) R.scl1591 := by
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
  have r := R.scl1591_correct w hn t rec (by rw [sv,al,bl])
    ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
  have val : (regValue (reg R 2) (run R.scl1591 rec t).basis : Int) ≡ 0 [ZMOD (2^(reg R 2).length : Nat)] := by
    change (regValue R.S _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec2] using ht.step hn 2 0 r.1 r.2.2 val


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
  have st1 := daddloZ2_transition R w he hn s hc0 hi0 (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat) (sq_sub_even a)
    (by push_cast; simp [a])
  have st1' : Transition R s (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (vec A (b^2 : Nat) S (2*a*b : Nat)) (dAddZ2 R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add] using st1
  have st2 := daddhiZ2_transition R w he hn s hc0 hi0 A (b^2 : Nat) S (2*a*b : Nat) (sq_sub_even b)
    (by push_cast; simp [b])
  have st2' : Transition R s (vec A (b^2 : Nat) S (2*a*b : Nat))
      (vec A B S (2*a*b : Nat)) (dAddZ2 R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add] using st2
  have st3 := corrBackZ_transition R w he hh hn s hz0 hc0 hi0 A B (2*a*b : Nat)
  have st4 := addhiZ_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d) hB (by
    apply dvd_add
    · push_cast; exact ⟨(a:Int)*b, by ring⟩
    · dsimp only [d]
      apply dvd_sub
      · apply Dvd.dvd.mul_right
        push_cast; exact dvd_pow_self 2 (by omega)
      · push_cast; exact dvd_pow_self 2 (by omega))
  have norm := cross_normalize R.h a b hh alo bhi
  have norm' : ((2*a*b : Nat) : Int)+d+B+A=Z := by
    change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
      (2*a*b : Nat) at norm
    dsimp only [d]
    linarith only [norm]
  have bnd := KRegs.raw_low_bound R.h a b (by omega) alo bhi
  have hT1 : R.T.length=2*R.h+2 := by have := w.T; have := w.S; omega
  have zlt : Z<2^(2*R.h+2) := by
    have x := KRegs.raw_lo_le (R.h+1) S (by omega) (by rw [pow_succ]; dsimp only [S]; omega)
    rw [show 2*(R.h+1)=2*R.h+2 by ring] at x
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (by positivity)) x
  have p2 : 2^(2*R.h)≤2^(2*R.h+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hb1 : A≤Z%2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact bnd.1
  have hA1 : A<2^(R.T.length-1) := by rw [hT1,show 2*R.h+2-1=2*R.h+1 by omega]; exact lt_of_lt_of_le bnd.2 p2
  have hZ1 : Z<2^R.T.length := by rw [hT1]; exact zlt
  have st5 := addloW_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d+B) Z hA (rawValue_even _ _ (by omega)) norm' hZ1 hb1 hA1
  rw [norm'] at st5
  have st6 := rawclearSum_transitionT R w hn s hp0 hc0 A B S slt
  rw [hSS] at st6
  have st7 := clearSum_transition R w he hn s hz0 hc0 hi0 A B 0
  have st8 := rawclearhi_transitionT R w he hn s hp0 hc0 A 0 0
  have st9 := rawclearlo_transitionT R w he hn s hp0 hc0 0 0 0
  have st3' : Transition R s (vec A B S (2*a*b : Nat))
      (vec A B S ((2*a*b : Nat)+d)) (corrBackZ R) := by
    (convert st3 using 1; try rfl)
    simp only [d]
    congr 1
    ring
  have tail := ((((((((st1'.seq st2').seq st3').seq st4).seq st5).seq st6).seq st7).seq st8).seq st9)
  have initial := clearZ_start_shape R w he hn s (m.take (measurementCount R.c8g)) hd0 hS0 hT0 hz0 hc0 hi0
  have result := tail _ (m.drop (measurementCount R.c8g)) initial
  have final : Shape R s (run (clear R) m s) (vec 0 0 0 0) := by
    simpa only [clear,run_append] using result
  refine ⟨final.phase,?_,final.exact 2 0 rfl (by norm_num),final.exact 3 0 rfl (by norm_num),final.rest⟩
  have zlo : regValue R.dlo (run (clear R) m s).basis=0 := final.exact 0 0 rfl (by norm_num)
  have zhi : regValue R.dhi (run (clear R) m s).basis=0 := final.exact 1 0 rfl (by norm_num)
  rw [R.dst_value w,zlo,zhi]
  simp

variable (R : KRegs)

theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.makeZ R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := DiagSq.makeZ_correct R w he hh hn s m hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩

theorem diag_sq_full_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clear R) R.invF := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  have r := clear_correct R w he hh hn s m hd0 (by rw [hI.1,R.lo_mod w,R.hi_div w]) (by rw [hI.2,R.lo_mod w,R.hi_div w])
    (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [regValue_append,r.2.2.1,r.2.2.2.1]; simp

theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (DiagSq.makeZ R))
  let b := m.drop (measurementCount (DiagSq.makeZ R))
  have r := DiagSq.makeZ_correct R w he hh hn s a hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (DiagSq.makeZ R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,run_append,←hu]
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
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (clearC R) R.invC := by
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
  have c := clear_correct R w he hh hn u b (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),bk]; exact hd0)
    (by rw [r.2.1,lo,hi])
    (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))),hI.2,lo,hi,R.lo_mod w,R.hi_div w])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inl h))))).trans hp0)
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((r.2.2 _ (o _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hi0)
  have eq : run (clearC R) m s=run (clear R) b u := by
    rw [clearC,run_append,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)


theorem clear_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clear R)+(R.bank.length-R.h)+12+DiagSq.parR R=toffoliCount (DiagSq.clear R) ∧
    measurementCount (clear R)+4+DiagSq.parR R=measurementCount (DiagSq.clear R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z8 := R.c8g_counts w; have z7 := R.c7g_counts w; have z6 := R.c6w_counts w
  have cb := DiagSq.corrBackZ_counts R w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad; have hh := w.hh; have h5 := w.h5
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have r1 := DiagSq.rawClearT_counts R.lo R.dlo R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r2 := DiagSq.rawClearT_counts R.hi R.dhi R.pad R.carry (by omega) (by omega) hpl (by omega)
  have r5 := DiagSq.rawClearT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  have da1 := DiagSq.dAddZ_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have da2 := DiagSq.dAddZ_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  have db1 := DiagSq.dAddZ2_counts R.lo R.dlo R.carry R.cin (by omega) (by omega) (by omega)
  have db2 := DiagSq.dAddZ2_counts R.hi R.dhi R.carry R.cin (by omega) (by omega) (by omega)
  simp only [clear,DiagSq.clear,toffoliCount_append,measurementCount_append,DiagSq.parR]
  constructor <;> omega

theorem makeC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (makeC R)+(R.bank.length-R.h)+11+DiagSq.parR R=toffoliCount (DiagSq.makeC R) ∧
    measurementCount (makeC R)+4+DiagSq.parR R=measurementCount (DiagSq.makeC R) := by
  have a := R.piece_counts w
  have b := R.scl1591_counts w
  have z := DiagSq.makeZ_counts_rel R w
  simp only [makeC,DiagSq.makeC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clearC_counts_diff (R : KRegs) (w : R.W) :
    toffoliCount (clearC R)+(R.bank.length-R.h)+12+DiagSq.parR R=toffoliCount (DiagSq.clearC R) ∧
    measurementCount (clearC R)+4+DiagSq.parR R=measurementCount (DiagSq.clearC R) := by
  have h := clear_counts_diff R w
  simp only [clearC,DiagSq.clearC,toffoliCount_append,measurementCount_append]
  constructor <;> omega

theorem clear_support (R : KRegs) (w : R.W) : wires (clear R)⊆R.all.toFinset := by
  have old := (DiagSq.steps_support R w).2
  have new := R.scl1591_support w
  have pcs := R.piece_support w
  have q2 := pcs.2.2.2.1
  simp only [wires_append,Finset.union_subset_iff] at q2
  have c8w : wires R.c8g⊆R.all.toFinset := R.c8g_wires.trans q2.1.1
  have c7w : wires R.c7g⊆R.all.toFinset := R.c7g_wires.trans q2.1.2
  have c6w' : wires R.c6w⊆R.all.toFinset := R.c6w_wires.trans q2.2
  clear q2 pcs
  simp only [clear,DiagSq.clear,wires_append,Finset.union_subset_iff] at old ⊢
  have rS : wires (rawClearT R.S R.T R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rH : wires (rawClearT R.hi R.dhi R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have rL : wires (rawClearT R.lo R.dlo R.pad R.carry)⊆R.all.toFinset :=
    (DiagSq.rawClearT_wires_sub _ _ _ _).trans (by tauto)
  have cbw : wires (corrBackZ R)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.corrBackZ_mem R)).trans (by tauto)
  have daw1 : wires (dAddZ R.lo R.dlo R.carry R.cin)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.dAddZ_mem _ _ _ _)).trans (by tauto)
  have daw2 : wires (dAddZ R.hi R.dhi R.carry R.cin)⊆R.all.toFinset := (DiagSq.wires_of_mem (DiagSq.dAddZ_mem _ _ _ _)).trans (by tauto)
  have dbw1 : wires (dAddZ2 R.lo R.dlo R.carry R.cin)⊆R.all.toFinset :=
    (DiagSq.dAddZ2_wires_le _ _ _ _).trans daw1
  have dbw2 : wires (dAddZ2 R.hi R.dhi R.carry R.cin)⊆R.all.toFinset :=
    (DiagSq.dAddZ2_wires_le _ _ _ _).trans daw2
  tauto

theorem makeC_support (R : KRegs) (w : R.W) : wires (makeC R)⊆R.all.toFinset := by
  simpa only [makeC,wires_append,Finset.union_subset_iff] using
    And.intro (DiagSq.makeZ_support R w) (R.scl1591_support w)

theorem clearC_support (R : KRegs) (w : R.W) : wires (clearC R)⊆R.all.toFinset := by
  simpa only [clearC,wires_append,Finset.union_subset_iff] using
    And.intro (R.piece_support w).1 (clear_support R w)

theorem clear_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clear R) := by
  have old := (DiagSq.steps_physical R w hn).2
  have new := R.scl1591_physical w hn
  have z8 := R.c8g_physical hn; have z7 := R.c7g_physical hn; have z6 := R.c6w_physical hn
  have oldm := (DiagSq.steps_physical R w hn).1
  simp only [DiagSq.make,DiagSq.headBlock,DiagSq.seeds,gatePhysical_append] at oldm
  simp only [clear,DiagSq.clear,gatePhysical_append] at old ⊢
  have rS := DiagSq.rawClearT_physical_of R.S R.T R.pad R.carry (by tauto) (by tauto)
  have rH := DiagSq.rawClearT_physical_of R.hi R.dhi R.pad R.carry (by tauto) (by tauto)
  have rL := DiagSq.rawClearT_physical_of R.lo R.dlo R.pad R.carry (by tauto) (by tauto)
  have cbp : GatePhysical (corrBackZ R) := fun i hi => (show GatePhysical (corrBack R) by tauto) i (DiagSq.corrBackZ_mem R i hi)
  have dap1 : GatePhysical (dAddZ R.lo R.dlo R.carry R.cin) := fun i hi => (show GatePhysical (mappedDiagAdd R.lo R.dlo R.carry R.cin) by tauto) i (DiagSq.dAddZ_mem _ _ _ _ i hi)
  have dap2 : GatePhysical (dAddZ R.hi R.dhi R.carry R.cin) := fun i hi => (show GatePhysical (mappedDiagAdd R.hi R.dhi R.carry R.cin) by tauto) i (DiagSq.dAddZ_mem _ _ _ _ i hi)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have he5 := w.h5; have hh := w.hh
  have dc : ∀q∈R.dst,q∉R.carry := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have dbp1 : GatePhysical (dAddZ2 R.lo R.dlo R.carry R.cin) :=
    DiagSq.dAddZ2_physical _ _ _ _ (by omega) (by omega) (by omega) (fun q h => dc q (List.mem_of_mem_take h)) dap1
  have dbp2 : GatePhysical (dAddZ2 R.hi R.dhi R.carry R.cin) :=
    DiagSq.dAddZ2_physical _ _ _ _ (by omega) (by omega) (by omega) (fun q h => dc q (List.mem_of_mem_drop h)) dap2
  tauto

theorem makeC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) := by
  simpa only [makeC,gatePhysical_append] using
    And.intro (DiagSq.makeZ_physical R w hn) (R.scl1591_physical w hn)

theorem clearC_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (clearC R) := by
  simpa only [clearC,gatePhysical_append] using
    And.intro (R.piece_physical hn).1 (clear_physical R w hn)

theorem clear_slots_le (R : KRegs) : Challenge.gateSlots (clear R)≤Challenge.gateSlots (DiagSq.clear R) := by
  have h := R.scl1591_slots
  have z8 := R.c8g_slots; have z7 := R.c7g_slots; have z6 := R.c6w_slots
  have rS := DiagSq.rawClearT_slots_le R.S R.T R.pad R.carry
  have rH := DiagSq.rawClearT_slots_le R.hi R.dhi R.pad R.carry
  have rL := DiagSq.rawClearT_slots_le R.lo R.dlo R.pad R.carry
  have cb := DiagSq.corrBackZ_slots R
  have da1 := DiagSq.dAddZ_slots R.lo R.dlo R.carry R.cin; have da2 := DiagSq.dAddZ_slots R.hi R.dhi R.carry R.cin
  have db1 := DiagSq.dAddZ2_slots_eq R.lo R.dlo R.carry R.cin; have db2 := DiagSq.dAddZ2_slots_eq R.hi R.dhi R.carry R.cin
  simp only [clear,DiagSq.clear,Challenge.gateSlots_append] at *
  omega

theorem makeC_slots_le (R : KRegs) : Challenge.gateSlots (makeC R)≤Challenge.gateSlots (DiagSq.makeC R) := by
  have h := R.scl1591_slots
  have z := DiagSq.makeZ_slots R
  simp only [makeC,DiagSq.makeC,Challenge.gateSlots_append] at *
  omega

theorem clearC_slots_le (R : KRegs) : Challenge.gateSlots (clearC R)≤Challenge.gateSlots (DiagSq.clearC R) := by
  have h := clear_slots_le R
  simp only [clearC,DiagSq.clearC,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.Z5Diagonal

namespace ECDSAAdd.Entrant.Z5Diagonal
open Arithmetic

theorem clear_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (clear R)=DiagSq.cost R-R.h-12-DiagSq.parR R ∧ measurementCount (clear R)+4+DiagSq.parR R=DiagSq.cost R := by
  have a := clear_counts_diff R w
  have b := DiagSq.clear_counts R w he
  constructor <;> omega

theorem steps_support (R : KRegs) (w : R.W) :
    wires (DiagSq.makeZ R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset :=
  ⟨DiagSq.makeZ_support R w,clear_support R w⟩

theorem steps_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (DiagSq.makeZ R) ∧ GatePhysical (clear R) :=
  ⟨DiagSq.makeZ_physical R w hn,clear_physical R w hn⟩

theorem tiny_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (DiagSq.makeZ R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 :=
  ⟨(DiagSq.makeZ_slots R).trans (DiagSq.tiny_slots R w he hh).1,(clear_slots_le R).trans (DiagSq.tiny_slots R w he hh).2⟩

end ECDSAAdd.Entrant.Z5Diagonal
end

section
namespace ECDSAAdd.Entrant.TrimSquare3
open Arithmetic
theorem tsq3_slots_rel (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsq3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsq2 xs dst pad carry cin) ∧
    Challenge.gateSlots (tsqc3 xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsqc2 xs dst pad carry cin) := by
  rcases tsq3_form xs dst pad carry cin with ⟨e1,e2⟩|⟨A,B,A',B',x,y,cy,c,e1,e2,e3,e4⟩
  · rw [e1,e2]; exact ⟨le_refl _,le_refl _⟩
  · rw [e1,e2,e3,e4]
    have d := addDrop_slots x y cy c
    simp only [Challenge.gateSlots_append]
    constructor <;> omega
theorem tsqM_slots_rel (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (TrimMid.tsqM xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsq2 xs dst pad carry cin) ∧
    Challenge.gateSlots (TrimMid.tsqcM xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsqc2 xs dst pad carry cin) :=
  ⟨(TrimMid.tsqM_rel xs dst pad carry cin).1.2.1.trans (tsq3_slots_rel xs dst pad carry cin).1,
    (TrimMid.tsqM_rel xs dst pad carry cin).2.2.1.trans (tsq3_slots_rel xs dst pad carry cin).2⟩
end ECDSAAdd.Entrant.TrimSquare3
end

section
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TrimSquare4
set_option linter.unusedVariables false
open Arithmetic

/-! Bit 1 of `TrimSquare.drop2` in the square clear `tsqc3`. At the start of `tsqc3` the destination holds
exactly `X²` and the carries are clean. `drop2` copies the dead bit-0 carry (`CX x₀ c`), and the bit-1
majority then fires on `(y₁ ⊕ x₁) ∧ (x₀ ⊕ x₁) = x₁ ∧ ¬x₀ = y₂` (bits of a square), so its Toffoli is
the CNOT `y₂ → c₁`. -/

def d3Pre (a c a1 y1 : Wire) : Program := [.CX a c,.CX a1 y1,.CX a1 c]

def d3Post (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) : Program :=
  ([.CX a1 c1,.CX a1 c,.CX a1 y1]++(mappedAdd (b''::bits) (y2::ys) cs c1++mappedEraseCarry ⟨some a1,false⟩ y1 c c1++
    mappedSum ⟨some a1,false⟩ y1 c))++[.CX a c]++mappedSum ⟨some a,false⟩ y cin

def drop3 (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) : Program :=
  match bits, ys, carry with
  | ⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits', y::y1::y2::y3::ys', c::c1::c2::cs =>
      d3Pre a c a1 y1++(.CX y2 c1::d3Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs))
  | bits, ys, carry => TrimSquare.drop2 bits ys carry cin

theorem drop2_split1 (a y cin c a1 y1 c1 : Wire) (b'' : MappedBit) (bits : List MappedBit)
    (y2 : Wire) (ys cs : List Wire) :
    TrimSquare.drop2 (⟨some a,false⟩::⟨some a1,false⟩::b''::bits) (y::y1::y2::ys) (c::c1::cs) cin=
      d3Pre a c a1 y1++(.CCX y1 c c1::d3Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  simp [TrimSquare.drop2,mappedAdd,mappedMajority,majority,d3Pre,d3Post,List.append_assoc]

theorem drop3_run (a a1 y y1 y2 y3 c c1 c2 cin : Wire) (b'' b3 : MappedBit) (bits : List MappedBit)
    (ys cs : List Wire) (m : List Bool) (s : State)
    (hd : [a,a1,y1,y2,c].Nodup)
    (hcopy : ((s.basis y1 ^^ s.basis a1) && (s.basis c ^^ s.basis a ^^ s.basis a1))=s.basis y2) :
    run (drop3 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s=
      run (TrimSquare.drop2 (⟨some a,false⟩::⟨some a1,false⟩::b''::b3::bits) (y::y1::y2::y3::ys) (c::c1::c2::cs) cin) m s := by
  rw [drop2_split1]
  simp only [drop3]
  have m0 : measurementCount (d3Pre a c a1 y1)=0 := rfl
  rw [run_append,run_append,m0,List.take_zero,List.drop_zero]
  symm
  apply DiagSq.ccx_as_cx
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,not_or,or_false,
    not_false_eq_true,and_true] at hd
  obtain ⟨⟨h1,h2,h3,h4⟩,⟨h5,h6,h7⟩,⟨h8,h9⟩,h10⟩ := hd
  simp only [d3Pre,run,writeBit,Function.update]
  simp [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5,
    Ne.symm h6,Ne.symm h7,Ne.symm h8,Ne.symm h9,Ne.symm h10] at hcopy ⊢
  try (rw [← hcopy])

def tsqc4 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++signedSquareTop xs dst++
    TrimSquare3.rowsClear3 xs dst pad carry

theorem drop3_shape (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : dst.length-1≤carry.length) :
    ∃ x0 x1 xt y0 y1 y2 y3 ys c c1 c2 cs b'' b3 bits,xs=x0::x1::xt ∧ dst=y0::y1::y2::y3::ys ∧
      carry.take (dst.length-1)=c::c1::c2::cs ∧
      mappedDiagonal xs=⟨some x0,false⟩::⟨some x1,false⟩::b''::b3::bits := by
  obtain ⟨x0,x1,xt,rfl⟩ : ∃ x0 x1 xt,xs=x0::x1::xt := by
    match xs, hx with
    | x0::x1::xt, _ => exact ⟨x0,x1,xt,rfl⟩
  obtain ⟨y0,y1,y2,y3,ys,rfl⟩ : ∃ y0 y1 y2 y3 ys,dst=y0::y1::y2::y3::ys := by
    match dst, hd with
    | y0::y1::y2::y3::ys, _ => exact ⟨y0,y1,y2,y3,ys,rfl⟩
  obtain ⟨c,c1,c2,cs,hct⟩ : ∃ c c1 c2 cs,carry.take ((y0::y1::y2::y3::ys).length-1)=c::c1::c2::cs := by
    have hl : 3≤(carry.take ((y0::y1::y2::y3::ys).length-1)).length := by
      rw [List.length_take]; simp only [List.length_cons] at hc ⊢; omega
    match carry.take ((y0::y1::y2::y3::ys).length-1), hl with
    | c::c1::c2::cs, _ => exact ⟨c,c1,c2,cs,rfl⟩
  obtain ⟨b'',b3,bits,e⟩ := DiagSq.diag_cons3 x0 x1 xt
  exact ⟨x0,x1,xt,y0,y1,y2,y3,ys,c,c1,c2,cs,b'',b3,bits,rfl,rfl,hct,e⟩

theorem drop3_eq (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : dst.length-1≤carry.length) :
    ∃ a a1 y y1 y2 c c1 b'' bits ys cs,y2∈dst ∧ c1∈carry ∧
      drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin=
        d3Pre a c a1 y1++(.CX y2 c1::d3Post a y cin c a1 y1 c1 b'' bits y2 ys cs) ∧
      TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin=
        d3Pre a c a1 y1++(.CCX y1 c c1::d3Post a y cin c a1 y1 c1 b'' bits y2 ys cs) := by
  obtain ⟨x0,x1,xt,y0,y1,y2,y3,ys,c,c1,c2,cs,b'',b3,bits,rfl,rfl,hct,e⟩ := drop3_shape xs dst carry cin hx hd hc
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  refine ⟨x0,x1,y0,y1,y2,c,c1,b'',b3::bits,y3::ys,c2::cs,by simp,hcm c1 (by simp),?_,?_⟩
  · rw [e,hct]; rfl
  · rw [e,hct]; exact drop2_split1 _ _ _ _ _ _ _ _ _ _ _ _

theorem drop3_counts (xs dst carry : List Wire) (cin : Wire) (hx : 2≤xs.length) (hd : 4≤dst.length)
    (hc : dst.length-1≤carry.length) :
    toffoliCount (drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)+1=
      toffoliCount (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) ∧
    measurementCount (drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin)=
      measurementCount (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin) := by
  obtain ⟨a,a1,y,y1,y2,c,c1,b'',bits,ys,cs,-,-,e2,e1⟩ := drop3_eq xs dst carry cin hx hd hc
  rw [e2,e1]
  have t1 : ∀ (u v : Wire) (p : Program),toffoliCount (.CX u v::p)=toffoliCount p := fun _ _ _ => rfl
  have t2 : ∀ (u v w : Wire) (p : Program),toffoliCount (.CCX u v w::p)=1+toffoliCount p := fun _ _ _ _ => rfl
  simp only [toffoliCount_append,measurementCount_append,t1,t2]
  exact ⟨by omega,rfl⟩

theorem drop3_slots (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (drop3 bits ys carry cin)=Challenge.gateSlots (TrimSquare.drop2 bits ys carry cin) := by
  unfold drop3
  split
  · rw [drop2_split1]
    simp [Challenge.gateSlots_append,Challenge.gateSlots,Challenge.instructionSlots]
  · rfl

theorem drop3_wires_le (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (drop3 bits ys carry cin)⊆wires (TrimSquare.drop2 bits ys carry cin) := by
  unfold drop3
  split
  · rename_i a a1 b'' b3 bits' y y1 y2 y3 ys' c c1 c2 cs
    rw [drop2_split1]
    have hy2 : y2∈wires (d3Post a y cin c a1 y1 c1 b'' (b3::bits') y2 (y3::ys') (c2::cs)) := by
      have h := DiagSq.y_mem_mappedMajority b'' y2 c1 c2
      simp only [d3Post,mappedAdd,wires_append,Finset.mem_union] at h ⊢
      tauto
    simp only [wires_append,wires,Instr.wires]
    apply Finset.union_subset_union (Finset.Subset.refl _)
    intro q hq
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hq ⊢
    rcases hq with (rfl|rfl)|h
    · exact Or.inr hy2
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr h
  · exact Finset.Subset.refl _

theorem drop3_physical (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) (hdc : ∀q∈ys,q∉carry)
    (h : GatePhysical (TrimSquare.drop2 bits ys carry cin)) :
    GatePhysical (drop3 bits ys carry cin) := by
  unfold drop3
  split
  · rename_i a a1 b'' b3 bits' y y1 y2 y3 ys' c c1 c2 cs
    rw [drop2_split1] at h
    intro i hi
    simp only [List.mem_append,List.mem_cons] at hi
    rcases hi with hi|hi|hi
    · exact h i (List.mem_append_left _ hi)
    · subst hi
      show y2≠c1
      intro e; exact hdc y2 (by simp) (by rw [e]; simp)
    · exact h i (List.mem_append_right _ (List.mem_cons_of_mem _ hi))
  · exact h

/-- `drop3` runs exactly like `drop2`, followed by any program, from a state whose destination holds
the square and whose carries are clean. -/
theorem drop3_prefix_run (cin : Wire) (xs dst pad carry : List Wire) (T : Program)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) :
    run (drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++T) records s=
      run (TrimSquare.drop2 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++T) records s := by
  obtain ⟨x0,x1,xt,y0,y1,y2,y3,ys,c,c1,c2,cs,b'',b3,bits,rfl,rfl,hct,e⟩ :=
    drop3_shape xs dst carry cin hx (by omega) hc
  have mc := (drop3_counts (x0::x1::xt) (y0::y1::y2::y3::ys) carry cin hx
    (by simp only [List.length_cons] at hd ⊢; omega) hc).2
  have hcm : ∀q∈c::c1::c2::cs,q∈carry := fun q h => List.mem_of_mem_take (hct ▸ h)
  rw [run_append,run_append (TrimSquare.drop2 _ _ _ _),mc]
  congr 1
  rw [e,hct]
  have cnt := fun w => List.nodup_iff_count.mp hn w
  have cpos := fun w (h : w∈carry) => List.count_pos_iff.mpr h
  have nd : [x0,x1,y1,y2,c].Nodup := by
    have s1 : [x0,x1].Sublist (cin::x0::x1::xt) := (List.sublist_append_left [x0,x1] xt).cons cin
    have s2 : [y1,y2].Sublist (y0::y1::y2::y3::ys) := (List.sublist_append_left [y1,y2] (y3::ys)).cons y0
    have s3 : [c].Sublist carry := List.singleton_sublist.mpr (hcm c (by simp))
    apply List.nodup_iff_count.mpr; intro w
    have h := cnt w
    have t1 := s1.count_le w; have t2 := s2.count_le w; have t3 := s3.count_le w
    have e : [x0,x1,y1,y2,c].count w=[x0,x1].count w+[y1,y2].count w+[c].count w := by
      simp only [List.count_cons,List.count_nil]; omega
    simp only [List.count_append] at h
    omega
  apply drop3_run x0 x1 y0 y1 y2 y3 c c1 c2 cin b'' b3 bits ys cs _ s nd
  have cz : s.basis c=false := (regValue_zero _ _).mp hc0 c (hcm c (by simp))
  rw [cz,Bool.false_xor]
  apply DiagSq.bits_of_sq8 y0 y1 y2 x0 x1 (y3::ys) xt s.basis ((regValue (y0::y1::y2::y3::ys) s.basis : Nat) : Int)
    (Int.ModEq.refl _)
  rw [hval]; push_cast; simp

theorem tsqc4_run (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) :
    run (tsqc4 xs dst pad carry cin) records s=run (TrimSquare3.tsqc3 xs dst pad carry cin) records s := by
  unfold tsqc4 TrimSquare3.tsqc3
  rw [List.append_assoc,List.append_assoc]
  exact drop3_prefix_run cin xs dst pad carry _ hn hx hd hc s records hval hc0

theorem tsqc4_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqc4 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqc4 xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (tsqc4 xs dst pad carry cin) records s).basis q=s.basis q := by
  rw [tsqc4_run cin xs dst pad carry hn hx hd hc s records hval hc0]
  exact TrimSquare3.tsqc3_correct cin xs dst pad carry hn hx hd hp hc s records hval hp0 hc0 hi0

theorem tsqc4_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    toffoliCount (tsqc4 xs dst pad carry cin)+1=toffoliCount (TrimSquare3.tsqc3 xs dst pad carry cin) ∧
    measurementCount (tsqc4 xs dst pad carry cin)=measurementCount (TrimSquare3.tsqc3 xs dst pad carry cin) := by
  have d := drop3_counts xs dst carry cin hx (by omega) hc
  unfold tsqc4 TrimSquare3.tsqc3
  simp only [toffoliCount_append,measurementCount_append]
  omega

theorem tsqc4_slots (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsqc4 xs dst pad carry cin)=Challenge.gateSlots (TrimSquare3.tsqc3 xs dst pad carry cin) := by
  unfold tsqc4 TrimSquare3.tsqc3
  simp only [Challenge.gateSlots_append,drop3_slots]

theorem tsqc4_wires_le (xs dst pad carry : List Wire) (cin : Wire) :
    wires (tsqc4 xs dst pad carry cin)⊆wires (TrimSquare3.tsqc3 xs dst pad carry cin) := by
  unfold tsqc4 TrimSquare3.tsqc3
  simp only [wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (drop3_wires_le _ _ _ _) (subset_refl _)) (subset_refl _)

theorem tsqc4_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup)
    (h : GatePhysical (TrimSquare3.tsqc3 xs dst pad carry cin)) :
    GatePhysical (tsqc4 xs dst pad carry cin) := by
  have hdc : ∀q∈dst,q∉carry.take (dst.length-1) := by
    intro q h1 h2
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr h1
    have b := List.count_pos_iff.mpr (List.mem_of_mem_take h2)
    simp only [List.count_cons,List.count_append] at h; omega
  unfold tsqc4 TrimSquare3.tsqc3 at *
  simp only [gatePhysical_append] at h ⊢
  exact ⟨⟨drop3_physical _ _ _ _ hdc h.1.1,h.1.2⟩,h.2⟩

/-! The same trim inside lane B's parity-adaptive clear `TrimMid.tsqcM`, which starts with the
same `drop2` in both branches. -/

def tsqcM4 (xs dst pad carry : List Wire) (cin : Wire) : Program :=
  if TrimMid.oddLeaf xs.length then
    drop3 (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin++TrimMid.clM (xs.length/2-1) xs dst pad carry
  else tsqc4 xs dst pad carry cin

theorem tsqcM4_run (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hc0 : regValue carry s.basis=0) :
    run (tsqcM4 xs dst pad carry cin) records s=run (TrimMid.tsqcM xs dst pad carry cin) records s := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · exact drop3_prefix_run cin xs dst pad carry _ hn hx hd hc s records hval hc0
  · exact tsqc4_run cin xs dst pad carry hn hx hd hc s records hval hc0

theorem tsqcM4_correct (cin : Wire) (xs dst pad carry : List Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hval : regValue dst s.basis=(regValue xs s.basis)^2)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0)
    (hi0 : s.basis cin=false) :
    (run (tsqcM4 xs dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (tsqcM4 xs dst pad carry cin) records s).basis=0 ∧
    ∀q,q∉dst → (run (tsqcM4 xs dst pad carry cin) records s).basis q=s.basis q := by
  rw [tsqcM4_run cin xs dst pad carry hn hx hd hc s records hval hc0]
  exact TrimMid.tsqcM_correct cin xs dst pad carry hn hx hd hp hc s records hval hp0 hc0 hi0

theorem tsqcM4_counts (xs dst pad carry : List Wire) (cin : Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : dst.length-1≤carry.length) :
    toffoliCount (tsqcM4 xs dst pad carry cin)+1=toffoliCount (TrimMid.tsqcM xs dst pad carry cin) ∧
    measurementCount (tsqcM4 xs dst pad carry cin)=measurementCount (TrimMid.tsqcM xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · have d := drop3_counts xs dst carry cin hx (by omega) hc
    simp only [toffoliCount_append,measurementCount_append]
    omega
  · exact tsqc4_counts xs dst pad carry cin hx hd hp hc

theorem tsqcM4_slots (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (tsqcM4 xs dst pad carry cin)=Challenge.gateSlots (TrimMid.tsqcM xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · simp only [Challenge.gateSlots_append,drop3_slots]
  · exact tsqc4_slots xs dst pad carry cin

theorem tsqcM4_wires_le (xs dst pad carry : List Wire) (cin : Wire) :
    wires (tsqcM4 xs dst pad carry cin)⊆wires (TrimMid.tsqcM xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM
  split_ifs
  · simp only [wires_append]
    exact Finset.union_subset_union (drop3_wires_le _ _ _ _) (subset_refl _)
  · exact tsqc4_wires_le xs dst pad carry cin

theorem tsqcM4_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++pad++carry).Nodup)
    (h : GatePhysical (TrimMid.tsqcM xs dst pad carry cin)) :
    GatePhysical (tsqcM4 xs dst pad carry cin) := by
  unfold tsqcM4 TrimMid.tsqcM at *
  split_ifs at h ⊢
  · have hdc : ∀q∈dst,q∉carry.take (dst.length-1) := by
      intro q h1 h2
      have h := List.nodup_iff_count.mp hn q
      have a := List.count_pos_iff.mpr h1
      have b := List.count_pos_iff.mpr (List.mem_of_mem_take h2)
      simp only [List.count_cons,List.count_append] at h; omega
    simp only [gatePhysical_append] at h ⊢
    exact ⟨drop3_physical _ _ _ _ hdc h.1,h.2⟩
  · exact tsqc4_physical xs dst pad carry cin hn h

end ECDSAAdd.Entrant.TrimSquare4
end

section

namespace ECDSAAdd.Entrant.LowZero18LowK
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
theorem sq_mid4_clear (cin : Wire) (xs dst pad carry z : List Wire)
    (hnd : (cin::xs++dst++pad++carry).Nodup) (h2 : 2≤xs.length) (hd : dst.length=2*xs.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    SqClear xs dst [] pad carry z cin (ECDSAAdd.Entrant.TrimSquare4.tsqcM4 xs dst pad carry cin) (fun _ _ => True) := by
  intro s m h0 _ hp0 hc0 _ hi0
  have r := ECDSAAdd.Entrant.TrimSquare4.tsqcM4_correct cin xs dst pad carry hnd h2 hd hp hc s m h0 hp0 hc0 hi0
  exact ⟨r.1,r.2.1,rfl,fun q h _ => r.2.2 q h⟩
end ECDSAAdd.Entrant.LowZero18LowK

end


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.LowZero18Core =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18KRegs
-- consolidated import: import ECDSAAdd.Submission.Entrant.FrontierSumCleanup1591LowK

/-! LowZero changes only the final inner addition and four outer additions.
The old raw leaves and the checked675 sum cleanup remain in use. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.LowZero18Diagonal
open Arithmetic DiagSq

def make (R : KRegs) : Program := DiagSq.makeZ R
def makeC (R : KRegs) : Program := make R++R.scl1591
abbrev clear := Z5Diagonal.clear
abbrev clearC := Z5Diagonal.clearC

theorem make_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (make R) m s).phase=s.phase ∧
    regValue R.dst (run (make R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (make R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (make R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (make R) m s).basis q=s.basis q :=
  DiagSq.makeZ_correct R w he hh hn s m hd0 hS0 hT0 hz0 hp0 hc0 hi0

variable (R : KRegs)

theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (make R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := make_correct R w he hh hn s m hd0 (KRegs.xz hX (fun q h => List.mem_append_left _ h))
    (KRegs.xz hX (fun q h => List.mem_append_right _ h)) (KRegs.xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [KRegs.invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩
theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (make R))
  let b := m.drop (measurementCount (make R))
  have r := make_correct R w he hh hn s a hd0 (KRegs.xz hX (fun q h => List.mem_append_left _ h))
    (KRegs.xz hX (fun q h => List.mem_append_right _ h)) (KRegs.xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (make R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl1591_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (KRegs.xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (makeC R) m s=run R.scl1591 b u := by
    rw [makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

abbrev diag_sq_full_clear := Z5Diagonal.diag_sq_full_clear
abbrev diag_sq_cl_clear := Z5Diagonal.diag_sq_cl_clear

attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots

theorem make_counts_diff (w : R.W) :
    toffoliCount (make R)+11+DiagSq.parR R=toffoliCount (DiagSq.make R) ∧
    measurementCount (make R)+4+DiagSq.parR R=measurementCount (DiagSq.make R) :=
  DiagSq.makeZ_counts_rel R w

theorem make_counts (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (make R)=DiagSq.cost R-11-DiagSq.parR R ∧ measurementCount (make R)=DiagSq.cost R-4-DiagSq.parR R := by
  have a := DiagSq.makeZ_counts R w he
  unfold make
  constructor <;> omega

theorem make_support_subset (w : R.W) : wires (make R)⊆wires (DiagSq.make R) := by
  have a := R.m6w_wires; have b := R.m7g_wires; have c := R.m8g_wires
  have d := seedsT_wires R
  have e := (DiagSq.corrZ2_wires R).trans (wires_of_mem (corrZ_mem R))
  have f1 := wires_of_mem (dSubZ_mem R.lo R.dlo R.carry R.cin)
  have f2 := wires_of_mem (dSubZ_mem R.hi R.dhi R.carry R.cin)
  simp only [make,DiagSq.makeZ,DiagSq.make,headBlockZ,headBlock,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union d (Finset.union_subset_union
    (Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union a b) e) f1) f2)) c

theorem makeC_support_subset (w : R.W) :
    wires (makeC R)⊆wires (FrontierSumCleanup1591Diagonal.makeC R) := by
  simp only [makeC,FrontierSumCleanup1591Diagonal.makeC,wires_append]
  exact Finset.union_subset_union (make_support_subset R w) (Finset.Subset.refl _)

theorem make_support (w : R.W) : wires (make R)⊆R.all.toFinset :=
  (make_support_subset R w).trans (DiagSq.steps_support R w).1

theorem makeC_support (w : R.W) : wires (makeC R)⊆R.all.toFinset :=
  (makeC_support_subset R w).trans (FrontierSumCleanup1591Diagonal.makeC_support R w)

theorem clear_support_subset : wires (clear R)⊆wires (FrontierSumCleanup1591Diagonal.clear R) := by
  have z8 := R.c8g_wires; have z7 := R.c7g_wires; have z6 := R.c6w_wires
  simp only [clear,Z5Diagonal.clear,FrontierSumCleanup1591Diagonal.clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact z8 | exact z7 | exact z6 | exact wires_of_mem (dAddZ_mem _ _ _ _) |
    exact (dAddZ2_wires_le _ _ _ _).trans (wires_of_mem (dAddZ_mem _ _ _ _)) |
    exact wires_of_mem (corrBackZ_mem R) | exact rawClearT_wires_sub _ _ _ _ | exact Finset.Subset.refl _

theorem clearC_support_subset : wires (clearC R)⊆wires (FrontierSumCleanup1591Diagonal.clearC R) := by
  simp only [clearC,Z5Diagonal.clearC,FrontierSumCleanup1591Diagonal.clearC,wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) (clear_support_subset R)

theorem clear_slots_old : Challenge.gateSlots (clear R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.clear R) := by
  have z8 := R.c8g_slots; have z7 := R.c7g_slots; have z6 := R.c6w_slots
  have rS := DiagSq.rawClearT_slots_le R.S R.T R.pad R.carry
  have rH := DiagSq.rawClearT_slots_le R.hi R.dhi R.pad R.carry
  have rL := DiagSq.rawClearT_slots_le R.lo R.dlo R.pad R.carry
  have cb := DiagSq.corrBackZ_slots R
  have da1 := DiagSq.dAddZ_slots R.lo R.dlo R.carry R.cin
  have da2 := DiagSq.dAddZ_slots R.hi R.dhi R.carry R.cin
  have db1 := DiagSq.dAddZ2_slots_eq R.lo R.dlo R.carry R.cin
  have db2 := DiagSq.dAddZ2_slots_eq R.hi R.dhi R.carry R.cin
  simp only [clear,Z5Diagonal.clear,FrontierSumCleanup1591Diagonal.clear,Challenge.gateSlots_append] at *
  omega

theorem clearC_slots_old : Challenge.gateSlots (clearC R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.clearC R) := by
  have h := clear_slots_old R
  simp only [clear,clearC,Z5Diagonal.clearC,FrontierSumCleanup1591Diagonal.clearC,Challenge.gateSlots_append] at *
  omega

abbrev clear_counts := Z5Diagonal.clear_counts
abbrev clear_support := Z5Diagonal.clear_support
abbrev clearC_support := Z5Diagonal.clearC_support
abbrev clear_physical := Z5Diagonal.clear_physical
abbrev clearC_physical := Z5Diagonal.clearC_physical
abbrev clear_slots_le := Z5Diagonal.clear_slots_le
abbrev clearC_slots_le := Z5Diagonal.clearC_slots_le

theorem steps_support (w : R.W) :
    wires (make R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset :=
  ⟨make_support R w,clear_support R w⟩

theorem make_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical (make R) :=
  DiagSq.makeZ_physical R w hn

theorem makeC_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical (makeC R) :=
  (gatePhysical_append _ _).mpr ⟨make_physical R w hn,R.scl1591_physical w hn⟩

theorem steps_physical (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (make R) ∧ GatePhysical (clear R) :=
  ⟨make_physical R w hn,clear_physical R w hn⟩

theorem make_slots_le (w : R.W) :
    Challenge.gateSlots (make R)≤Challenge.gateSlots (DiagSq.make R) :=
  DiagSq.makeZ_slots R

theorem makeC_slots_old (w : R.W) :
    Challenge.gateSlots (makeC R)≤Challenge.gateSlots (FrontierSumCleanup1591Diagonal.makeC R) := by
  have z := make_slots_le R w
  simp only [makeC,FrontierSumCleanup1591Diagonal.makeC,Challenge.gateSlots_append]
  omega

theorem makeC_slots_le (w : R.W) :
    Challenge.gateSlots (makeC R)≤Challenge.gateSlots (DiagSq.makeC R) :=
  (makeC_slots_old R w).trans (FrontierSumCleanup1591Diagonal.makeC_slots_le R)

theorem tiny_slots (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (make R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 :=
  ⟨(make_slots_le R w).trans (DiagSq.tiny_slots R w he hh).1,
    (Z5Diagonal.tiny_slots R w he hh).2⟩

end ECDSAAdd.Entrant.LowZero18Diagonal

namespace ECDSAAdd.Entrant.ConstCarry
open ECDSAAdd ECDSAAdd.Arithmetic

/-- `addInPlace` whose second majority is the single CNOT `c₀ → c₁`. -/
def addInPlace2 : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, cin =>
      majority a0 b0 cin c0 ++ ([.CX c0 c1] ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++ eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => addInPlace x y c cin

/-- `subInPlace` with `addInPlace2`. -/
def subInPlace2 (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addInPlace2 x y carry cin ++ notRegister y

theorem addInPlace_shape3 (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin =
      majority a0 b0 cin c0 ++ (majority a1 b1 c0 c1 ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++ eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0] := by
  simp only [addInPlace]

theorem run_pre (p q : Program) (hp : measurementCount p = 0) (m : List Bool) (s : State) :
    run (p ++ q) m s = run q m (run p [] s) := by
  rw [run_append, hp]; simp

theorem majority_mc (a b c d : Wire) : measurementCount (majority a b c d) = 0 := by
  simp [majority, measurementCount]

/-- When the first two inputs differ the majority is a copy of the carry-in. -/
theorem majority_ne (a b cin carry : Wire) (hnd : [a, b, cin, carry].Nodup) (s : State)
    (h : s.basis a ≠ s.basis b) :
    run (majority a b cin carry) [] s = run [.CX cin carry] [] s := by
  rw [majority_correct a b cin carry hnd]
  simp only [run]
  congr 2
  cases ha : s.basis a <;> cases hb : s.basis b <;> cases s.basis cin <;> simp_all [carryBit]

theorem notRegister_mc (r : List Wire) : measurementCount (notRegister r) = 0 := by
  induction r with
  | nil => rfl
  | cons w r ih => simpa [notRegister, measurementCount] using ih

theorem addInPlace2_run (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (h0 : [a0, b0, cin, c0].Nodup) (h1 : [a1, b1, c0, c1].Nodup) (ha : a1 ≠ c0) (hb : b1 ≠ c0)
    (s : State) (m : List Bool) (h : s.basis a1 ≠ s.basis b1) :
    run (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s =
      run (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, List.append_assoc]
  rw [run_pre _ _ (majority_mc _ _ _ _), run_pre _ _ (majority_mc _ _ _ _),
    run_pre [.CX c0 c1] _ (by simp [measurementCount]), run_pre _ _ (majority_mc _ _ _ _)]
  congr 1
  have t := majority_correct a0 b0 cin c0 h0 s []
  have e := majority_ne a1 b1 c0 c1 h1 (run (majority a0 b0 cin c0) [] s) (by
    rw [t]; simpa [writeBit, Function.update, ha, hb] using h)
  exact e.symm

theorem subInPlace2_run (x y carry : List Wire) (cin : Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) (s : State) (m : List Bool)
    (hb : s.basis (y.getD 1 0) = s.basis (x.getD 1 0)) :
    run (subInPlace2 x y carry cin) m s = run (subInPlace x y carry cin) m s := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have hyn : (b0 :: b1 :: b2 :: bs).Nodup :=
      (List.nodup_cons.mp hn).2.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
    simp only [List.Nodup, List.cons_append, List.pairwise_cons, List.pairwise_append, List.mem_cons,
      List.mem_append, List.append_assoc, forall_eq, or_imp, forall_and] at hn
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hb
    have mz : measurementCount (notRegister (b0 :: b1 :: b2 :: bs)) = 0 := notRegister_mc _
    have mc2 : measurementCount (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) =
        measurementCount (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
      rw [addInPlace_shape3]; simp [addInPlace2, measurementCount_append, majority_mc, measurementCount]
    simp only [subInPlace2, subInPlace, List.append_assoc]
    rw [run_pre _ _ mz, run_pre _ _ mz, run_append, run_append (addInPlace _ _ _ _), mc2]
    congr 1
    rw [notRegister_correct _ hyn]
    apply addInPlace2_run
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · tauto
    · tauto
    · have a1y : a1 ∉ b0 :: b1 :: b2 :: bs := by simp only [List.mem_cons, not_or]; tauto
      have b1y : b1 ∈ b0 :: b1 :: b2 :: bs := by simp
      clear hn
      show (if a1 ∈ b0 :: b1 :: b2 :: bs then !s.basis a1 else s.basis a1) ≠
        (if b1 ∈ b0 :: b1 :: b2 :: bs then !s.basis b1 else s.basis b1)
      rw [if_neg a1y, if_pos b1y, hb]
      cases s.basis a1 <;> decide

theorem mem_addInPlace2 (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) (i : Instr)
    (h : i ∈ addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) :
    i ∈ addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin ∨ i = .CX c0 c1 := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, List.mem_append, List.mem_cons, List.not_mem_nil] at h ⊢
  tauto

theorem addInPlace2_counts (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    toffoliCount (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin)+1 =
      toffoliCount (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) ∧
    measurementCount (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) =
      measurementCount (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, toffoliCount_append, measurementCount_append]
  simp [majority, toffoliCount, measurementCount]
  omega

theorem addInPlace2_wires (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    wires (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) ⊆
      wires (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, wires_append]
  have : wires [Instr.CX c0 c1] ⊆ wires (majority a1 b1 c0 c1) := by
    intro w hw
    simp [wires, Instr.wires, majority] at hw ⊢
    tauto
  intro w hw
  simp only [Finset.mem_union] at hw ⊢
  have := @this w
  tauto

theorem addInPlace2_slots (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) :
    Challenge.gateSlots (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) ≤
      Challenge.gateSlots (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  rw [addInPlace_shape3]
  simp only [addInPlace2, Challenge.gateSlots_append]
  simp [majority, Challenge.gateSlots, Challenge.instructionSlots]

theorem addInPlace2_physical (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hp : GatePhysical (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin))
    (hc : c0 ≠ c1) :
    GatePhysical (addInPlace2 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) := by
  intro i hi
  rcases mem_addInPlace2 _ _ _ _ _ _ _ _ _ _ _ _ i hi with h | h
  · exact hp i h
  · subst h; exact hc

/-- Bit 1 of a register as a function of its value. -/
theorem bit1_value (r : List Wire) (st : BasisState) (h : 2 ≤ r.length) :
    st (r.getD 1 0) = decide (regValue r st / 2 % 2 = 1) := by
  match r, h with
  | w0 :: w1 :: ws, _ =>
    simp only [List.getD_cons_succ, List.getD_cons_zero, regValue, List.foldr_cons]
    by_cases h0 : st w0 <;> by_cases h1 : st w1 <;> simp [h0, h1] <;> omega

/-- Bit 1 of a square is clear. -/
theorem sq_bit1 (n : Nat) : n^2 / 2 % 2 = 0 := by
  have h : n^2 % 4 = (n % 4)^2 % 4 := Nat.pow_mod n 2 4
  have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e : n^2 / 2 % 2 = n^2 % 4 / 2 := by omega
  rw [e, h]
  interval_cases (n % 4) <;> norm_num

theorem subInPlace2_counts (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (subInPlace2 x y carry cin)+1=toffoliCount (subInPlace x y carry cin) ∧
    measurementCount (subInPlace2 x y carry cin)=measurementCount (subInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have e := addInPlace2_counts a0 a1 a2 b0 b1 b2 c0 c1 cin as bs cs
    simp only [subInPlace2, subInPlace, toffoliCount_append, measurementCount_append]
    omega

theorem subInPlace2_wires (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    wires (subInPlace2 x y carry cin)⊆wires (subInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have e := addInPlace2_wires a0 a1 a2 b0 b1 b2 c0 c1 cin as bs cs
    simp only [subInPlace2, subInPlace, wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) e) (Finset.Subset.refl _)

theorem subInPlace2_slots (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    Challenge.gateSlots (subInPlace2 x y carry cin)≤Challenge.gateSlots (subInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have e := addInPlace2_slots a0 a1 a2 b0 b1 b2 c0 c1 cin as bs cs
    simp only [subInPlace2, subInPlace, Challenge.gateSlots_append]
    omega

theorem subInPlace2_physical (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) (hnd : carry.Nodup)
    (hp : GatePhysical (subInPlace x y carry cin)) : GatePhysical (subInPlace2 x y carry cin) := by
  match x, y, carry, hx, hy, hc, hnd with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _, hnd =>
    simp only [subInPlace2, subInPlace, gatePhysical_append] at hp ⊢
    refine ⟨⟨hp.1.1, addInPlace2_physical _ _ _ _ _ _ _ _ _ _ _ _ hp.1.2 ?_⟩, hp.2⟩
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    exact hnd.1.1

end ECDSAAdd.Entrant.ConstCarry

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic
variable (R : KRegs)

/-- `m6` with the second majority of its carry chain reduced to one CNOT. -/
def m6c : Program := ConstCarry.subInPlace2 (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m6c_lens (w : R.W) : 3 ≤ (R.dlo++R.zA).length ∧ 3 ≤ R.T.length ∧ 2 ≤ (R.carry.take (R.T.length-1)).length ∧
    2 ≤ R.dlo.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  simp only [List.length_append, List.length_take]
  omega

theorem m6c_counts (w : R.W) : toffoliCount R.m6c+1=toffoliCount R.m6 ∧
    measurementCount R.m6c=measurementCount R.m6 := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_counts _ _ _ _ l.1 l.2.1 l.2.2.1

theorem m6c_wires (w : R.W) : wires R.m6c⊆wires R.m6 := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_wires _ _ _ _ l.1 l.2.1 l.2.2.1

theorem m6c_slots (w : R.W) : Challenge.gateSlots R.m6c≤Challenge.gateSlots R.m6 := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_slots _ _ _ _ l.1 l.2.1 l.2.2.1

theorem m6c_physical (w : R.W) (hc : (R.carry.take (R.T.length-1)).Nodup) (hp : GatePhysical R.m6) :
    GatePhysical R.m6c := by
  have l := R.m6c_lens w
  exact ConstCarry.subInPlace2_physical _ _ _ _ l.1 l.2.1 l.2.2.1 hc hp

theorem carry_take_nodup (hn : R.all.Nodup) (n : Nat) : (R.carry.take n).Nodup :=
  hn.sublist ((List.take_sublist _ _).trans ((List.sublist_append_right _ _).trans (List.sublist_cons_self _ _)))

/-- With bit 1 of `T` equal to bit 1 of the diagonal, `m6c` runs exactly like `m6`. -/
theorem m6c_run (w : R.W) (hn : (R.cin::((R.dlo++R.zA)++R.T++R.carry.take (R.T.length-1))).Nodup)
    (s : State) (m : List Bool) (hb : s.basis (R.T.getD 1 0)=s.basis (R.dlo.getD 1 0)) :
    run R.m6c m s=run R.m6 m s := by
  have l := R.m6c_lens w
  apply ConstCarry.subInPlace2_run _ _ _ _ hn l.1 l.2.1 l.2.2.1
  rw [hb, List.getD_append _ _ _ _ (by omega)]

/-- Squares: bit 1 of `T` and of the low diagonal are both clear. -/
theorem m6c_bits (w : R.W) (st : BasisState) (A B : Nat) (hT : regValue R.T st=A^2)
    (hd : regValue R.dlo st=B^2) : st (R.T.getD 1 0)=st (R.dlo.getD 1 0) := by
  have l := R.m6c_lens w
  rw [ConstCarry.bit1_value R.T st (by omega), ConstCarry.bit1_value R.dlo st l.2.2.2, hT, hd,
    ConstCarry.sq_bit1, ConstCarry.sq_bit1]

end ECDSAAdd.Entrant.KRegs

namespace ECDSAAdd.Entrant.ConstCarry
open ECDSAAdd ECDSAAdd.Arithmetic

/-- `addInPlace` whose second majority is the single CNOT `b₁ → c₁`. -/
def addInPlace3 : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, cin =>
      majority a0 b0 cin c0 ++ ([.CX b1 c1] ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++ eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => addInPlace x y c cin

/-- When the second and third inputs agree the majority is a copy of the second. -/
theorem majority_eq (a b cin carry : Wire) (hnd : [a, b, cin, carry].Nodup) (s : State)
    (h : s.basis b = s.basis cin) :
    run (majority a b cin carry) [] s = run [.CX b carry] [] s := by
  rw [majority_correct a b cin carry hnd]
  simp only [run]
  congr 2
  rw [← h]
  cases s.basis a <;> cases s.basis b <;> simp [carryBit]

theorem addInPlace3_run (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (h0 : [a0, b0, cin, c0].Nodup) (h1 : [a1, b1, c0, c1].Nodup) (hb : b1 ≠ c0)
    (s : State) (m : List Bool) (hc : s.basis c0 = false)
    (h : s.basis b1 = carryBit (s.basis a0) (s.basis b0) (s.basis cin)) :
    run (addInPlace3 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s =
      run (addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) m s := by
  rw [addInPlace_shape3]
  simp only [addInPlace3, List.append_assoc]
  rw [run_pre _ _ (majority_mc _ _ _ _), run_pre _ _ (majority_mc _ _ _ _),
    run_pre [.CX b1 c1] _ (by simp [measurementCount]), run_pre _ _ (majority_mc _ _ _ _)]
  congr 1
  have t := majority_correct a0 b0 cin c0 h0 s []
  have e := majority_eq a1 b1 c0 c1 h1 (run (majority a0 b0 cin c0) [] s) (by
    rw [t]; simp [writeBit, Function.update, hb, hc, h])
  exact e.symm

theorem mem_addInPlace3 (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire) (i : Instr)
    (h : i ∈ addInPlace3 (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin) :
    i ∈ addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin ∨ i = .CX b1 c1 := by
  rw [addInPlace_shape3]
  simp only [addInPlace3, List.mem_append, List.mem_cons, List.not_mem_nil] at h ⊢
  tauto

/-- Same run as `addInPlace` when bit 1 of `y` equals the bit-0 carry, with clean carries. -/
theorem addInPlace3_run_list (x y carry : List Wire) (cin : Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) (s : State) (m : List Bool)
    (hc0 : s.basis (carry.getD 0 0) = false)
    (hb : s.basis (y.getD 1 0) = carryBit (s.basis (x.getD 0 0)) (s.basis (y.getD 0 0)) (s.basis cin)) :
    run (addInPlace3 x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    simp only [List.Nodup, List.cons_append, List.pairwise_cons, List.pairwise_append, List.mem_cons,
      List.mem_append, List.append_assoc, forall_eq, or_imp, forall_and] at hn
    simp only [List.getD_cons_succ, List.getD_cons_zero] at hb hc0
    apply addInPlace3_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hb
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or]; tauto
    · tauto

theorem addInPlace3_counts (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (addInPlace3 x y carry cin)+1=toffoliCount (addInPlace x y carry cin) ∧
    measurementCount (addInPlace3 x y carry cin)=measurementCount (addInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    rw [addInPlace_shape3]
    simp only [addInPlace3, toffoliCount_append, measurementCount_append]
    simp [majority, toffoliCount, measurementCount]
    omega

theorem addInPlace3_wires (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    wires (addInPlace3 x y carry cin)⊆wires (addInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    rw [addInPlace_shape3]
    simp only [addInPlace3, wires_append]
    have : wires [Instr.CX b1 c1] ⊆ wires (majority a1 b1 c0 c1) := by
      intro w hw
      simp [wires, Instr.wires, majority] at hw ⊢
      tauto
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    have := @this w
    tauto

theorem addInPlace3_slots (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    Challenge.gateSlots (addInPlace3 x y carry cin)≤Challenge.gateSlots (addInPlace x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    rw [addInPlace_shape3]
    simp only [addInPlace3, Challenge.gateSlots_append]
    simp [majority, Challenge.gateSlots, Challenge.instructionSlots]

theorem addInPlace3_physical (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length)
    (hp : GatePhysical (addInPlace x y carry cin)) : GatePhysical (addInPlace3 x y carry cin) := by
  match x, y, carry, hx, hy, hc with
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, _, _, _ =>
    have hm : Instr.CCX b1 c0 c1 ∈ addInPlace (a0 :: a1 :: a2 :: as) (b0 :: b1 :: b2 :: bs) (c0 :: c1 :: cs) cin := by
      rw [addInPlace_shape3]; simp [majority]
    have pc := hp _ hm
    intro i hi
    rcases mem_addInPlace3 _ _ _ _ _ _ _ _ _ _ _ _ i hi with h | h
    · exact hp i h
    · subst h; exact pc.1

/-- Bit 0 of a register as a function of its value. -/
theorem bit0_value (r : List Wire) (st : BasisState) (h : 1 ≤ r.length) :
    st (r.getD 0 0) = decide (regValue r st % 2 = 1) := by
  match r, h with
  | w0 :: ws, _ =>
    simp only [List.getD_cons_zero, regValue, List.foldr_cons]
    by_cases h0 : st w0 <;> simp [h0]

theorem getD0_mem (l : List Wire) (h : 1 ≤ l.length) : l.getD 0 0 ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs => simp

theorem cross_bits (A B : Nat) :
    (2*A*B+B^2) / 2 % 2 = 1 ↔ (A^2 % 2 = 1 ∧ (2*A*B+B^2) % 2 = 1) := by
  have h1 : (2*A*B+B^2) % 4 = (2*(A%4)*(B%4)+(B%4)^2) % 4 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have h2 : A^2 % 2 = (A%4)^2 % 2 := by
    rw [Nat.pow_mod]; conv_rhs => rw [Nat.pow_mod]
    congr 2; omega
  have e1 : (2*A*B+B^2) / 2 % 2 = (2*A*B+B^2) % 4 / 2 := by omega
  have e2 : (2*A*B+B^2) % 2 = (2*A*B+B^2) % 4 % 2 := by omega
  rw [e1, e2, h1, h2]
  have : A % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have : B % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (A % 4) <;> interval_cases (B % 4) <;> norm_num

end ECDSAAdd.Entrant.ConstCarry

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic
variable (R : KRegs)

/-- `c6` with the second majority of its carry chain reduced to one CNOT. -/
def c6c : Program := ConstCarry.addInPlace3 (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c6c_counts (w : R.W) : toffoliCount R.c6c+1=toffoliCount R.c6 ∧
    measurementCount R.c6c=measurementCount R.c6 := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_counts _ _ _ _ l.1 l.2.1 l.2.2.1

theorem c6c_wires (w : R.W) : wires R.c6c⊆wires R.c6 := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_wires _ _ _ _ l.1 l.2.1 l.2.2.1

theorem c6c_slots (w : R.W) : Challenge.gateSlots R.c6c≤Challenge.gateSlots R.c6 := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_slots _ _ _ _ l.1 l.2.1 l.2.2.1

theorem c6c_physical (w : R.W) (hp : GatePhysical R.c6) : GatePhysical R.c6c := by
  have l := R.m6c_lens w
  exact ConstCarry.addInPlace3_physical _ _ _ _ l.1 l.2.1 l.2.2.1 hp

/-- With bit 1 of `T` equal to the bit-0 carry of `dlo + T`, `c6c` runs exactly like `c6`. -/
theorem c6c_run (w : R.W) (hn : (R.cin::((R.dlo++R.zA)++R.T++R.carry.take (R.T.length-1))).Nodup)
    (s : State) (m : List Bool) (hc0 : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hi : s.basis R.cin=false)
    (hb : s.basis (R.T.getD 1 0)=(s.basis (R.dlo.getD 0 0) && s.basis (R.T.getD 0 0))) :
    run R.c6c m s=run R.c6 m s := by
  have l := R.m6c_lens w
  apply ConstCarry.addInPlace3_run_list _ _ _ _ hn l.1 l.2.1 l.2.2.1
  · exact hc0 _ (ConstCarry.getD0_mem _ (by omega))
  · rw [hb, List.getD_append _ _ _ _ (by omega), hi]
    cases s.basis (R.dlo.getD 0 0) <;> cases s.basis (R.T.getD 0 0) <;> rfl

theorem c6c_bits (w : R.W) (st : BasisState) (A B : Nat) (hT : regValue R.T st=2*A*B+B^2)
    (hd : regValue R.dlo st=A^2) : st (R.T.getD 1 0)=(st (R.dlo.getD 0 0) && st (R.T.getD 0 0)) := by
  have l := R.m6c_lens w
  rw [ConstCarry.bit1_value R.T st (by omega), ConstCarry.bit0_value R.T st (by omega),
    ConstCarry.bit0_value R.dlo st (by omega), hT, hd]
  have := ConstCarry.cross_bits A B
  by_cases h1 : A^2 % 2 = 1 <;> by_cases h2 : (2*A*B+B^2) % 2 = 1 <;> simp_all

end ECDSAAdd.Entrant.KRegs

section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic

/-! In the 129-bit leaf (`2h+1 ≤ n`), `T = 2ab+b² < 2^(|T|-1)` before `T −= b²` and after
`T += b²`, so the borrow/carry into the top bit of `T` is always zero and both adders can run
on the low `|T|-1` bits (one majority/erase pair fewer each). -/

theorem addHeadI_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+3)
    (hy : y.length=n+3) (hc : c.length=n+2) :
    (addHeadI (x.take (n+2)) (y.take (n+2)) (c.take (n+1)) cin).Sublist (addHeadI x y c cin) := by
  match x, y, c, hx, hy, hc with
  | a::a'::x', b::b'::y', c0::c', hx, hy, hc =>
    have r := add_take_sublist n (a'::x') (b'::y') c' c0 (by simpa using hx) (by simpa using hy)
      (by simpa using hc)
    simp only [List.take_succ_cons] at r ⊢
    simp only [addHeadI]
    exact (List.Sublist.refl _).append ((r.append (List.Sublist.refl _)).append (List.Sublist.refl _))

theorem addLowNC1_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+4)
    (hy : y.length=n+4) (hc : c.length=n+3) :
    (addLowNC1 (x.take (n+3)) (y.take (n+3)) (c.take (n+2)) cin).Sublist (addLowNC1 x y c cin) := by
  match x, y, c, hx, hy, hc with
  | a::x', b::y', c0::c', hx, hy, hc =>
    have r := addHeadI_take_sublist n x' y' c' cin (by simpa using hx) (by simpa using hy)
      (by simpa using hc)
    simp only [addLowNC1,List.take_succ_cons,List.tail_cons,List.headD_cons]
    exact (r.append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem subLowNC1_take_sublist (n : Nat) (x y c : List Wire) (cin : Wire) (hx : x.length=n+4)
    (hy : y.length=n+4) (hc : c.length=n+3) :
    (subLowNC1 (x.take (n+3)) (y.take (n+3)) (c.take (n+2)) cin).Sublist (subLowNC1 x y c cin) := by
  simp only [subLowNC1]
  exact ((notRegister_take_sublist y (n+3)).append (addLowNC1_take_sublist n x y c cin hx hy hc)).append
    (notRegister_take_sublist y (n+3))

theorem take_tail_headD (l : List Wire) (k : Nat) (hk : 2≤k) : (l.take k).tail.headD 0=l.tail.headD 0 := by
  rcases l with _|⟨a,l⟩
  · simp
  · obtain ⟨j,rfl⟩ : ∃j,k=j+1 := ⟨k-1,by omega⟩
    simp only [List.take_succ_cons,List.tail_cons]
    exact take_headD l j (by omega)

theorem trim_pow (n h : Nat) : 2^(2*(n-h+1)-1)=2*2^(n-h)*2^(n-h) := by
  rw [show 2*(n-h+1)-1=((n-h)+(n-h))+1 by omega,pow_succ,pow_add]; ring

theorem trim_bound (n h a b : Nat) (hc : 2*h+1≤n) (ha : a<2^h) (hb : b<2^(n-h)) :
    2*a*b+b^2<2^(2*(n-h+1)-1) := by
  rw [trim_pow]
  have hB : 2*2^h≤2^(n-h) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2^(n-h)=B at *
  have h2a : 2*a+1≤B := by omega
  have h1 := Nat.mul_le_mul_right b h2a
  have h2 : b*b≤b*B := Nat.mul_le_mul_left b hb.le
  have h3 : b*B<B*B := Nat.mul_lt_mul_of_pos_right hb (by omega)
  nlinarith

theorem sq_trim_bound (n h b : Nat) (hb : b<2^(n-h)) : b^2<2^(2*(n-h+1)-1) := by
  rw [trim_pow]
  generalize 2^(n-h)=B at *
  have h2 : b*b≤b*B := Nat.mul_le_mul_left b hb.le
  have h3 : b*B<B*B := Nat.mul_lt_mul_of_pos_right hb (by omega)
  nlinarith

variable (R : KRegs)

def trimOK : Prop := 2*R.h+1≤R.bank.length
instance : Decidable R.trimOK := by unfold trimOK; infer_instance

def topOK : Prop := R.trimOK ∧ (R.dhi++R.zB).length=R.T.length ∧
  (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 4≤R.T.length
instance : Decidable R.topOK := by unfold topOK; infer_instance

/-- `m7y` on the low `|T|-1` bits when the top bit of `T` is provably clear. -/
def m7t : Program := if R.topOK then
  subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.m7y
/-- `c7y` on the low `|T|-1` bits when the top bit of `T` is provably clear. -/
def c7t : Program := if R.topOK then
  addLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.c7y

theorem topOK_of (w : R.W) (hc : R.trimOK) : R.topOK := by
  have l := R.t_lensg w
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
  exact ⟨hc,l.1,l.2.1,by omega⟩

theorem m7t_sub : R.m7t.Sublist R.m7y := by
  unfold m7t
  split_ifs with h
  · obtain ⟨-,h1,h2,h3⟩ := h
    have e : R.m7y=subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨h1,h2,by omega⟩
    rw [e]
    have e1 : R.T.length-1=(R.T.length-4)+3 := by omega
    have e2 : R.T.length-2=(R.T.length-4)+2 := by omega
    rw [e1,e2]
    exact subLowNC1_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _

theorem c7t_sub : R.c7t.Sublist R.c7y := by
  unfold c7t
  split_ifs with h
  · obtain ⟨-,h1,h2,h3⟩ := h
    have e : R.c7y=addLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨h1,h2,by omega⟩
    rw [e]
    have e1 : R.T.length-1=(R.T.length-4)+3 := by omega
    have e2 : R.T.length-2=(R.T.length-4)+2 := by omega
    rw [e1,e2]
    exact addLowNC1_take_sublist _ _ _ _ _ (by omega) (by omega)
      (by rw [List.length_take]; simp only [List.length_take] at h2; omega)
  · exact List.Sublist.refl _

theorem m7t_wires : wires R.m7t⊆wires R.m7 :=
  (DiagSq.wires_of_mem (fun _ h => (R.m7t_sub).subset h)).trans R.m7y_wires
theorem c7t_wires : wires R.c7t⊆wires R.c7 :=
  (DiagSq.wires_of_mem (fun _ h => (R.c7t_sub).subset h)).trans R.c7y_wires
theorem m7t_physical (hn : R.all.Nodup) : GatePhysical R.m7t :=
  fun i h => R.m7y_physical hn i ((R.m7t_sub).subset h)
theorem c7t_physical (hn : R.all.Nodup) : GatePhysical R.c7t :=
  fun i h => R.c7y_physical hn i ((R.c7t_sub).subset h)
theorem m7t_slots : Challenge.gateSlots R.m7t≤Challenge.gateSlots R.m7 :=
  (slots_sublist R.m7t_sub).trans R.m7y_slots
theorem c7t_slots : Challenge.gateSlots R.c7t≤Challenge.gateSlots R.c7 :=
  (slots_sublist R.c7t_sub).trans R.c7y_slots

theorem m7t_counts (w : R.W) : toffoliCount R.m7t+(if R.trimOK then 1 else 0)+2=toffoliCount R.m7 ∧
    measurementCount R.m7t+(if R.trimOK then 1 else 0)=measurementCount R.m7 := by
  have y := R.m7y_counts w
  have l := R.t_lensg w
  by_cases hc : R.trimOK
  · rw [if_pos hc]
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
    have em : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
    have ey : R.m7y=subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨l.1,l.2.1,l.2.2.1⟩
    have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
      simp only [List.length_take]; omega
    have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
      have := l.2.1; simp only [List.length_take] at this ⊢; omega
    have a := subLowNC1_counts ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
      (by rw [lx]; simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
      (by simp only [List.length_take] at lc ⊢; omega)
    have b := LowZero.subLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
    have c := subInPlace_counts _ _ _ R.cin lx lc
    have a' := subLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
      (by rw [l.1]; omega) (by omega) (by have := l.2.1; omega)
    have b' := LowZero.subLowNC_counts _ _ _ R.cin l.1 l.2.1 l.2.2.1
    have c' := subInPlace_counts _ _ _ R.cin l.1 l.2.1
    have ma : measurementCount (subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin)=
        measurementCount (LowZero.subLowNC ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) := by
      simp only [subLowNC1,LowZero.subLowNC,measurementCount_append,addLowNC1_mc]
    have ma' : measurementCount (subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin)=
        measurementCount (LowZero.subLowNC (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin) := by
      simp only [subLowNC1,LowZero.subLowNC,measurementCount_append,addLowNC1_mc]
    rw [em]; rw [ey] at y
    simp only [List.length_take] at c
    constructor <;> omega
  · rw [if_neg hc]
    have em : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [em]; exact ⟨by omega,by omega⟩

theorem c7t_counts (w : R.W) : toffoliCount R.c7t+(if R.trimOK then 1 else 0)+2=toffoliCount R.c7 ∧
    measurementCount R.c7t+(if R.trimOK then 1 else 0)=measurementCount R.c7 := by
  have y := R.c7y_counts w
  have l := R.t_lensg w
  by_cases hc : R.trimOK
  · rw [if_pos hc]
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
    have em : R.c7t=addLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
    have ey : R.c7y=addLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
      if_pos ⟨l.1,l.2.1,l.2.2.1⟩
    have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
      simp only [List.length_take]; omega
    have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
      have := l.2.1; simp only [List.length_take] at this ⊢; omega
    have a := addLowNC1_counts ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
      (by rw [lx]; simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
      (by simp only [List.length_take] at lc ⊢; omega)
    have b := LowZero.addLowNC_counts _ _ _ R.cin lx lc (by simp only [List.length_take]; omega)
    have c := addInPlace_counts _ _ _ R.cin lx lc
    have a' := addLowNC1_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
      (by rw [l.1]; omega) (by omega) (by have := l.2.1; omega)
    have b' := LowZero.addLowNC_counts _ _ _ R.cin l.1 l.2.1 l.2.2.1
    have c' := addInPlace_counts _ _ _ R.cin l.1 l.2.1
    have ma := addLowNC1_mc ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
    have ma' := addLowNC1_mc (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    rw [em]; rw [ey] at y
    simp only [List.length_take] at c
    constructor <;> omega
  · rw [if_neg hc]
    have em : R.c7t=R.c7y := if_neg (fun h => hc h.1)
    rw [em]; exact ⟨by omega,by omega⟩

theorem top_nodup (hn : R.all.Nodup) :
    (R.cin::(((R.dhi++R.zB).take (R.T.length-1))++(R.T.take (R.T.length-1))++
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)))).Nodup := by
  have full : (R.cin::((R.dhi++R.zB)++R.T++(R.carry.take (R.T.length-1)))).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  exact full.sublist ((((List.take_sublist _ _).append (List.take_sublist _ _)).append
    (List.take_sublist _ _)).cons₂ _)

theorem m7t_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hA : R.trimOK → regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1))
    (hb : R.trimOK → regValue (R.dhi++R.zB) s.basis≤regValue R.T s.basis%2^(R.T.length-1)) :
    (run R.m7t m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.m7t m s).basis q=s.basis q) ∧
    regValue R.T (run R.m7t m s).basis=(regValue R.T s.basis+2^R.T.length-regValue (R.dhi++R.zB) s.basis-(s.basis R.cin).toNat)%2^R.T.length := by
  by_cases hc : R.trimOK
  swap
  · have em : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [em]; exact R.m7y_correct w hn s m hcl hnc hi h1
  have hA := hA hc
  have hb := hb hc
  have top := R.topOK_of w hc
  obtain ⟨-,h1l,h2,h3⟩ := top
  have em : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
  have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have e2 := subLowNC1_run ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin m s (R.top_nodup hn) hi
      (by rw [take_tail_headD _ _ (by omega)]; exact h1) (by simp only [List.length_take]; omega)
  have r := LowZero.subLowNC_correct _ _ _ R.cin (R.top_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em,e2]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.subLowNC ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dhi++R.zB).take (R.T.length-1)) s.basis=regValue (R.dhi++R.zB) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    exact List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue R.T s.basis%P-regValue (R.dhi++R.zB) s.basis := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.sub_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    rw [show regValue R.T s.basis%P+P-regValue (R.dhi++R.zB) s.basis=
      (regValue R.T s.basis%P-regValue (R.dhi++R.zB) s.basis)+P by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := Nat.mod_lt (regValue R.T s.basis) Ppos; omega)]
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.sub_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dhi++R.zB) s.basis=AV at *
  have dq : P*D=TV-M := by omega
  rw [dq,show TV+2*P-AV=(TV-AV)+2*P by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  omega

theorem c7t_correct (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hA : R.trimOK → regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1))
    (hb : R.trimOK → regValue R.T s.basis%2^(R.T.length-1)+regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1)) :
    (run R.c7t m s).phase=s.phase ∧ (∀q,q∉R.T → (run R.c7t m s).basis q=s.basis q) ∧
    regValue R.T (run R.c7t m s).basis=(regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis+(s.basis R.cin).toNat)%2^R.T.length := by
  by_cases hc : R.trimOK
  swap
  · have em : R.c7t=R.c7y := if_neg (fun h => hc h.1)
    rw [em]; exact R.c7y_correct w hn s m hcl hnc hi h1
  have hA := hA hc
  have hb := hb hc
  have top := R.topOK_of w hc
  obtain ⟨-,h1l,h2,h3⟩ := top
  have em : R.c7t=addLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos (R.topOK_of w hc)
  have lx : ((R.dhi++R.zB).take (R.T.length-1)).length=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take]; omega
  have lc : ((R.carry.take (R.T.length-1)).take (R.T.length-2)).length+1=(R.T.take (R.T.length-1)).length := by
    simp only [List.length_take] at h2 ⊢; omega
  have hTn : R.T.Nodup := knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have e2 := addLowNC1_run ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin m s (R.top_nodup hn) hi
      (by rw [take_tail_headD _ _ (by omega)]; exact h1)
  have r := LowZero.addLowNC_correct _ _ _ R.cin (R.top_nodup hn) lx lc (by simp only [List.length_take]; omega) s m
    (fun q h => hcl q (List.mem_of_mem_take h))
    (by rw [take_headD _ _ (by omega),take_headD _ _ (by omega)]; exact hnc) hi
  rw [em,e2]
  refine ⟨r.1,fun q h => r.2.1 q (fun h' => h (List.mem_of_mem_take h')),?_⟩
  set t := run (LowZero.addLowNC ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
      ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin) m s with ht
  set P := 2^(R.T.length-1) with hP
  have h2P : 2^R.T.length=2*P := by rw [hP,← pow_succ']; congr 1; omega
  have xv : regValue ((R.dhi++R.zB).take (R.T.length-1)) s.basis=regValue (R.dhi++R.zB) s.basis := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
  have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%P :=
    CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
  have dkeep : regValue (R.T.drop (R.T.length-1)) t.basis=regValue (R.T.drop (R.T.length-1)) s.basis := by
    apply regValue_congr
    intro q hq
    apply r.2.1
    intro hq'
    exact List.disjoint_take_drop hTn (le_refl (R.T.length-1)) hq' hq
  have split (st : BasisState) : regValue R.T st=regValue (R.T.take (R.T.length-1)) st+
      P*regValue (R.T.drop (R.T.length-1)) st := by
    have e := regValue_append (R.T.take (R.T.length-1)) (R.T.drop (R.T.length-1)) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left (by omega)] at e
    exact e
  have dv : regValue (R.T.drop (R.T.length-1)) s.basis=regValue R.T s.basis/P :=
    CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by omega) _
  have tlt : regValue R.T s.basis<2*P := by rw [← h2P]; exact regValue_lt _ _
  have md := Nat.mod_add_div (regValue R.T s.basis) P
  have Ppos : 0<P := by rw [hP]; positivity
  have lowv : regValue (R.T.take (R.T.length-1)) t.basis=regValue (R.dhi++R.zB) s.basis+regValue R.T s.basis%P := by
    rw [r.2.2,xv,yv,hi,Bool.toNat_false,Nat.add_zero,List.length_take,Nat.min_eq_left (by omega),← hP]
    exact Nat.mod_eq_of_lt (by omega)
  rw [split t.basis,lowv,dkeep,dv,hi,Bool.toNat_false,Nat.add_zero,h2P]
  have mle := Nat.mod_le (regValue R.T s.basis) P
  have dle : regValue R.T s.basis/P≤1 := by
    have := Nat.div_lt_of_lt_mul (show regValue R.T s.basis<P*2 by omega); omega
  generalize regValue R.T s.basis%P=M at *
  generalize regValue R.T s.basis/P=D at *
  generalize regValue R.T s.basis=TV at *
  generalize regValue (R.dhi++R.zB) s.basis=AV at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp dle with e|e
  · subst e; simp only [Nat.mul_zero,Nat.add_zero] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · subst e; simp only [Nat.mul_one] at md ⊢
    rw [Nat.mod_eq_of_lt (by omega)]; omega

end ECDSAAdd.Entrant.KRegs

section
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.KnownTop
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant.TopCarry

/-- In-place adder whose highest carry is the affine bit `a' ⊕ b' ⊕ r`; valid when bit
`n-1` of the sum is known to be `r`. -/
def addKT (r : Bool) : List Wire → List Wire → List Wire → Wire → Program
  | a :: (a' :: as), b :: (b' :: bs), c :: cs, cin =>
      (if as = [] then ([.CX a' c, .CX b' c] ++ (if r then [.X c] else [])) else majority a b cin c) ++
        addKT r (a' :: as) (b' :: bs) cs c ++ eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | [a], [b], _, cin => [.CX a b, .CX cin b]
  | _, _, _, _ => []

theorem addKT_counts (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    toffoliCount (addKT r x y carry cin) = n ∧
    measurementCount (addKT r x y carry cin) = n + 1 := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    cases r <;> simp [addKT, eraseCarry, toffoliCount, measurementCount]
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addKT, List.cons_ne_nil, if_false, toffoliCount_append,
        measurementCount_append, h.1, h.2, majority, eraseCarry, toffoliCount, measurementCount]
    omega

private theorem kt_base (A A' B B' C r : Bool)
    (hS : (2 ≤ (A.toNat + 2 * A'.toNat + (B.toNat + 2 * B'.toNat) + C.toNat) % 4) = (r = true)) :
    carryBit A B C = (A' ^^ B' ^^ r) := by
  revert hS
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> cases r <;> decide

/-- The affine top carry agrees with the majority whenever the top sum bit is `r`. -/
theorem addKT_eq (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → ∀ (s : State) (m : List Bool),
    (∀ w ∈ carry, s.basis w = false) →
    (2^(n+1) ≤ (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^(n+2)) = (r = true) →
    run (addKT r x y carry cin) m s = run (addInPlace x y carry cin) m s := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd s m hclean hS
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have ha'c : a' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hzero : s.basis c = false := hclean c (by simp)
    have hK : carryBit (s.basis a) (s.basis b) (s.basis cin) = (s.basis a' ^^ s.basis b' ^^ r) := by
      apply kt_base
      simpa [regValue_cons', regValue_nil'] using hS
    have hm1 : measurementCount (([.CX a' c, .CX b' c] ++ (if r then [.X c] else [])) : Program) = 0 := by
      cases r <;> rfl
    have hm2 : measurementCount (majority a b cin c) = 0 := rfl
    have hmid : run (([.CX a' c, .CX b' c] ++ (if r then [.X c] else [])) : Program) [] s =
        run (majority a b cin c) [] s := by
      rw [majority_correct _ _ _ _ h4]
      cases r <;>
      · simp only [run, List.cons_append, List.nil_append, if_true, if_false, Bool.false_eq_true]
        apply State.extensionality
        · rfl
        · funext w
          simp only [writeBit, Function.update]
          by_cases hwc : w = c
          · subst hwc
            simp [ha'c, hb'c, hzero, hK]
          · simp [hwc]
    simp only [addKT, addInPlace, if_pos (rfl : ([] : List Wire) = []), List.append_assoc]
    exact run_head_congr _ _ _ m s hm1 hm2 hmid
  | succ n ih =>
    intro x y carry cin hy hx hc hnd s m hclean hS
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have h4 : [a, b, cin, c].Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append, List.count_nil] at this ⊢; omega
    have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    have hcx : c ∉ a' :: a'' :: as := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hcy : c ∉ b' :: b'' :: bs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hccs : c ∉ cs := fun h => by
      have h1 := hcnt c; have h2 := List.count_pos_iff.mpr h
      simp only [List.count_cons, List.count_append, beq_self_eq_true, if_true] at h1 h2; omega
    have hzero : s.basis c = false := hclean c (by simp)
    let A := s.basis a
    let B := s.basis b
    let C := s.basis cin
    let s1 : State := ⟨s.phase, writeBit s.basis c (carryBit A B C)⟩
    have hfirst (record : List Bool) : run (majority a b cin c) record s = s1 := by
      rw [majority_correct _ _ _ _ h4]; simp [s1, hzero, A, B, C]
    have hs1 (w : Wire) (hw : w ≠ c) : s1.basis w = s.basis w := by simp [s1, writeBit, hw]
    have hclean' : ∀ d ∈ cs, s1.basis d = false := by
      intro d hd; rw [hs1 d (fun h => hccs (h ▸ hd))]; exact hclean d (by simp [hd])
    have hxs : regValue (a' :: a'' :: as) s1.basis = regValue (a' :: a'' :: as) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcx (h ▸ hw)))
    have hys : regValue (b' :: b'' :: bs) s1.basis = regValue (b' :: b'' :: bs) s.basis :=
      regValue_congr _ _ _ (fun w hw => hs1 w (fun h => hcy (h ▸ hw)))
    have hc1 : s1.basis c = carryBit A B C := by simp [s1, writeBit]
    have hp3 : 2^(n+1+2) = 2 * 2^(n+2) := by rw [show n+1+2 = (n+2)+1 by omega, pow_succ]; ring
    have hp2 : 2^(n+1+1) = 2 * 2^(n+1) := by rw [pow_succ]; ring
    rw [regValue_cons' a, regValue_cons' b] at hS
    have step := sum_value_step A B C (regValue (a' :: a'' :: as) s.basis)
      (regValue (b' :: b'' :: bs) s.basis) (n+2)
    have hsb : (sumBit A B C).toNat ≤ 1 := by cases sumBit A B C <;> decide
    have hS' : (2^(n+1) ≤ (regValue (a' :: a'' :: as) s1.basis + regValue (b' :: b'' :: bs) s1.basis +
          (s1.basis c).toNat) % 2^(n+2)) = (r = true) := by
      rw [hxs, hys, hc1, ← hS]
      change (sumBit A B C).toNat + 2 * ((regValue (a' :: a'' :: as) s.basis +
        regValue (b' :: b'' :: bs) s.basis + (carryBit A B C).toNat) % 2^(n+2)) =
        ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
          (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+2+1) at step
      rw [show n+2+1 = n+1+2 by omega] at step
      generalize (regValue (a' :: a'' :: as) s.basis + regValue (b' :: b'' :: bs) s.basis +
        (carryBit A B C).toNat) % 2^(n+2) = S' at step ⊢
      generalize ((A.toNat + 2 * regValue (a' :: a'' :: as) s.basis) +
        (B.toNat + 2 * regValue (b' :: b'' :: bs) s.basis) + C.toNat) % 2^(n+1+2) = S at step ⊢
      apply propext
      constructor <;> intro h <;> omega
    have hmc : measurementCount (addKT r (a' :: a'' :: as) (b' :: b'' :: bs) cs c) =
        measurementCount (addInPlace (a' :: a'' :: as) (b' :: b'' :: bs) cs c) := by
      rw [(addKT_counts r n _ _ _ c (by simpa using hy) (by simpa using hx)
          (by simpa using hc)).2,
        (addInPlace_counts _ _ _ c (by simpa using hx) (by simpa using hc)).2]
      simp only [List.length_cons] at hy ⊢
      omega
    have hm0 : measurementCount (majority a b cin c) = 0 := rfl
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false]
    rw [List.append_assoc (majority a b cin c ++ _), List.append_assoc (majority a b cin c ++ _)]
    apply run_mid_congr _ _ _ _ m s hm0 hmc
    intro record
    rw [hfirst]
    exact ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' s1 record
      hclean' hS'


theorem addKT_wires (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    wires (addKT r x y carry cin) ⊆ wires (addInPlace x y carry cin) := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    intro w hw
    cases r <;> simp [addKT, addInPlace, wires, Instr.wires, majority, eraseCarry] at hw ⊢ <;> tauto
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false, wires_append]
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    have := @h w
    tauto

theorem addKT_physical (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    (cin :: (x ++ y ++ carry)).Nodup → GatePhysical (addInPlace x y carry cin) →
    GatePhysical (addKT r x y carry cin) := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc hnd hp
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have ha'c : a' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    have hb'c : b' ≠ c := fun h => by
      have := hcnt c; subst h
      simp only [List.count_cons, List.count_append, List.count_nil, beq_self_eq_true, if_true] at this; omega
    simp only [addKT, addInPlace, if_pos (rfl : ([] : List Wire) = []), gatePhysical_append] at hp ⊢
    refine ⟨⟨⟨?_, hp.1.1.2⟩, hp.1.2⟩, hp.2⟩
    cases r <;> intro i hi <;> simp at hi <;> rcases hi with rfl | rfl | rfl <;>
      simp [RecordedQuantum.PhysicalInstr, ProperGate, ha'c, hb'c]
  | succ n ih =>
    intro x y carry cin hy hx hc hnd hp
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have hcnt := List.nodup_iff_count.mp hnd
    have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have := hcnt w
      simp only [List.count_cons, List.count_append] at this ⊢; omega
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false, gatePhysical_append] at hp ⊢
    exact ⟨⟨⟨hp.1.1.1, ih _ _ _ c (by simpa using hy) (by simpa using hx) (by simpa using hc) hnd' hp.1.1.2⟩,
      hp.1.2⟩, hp.2⟩

open ECDSAAdd.Entrant.KRegs in
/-- `addHeadI` whose inner adder has the affine top carry. -/
def addHeadIKT (r : Bool) : List Wire → List Wire → List Wire → Wire → Program
  | a::a'::a''::as, b::b'::b''::bs, c::cs, cin =>
      DiagSq.maj0 a b cin c++(addKT r (a'::a''::as) (b'::b''::bs) cs c++eraseCarry a b cin c++[.CX a b,.CX cin b])
  | x, y, c, cin => KRegs.addHeadI x y c cin

theorem addHeadIKT_mc (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h3 : 3 ≤ y.length) :
    measurementCount (addHeadIKT r x y carry cin) = measurementCount (KRegs.addHeadI x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc h3 <;> try omega
  ·
    have k := addKT_counts r as.length (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega)
      (by simp at hx ⊢; omega) (by simp at hx hc ⊢; omega)
    have k2 := addInPlace_counts (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    simp only [addHeadIKT, KRegs.addHeadI, measurementCount_append, k.2, k2.2]
    simp [DiagSq.maj0, measurementCount]
    simp at hx; omega

theorem addHeadIKT_counts (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h3 : 3 ≤ y.length) :
    toffoliCount (addHeadIKT r x y carry cin) + 1 = toffoliCount (KRegs.addHeadI x y carry cin) := by
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc h3 <;> try omega
  ·
    have k := addKT_counts r as.length (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega)
      (by simp at hx ⊢; omega) (by simp at hx hc ⊢; omega)
    have k2 := addInPlace_counts (a'::a''::as) (b'::b''::bs) cs c (by simp at hx ⊢; omega) (by simp at hc ⊢; omega)
    simp only [addHeadIKT, KRegs.addHeadI, toffoliCount_append, k.1, k2.1]
    simp [DiagSq.maj0, toffoliCount, eraseCarry]
    simp at hx; omega

theorem addHeadIKT_run (r : Bool) (n : Nat) (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hy : y.length = n + 3) (hx : x.length = y.length) (hc : carry.length + 1 = y.length)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hcl : ∀ w ∈ carry, s.basis w = false)
    (hi : s.basis cin=false) (h0 : ∀a as,x=a::as → s.basis a=false)
    (hd : ∀a as b bs,x=a::as → y=b::bs → a≠b ∧ a≠cin ∧ b≠cin)
    (hS : (2^(n+2) ≤ (regValue x s.basis + regValue y s.basis + (s.basis cin).toNat) % 2^(n+3)) = (r = true)) :
    run (addHeadIKT r x y carry cin) m s=run (KRegs.addHeadI x y carry cin) m s := by
  rw [KRegs.addHeadI_run x y carry cin m s hi h0 hd,
    ← addKT_eq r (n+1) x y carry cin hy hx hc hn s m hcl hS]
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc hy <;> try omega
  ·
    obtain ⟨h1,-,h3⟩ := hd a _ b _ rfl rfl
    simp only [addHeadIKT, addKT, List.cons_ne_nil, if_false, DiagSq.maj0, majority, List.cons_append, List.nil_append,
      List.append_assoc]
    exact (DiagSq.run_maj_idle a b cin c _ m s hi (by intro h; rw [h0 a _ rfl] at h; cases h) h1 h3).symm

def addLowNC1KT (r : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  addHeadIKT r x.tail y.tail carry.tail cin ++ [.measureX (carry.headD 0) [] []] ++
    [.CX (x.headD 0) (y.headD 0), .CX cin (y.headD 0)]

def subLowNC1KT (r : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addLowNC1KT r x y carry cin ++ notRegister y

theorem tail_nodup (x y carry : List Wire) (cin : Wire) (hn : (cin :: (x ++ y ++ carry)).Nodup) :
    (cin :: (x.tail ++ y.tail ++ carry.tail)).Nodup := by
  exact List.Nodup.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.Sublist.append (List.tail_sublist x)
    (List.tail_sublist y)) (List.tail_sublist carry))) hn

theorem addLowNC1KT_run (r : Bool) (n : Nat) (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hy : y.tail.length = n + 3) (hx : x.tail.length = y.tail.length) (hc : carry.tail.length + 1 = y.tail.length)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hcl : ∀ w ∈ carry.tail, s.basis w = false)
    (hi : s.basis cin=false) (h1 : s.basis (x.tail.headD 0)=false)
    (hS : (2^(n+2) ≤ (regValue x.tail s.basis + regValue y.tail s.basis) % 2^(n+3)) = (r = true)) :
    run (addLowNC1KT r x y carry cin) m s=run (KRegs.addLowNC1 x y carry cin) m s := by
  have hd : ∀a as b bs,x.tail=a::as → y.tail=b::bs → a≠b ∧ a≠cin ∧ b≠cin := by
    intro a as b bs ha hb
    have ax : a∈x := List.mem_of_mem_tail (by rw [ha]; simp)
    have bx : b∈y := List.mem_of_mem_tail (by rw [hb]; simp)
    have hc := (List.nodup_cons.mp hn).1
    refine ⟨fun e => ?_,fun e => hc (by rw [← e]; simp [ax]),fun e => hc (by rw [← e]; simp [bx])⟩
    rw [e] at ax
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) b ax bx
  have h0 : ∀a as,x.tail=a::as → s.basis a=false := by
    intro a as h; have := h1; rw [h] at this; simpa using this
  have e := addHeadIKT_run r n x.tail y.tail carry.tail cin
    (m.take (measurementCount (KRegs.addHeadI x.tail y.tail carry.tail cin))) s hy hx hc
    (tail_nodup x y carry cin hn) hcl hi h0 hd (by rw [hi]; simpa using hS)
  simp only [addLowNC1KT,KRegs.addLowNC1,List.append_assoc]
  rw [run_append (addHeadIKT _ _ _ _ _),run_append (KRegs.addHeadI _ _ _ _),
    addHeadIKT_mc r _ _ _ _ hx hc (by omega),e]

theorem subLowNC1KT_run (r : Bool) (n : Nat) (x y carry : List Wire) (cin : Wire) (m : List Bool) (s : State)
    (hy : y.tail.length = n + 3) (hx : x.tail.length = y.tail.length) (hc : carry.tail.length + 1 = y.tail.length)
    (hn : (cin :: (x ++ y ++ carry)).Nodup) (hcl : ∀ w ∈ carry.tail, s.basis w = false)
    (hi : s.basis cin=false) (h1 : s.basis (x.tail.headD 0)=false)
    (hS : (2^(n+2) ≤ (regValue x.tail s.basis + (2^(n+3) - 1 - regValue y.tail s.basis)) % 2^(n+3)) = (r = true)) :
    run (subLowNC1KT r x y carry cin) m s=run (KRegs.subLowNC1 x y carry cin) m s := by
  have hm : measurementCount (notRegister y)=0 := (notRegister_counts y).2
  have hyn : y.Nodup := DiagSq.nd_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega)
  have nr := notRegister_correct y hyn s []
  have hcy : cin∉y := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hx2 : x.tail.headD 0∉y := by
    have hx1 : x.tail.headD 0∈x := by
      rcases x with _|⟨a,_|⟨b,xs⟩⟩
      · simp at hx hy; omega
      · simp at hx hy; omega
      · simp
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ hx1
  have xty : ∀ q ∈ x.tail, q ∉ y := fun q hq =>
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ (List.mem_of_mem_tail hq)
  have cty : ∀ q ∈ carry.tail, q ∉ y := fun q hq hqy =>
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons,List.count_append]; omega) _ hqy (List.mem_of_mem_tail hq)
  have ytl : ∀ q ∈ y.tail, q ∈ y := fun q hq => List.mem_of_mem_tail hq
  simp only [subLowNC1KT,KRegs.subLowNC1,List.append_assoc]
  rw [run_append (notRegister y),run_append (notRegister y),hm]
  simp only [List.take_zero,List.drop_zero]
  rw [run_append (addLowNC1KT r x y carry cin),
    run_append (KRegs.addLowNC1 x y carry cin),
    show measurementCount (addLowNC1KT r x y carry cin) = measurementCount (KRegs.addLowNC1 x y carry cin) by
      simp only [addLowNC1KT, KRegs.addLowNC1, measurementCount_append, addHeadIKT_mc r _ _ _ _ hx hc (by omega)],
    addLowNC1KT_run r n x y carry cin _ _ hy hx hc hn]
  · intro q hq; rw [nr]; dsimp only; rw [if_neg (cty q hq)]; exact hcl q hq
  · rw [nr]; simp [hcy,hi]
  · rw [nr]; dsimp only; rw [if_neg hx2]; exact h1
  · rw [nr]
    have ex : regValue x.tail (fun w => if w ∈ y then !s.basis w else s.basis w) = regValue x.tail s.basis :=
      regValue_congr _ _ _ (fun q hq => by simp [xty q hq])
    have ey : regValue y.tail (fun w => if w ∈ y then !s.basis w else s.basis w) = 2^y.tail.length - 1 - regValue y.tail s.basis := by
      rw [regValue_congr y.tail _ (fun w => !s.basis w) (fun q hq => by simp [ytl q hq]), regValue_complement]
    dsimp only
    rw [ex, ey, hy]
    exact hS

theorem addKT_slots (r : Bool) : ∀ (n : Nat) (x y carry : List Wire) (cin : Wire),
    y.length = n + 2 → x.length = y.length → carry.length + 1 = y.length →
    Challenge.gateSlots (addKT r x y carry cin) ≤ Challenge.gateSlots (addInPlace x y carry cin) := by
  intro n
  induction n with
  | zero =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', b, b', c, rfl, rfl, rfl⟩ := shape_two hy hx hc
    cases r <;> simp [addKT, addInPlace, majority, Challenge.gateSlots, Challenge.instructionSlots] <;> omega
  | succ n ih =>
    intro x y carry cin hy hx hc
    obtain ⟨a, a', a'', as, b, b', b'', bs, c, cs, rfl, rfl, rfl⟩ := shape_succ hy hx hc
    have h := ih (a' :: a'' :: as) (b' :: b'' :: bs) cs c (by simpa using hy)
        (by simpa using hx) (by simpa using hc)
    simp only [addKT, addInPlace, List.cons_ne_nil, if_false, Challenge.gateSlots_append]
    omega

theorem addHeadIKT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h3 : 3 ≤ y.length) :
    wires (addHeadIKT r x y carry cin) ⊆ wires (KRegs.addHeadI x y carry cin) ∧
    Challenge.gateSlots (addHeadIKT r x y carry cin) ≤ Challenge.gateSlots (KRegs.addHeadI x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (KRegs.addHeadI x y carry cin) →
      GatePhysical (addHeadIKT r x y carry cin)) := by
  rcases x with _|⟨a,_|⟨a',_|⟨a'',as⟩⟩⟩ <;> rcases y with _|⟨b,_|⟨b',_|⟨b'',bs⟩⟩⟩ <;>
    rcases carry with _|⟨c,cs⟩ <;> simp only [List.length_cons, List.length_nil] at hx hc h3 <;> try omega
  · have hy : (b'::b''::bs).length = as.length + 2 := by simp at hx ⊢; omega
    have hx' : (a'::a''::as).length = (b'::b''::bs).length := by simp at hx ⊢; omega
    have hc' : cs.length + 1 = (b'::b''::bs).length := by simp at hx hc ⊢; omega
    have kw := addKT_wires r as.length _ _ cs c hy hx' hc'
    have ks := addKT_slots r as.length _ _ cs c hy hx' hc'
    refine ⟨?_, ?_, ?_⟩
    · simp only [addHeadIKT, KRegs.addHeadI, wires_append]
      intro w hw
      simp only [Finset.mem_union] at hw ⊢
      have := @kw w
      tauto
    · simp only [addHeadIKT, KRegs.addHeadI, Challenge.gateSlots_append]
      omega
    · intro hnd hp
      have hcnt := List.nodup_iff_count.mp hnd
      have hnd' : (c :: ((a' :: a'' :: as) ++ (b' :: b'' :: bs) ++ cs)).Nodup := by
        apply List.nodup_iff_count.mpr; intro w; have := hcnt w
        simp only [List.count_cons, List.count_append] at this ⊢; omega
      simp only [addHeadIKT, KRegs.addHeadI, gatePhysical_append] at hp ⊢
      exact ⟨hp.1, ⟨⟨addKT_physical r as.length _ _ cs c hy hx' hc' hnd' hp.2.1.1, hp.2.1.2⟩, hp.2.2⟩⟩

theorem subLowNC1KT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    toffoliCount (subLowNC1KT r x y carry cin) + 1 = toffoliCount (KRegs.subLowNC1 x y carry cin) ∧
    measurementCount (subLowNC1KT r x y carry cin) = measurementCount (KRegs.subLowNC1 x y carry cin) ∧
    wires (subLowNC1KT r x y carry cin) ⊆ wires (KRegs.subLowNC1 x y carry cin) ∧
    Challenge.gateSlots (subLowNC1KT r x y carry cin) ≤ Challenge.gateSlots (KRegs.subLowNC1 x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (KRegs.subLowNC1 x y carry cin) →
      GatePhysical (subLowNC1KT r x y carry cin)) := by
  have hx' : x.tail.length = y.tail.length := by simp [hx]
  have hc' : carry.tail.length + 1 = y.tail.length := by simp; omega
  have h3 : 3 ≤ y.tail.length := by simp; omega
  have tc := addHeadIKT_counts r _ _ _ cin hx' hc' h3
  have mc := addHeadIKT_mc r _ _ _ cin hx' hc' h3
  have res := addHeadIKT_res r _ _ _ cin hx' hc' h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, toffoliCount_append]; omega
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, measurementCount_append]; omega
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, wires_append]
    intro w hw
    simp only [Finset.mem_union] at hw ⊢
    have := @res.1 w
    tauto
  · simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, Challenge.gateSlots_append]
    have := res.2.1; omega
  · intro hnd hp
    simp only [subLowNC1KT, KRegs.subLowNC1, addLowNC1KT, KRegs.addLowNC1, gatePhysical_append] at hp ⊢
    exact ⟨⟨hp.1.1, ⟨res.2.2 (tail_nodup x y carry cin hnd) hp.1.2.1.1, hp.1.2.1.2⟩, hp.1.2.2⟩, hp.2⟩

end ECDSAAdd.Entrant.KnownTop

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic
variable (R : KRegs)

theorem regValue_head_tail (l : List Wire) (st : BasisState) (hne : l ≠ []) :
    regValue l st = (st (l.headD 0)).toNat + 2 * regValue l.tail st := by
  match l, hne with
  | w :: ws, _ => exact TopCarry.regValue_cons' w ws st

/-- `m7y` with its top carry made affine: the difference `T - b²` stays below `2^(|T|-1)`. -/
def m7f : Program :=
  if (R.dhi++R.zB).length=R.T.length ∧ (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 4≤R.T.length then
    KnownTop.subLowNC1KT true (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin else R.m7y

theorem m7f_lens (w : R.W) : (R.dhi++R.zB).length=R.T.length ∧
    (R.carry.take (R.T.length-1)).length+1=R.T.length ∧ 4≤R.T.length := by
  have l := R.t_lensg w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S; have hTl := w.T
  exact ⟨l.1, l.2.1, by omega⟩

theorem m7f_run (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hle : regValue (R.dhi++R.zB) s.basis ≤ regValue R.T s.basis)
    (hlt : regValue R.T s.basis < regValue (R.dhi++R.zB) s.basis + 2^(R.T.length-1)) :
    run R.m7f m s=run R.m7y m s := by
  have l := R.t_lensg w
  have l4 := R.m7f_lens w
  unfold m7f m7y
  rw [if_pos l4, if_pos ⟨l.1,l.2.1,l.2.2.1⟩]
  obtain ⟨n, hn4⟩ : ∃ n, R.T.length = n + 4 := ⟨R.T.length - 4, by omega⟩
  have hTne : R.T ≠ [] := fun e => by rw [e] at hn4; simp at hn4
  have hXne : R.dhi++R.zB ≠ [] := fun e => by have := congrArg List.length e; simp only [List.length_nil] at this; omega
  apply KnownTop.subLowNC1KT_run true n _ _ _ _ m s (by simp; omega) (by simp [l.1])
    (by simp only [List.length_tail]; omega)
    (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (fun q hq => hcl q (List.mem_of_mem_tail hq)) hi h1
  refine propext ⟨fun _ => rfl, fun _ => ?_⟩
  rw [regValue_head_tail _ _ hXne] at hle hlt
  rw [regValue_head_tail _ _ hTne] at hle hlt
  have ttl : regValue R.T.tail s.basis < 2^(n+3) := by
    have := regValue_lt R.T.tail s.basis; simp only [List.length_tail] at this; rwa [show R.T.length - 1 = n+3 by omega] at this
  have x0 : (s.basis ((R.dhi++R.zB).headD 0)).toNat ≤ (s.basis (R.T.headD 0)).toNat := by
    revert hnc; cases s.basis ((R.dhi++R.zB).headD 0) <;> cases s.basis (R.T.headD 0) <;> decide
  have t0 : (s.basis (R.T.headD 0)).toNat ≤ 1 := by cases s.basis (R.T.headD 0) <;> decide
  rw [show R.T.length - 1 = n + 3 by omega] at hlt
  have p3 : 2^(n+3) = 2 * 2^(n+2) := by rw [pow_succ]; ring
  rw [p3] at hlt ttl ⊢
  generalize 2^(n+2) = P at hlt ttl ⊢
  generalize regValue R.T.tail s.basis = tt at hle hlt ttl ⊢
  generalize regValue (R.dhi++R.zB).tail s.basis = xt at hle hlt ⊢
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem m7f_res (w : R.W) : toffoliCount R.m7f+1=toffoliCount R.m7y ∧
    measurementCount R.m7f=measurementCount R.m7y ∧ wires R.m7f⊆wires R.m7y ∧
    Challenge.gateSlots R.m7f≤Challenge.gateSlots R.m7y ∧ (R.all.Nodup → GatePhysical R.m7f) := by
  have l := R.t_lensg w
  have l4 := R.m7f_lens w
  have res := KnownTop.subLowNC1KT_res true (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin l4.1 l4.2.1 l4.2.2
  have e1 : R.m7f = KnownTop.subLowNC1KT true (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin := if_pos l4
  have e2 : R.m7y = KRegs.subLowNC1 (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin :=
    if_pos ⟨l.1,l.2.1,l.2.2.1⟩
  rw [e1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e2]; exact res.1
  · rw [e2]; exact res.2.1
  · rw [e2]; exact res.2.2.1
  · rw [e2]; exact res.2.2.2.1
  · intro hn
    have hp := R.m7y_physical hn
    rw [e2] at hp
    exact res.2.2.2.2 (knd hn (fun q => by
      have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)) hp


theorem m7f_counts (w : R.W) : toffoliCount R.m7f+1=toffoliCount R.m7y ∧
    measurementCount R.m7f=measurementCount R.m7y := ⟨(R.m7f_res w).1,(R.m7f_res w).2.1⟩

theorem kt_arith (x0 t0 xt yt Q : Nat) (hx0 : x0 ≤ t0) (ht0 : t0 ≤ 1)
    (hle : x0 + 2*xt ≤ t0 + 2*yt) (hlt : t0 + 2*yt < x0 + 2*xt + 2*Q) (hyt : yt < 2*Q) :
    Q ≤ (xt + (2*Q - 1 - yt)) % (2*Q) := by
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `m7t` with its top carry made affine (trimmed register when `trimOK`, full register otherwise). -/
def m7k : Program := if R.topOK then
  KnownTop.subLowNC1KT true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
    ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin else R.m7f

theorem m7k_run (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcl : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hnc : (s.basis ((R.dhi++R.zB).headD 0) && !s.basis (R.T.headD 0))=false) (hi : s.basis R.cin=false)
    (h1 : s.basis ((R.dhi++R.zB).tail.headD 0)=false)
    (hT : R.trimOK → regValue (R.dhi++R.zB) s.basis<2^(R.T.length-1) ∧
      regValue (R.dhi++R.zB) s.basis≤regValue R.T s.basis%2^(R.T.length-1) ∧
      regValue R.T s.basis%2^(R.T.length-1)<regValue (R.dhi++R.zB) s.basis+2^(R.T.length-2))
    (hF : ¬R.trimOK → regValue (R.dhi++R.zB) s.basis≤regValue R.T s.basis ∧
      regValue R.T s.basis<regValue (R.dhi++R.zB) s.basis+2^(R.T.length-1)) :
    run R.m7k m s=run R.m7t m s := by
  by_cases hc : R.trimOK
  · have top := R.topOK_of w hc
    obtain ⟨hA,hb,hlt⟩ := hT hc
    have e1 : R.m7k=KnownTop.subLowNC1KT true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    have e2 : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    obtain ⟨-,h1l,h2,h3⟩ := top
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have hh4 := w.h4; have hSl := w.S; have hTl := w.T
    have hc' : 2*R.h+1≤R.bank.length := hc
    obtain ⟨n, hn5⟩ : ∃ n, R.T.length = n + 6 := ⟨R.T.length - 6, by omega⟩
    rw [e1,e2]
    apply KnownTop.subLowNC1KT_run true (n+1) _ _ _ _ m s (by simp only [List.length_tail,List.length_take]; omega)
      (by simp only [List.length_tail,List.length_take]; omega) (by simp only [List.length_tail,List.length_take] at h2 ⊢; omega)
      (R.top_nodup hn) (fun q hq => hcl q (List.mem_of_mem_take (List.mem_of_mem_tail hq))) hi
      (by rw [take_tail_headD _ _ (by omega)]; exact h1)
    refine propext ⟨fun _ => rfl, fun _ => ?_⟩
    have xne : (R.dhi++R.zB).take (R.T.length-1)≠[] := by
      intro e; have := congrArg List.length e; simp only [List.length_take,List.length_nil] at this; omega
    have yne : R.T.take (R.T.length-1)≠[] := by
      intro e; have := congrArg List.length e; simp only [List.length_take,List.length_nil] at this; omega
    have xv : regValue ((R.dhi++R.zB).take (R.T.length-1)) s.basis=regValue (R.dhi++R.zB) s.basis := by
      rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega),Nat.mod_eq_of_lt hA]
    have yv : regValue (R.T.take (R.T.length-1)) s.basis=regValue R.T s.basis%2^(R.T.length-1) :=
      CuccaroStreamedSquareWideLayout.regValue_take_mod _ _ (by omega) _
    have xh := regValue_head_tail _ s.basis xne
    have yh := regValue_head_tail _ s.basis yne
    rw [take_headD _ _ (by omega)] at xh yh
    rw [xv] at xh; rw [yv] at yh
    have ttl : regValue (R.T.take (R.T.length-1)).tail s.basis<2^(n+1+3) := by
      have := regValue_lt (R.T.take (R.T.length-1)).tail s.basis
      simp only [List.length_tail,List.length_take] at this
      rwa [show min (R.T.length-1) R.T.length-1=n+1+3 by omega] at this
    have x0 : (s.basis ((R.dhi++R.zB).headD 0)).toNat ≤ (s.basis (R.T.headD 0)).toNat := by
      revert hnc; cases s.basis ((R.dhi++R.zB).headD 0) <;> cases s.basis (R.T.headD 0) <;> decide
    have t0 : (s.basis (R.T.headD 0)).toNat ≤ 1 := by cases s.basis (R.T.headD 0) <;> decide
    have p3 : 2^(n+1+3)=2*2^(n+1+2) := by rw [show n+1+3=(n+1+2)+1 by omega,pow_succ]; ring
    have pl : 2^(R.T.length-2)=2^(n+1+3) := by congr 1; omega
    rw [pl] at hlt
    rw [p3] at ttl hlt ⊢
    exact kt_arith _ _ _ _ _ x0 t0 (by omega) (by omega) ttl
  · have e1 : R.m7k=R.m7f := if_neg (fun h => hc h.1)
    have e2 : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [e1,e2]
    exact R.m7f_run w hn s m hcl hnc hi h1 (hF hc).1 (hF hc).2

theorem m7k_res (w : R.W) : toffoliCount R.m7k+1=toffoliCount R.m7t ∧
    measurementCount R.m7k=measurementCount R.m7t ∧ wires R.m7k⊆wires R.m7t ∧
    Challenge.gateSlots R.m7k≤Challenge.gateSlots R.m7t ∧ (R.all.Nodup → GatePhysical R.m7k) := by
  by_cases hc : R.trimOK
  · have top := R.topOK_of w hc
    have e1 : R.m7k=KnownTop.subLowNC1KT true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    have e2 : R.m7t=subLowNC1 ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin := if_pos top
    obtain ⟨-,h1l,h2,h3⟩ := top
    obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
    have hh4 := w.h4; have hSl := w.S; have hTl := w.T
    have hc' : 2*R.h+1≤R.bank.length := hc
    have res := KnownTop.subLowNC1KT_res true ((R.dhi++R.zB).take (R.T.length-1)) (R.T.take (R.T.length-1))
        ((R.carry.take (R.T.length-1)).take (R.T.length-2)) R.cin
        (by simp only [List.length_take]; omega) (by simp only [List.length_take] at h2 ⊢; omega)
        (by simp only [List.length_take]; omega)
    rw [e1,e2]
    refine ⟨res.1,res.2.1,res.2.2.1,res.2.2.2.1,fun hn => ?_⟩
    have hp := R.m7t_physical hn
    rw [e2] at hp
    exact res.2.2.2.2 (R.top_nodup hn) hp
  · have e1 : R.m7k=R.m7f := if_neg (fun h => hc h.1)
    have e2 : R.m7t=R.m7y := if_neg (fun h => hc h.1)
    rw [e1,e2]
    exact R.m7f_res w

theorem m7k_counts (w : R.W) : toffoliCount R.m7k+1=toffoliCount R.m7t ∧
    measurementCount R.m7k=measurementCount R.m7t := ⟨(R.m7k_res w).1,(R.m7k_res w).2.1⟩
theorem m7k_wires (w : R.W) : wires R.m7k⊆wires R.m7 := (R.m7k_res w).2.2.1.trans R.m7t_wires
theorem m7k_slots (w : R.W) : Challenge.gateSlots R.m7k≤Challenge.gateSlots R.m7 :=
  (R.m7k_res w).2.2.2.1.trans R.m7t_slots
theorem m7k_physical (w : R.W) (hn : R.all.Nodup) : GatePhysical R.m7k := (R.m7k_res w).2.2.2.2 hn

end ECDSAAdd.Entrant.KRegs
end

end

-- Research extension: m6 second and high carry; full integration pending.
section

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Entrant.CodexM6Carry
open ECDSAAdd ECDSAAdd.Arithmetic

/-- Keep ConstCarry's second-majority reduction and replace the independent
    final majority using KnownTop. At least four bits separates the two sites. -/
def addInPlace2KT (r : Bool) : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: a3 :: as, b0 :: b1 :: b2 :: b3 :: bs, c0 :: c1 :: cs, cin =>
      majority a0 b0 cin c0 ++
        ([.CX c0 c1] ++ KnownTop.addKT r (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 ++
          eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++
        eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => ConstCarry.addInPlace2 x y c cin

def subInPlace2KT (r : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ addInPlace2KT r x y carry cin ++ notRegister y

theorem addKT_shape4 (r : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire)
    (as bs cs : List Wire) :
    KnownTop.addKT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin =
      majority a0 b0 cin c0 ++
        (majority a1 b1 c0 c1 ++ KnownTop.addKT r (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 ++
          eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++
        eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0] := by
  simp only [KnownTop.addKT, List.cons_ne_nil, if_false]

/-- This local rewrite needs no top-bit hypothesis: both programs use the same
    KnownTop tail; only the second majority is compared. -/
theorem addInPlace2KT_run (r : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire)
    (as bs cs : List Wire)
    (h0 : [a0, b0, cin, c0].Nodup) (h1 : [a1, b1, c0, c1].Nodup)
    (ha : a1 ≠ c0) (hb : b1 ≠ c0) (s : State) (m : List Bool)
    (h : s.basis a1 ≠ s.basis b1) :
    run (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) m s =
    run (KnownTop.addKT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) m s := by
  rw [addKT_shape4]
  simp only [addInPlace2KT, List.append_assoc]
  rw [ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _),
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _),
    ConstCarry.run_pre [.CX c0 c1] _ (by simp [measurementCount]),
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _)]
  congr 1
  have t := majority_correct a0 b0 cin c0 h0 s []
  have e := ConstCarry.majority_ne a1 b1 c0 c1 h1
    (run (majority a0 b0 cin c0) [] s) (by
      rw [t]; simpa [writeBit, Function.update, ha, hb] using h)
  exact e.symm

theorem addInPlace2KT_counts_shape (r : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hx : as.length = bs.length) (hc : cs.length + 1 = bs.length + 2) :
    toffoliCount (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) + 1 =
      toffoliCount (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ∧
    measurementCount (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) =
      measurementCount (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) := by
  have kt := KnownTop.addKT_counts r as.length (a2 :: a3 :: as)
    (b2 :: b3 :: bs) cs c1 (by simp; omega) (by simp; omega) (by simp; omega)
  have old := addInPlace_counts (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1
    (by simp; omega) (by simp; omega)
  simp only [List.length_cons] at old
  simp only [addInPlace2KT, ConstCarry.addInPlace2,
    toffoliCount_append, measurementCount_append]
  constructor <;> omega

theorem addInPlace2KT_counts (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    toffoliCount (addInPlace2KT r x y carry cin) + 1 =
      toffoliCount (ConstCarry.addInPlace2 x y carry cin) ∧
    measurementCount (addInPlace2KT r x y carry cin) =
      measurementCount (ConstCarry.addInPlace2 x y carry cin) := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hc h4 <;> try omega
  exact addInPlace2KT_counts_shape r _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)

theorem subInPlace2KT_counts (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    toffoliCount (subInPlace2KT r x y carry cin) + 1 =
      toffoliCount (ConstCarry.subInPlace2 x y carry cin) ∧
    measurementCount (subInPlace2KT r x y carry cin) =
      measurementCount (ConstCarry.subInPlace2 x y carry cin) := by
  have h := addInPlace2KT_counts r x y carry cin hx hc h4
  simp only [subInPlace2KT, ConstCarry.subInPlace2,
    toffoliCount_append, measurementCount_append]
  constructor <;> omega

theorem addInPlace2KT_res_shape (r : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hx : as.length = bs.length) (hc : cs.length + 1 = bs.length + 2) :
    wires (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ⊆
      wires (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ∧
    Challenge.gateSlots (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ≤
      Challenge.gateSlots (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) ∧
    ((cin :: ((a0 :: a1 :: a2 :: a3 :: as) ++
        (b0 :: b1 :: b2 :: b3 :: bs) ++ (c0 :: c1 :: cs))).Nodup →
      GatePhysical (ConstCarry.addInPlace2 (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) →
      GatePhysical (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin)) := by
  have hy' : (b2 :: b3 :: bs).length = as.length + 2 := by simp; omega
  have hx' : (a2 :: a3 :: as).length = (b2 :: b3 :: bs).length := by simp; omega
  have hc' : cs.length + 1 = (b2 :: b3 :: bs).length := by simp; omega
  have kw := KnownTop.addKT_wires r as.length (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 hy' hx' hc'
  have ks := KnownTop.addKT_slots r as.length (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1 hy' hx' hc'
  refine ⟨?_, ?_, ?_⟩
  · simp only [addInPlace2KT, ConstCarry.addInPlace2, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    have := @kw q
    tauto
  · simp only [addInPlace2KT, ConstCarry.addInPlace2, Challenge.gateSlots_append]
    omega
  · intro hn hp
    have hcnt := List.nodup_iff_count_le_one.mp hn
    have hnt : (c1 :: ((a2 :: a3 :: as) ++ (b2 :: b3 :: bs) ++ cs)).Nodup := by
      apply List.nodup_iff_count_le_one.mpr
      intro q
      have := hcnt q
      simp only [List.count_cons, List.count_append] at this ⊢
      omega
    have hpt : GatePhysical (addInPlace (a2 :: a3 :: as) (b2 :: b3 :: bs) cs c1) := by
      simp only [ConstCarry.addInPlace2, gatePhysical_append] at hp
      tauto
    have hnew := KnownTop.addKT_physical r as.length (a2 :: a3 :: as)
      (b2 :: b3 :: bs) cs c1 hy' hx' hc' hnt hpt
    simp only [addInPlace2KT, ConstCarry.addInPlace2, gatePhysical_append] at hp ⊢
    tauto

theorem addInPlace2KT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    wires (addInPlace2KT r x y carry cin) ⊆ wires (ConstCarry.addInPlace2 x y carry cin) ∧
    Challenge.gateSlots (addInPlace2KT r x y carry cin) ≤
      Challenge.gateSlots (ConstCarry.addInPlace2 x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (ConstCarry.addInPlace2 x y carry cin) →
      GatePhysical (addInPlace2KT r x y carry cin)) := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hc h4 <;> try omega
  exact addInPlace2KT_res_shape r _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)

theorem subInPlace2KT_res (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length) :
    wires (subInPlace2KT r x y carry cin) ⊆ wires (ConstCarry.subInPlace2 x y carry cin) ∧
    Challenge.gateSlots (subInPlace2KT r x y carry cin) ≤
      Challenge.gateSlots (ConstCarry.subInPlace2 x y carry cin) ∧
    ((cin :: (x ++ y ++ carry)).Nodup → GatePhysical (ConstCarry.subInPlace2 x y carry cin) →
      GatePhysical (subInPlace2KT r x y carry cin)) := by
  have h := addInPlace2KT_res r x y carry cin hx hc h4
  refine ⟨?_, ?_, ?_⟩
  · simp only [subInPlace2KT, ConstCarry.subInPlace2, wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h.1)
      (Finset.Subset.refl _)
  · have hs := h.2.1
    simp only [subInPlace2KT, ConstCarry.subInPlace2, Challenge.gateSlots_append]
    omega
  · intro hn hp
    simp only [subInPlace2KT, ConstCarry.subInPlace2, gatePhysical_append] at hp ⊢
    have ha : GatePhysical (ConstCarry.addInPlace2 x y carry cin) := by tauto
    have hnw := h.2.2 hn ha
    tauto

/-- Reuse the existing full-register KnownTop proof after rewriting only the
    low second majority. The final notRegister restores the subtraction domain. -/
theorem subInPlace2KT_run (r : Bool) (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x ++ y ++ carry)).Nodup)
    (hx : x.length = y.length) (hc : carry.length + 1 = y.length) (h4 : 4 ≤ y.length)
    (s : State) (m : List Bool) (hclean : ∀ q ∈ carry, s.basis q = false)
    (hi : s.basis cin = false)
    (hb : s.basis (y.getD 1 0) = s.basis (x.getD 1 0))
    (hS : (2^(y.length - 1) ≤
      (regValue x s.basis + (2^y.length - 1 - regValue y s.basis)) % 2^y.length) = (r = true)) :
    run (subInPlace2KT r x y carry cin) m s = run (subInPlace x y carry cin) m s := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hc h4 <;> try omega
  have hnfull := hn
  have hyn : (b0 :: b1 :: b2 :: b3 :: bs).Nodup :=
    DiagSq.nd_count hn (fun q => by simp only [List.count_cons, List.count_append]; omega)
  have xny : ∀ q ∈ a0 :: a1 :: a2 :: a3 :: as, q ∉ b0 :: b1 :: b2 :: b3 :: bs :=
    DiagSq.dis_count hn (fun q => by simp only [List.count_cons, List.count_append]; omega)
  have cny : ∀ q ∈ c0 :: c1 :: cs, q ∉ b0 :: b1 :: b2 :: b3 :: bs := by
    intro q hq hqy
    exact DiagSq.dis_count hn (fun q => by simp only [List.count_cons, List.count_append]; omega) q hqy hq
  have cinny : cin ∉ b0 :: b1 :: b2 :: b3 :: bs := by
    intro h
    exact (List.nodup_cons.mp hn).1 (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))
  have nr := notRegister_correct (b0 :: b1 :: b2 :: b3 :: bs) hyn s []
  have mz := ConstCarry.notRegister_mc (b0 :: b1 :: b2 :: b3 :: bs)
  have mnew := addInPlace2KT_counts r (a0 :: a1 :: a2 :: a3 :: as)
    (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin
    (by simpa using hx) (by simpa using hc) (by simp)
  have mold := ConstCarry.addInPlace2_counts a0 a1 a2 b0 b1 b2 c0 c1 cin
    (a3 :: as) (b3 :: bs) cs
  have mc : measurementCount (addInPlace2KT r (a0 :: a1 :: a2 :: a3 :: as)
      (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) =
      measurementCount (addInPlace (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) := mnew.2.trans mold.2
  simp only [subInPlace2KT, subInPlace, List.append_assoc]
  rw [ConstCarry.run_pre _ _ mz, ConstCarry.run_pre _ _ mz,
    run_append, run_append (addInPlace _ _ _ _), mc]
  congr 1
  calc
    _ = run (KnownTop.addKT r (a0 :: a1 :: a2 :: a3 :: as)
        (b0 :: b1 :: b2 :: b3 :: bs) (c0 :: c1 :: cs) cin) _
        (run (notRegister (b0 :: b1 :: b2 :: b3 :: bs)) [] s) := by
      apply addInPlace2KT_run
      · exact DiagSq.nd_count hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega)
      · exact DiagSq.nd_count hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega)
      · intro he
        have hd := DiagSq.dis_count (r := [a1]) (t := [c0]) hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega) a1 (by simp)
        exact hd (by simpa using he)
      · intro he
        have hd := DiagSq.dis_count (r := [b1]) (t := [c0]) hn (fun q => by
          simp only [List.count_cons, List.count_nil, List.count_append]; omega) b1 (by simp)
        exact hd (by simpa using he)
      · rw [nr]
        simp only [List.getD_cons_succ, List.getD_cons_zero] at hb
        dsimp only
        rw [if_neg (xny a1 (by simp)), if_pos (by simp : b1 ∈ b0 :: b1 :: b2 :: b3 :: bs), hb]
        cases s.basis a1 <;> decide
    _ = _ := by
      apply KnownTop.addKT_eq r (bs.length + 2) _ _ _ _
        (by simp) (by simpa using hx) (by simpa using hc) hnfull
      · intro q hq
        rw [nr]
        dsimp only
        rw [if_neg (cny q hq)]
        exact hclean q hq
      · rw [nr]
        have ex : regValue (a0 :: a1 :: a2 :: a3 :: as)
            (fun q => if q ∈ b0 :: b1 :: b2 :: b3 :: bs then !s.basis q else s.basis q) =
            regValue (a0 :: a1 :: a2 :: a3 :: as) s.basis :=
          regValue_congr _ _ _ (fun q hq => by simp [xny q hq])
        have ey : regValue (b0 :: b1 :: b2 :: b3 :: bs)
            (fun q => if q ∈ b0 :: b1 :: b2 :: b3 :: bs then !s.basis q else s.basis q) =
            2^(b0 :: b1 :: b2 :: b3 :: bs).length - 1 -
              regValue (b0 :: b1 :: b2 :: b3 :: bs) s.basis := by
          rw [regValue_congr _ _ (fun q => !s.basis q) (fun q hq => by simp [hq]),
            regValue_complement]
        dsimp only
        rw [ex, ey, if_neg cinny, hi, Bool.toNat_false, Nat.add_zero]
        simpa [List.length_cons, Nat.add_assoc] using hS

/-- Numeric top-bit condition for subtraction's complemented add domain.
    Unlike m7's low-no-carry wrapper, m6 uses the full register, so no head/tail
    division or low-bit no-borrow lemma is needed here. -/
theorem sub_top (x y n : Nat) (hy : y < 2^(n+1))
    (hle : x ≤ y) (hlt : y < x + 2^n) :
    2^n ≤ (x + (2^(n+1) - 1 - y)) % 2^(n+1) := by
  have hp : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
  rw [hp] at hy ⊢
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

end ECDSAAdd.Entrant.CodexM6Carry



set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Entrant.KRegs
open ECDSAAdd ECDSAAdd.Arithmetic

/-- Only the 129-bit outer leaf uses this branch. The 128-bit leaves retain m6c. -/
def m6k (R : KRegs) : Program :=
  if R.trimOK then CodexM6Carry.subInPlace2KT true (R.dlo ++ R.zA) R.T
    (R.carry.take (R.T.length - 1)) R.cin else R.m6c

theorem m6k_lens (R : KRegs) (w : R.W) :
    (R.dlo ++ R.zA).length = R.T.length ∧
    (R.carry.take (R.T.length - 1)).length + 1 = R.T.length ∧ 4 ≤ R.T.length := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hSl := w.S
  have hTl := w.T; have hcl := w.carry
  simp only [List.length_append, List.length_take]
  omega

theorem m6k_counts (R : KRegs) (w : R.W) :
    toffoliCount R.m6k + (if R.trimOK then 1 else 0) = toffoliCount R.m6c ∧
    measurementCount R.m6k = measurementCount R.m6c := by
  have l := m6k_lens R w
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact CodexM6Carry.subInPlace2KT_counts true _ _ _ _ l.1 l.2.1 l.2.2
  · simp only [m6k, if_neg ht, Nat.add_zero, and_self]

theorem m6k_wires (R : KRegs) (w : R.W) : wires R.m6k ⊆ wires R.m6 := by
  have l := R.m6k_lens w
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact (CodexM6Carry.subInPlace2KT_res true _ _ _ _ l.1 l.2.1 l.2.2).1.trans
      (R.m6c_wires w)
  · simpa only [m6k, if_neg ht] using R.m6c_wires w

theorem m6k_slots (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.m6k ≤ Challenge.gateSlots R.m6 := by
  have l := R.m6k_lens w
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact (CodexM6Carry.subInPlace2KT_res true _ _ _ _ l.1 l.2.1 l.2.2).2.1.trans
      (R.m6c_slots w)
  · simpa only [m6k, if_neg ht] using R.m6c_slots w

theorem m6k_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (hp : GatePhysical R.m6) : GatePhysical R.m6k := by
  have l := R.m6k_lens w
  have old := R.m6c_physical w (R.carry_take_nodup hn _) hp
  by_cases ht : R.trimOK
  · simp only [m6k, if_pos ht]
    exact (CodexM6Carry.subInPlace2KT_res true _ _ _ _ l.1 l.2.1 l.2.2).2.2
      (knd hn (fun q => by
        have c := R.counts q
        simp only [KRegs.all, List.count_cons, List.count_append] at c ⊢
        omega)) old
  · simpa only [m6k, if_neg ht] using old

/-- Drop-in replacement for the existing st6 rewrite, with clean carries and
    the conditional half-range bound that make_correct already proves. -/
theorem m6k_run (R : KRegs) (w : R.W)
    (hn : (R.cin :: ((R.dlo ++ R.zA) ++ R.T ++ R.carry.take (R.T.length - 1))).Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀ q ∈ R.carry.take (R.T.length - 1), s.basis q = false)
    (hi : s.basis R.cin = false)
    (hb : s.basis (R.T.getD 1 0) = s.basis (R.dlo.getD 1 0))
    (hbound : R.trimOK → regValue (R.dlo ++ R.zA) s.basis ≤ regValue R.T s.basis ∧
      regValue R.T s.basis < regValue (R.dlo ++ R.zA) s.basis + 2^(R.T.length - 1)) :
    run R.m6k m s = run R.m6 m s := by
  by_cases ht : R.trimOK
  · have l := R.m6k_lens w
    have ml := R.m6c_lens w
    obtain ⟨hle, hlt⟩ := hbound ht
    simp only [m6k, if_pos ht, m6]
    apply CodexM6Carry.subInPlace2KT_run true _ _ _ _ hn l.1 l.2.1 l.2.2
      s m hclean hi
    · rw [hb, List.getD_append _ _ _ _ (by omega)]
    · refine propext ⟨fun _ => rfl, fun _ => ?_⟩
      have htlen : R.T.length - 1 + 1 = R.T.length := by omega
      have htv := regValue_lt R.T s.basis
      have h := CodexM6Carry.sub_top (regValue (R.dlo ++ R.zA) s.basis)
        (regValue R.T s.basis) (R.T.length - 1) (by simpa [htlen] using htv) hle hlt
      simpa [htlen] using h
  · simp only [m6k, if_neg ht]
    exact R.m6c_run w hn s m hb

/-- The concrete square-state premises already available before m6. -/
theorem m6k_square_run (R : KRegs) (w : R.W)
    (hn : (R.cin :: ((R.dlo ++ R.zA) ++ R.T ++ R.carry.take (R.T.length - 1))).Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀ q ∈ R.carry.take (R.T.length - 1), s.basis q = false)
    (hi : s.basis R.cin = false)
    (a b : Nat) (ha : a < 2^R.h) (hb : b < 2^(R.bank.length-R.h))
    (hT : regValue R.T s.basis = (a+b)^2)
    (hA : regValue R.dlo s.basis = a^2)
    (hz : regValue R.zA s.basis = 0) :
    run R.m6k m s = run R.m6 m s := by
  apply R.m6k_run w hn s m hclean hi (R.m6c_bits w s.basis (a+b) a hT hA)
  intro ht
  have hx : regValue (R.dlo ++ R.zA) s.basis = a^2 := by
    rw [regValue_append, hA, hz, Nat.mul_zero, Nat.add_zero]
  have hp := trim_bound R.bank.length R.h a b ht ha hb
  have hTl := w.T
  have hSl := w.S
  rw [hx, hT, hTl, hSl]
  have ex : (a+b)^2 = a^2 + (2*a*b+b^2) := by ring
  rw [ex]
  constructor <;> omega

end ECDSAAdd.Entrant.KRegs

end

-- Affine first m6 carry: checked generic and actual KRegs components.
section

set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexM6AffineHead
open ECDSAAdd ECDSAAdd.Arithmetic

def bit0 (n : Nat) : Bool := decide (n % 2 = 1)
def bit1 (n : Nat) : Bool := decide (n / 2 % 2 = 1)

theorem bit0_square (n : Nat) : bit0 (n^2) = bit0 n := by
  have hm := Nat.mod_lt n (by decide : 0 < 2)
  have he := Nat.pow_mod n 2 2
  unfold bit0
  rw [he]
  interval_cases n % 2 <;> norm_num

theorem head_sum_formula (a b : Nat) :
    (bit0 a && !bit0 (a+b)) = ((bit1 (a+b) ^^ bit1 a) ^^ bit1 b) := by
  unfold bit0 bit1
  have ha := Nat.mod_lt a (by decide : 0 < 2)
  have hb := Nat.mod_lt b (by decide : 0 < 2)
  have hs := Nat.mod_lt (a+b) (by decide : 0 < 2)
  have ha1 := Nat.mod_lt (a/2) (by decide : 0 < 2)
  have hb1 := Nat.mod_lt (b/2) (by decide : 0 < 2)
  have hs1 := Nat.mod_lt ((a+b)/2) (by decide : 0 < 2)
  by_cases a0 : a % 2 = 1 <;> by_cases b0 : b % 2 = 1 <;>
    by_cases s0 : (a+b) % 2 = 1 <;> by_cases a1 : a/2 % 2 = 1 <;>
    by_cases b1 : b/2 % 2 = 1 <;> by_cases s1 : (a+b)/2 % 2 = 1 <;>
    simp_all <;> omega

theorem square_head_formula (a b : Nat) :
    carryBit (bit0 (a^2)) (!bit0 ((a+b)^2)) false =
      ((bit1 (a+b) ^^ bit1 a) ^^ bit1 b) := by
  rw [bit0_square, bit0_square]
  simpa [carryBit] using head_sum_formula a b

def program (u v w c : Wire) : Program := [.CX u c, .CX v c, .CX w c]

theorem program_run (u v w c : Wire) (_hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (s : State) (m : List Bool) :
    run (program u v w c) m s =
      ⟨s.phase, writeBit s.basis c (s.basis c ^^ ((s.basis u ^^ s.basis v) ^^ s.basis w))⟩ := by
  simp only [program, run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q = c <;>
    simp_all [writeBit, Function.update]

theorem majority_eq (a b cin c u v w : Wire)
    (hn : [a,b,cin,c].Nodup) (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis a) (s.basis b) (s.basis cin) =
      ((s.basis u ^^ s.basis v) ^^ s.basis w)) :
    run (program u v w c) m s = run (majority a b cin c) m s := by
  rw [program_run u v w c hu hv hw, majority_correct a b cin c hn, hcarry]

theorem counts (u v w c : Wire) :
    toffoliCount (program u v w c) = 0 ∧ measurementCount (program u v w c) = 0 := by
  simp [program, toffoliCount, measurementCount]

theorem physical (u v w c : Wire) (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c) :
    GatePhysical (program u v w c) := by
  simp [program, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hu, hv, hw]

end ECDSAAdd.Entrant.CodexM6AffineHead


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexM6AffineHead
open ECDSAAdd ECDSAAdd.Arithmetic

def replaceHead (p : Program) (u v w c : Wire) : Program :=
  program u v w c ++ p.drop 6

theorem replaceHead_shape (a b cin c u v w : Wire) (tail : Program) :
    replaceHead (majority a b cin c ++ tail) u v w c = program u v w c ++ tail := by
  simp [replaceHead, majority]

theorem replaceHead_run (a b cin c u v w : Wire) (tail : Program)
    (hn : [a,b,cin,c].Nodup) (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis a) (s.basis b) (s.basis cin) =
      ((s.basis u ^^ s.basis v) ^^ s.basis w)) :
    run (replaceHead (majority a b cin c ++ tail) u v w c) m s =
      run (majority a b cin c ++ tail) m s := by
  rw [replaceHead_shape,
    ConstCarry.run_pre _ _ (counts u v w c).2,
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc a b cin c),
    majority_eq a b cin c u v w hn hu hv hw s [] hcarry]

theorem replaceHead_counts (a b cin c u v w : Wire) (tail : Program) :
    toffoliCount (replaceHead (majority a b cin c ++ tail) u v w c) + 1 =
      toffoliCount (majority a b cin c ++ tail) ∧
    measurementCount (replaceHead (majority a b cin c ++ tail) u v w c) =
      measurementCount (majority a b cin c ++ tail) := by
  rw [replaceHead_shape]
  simp [program, majority, toffoliCount, measurementCount, Nat.add_comm]

theorem replaceHead_slots (a b cin c u v w : Wire) (tail : Program) :
    Challenge.gateSlots (replaceHead (majority a b cin c ++ tail) u v w c) ≤
      Challenge.gateSlots (majority a b cin c ++ tail) := by
  rw [replaceHead_shape]
  simp [program, majority, Challenge.gateSlots, Challenge.instructionSlots]
  omega

theorem replaceHead_wires (a b cin c u v w : Wire) (tail : Program) :
    wires (replaceHead (majority a b cin c ++ tail) u v w c) ⊆
      wires (majority a b cin c ++ tail) ∪ {u,v,w} := by
  simp only [replaceHead_shape, wires_append]
  intro q hq
  simp [program, majority, wires, Instr.wires] at hq ⊢
  tauto

theorem replaceHead_physical (a b cin c u v w : Wire) (tail : Program)
    (hu : u ≠ c) (hv : v ≠ c) (hw : w ≠ c)
    (hp : GatePhysical (majority a b cin c ++ tail)) :
    GatePhysical (replaceHead (majority a b cin c ++ tail) u v w c) := by
  rw [replaceHead_shape, gatePhysical_append]
  exact ⟨physical u v w c hu hv hw, ((gatePhysical_append _ _).mp hp).2⟩

def addBase (top : Bool) (x y carry : List Wire) (cin : Wire) : Program :=
  if top then CodexM6Carry.addInPlace2KT true x y carry cin
  else ConstCarry.addInPlace2 x y carry cin

theorem addBase_shape (top : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 cin : Wire)
    (as bs cs : List Wire) :
    ∃ tail, addBase top (a0::a1::a2::a3::as) (b0::b1::b2::b3::bs) (c0::c1::cs) cin =
      majority a0 b0 cin c0 ++ tail := by
  cases top <;> simp only [addBase, Bool.false_eq_true, if_false, if_true,
    CodexM6Carry.addInPlace2KT, ConstCarry.addInPlace2, List.append_assoc] <;> exact ⟨_, rfl⟩


theorem addBase_has_head (top : Bool) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    ∃ tail, addBase top x y carry cin =
      majority (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) ++ tail := by
  rcases x with _|⟨a0,_|⟨a1,_|⟨a2,_|⟨a3,as⟩⟩⟩⟩ <;>
    rcases y with _|⟨b0,_|⟨b1,_|⟨b2,_|⟨b3,bs⟩⟩⟩⟩ <;>
    rcases carry with _|⟨c0,_|⟨c1,cs⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hx hy hc <;> try omega
  exact addBase_shape top _ _ _ _ _ _ _ _ _ _ _ _ _ _

def subAffine (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire) : Program :=
  notRegister y ++ replaceHead (addBase top x y carry cin) u v w (carry.getD 0 0) ++
    notRegister y

theorem subAffine_run (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length)
    (hn : [x.getD 0 0, y.getD 0 0, cin, carry.getD 0 0].Nodup) (hyn : y.Nodup)
    (hxn : x.getD 0 0 ∉ y) (hin : cin ∉ y)
    (hun : u ∉ y) (hvn : v ∉ y) (hwn : w ∉ y)
    (hu : u ≠ carry.getD 0 0) (hv : v ≠ carry.getD 0 0) (hw : w ≠ carry.getD 0 0)
    (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis (x.getD 0 0)) (!s.basis (y.getD 0 0)) (s.basis cin) =
      ((s.basis u ^^ s.basis v) ^^ s.basis w)) :
    run (subAffine top u v w x y carry cin) m s =
      run (notRegister y ++ addBase top x y carry cin ++ notRegister y) m s := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have hy0 : y.getD 0 0 ∈ y := by
    cases y with
    | nil => simp at hy
    | cons b bs => simp
  have hct := replaceHead_counts (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [subAffine, List.append_assoc]
  rw [ConstCarry.run_pre _ _ (ConstCarry.notRegister_mc _),
    ConstCarry.run_pre _ _ (ConstCarry.notRegister_mc _), he,
    run_append, run_append (majority _ _ _ _ ++ tail), hct.2]
  congr 1
  apply replaceHead_run _ _ _ _ _ _ _ _ hn hu hv hw
  rw [notRegister_correct y hyn s []]
  simpa only [if_neg hxn, if_pos hy0, if_neg hin, if_neg hun, if_neg hvn, if_neg hwn] using hcarry


theorem subAffine_counts (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (subAffine top u v w x y carry cin) + 1 =
      toffoliCount (notRegister y ++ addBase top x y carry cin ++ notRegister y) ∧
    measurementCount (subAffine top u v w x y carry cin) =
      measurementCount (notRegister y ++ addBase top x y carry cin ++ notRegister y) := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have h := replaceHead_counts (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [toffoliCount_append, measurementCount_append] at h
  simp only [subAffine, he, toffoliCount_append, measurementCount_append]
  constructor <;> omega

theorem subAffine_slots (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    Challenge.gateSlots (subAffine top u v w x y carry cin) ≤
      Challenge.gateSlots (notRegister y ++ addBase top x y carry cin ++ notRegister y) := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have h := replaceHead_slots (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [Challenge.gateSlots_append] at h
  simp only [subAffine, he, Challenge.gateSlots_append]
  omega

theorem subAffine_wires (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length) :
    wires (subAffine top u v w x y carry cin) ⊆
      wires (notRegister y ++ addBase top x y carry cin ++ notRegister y) ∪ {u,v,w} := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  have h := replaceHead_wires (x.getD 0 0) (y.getD 0 0) cin (carry.getD 0 0) u v w tail
  simp only [subAffine, he, wires_append]
  intro q hq
  have hq' := @h q
  simp only [wires_append, Finset.mem_union] at hq hq' ⊢
  tauto

theorem subAffine_physical (top : Bool) (u v w : Wire) (x y carry : List Wire) (cin : Wire)
    (hx : 4 ≤ x.length) (hy : 4 ≤ y.length) (hc : 2 ≤ carry.length)
    (hu : u ≠ carry.getD 0 0) (hv : v ≠ carry.getD 0 0) (hw : w ≠ carry.getD 0 0)
    (hp : GatePhysical (notRegister y ++ addBase top x y carry cin ++ notRegister y)) :
    GatePhysical (subAffine top u v w x y carry cin) := by
  obtain ⟨tail, he⟩ := addBase_has_head top x y carry cin hx hy hc
  simp only [subAffine, he, gatePhysical_append] at hp ⊢
  exact ⟨⟨hp.1.1, replaceHead_physical _ _ _ _ _ _ _ _ hu hv hw ((gatePhysical_append _ _).mpr hp.1.2)⟩, hp.2⟩

end ECDSAAdd.Entrant.CodexM6AffineHead


set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexM6AffineHead
open ECDSAAdd ECDSAAdd.Arithmetic

theorem selected_mem (r : List Wire) (i : Nat) (hi : i < r.length) : r.getD i 0 ∈ r := by
  induction r generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih _ (by simpa using hi))

theorem selected_count (r : List Wire) (i : Nat) (hi : i < r.length) (q : Wire) :
    [r.getD i 0].count q ≤ r.count q := by
  exact (List.singleton_sublist.mpr (selected_mem r i hi)).count_le q

theorem bit0_value (r : List Wire) (s : BasisState) (h : 0 < r.length) :
    s (r.getD 0 0) = bit0 (regValue r s) := by
  have hv := regValue_bit r 0 0 s h
  cases he : s (r.getD 0 0) <;> simp_all [bit0]

end CodexM6AffineHead

namespace KRegs
open ECDSAAdd ECDSAAdd.Arithmetic CodexM6AffineHead

def m6h (R : KRegs) : Program :=
  subAffine (decide R.trimOK) (R.S.getD 1 0) (R.lo.getD 1 0) (R.hi.getD 1 0)
    (R.dlo ++ R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem m6k_as_base (R : KRegs) : R.m6k =
    notRegister R.T ++ addBase (decide R.trimOK) (R.dlo ++ R.zA) R.T
      (R.carry.take (R.T.length-1)) R.cin ++ notRegister R.T := by
  by_cases ht : R.trimOK <;>
    simp [m6k, addBase, ht, CodexM6Carry.subInPlace2KT, m6c, ConstCarry.subInPlace2]

theorem m6h_counts (R : KRegs) (w : R.W) :
    toffoliCount R.m6h + 1 = toffoliCount R.m6k ∧
    measurementCount R.m6h = measurementCount R.m6k := by
  rw [m6k_as_base]
  have l := R.m6k_lens w
  exact subAffine_counts _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)

theorem m6h_slots (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.m6h ≤ Challenge.gateSlots R.m6k := by
  rw [m6k_as_base]
  have l := R.m6k_lens w
  exact subAffine_slots _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)

theorem m6h_wires (R : KRegs) (w : R.W) :
    wires R.m6h ⊆ wires R.m6k ∪ {R.S.getD 1 0, R.lo.getD 1 0, R.hi.getD 1 0} := by
  rw [m6k_as_base]
  have l := R.m6k_lens w
  exact subAffine_wires _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)

theorem m6h_lengths (R : KRegs) (w : R.W) :
    1 < R.S.length ∧ 1 < R.lo.length ∧ 1 < R.hi.length := by
  have l := R.lens w
  have h4 := w.h4
  have hh := w.hh
  have hS := w.S
  omega

theorem m6h_run (R : KRegs) (w : R.W) (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hcarry : carryBit (s.basis ((R.dlo ++ R.zA).getD 0 0))
      (!s.basis (R.T.getD 0 0)) (s.basis R.cin) =
        ((s.basis (R.S.getD 1 0) ^^ s.basis (R.lo.getD 1 0)) ^^ s.basis (R.hi.getD 1 0))) :
    run R.m6h m s = run R.m6k m s := by
  have l := R.m6k_lens w
  have l2 := R.m6h_lengths w
  have mx := selected_mem (R.dlo ++ R.zA) 0 (by omega)
  have my := selected_mem R.T 0 (by omega)
  have mc := selected_mem (R.carry.take (R.T.length-1)) 0 (by omega)
  have mu := selected_mem R.S 1 l2.1
  have mv := selected_mem R.lo 1 l2.2.1
  have mw := selected_mem R.hi 1 l2.2.2
  rw [m6k_as_base]
  apply subAffine_run _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega)
  · apply knd hn
    intro q
    have c := R.counts q
    have cx := selected_count (R.dlo ++ R.zA) 0 (by omega) q
    have cy := selected_count R.T 0 (by omega) q
    have cc := selected_count (R.carry.take (R.T.length-1)) 0 (by omega) q
    simp only [all, List.count_cons, List.count_append, List.count_nil] at cx cy cc ⊢
    omega
  · exact knd hn (fun q => by simp only [all, List.count_cons, List.count_append]; omega)
  · exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mx
  · have h : R.cin ∈ [R.cin] := by simp
    exact kdis hn (fun q => by simp only [all, List.count_cons, List.count_append, List.count_nil]; omega) _ h
  · exact kdis hn (fun q => by simp only [all, List.count_cons, List.count_append]; omega) _ mu
  · exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mv
  · exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mw
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mu (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mv (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mw (he ▸ mc)
  · exact hcarry


theorem m6h_square_run (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (s : State) (m : List Bool)
    (hclean : ∀ q ∈ R.carry.take (R.T.length - 1), s.basis q = false)
    (hi : s.basis R.cin = false)
    (a b : Nat) (ha : a < 2^R.h) (hb : b < 2^(R.bank.length-R.h))
    (hT : regValue R.T s.basis = (a+b)^2)
    (hA : regValue R.dlo s.basis = a^2)
    (hz : regValue R.zA s.basis = 0)
    (hS : regValue R.S s.basis = a+b)
    (hlo : regValue R.lo s.basis = a)
    (hhi : regValue R.hi s.basis = b) :
    run R.m6h m s = run R.m6 m s := by
  trans run R.m6k m s
  · apply R.m6h_run w hn s m
    have l := R.m6k_lens w
    have la := R.m6c_lens w
    have lc := R.m6h_lengths w
    rw [List.getD_append _ _ _ _ (by omega),
      bit0_value R.dlo s.basis (by omega), bit0_value R.T s.basis (by omega), hA, hT, hi,
      ConstCarry.bit1_value R.S s.basis (by omega),
      ConstCarry.bit1_value R.lo s.basis (by omega),
      ConstCarry.bit1_value R.hi s.basis (by omega), hS, hlo, hhi]
    exact square_head_formula a b
  · apply R.m6k_square_run w _ s m hclean hi a b ha hb hT hA hz
    exact knd hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega)

theorem m6h_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (hp : GatePhysical R.m6) : GatePhysical R.m6h := by
  have l := R.m6k_lens w
  have l2 := R.m6h_lengths w
  have mc := selected_mem (R.carry.take (R.T.length-1)) 0 (by omega)
  have mu := selected_mem R.S 1 l2.1
  have mv := selected_mem R.lo 1 l2.2.1
  have mw := selected_mem R.hi 1 l2.2.2
  have old := R.m6k_physical w hn hp
  rw [m6k_as_base] at old
  apply subAffine_physical _ _ _ _ _ _ _ _ (by omega) l.2.2 (by omega) _ _ _ old
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mu (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mv (he ▸ mc)
  · intro he
    exact kdis hn (fun q => by have c := R.counts q; simp only [all, List.count_cons, List.count_append]; omega) _ mw (he ▸ mc)

theorem m6h_support (R : KRegs) (w : R.W) (hp : wires R.m6 ⊆ R.all.toFinset) :
    wires R.m6h ⊆ R.all.toFinset := by
  have l := R.m6h_lengths w
  intro q hq
  have h := R.m6h_wires w hq
  rcases Finset.mem_union.mp h with h | h
  · exact hp (R.m6k_wires w h)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · subst q
      have hu := selected_mem R.S 1 l.1
      simp only [all, List.mem_toFinset, List.mem_cons, List.mem_append]
      tauto
    · subst q
      have hv := List.mem_of_mem_take (selected_mem R.lo 1 l.2.1)
      simp only [all, List.mem_toFinset, List.mem_cons, List.mem_append]
      tauto
    · subst q
      have hw := List.mem_of_mem_drop (selected_mem R.hi 1 l.2.2)
      simp only [all, List.mem_toFinset, List.mem_cons, List.mem_append]
      tauto

end KRegs
end ECDSAAdd.Entrant

set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic CodexM6AffineHead

theorem m6h_controls_smk (R : KRegs) (w : R.W) :
    ({R.S.getD 1 0, R.lo.getD 1 0, R.hi.getD 1 0} : Finset Wire) ⊆ wires R.smk := by
  have l := R.lens w
  have lc := R.m6h_lengths w
  have hh := w.hh
  have h4 := w.h4
  have hSl := w.S
  have hcl := w.carry
  have hw4 := addInPlace_wires (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega)
    (by simp only [List.length_take]; omega)
  have hw3 := copyRegister_wires none R.lo (R.S.take R.h) (by omega)
  have he : R.lo.isEmpty = false := by
    cases hlo : R.lo with
    | nil => simp [hlo] at lc
    | cons a as => rfl
  rw [he] at hw3
  simp only [Bool.false_eq_true, if_false, Option.toList_none, List.nil_append] at hw3
  simp only [smk, wires_append, m3, m4, hw3, hw4]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with hq | hq | hq
  · subst q
    have hu := selected_mem R.S 1 lc.1
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · subst q
    have hv := selected_mem R.lo 1 lc.2.1
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  · subst q
    have hw := selected_mem R.hi 1 lc.2.2
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto

theorem m6h_wires_smk (R : KRegs) (w : R.W) :
    wires R.m6h ⊆ wires R.m6 ∪ wires R.smk :=
  (R.m6h_wires w).trans (Finset.union_subset_union (R.m6k_wires w) (R.m6h_controls_smk w))

end ECDSAAdd.Entrant.KRegs

end

-- First c6 carry is already present in target bit1.
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.CodexC6Head
open ECDSAAdd ECDSAAdd.Arithmetic

def add3h : List Wire → List Wire → List Wire → Wire → Program
  | a0 :: a1 :: a2 :: as, b0 :: b1 :: b2 :: bs, c0 :: c1 :: cs, cin =>
      [.CX b1 c0] ++ ([.CX b1 c1] ++ addInPlace (a2 :: as) (b2 :: bs) cs c1 ++
        eraseCarry a1 b1 c0 c1 ++ [.CX a1 b1, .CX c0 b1]) ++
        eraseCarry a0 b0 cin c0 ++ [.CX a0 b0, .CX cin b0]
  | x, y, c, cin => ConstCarry.addInPlace3 x y c cin

theorem head_eq (a b cin c u : Wire) (hn : [a,b,cin,c].Nodup)
    (s : State) (m : List Bool)
    (hb : s.basis u = carryBit (s.basis a) (s.basis b) (s.basis cin)) :
    run [.CX u c] m s = run (majority a b cin c) m s := by
  rw [majority_correct a b cin c hn s m]
  simp only [run, hb]

theorem run_shape (a0 a1 a2 b0 b1 b2 c0 c1 cin : Wire) (as bs cs : List Wire)
    (hn : [a0,b0,cin,c0].Nodup) (s : State) (m : List Bool)
    (hb : s.basis b1 = carryBit (s.basis a0) (s.basis b0) (s.basis cin)) :
    run (add3h (a0::a1::a2::as) (b0::b1::b2::bs) (c0::c1::cs) cin) m s =
      run (ConstCarry.addInPlace3 (a0::a1::a2::as) (b0::b1::b2::bs) (c0::c1::cs) cin) m s := by
  simp only [add3h, ConstCarry.addInPlace3, List.append_assoc]
  rw [ConstCarry.run_pre _ _ (by simp [measurementCount]),
    ConstCarry.run_pre _ _ (ConstCarry.majority_mc _ _ _ _),
    head_eq _ _ _ _ _ hn s [] hb]

theorem run_eq (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x++y++carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length)
    (s : State) (m : List Bool)
    (hb : s.basis (y.getD 1 0) = carryBit (s.basis (x.getD 0 0))
      (s.basis (y.getD 0 0)) (s.basis cin)) :
    run (add3h x y carry cin) m s = run (ConstCarry.addInPlace3 x y carry cin) m s := by
  match x,y,carry,hx,hy,hc with
  | a0::a1::a2::as, b0::b1::b2::bs, c0::c1::cs, _,_,_ =>
    simp only [List.getD_cons_succ,List.getD_cons_zero] at hb
    apply run_shape _ _ _ _ _ _ _ _ _ _ _ _ _ s m hb
    exact knd hn (fun q => by simp only [List.count_cons,List.count_nil,List.count_append]; omega)

theorem resources (x y carry : List Wire) (cin : Wire)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length) :
    toffoliCount (add3h x y carry cin)+1 = toffoliCount (ConstCarry.addInPlace3 x y carry cin) ∧
    measurementCount (add3h x y carry cin) = measurementCount (ConstCarry.addInPlace3 x y carry cin) ∧
    wires (add3h x y carry cin) ⊆ wires (ConstCarry.addInPlace3 x y carry cin) ∧
    Challenge.gateSlots (add3h x y carry cin) ≤ Challenge.gateSlots (ConstCarry.addInPlace3 x y carry cin) := by
  match x,y,carry,hx,hy,hc with
  | a0::a1::a2::as, b0::b1::b2::bs, c0::c1::cs, _,_,_ =>
    refine ⟨?_,?_,?_,?_⟩
    · simp [add3h,ConstCarry.addInPlace3,majority,toffoliCount,Nat.add_comm]
    · simp [add3h,ConstCarry.addInPlace3,majority,measurementCount]
    · simp only [add3h,ConstCarry.addInPlace3,wires_append]
      intro q hq
      simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] at hq
      simp only [majority,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty]
      tauto
    · simp only [add3h,ConstCarry.addInPlace3,Challenge.gateSlots_append]
      simp [majority,Challenge.gateSlots,Challenge.instructionSlots]

theorem physical (x y carry : List Wire) (cin : Wire)
    (hn : (cin :: (x++y++carry)).Nodup)
    (hx : 3 ≤ x.length) (hy : 3 ≤ y.length) (hc : 2 ≤ carry.length)
    (hp : GatePhysical (ConstCarry.addInPlace3 x y carry cin)) :
    GatePhysical (add3h x y carry cin) := by
  match x,y,carry,hx,hy,hc with
  | a0::a1::a2::as, b0::b1::b2::bs, c0::c1::cs, _,_,_ =>
    have hbc : b1 ≠ c0 := by
      intro he
      have hd := kdis (r := [b1]) (t := [c0]) hn (fun q => by
        simp only [List.count_cons,List.count_nil,List.count_append]; omega) b1 (by simp)
      exact hd (by simpa using he)
    have hp' : GatePhysical [.CX b1 c0] := by
      simp [GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, hbc]
    simp only [add3h,ConstCarry.addInPlace3,gatePhysical_append] at hp ⊢
    tauto


end ECDSAAdd.Entrant.CodexC6Head

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic

def c6h (R : KRegs) : Program :=
  CodexC6Head.add3h (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin

theorem c6h_counts (R : KRegs) (w : R.W) :
    toffoliCount R.c6h + 1 = toffoliCount R.c6c ∧
    measurementCount R.c6h = measurementCount R.c6c := by
  have l := R.m6c_lens w
  have h := CodexC6Head.resources (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin l.1 l.2.1 l.2.2.1
  exact ⟨h.1,h.2.1⟩

theorem c6h_wires (R : KRegs) (w : R.W) : wires R.c6h ⊆ wires R.c6 := by
  have l := R.m6c_lens w
  have h := CodexC6Head.resources (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin l.1 l.2.1 l.2.2.1
  exact h.2.2.1.trans (R.c6c_wires w)

theorem c6h_slots (R : KRegs) (w : R.W) :
    Challenge.gateSlots R.c6h ≤ Challenge.gateSlots R.c6 := by
  have l := R.m6c_lens w
  have h := CodexC6Head.resources (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin l.1 l.2.1 l.2.2.1
  exact h.2.2.2.trans (R.c6c_slots w)

theorem c6h_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup)
    (hp : GatePhysical R.c6) : GatePhysical R.c6h := by
  have l := R.m6c_lens w
  apply CodexC6Head.physical _ _ _ _ _ l.1 l.2.1 l.2.2.1 (R.c6c_physical w hp)
  exact knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega)

theorem c6h_run (R : KRegs) (w : R.W)
    (hn : (R.cin::((R.dlo++R.zA)++R.T++R.carry.take (R.T.length-1))).Nodup)
    (s : State) (m : List Bool) (hc0 : ∀q∈R.carry.take (R.T.length-1),s.basis q=false)
    (hi : s.basis R.cin=false)
    (hb : s.basis (R.T.getD 1 0)=(s.basis (R.dlo.getD 0 0) && s.basis (R.T.getD 0 0))) :
    run R.c6h m s = run R.c6 m s := by
  trans run R.c6c m s
  · have l := R.m6c_lens w
    apply CodexC6Head.run_eq _ _ _ _ hn l.1 l.2.1 l.2.2.1
    rw [hb,List.getD_append _ _ _ _ (by omega),hi]
    cases s.basis (R.dlo.getD 0 0) <;> cases s.basis (R.T.getD 0 0) <;> rfl
  · exact R.c6c_run w hn s m hc0 hi hb

end ECDSAAdd.Entrant.KRegs

end

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic KG
variable (K : KG)
def make : Program := K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
def clear : Program := K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c
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
  obtain ⟨a7,r8,e8⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z) K.R.scl1591 m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k) K.R.m8z a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h) K.R.m7k a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.Q1++K.Q2++K.R.smk++K.Q5) K.R.m6h a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.Q1++K.Q2++K.R.smk) K.Q5 a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.Q1++K.Q2) K.R.smk a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.Q1 K.Q2 a2 s
  rw [show (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591 from rfl,e8,e7,e6,e5,e4,e3,e2]
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
  have st6 : (run K.R.m6h r5 s5).phase=s5.phase ∧ regValue K.R.T (run K.R.m6h r5 s5).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.m6h r5 s5).basis q=s5.basis q := by
    rw [K.R.m6h_square_run w hR
      s5 r5
      (fun q hq => (regValue_zero _ _).mp ((outV s5 G5 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      a b aLt bLt st5.2.1 dlo5
      ((outV s5 G5 K.R.zA (by intro q h; simp [mt h])).trans
        (zero K.R.zA K.R.z hz0 (fun q h =>
          List.mem_of_mem_take (show q∈K.R.z.take (K.R.T.length-2*K.R.h) from h))))
      S5
      ((outV s5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha)
      ((outV s5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb)]
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
  generalize run K.R.m6h r5 s5=s6 at st6 ⊢
  have G6 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s6.basis q=s.basis q :=
    fun q h hS hT x => (st6.2.2 q hT).trans (G5 q h hS hT x)
  have dlo6 : regValue K.R.dlo s6.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo5
  have dhi6 : regValue K.R.dhi s6.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st6.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi5
  -- T -= b^2
  have xv6 : regValue (K.R.dhi++K.R.zB) s6.basis=b^2 := by
    rw [regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h))]; simp
  have st7 : (run K.R.m7k r6 s6).phase=s6.phase ∧ regValue K.R.T (run K.R.m7k r6 s6).basis=2*a*b ∧
      ∀q,q∉K.R.T → (run K.R.m7k r6 s6).basis q=s6.basis q := by
    have hcl7 : ∀q∈K.R.carry.take (K.R.T.length-1),s6.basis q=false :=
      (fun q hq => (regValue_zero _ _).mp ((outV s6 G6 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
    have hnc7 : (s6.basis ((K.R.dhi++K.R.zB).headD 0) && !s6.basis (K.R.T.headD 0))=false :=
      (by
        have hT := LowZero.head_bit K.R.T [] s6.basis (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [LowZero.head_bit K.R.dhi K.R.zB s6.basis (K.R.dhi_ne w),hT,dhi6,st6.2.1,
          show 2*a*b+b^2=b^2+2*(a*b) by ring,Nat.add_mul_mod_self_left]
        cases decide (b^2%2=1) <;> rfl)
    have hi7 : s6.basis K.R.cin=false :=
      ((G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    have h17 : s6.basis ((K.R.dhi++K.R.zB).tail.headD 0)=false :=
      (by rw [ECDSAAdd.Entrant.KRegs.bit1 K.R.dhi K.R.zB s6.basis (K.R.dhi_two w),dhi6,ECDSAAdd.Entrant.KRegs.sq_bit1]; rfl)
    have hA7 : K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis<2^(K.R.T.length-1) :=
      (fun _ => by rw [xv6,hTl,hSl]; exact ECDSAAdd.Entrant.KRegs.sq_trim_bound K.R.bank.length K.R.h b bLt)
    have hb7 : K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis≤regValue K.R.T s6.basis%2^(K.R.T.length-1) :=
      (fun tc => by
        have tb := ECDSAAdd.Entrant.KRegs.trim_bound K.R.bank.length K.R.h a b tc aLt bLt
        rw [xv6,st6.2.1,hTl,hSl,Nat.mod_eq_of_lt tb]; omega)
    have hab7 : a*b<2^K.R.bank.length := by
      have e : 2^K.R.bank.length=2^K.R.h*2^(K.R.bank.length-K.R.h) := by rw [←pow_add]; congr 1; omega
      rw [e]; exact Nat.mul_lt_mul'' aLt bLt
    have p2b : 2^(K.R.bank.length+1)=2*2^K.R.bank.length := by rw [pow_succ]; ring
    have HT : K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis<2^(K.R.T.length-1) ∧
        regValue (K.R.dhi++K.R.zB) s6.basis≤regValue K.R.T s6.basis%2^(K.R.T.length-1) ∧
        regValue K.R.T s6.basis%2^(K.R.T.length-1)<regValue (K.R.dhi++K.R.zB) s6.basis+2^(K.R.T.length-2) := by
      intro tc
      refine ⟨hA7 tc,hb7 tc,?_⟩
      have tc' : 2*K.R.h+1≤K.R.bank.length := tc
      have tb := ECDSAAdd.Entrant.KRegs.trim_bound K.R.bank.length K.R.h a b tc aLt bLt
      have hpw : 2^(K.R.bank.length+1)≤2^(K.R.T.length-2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [xv6,st6.2.1,hTl,hSl,Nat.mod_eq_of_lt tb]
      rw [hTl,hSl] at hpw
      rw [show 2*a*b+b^2=2*(a*b)+b^2 by ring]; omega
    have HF : ¬K.R.trimOK → regValue (K.R.dhi++K.R.zB) s6.basis≤regValue K.R.T s6.basis ∧
        regValue K.R.T s6.basis<regValue (K.R.dhi++K.R.zB) s6.basis+2^(K.R.T.length-1) := by
      intro _
      have hpw : 2^(K.R.bank.length+1)≤2^(K.R.T.length-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [xv6,st6.2.1,show 2*a*b+b^2=2*(a*b)+b^2 by ring]
      constructor <;> omega
    rw [K.R.m7k_run w hR s6 r6 hcl7 hnc7 hi7 h17 HT HF]
    obtain ⟨p,f,v⟩ := K.R.m7t_correct w hR s6 r6 hcl7 hnc7 hi7 h17 hA7 hb7
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi6,outV s6 G6 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      st6.2.1,G6 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by omega) (by rw [ex] at sqLt; omega)]; omega
  generalize run K.R.m7k r6 s6=s7 at st7 ⊢
  have G7 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → s7.basis q=s.basis q :=
    fun q h hS hT x => (st7.2.2 q hT).trans (G6 q h hS hT x)
  have dlo7 : regValue K.R.dlo s7.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo6
  have dhi7 : regValue K.R.dhi s7.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st7.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi6
  have D7 : regValue K.R.dst s7.basis=a^2+2^(2*K.R.h)*b^2 := by rw [K.R.dst_value w,dlo7,dhi7]
  -- dst += 2^h * 2ab
  have st8 : (run K.R.m8z r7 s7).phase=s7.phase ∧
      regValue K.R.dmid (run K.R.m8z r7 s7).basis=(2*a*b+(a^2+2^(2*K.R.h)*b^2)/2^K.R.h)%2^(2*K.R.bank.length-K.R.h) ∧
      ∀q,q∉K.R.dmid → (run K.R.m8z r7 s7).basis q=s7.basis q := by
    obtain ⟨p,f,v⟩ := K.R.m8z_correct w hR s7 r7 (a*b)
      (fun q hq => (regValue_zero _ _).mp ((outV s7 G7 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [st7.2.1]; ring) ((G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,st7.2.1,outV s7 G7 K.R.zM (by intro q h; simp [mt h]),zero K.R.zM K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take (K.R.dmid.length-K.R.T.length) from h)),
      show regValue K.R.dmid s7.basis=regValue K.R.dst s7.basis/2^K.R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div K.R.dst K.R.h (by omega) s7.basis,D7,
      G7 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0,L4]
    simp
  generalize run K.R.m8z r7 s7=s8 at st8 ⊢
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
  have st9 := K.R.scl1591_correct w hR s8 r8
    (by rw [S8,(outV s8 G8 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV s8 G8 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV s8 G8 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV s8 G8 K.R.carry (by intro q h; simp [h])).trans hc0) ((G8 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r8 s8=s9 at st9 ⊢
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
  obtain ⟨a7,r8,e8⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c) K.Q1c m s
  obtain ⟨a6,r7,e7⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591) K.Q2c a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c) K.R.scl1591 a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h) K.Q5c a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (K.R.smk++K.R.c8z++K.R.c7t) K.R.c6h a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (K.R.smk++K.R.c8z) K.R.c7t a3 s
  obtain ⟨r1,r2,e2⟩ := kseq K.R.smk K.R.c8z a2 s
  rw [show (clear K)=K.R.smk++K.R.c8z++K.R.c7t++K.R.c6h++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c from rfl,e8,e7,e6,e5,e4,e3,e2]
  -- rebuild S
  have st1 := K.R.smk_correct w hR s r1 hS0 hz0 hc0 hi0
  rw [ha,hb] at st1
  generalize run K.R.smk r1 s=t1 at st1 ⊢
  have G1 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t1.basis q=s.basis q := fun q _ h _ _ => st1.2.2 q h
  have T1 : regValue K.R.T t1.basis=2*a*b := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hT0
  have D1 : regValue K.R.dst t1.basis=(a+2^K.R.h*b)^2 := (regValue_congr _ _ _ (fun q hq => st1.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans hd0
  -- dst -= 2^h * 2ab
  have st2 : (run K.R.c8z r2 t1).phase=t1.phase ∧
      regValue K.R.dst (run K.R.c8z r2 t1).basis=a^2+2^(2*K.R.h)*b^2 ∧
      ∀q,q∉K.R.dmid → (run K.R.c8z r2 t1).basis q=t1.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c8z_correct w hR t1 r2
      (fun q hq => (regValue_zero _ _).mp ((outV t1 G1 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by rw [LowZero.head_false_of_even K.R.T K.R.zM t1.basis (a*b) (by rw [T1]; ring) (K.R.T_ne w)]; rfl)
      ((G1 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
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
  generalize run K.R.c8z r2 t1=t2 at st2 ⊢
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
  have xv2 : regValue (K.R.dhi++K.R.zB) t2.basis=b^2 := by
    rw [regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h))]; simp
  have st3 : (run K.R.c7t r3 t2).phase=t2.phase ∧ regValue K.R.T (run K.R.c7t r3 t2).basis=2*a*b+b^2 ∧
      ∀q,q∉K.R.T → (run K.R.c7t r3 t2).basis q=t2.basis q := by
    obtain ⟨p,f,v⟩ := K.R.c7t_correct w hR t2 r3
      (fun q hq => (regValue_zero _ _).mp ((outV t2 G2 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq)
      (by
        have hT := LowZero.head_false_of_even K.R.T [] t2.basis (a*b) (by rw [T2]; ring) (K.R.T_ne w)
        rw [List.append_nil] at hT
        rw [hT]; exact Bool.and_false _)
      ((G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      (by rw [ECDSAAdd.Entrant.KRegs.bit1 K.R.dhi K.R.zB t2.basis (K.R.dhi_two w),dhi2,ECDSAAdd.Entrant.KRegs.sq_bit1]; rfl)
      (fun _ => by rw [xv2,hTl,hSl]; exact ECDSAAdd.Entrant.KRegs.sq_trim_bound K.R.bank.length K.R.h b bLt)
      (fun tc => by
        have tb := ECDSAAdd.Entrant.KRegs.trim_bound K.R.bank.length K.R.h a b tc aLt bLt
        rw [xv2,T2,hTl,hSl,Nat.mod_eq_of_lt (by omega)]; omega)
    refine ⟨p,?_,f⟩
    rw [v,regValue_append,dhi2,outV t2 G2 K.R.zB (by intro q h; simp [mt h]),zero K.R.zB K.R.z hz0 (fun q h => List.mem_of_mem_take (show q∈K.R.z.take 2 from h)),
      T2,G2 _ cinO.1 cinO.2.1 cinO.2.2 cinX,hi0]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false]
    rw [Nat.mod_eq_of_lt (by rw [ex] at sqLt; omega)]; ring
  generalize run K.R.c7t r3 t2=t3 at st3 ⊢
  have G3 : ∀q,q∉K.R.dst → q∉K.R.S → q∉K.R.T → q∉K.X → t3.basis q=s.basis q :=
    fun q h hS hT x => (st3.2.2 q hT).trans (G2 q h hS hT x)
  have dlo3 : regValue K.R.dlo t3.basis=a^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dlo2
  have dhi3 : regValue K.R.dhi t3.basis=b^2 := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans dhi2
  have S3 : regValue K.R.S t3.basis=a+b := (regValue_congr _ _ _ (fun q hq => st3.2.2 q (kdis hn (fun q => by have c := K.R.counts q; simp only [all,X,KRegs.all,List.count_cons,List.count_append]; omega) q hq))).trans S2
  -- T += a^2
  have st4 : (run K.R.c6h r4 t3).phase=t3.phase ∧ regValue K.R.T (run K.R.c6h r4 t3).basis=(a+b)^2 ∧
      ∀q,q∉K.R.T → (run K.R.c6h r4 t3).basis q=t3.basis q := by
    rw [K.R.c6h_run w (knd hR (fun q => by have c := K.R.counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      t3 r4 (fun q hq => (regValue_zero _ _).mp ((outV t3 G3 _ (by intro q h; simp [mt h])).trans
        (zero _ _ hc0 (fun q h => mt h))) q hq) ((G3 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
      (K.R.c6c_bits w t3.basis a b st3.2.1 dlo3)]
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
  generalize run K.R.c6h r4 t3=t4 at st4 ⊢
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
  have st6 := K.R.scl1591_correct w hR t5 r6
    (by rw [S5,(outV t5 G5 K.R.lo (fun q h => Or.inl (mt h))).trans ha,(outV t5 G5 K.R.hi (fun q h => Or.inl (md h))).trans hb])
    ((outV t5 G5 K.R.z (by intro q h; simp [h])).trans hz0)
    ((outV t5 G5 K.R.carry (by intro q h; simp [h])).trans hc0) ((G5 _ cinO.1 cinO.2.1 cinO.2.2 cinX).trans hi0)
  generalize run K.R.scl1591 r6 t5=t6 at st6 ⊢
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
    toffoliCount (make K)+6+2*(if K.R.trimOK then 1 else 0)=toffoliCount K.Q1+toffoliCount K.Q2+toffoliCount K.Q5+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (make K)+(if K.R.trimOK then 1 else 0)=measurementCount K.Q1+measurementCount K.Q2+measurementCount K.Q5+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mz := K.R.m8z_counts w
  have mz7 := K.R.m7t_counts w
  have mk7 := K.R.m7k_counts w
  have mc6 := K.R.m6c_counts w
  have mk6 := K.R.m6k_counts w
  have mh6 := K.R.m6h_counts w
  have e : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6h++K.R.m7k++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have q1 := p.2.2.2.2.1
  have q2 := p.2.2.2.2.2.1
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem clear_counts (w : K.R.W) :
    toffoliCount (clear K)+5+(if K.R.trimOK then 1 else 0)=toffoliCount K.Q1c+toffoliCount K.Q2c+toffoliCount K.Q5c+(kextra K.R.bank.length K.R.h-(K.R.bank.length-K.R.h)) ∧
    measurementCount (clear K)+(if K.R.trimOK then 1 else 0)=measurementCount K.Q1c+measurementCount K.Q2c+measurementCount K.Q5c+
      kextra K.R.bank.length K.R.h := by
  have p := K.R.piece_counts w
  have z := K.R.scl1591_counts w
  have mc8 := K.R.c8z_counts w
  have mc7 := K.R.c7t_counts w
  have cc6 := K.R.c6c_counts w
  have ch6 := K.R.c6h_counts w
  have e : (clear K)=K.R.smk++(K.R.c8z++K.R.c7t++K.R.c6h)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have q1 := p.2.2.2.2.2.2.1
  have q2 := p.2.2.2.2.2.2.2
  simp only [toffoliCount_append,measurementCount_append] at q1 q2
  rw [e]
  simp only [toffoliCount_append,measurementCount_append,p.1,p.2.1,z.1,z.2,kextra]
  constructor <;> omega

theorem r_sub (q : Wire) (h : q∈K.R.all.toFinset) : q∈K.all.toFinset := by
  simp only [List.mem_toFinset,all,List.mem_append] at h ⊢; exact Or.inl h

theorem steps_support (w : K.R.W)
    (s1 : ECDSAAdd.wires K.Q1⊆K.all.toFinset) (s1c : ECDSAAdd.wires K.Q1c⊆K.all.toFinset)
    (s2 : ECDSAAdd.wires K.Q2⊆K.all.toFinset) (s2c : ECDSAAdd.wires K.Q2c⊆K.all.toFinset)
    (s5 : ECDSAAdd.wires K.Q5⊆K.all.toFinset) (s5c : ECDSAAdd.wires K.Q5c⊆K.all.toFinset) :
    ECDSAAdd.wires (make K)⊆K.all.toFinset ∧ ECDSAAdd.wires (clear K)⊆K.all.toFinset := by
  have p := K.R.piece_support w
  have sc := K.R.scl1591_support w
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6h++K.R.m7k++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7t++K.R.c6h)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have lift {P : Program} (h : ECDSAAdd.wires P⊆K.R.all.toFinset) : ECDSAAdd.wires P⊆K.all.toFinset :=
    fun q hq => K.r_sub q (h hq)
  have ap {P Q : Program} (h1 : ECDSAAdd.wires P⊆K.all.toFinset) (h2 : ECDSAAdd.wires Q⊆K.all.toFinset) :
      ECDSAAdd.wires (P++Q)⊆K.all.toFinset := by rw [wires_append]; exact Finset.union_subset h1 h2
  have pz : ECDSAAdd.wires (K.R.m6h++K.R.m7k++K.R.m8z)⊆K.R.all.toFinset := by
    have h := p.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨K.R.m6h_support w h.1.1,(K.R.m7k_wires w).trans h.1.2⟩,(K.R.m8z_wires w).trans h.2⟩
  have cz : ECDSAAdd.wires (K.R.c8z++K.R.c7t++K.R.c6h)⊆K.R.all.toFinset := by
    have h := p.2.2.2.1
    simp only [wires_append,Finset.union_subset_iff] at h ⊢
    exact ⟨⟨(K.R.c8z_wires w).trans h.1.1,(K.R.c7t_wires).trans h.1.2⟩,(K.R.c6h_wires w).trans h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap s1 s2) (lift p.1)) s5) (lift pz)) (lift sc),
    ap (ap (ap (ap (ap (lift p.1) (lift cz)) s5c) (lift sc)) s2c) s1c⟩

theorem steps_physical (w : K.R.W) (hn : K.all.Nodup)
    (p1 : GatePhysical K.Q1) (p1c : GatePhysical K.Q1c) (p2 : GatePhysical K.Q2) (p2c : GatePhysical K.Q2c)
    (p5 : GatePhysical K.Q5) (p5c : GatePhysical K.Q5c) :
    GatePhysical (make K) ∧ GatePhysical (clear K) := by
  have p := K.R.piece_physical (K.rnd hn)
  have sc := K.R.scl1591_physical w (K.rnd hn)
  have e1 : (make K)=K.Q1++K.Q2++K.R.smk++K.Q5++(K.R.m6h++K.R.m7k++K.R.m8z)++K.R.scl1591 := by
    simp only [make,List.append_assoc]
  have e2 : (clear K)=K.R.smk++(K.R.c8z++K.R.c7t++K.R.c6h)++K.Q5c++K.R.scl1591++K.Q2c++K.Q1c := by
    simp only [clear,List.append_assoc]
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have pz : GatePhysical (K.R.m6h++K.R.m7k++K.R.m8z) := by
    have h := p.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨K.R.m6h_physical w (K.rnd hn) h.1.1,K.R.m7k_physical w (K.rnd hn)⟩,K.R.m8z_physical (K.rnd hn)⟩
  have cz : GatePhysical (K.R.c8z++K.R.c7t++K.R.c6h) := by
    have h := p.2.2.2.1
    simp only [gatePhysical_append] at h ⊢
    exact ⟨⟨K.R.c8z_physical w (K.rnd hn),K.R.c7t_physical (K.rnd hn)⟩,K.R.c6h_physical w (K.rnd hn) h.2⟩
  rw [e1,e2]
  exact ⟨ap (ap (ap (ap (ap p1 p2) p.1) p5) pz) sc,ap (ap (ap (ap (ap p.1 cz) p5c) sc) p2c) p1c⟩

end ECDSAAdd.Entrant.LowZero18KG

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic KG
variable (K : KG)
theorem steps_slots2 (w : K.R.W) :
    Challenge.gateSlots (make K)+Challenge.gateSlots (clear K) ≤
      Challenge.gateSlots K.Q1+Challenge.gateSlots K.Q1c+Challenge.gateSlots K.Q2+Challenge.gateSlots K.Q2c+
      Challenge.gateSlots K.Q5+Challenge.gateSlots K.Q5c+
      (2*(Challenge.gateSlots K.R.smk+Challenge.gateSlots K.R.scl)+Challenge.gateSlots (K.R.m6++K.R.m7++K.R.m8)+
      Challenge.gateSlots (K.R.c8++K.R.c7++K.R.c6)) := by
  have ms := K.R.m8z_slots w
  have ms7 := K.R.m7k_slots w
  have ms6 := (K.R.m6h_slots w).trans (K.R.m6k_slots w)
  have mc8 := K.R.c8z_slots w
  have mc7 := K.R.c7t_slots
  have mc6 := K.R.c6h_slots w
  have sc := K.R.scl1591_slots
  simp only [make,clear,Challenge.gateSlots_append] at sc ⊢; omega
end ECDSAAdd.Entrant.LowZero18KG

namespace ECDSAAdd.Entrant.LowZero18KG
open Arithmetic
variable (K : KG)
attribute [local irreducible] toffoliCount measurementCount Challenge.gateSlots wires

theorem make_counts_old (w : K.R.W) :
    toffoliCount (make K)+6+2*(if K.R.trimOK then 1 else 0)=toffoliCount (FrontierSumCleanup1591KG.make K) ∧
    measurementCount (make K)+(if K.R.trimOK then 1 else 0)=measurementCount (FrontierSumCleanup1591KG.make K) := by
  have a := make_counts K w
  have b := FrontierSumCleanup1591KG.make_counts K w
  constructor <;> omega

theorem clear_counts_old (w : K.R.W) :
    toffoliCount (clear K)+5+(if K.R.trimOK then 1 else 0)=toffoliCount (FrontierSumCleanup1591KG.clear K) ∧
    measurementCount (clear K)+(if K.R.trimOK then 1 else 0)=measurementCount (FrontierSumCleanup1591KG.clear K) := by
  have a := clear_counts K w
  have b := FrontierSumCleanup1591KG.clear_counts K w
  constructor <;> omega

theorem make_support_subset (w : K.R.W) :
    wires (make K)⊆wires (FrontierSumCleanup1591KG.make K) := by
  have a6 := K.R.m6h_wires_smk w
  have a7 := K.R.m7k_wires w
  have a8 := K.R.m8z_wires w
  simp only [make,FrontierSumCleanup1591KG.make,wires_append]
  intro q hq
  have h6 := @a6 q
  have h7 := @a7 q
  have h8 := @a8 q
  simp only [Finset.mem_union] at hq h6 ⊢
  tauto

theorem clear_support_subset (w : K.R.W) :
    wires (clear K)⊆wires (FrontierSumCleanup1591KG.clear K) := by
  simp only [clear,FrontierSumCleanup1591KG.clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact K.R.c8z_wires w | exact K.R.c7t_wires | exact K.R.c6h_wires w | exact Finset.Subset.refl _

theorem make_slots_old (w : K.R.W) :
    Challenge.gateSlots (make K)≤Challenge.gateSlots (FrontierSumCleanup1591KG.make K) := by
  have a := K.R.m7t_slots
  have a7 := K.R.m7k_slots w
  have a8 := (K.R.m7k_res w).2.2.2.1
  have b := K.R.m8z_slots w
  have c := (K.R.m6h_slots w).trans (K.R.m6k_slots w)
  simp only [make,FrontierSumCleanup1591KG.make,Challenge.gateSlots_append]
  omega

theorem clear_slots_old (w : K.R.W) :
    Challenge.gateSlots (clear K)≤Challenge.gateSlots (FrontierSumCleanup1591KG.clear K) := by
  have a := K.R.c8z_slots w
  have b := K.R.c7t_slots
  have c := K.R.c6h_slots w
  simp only [clear,FrontierSumCleanup1591KG.clear,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.LowZero18KG
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18LowK =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18Core
-- consolidated import: import ECDSAAdd.Submission.Entrant.SquareCarryLoan719BFProof

-- DIAGONAL COMPONENT LowK.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
section
namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

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
   Q1:=LowZero18Diagonal.makeC (iregs L ext src dst),Q1c:=LowZero18Diagonal.clearC (iregs L ext src dst),
   Q2:=LowZero18Diagonal.make (jregsH L ext src dst),Q2c:=LowZero18Diagonal.clear (jregsH L ext src dst),
   Q5:=TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q5c:=TrimSquare4.tsqcM4 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   I1:=(iregs L ext src dst).invC,I2:=(jregsH L ext src dst).invF,I5:=fun _ _ => True}

/-- 129-bit leaf: nested split of the low half and of the sum square, cleaned low inner sum. -/
def kgS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=[],X5:=(jregsS L ext src dst).S++(jregsS L ext src dst).T,
   Q1:=LowZero18Diagonal.makeC (iregs L ext src dst),Q1c:=LowZero18Diagonal.clearC (iregs L ext src dst),
   Q2:=TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,Q2c:=TrimSquare4.tsqcM4 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin,
   Q5:=LowZero18Diagonal.make (jregsS L ext src dst),Q5c:=LowZero18Diagonal.clear (jregsS L ext src dst),
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
  change q∈L.core.pad++L.overflowPad at h'
  change q∈L.core.wires++L.overflowPad
  rcases List.mem_append.mp h' with hp | he
  · apply List.mem_append_left _
    change q∈(((((L.core.y++L.core.out)++L.core.product)++L.core.pad)++L.core.work)++_)
    apply List.mem_append_left _
    apply List.mem_append_left _
    exact List.mem_append_right _ hp
  · exact List.mem_append_right _ he

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

end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs




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
  exact ⟨w,LowZero18Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    LowZero18Diagonal.diag_sq_full_make (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_full_clear (jregsH L ext src dst) wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).invF_local,
    ECDSAAdd.Entrant.sq_mid_make (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_mid4_clear (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
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
  exact ⟨w,LowZero18Diagonal.diag_sq_cl_make (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_cl_clear (iregs L ext src dst) wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    ECDSAAdd.Entrant.sq_mid_make (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_mid4_clear (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain_local,
    LowZero18Diagonal.diag_sq_full_make (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    LowZero18Diagonal.diag_sq_full_clear (jregsS L ext src dst) wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).invF_local⟩

end Inst
end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst3
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (he : 300≤ext.length)

attribute [local irreducible] toffoliCount measurementCount

include hw in
theorem oregs_lens (h : 128≤src.length) (h2 : src.length≤129) :
    (oregs L ext src dst).h=64 ∧ (oregs L ext src dst).bank.length=src.length := by
  have sz := L.measured_bank_widths hw
  refine ⟨rfl,?_⟩
  simp only [oregs,List.length_take,sz.1]; omega

include hw h128 hsmax hlen he in
theorem kgH_counts (h : src.length=128) :
    toffoliCount (LowZero18KG.make (kgH L ext src dst))=6565 ∧ measurementCount (LowZero18KG.make (kgH L ext src dst))=6681 ∧
    toffoliCount (LowZero18KG.clear (kgH L ext src dst))=6531 ∧ measurementCount (LowZero18KG.clear (kgH L ext src dst))=6681 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := LowZero18KG.make_counts (kgH L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgH L ext src dst) w
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsH L ext src dst).h=32 := rfl
  have pi : DiagSq.parR (iregs L ext src dst)=1 := by rw [DiagSq.parR_eq _ wi,il,ih]; decide
  have pj : DiagSq.parR (jregsH L ext src dst)=1 := by rw [DiagSq.parR_eq _ wj,jl,jh]; decide
  rw [pi] at i1 i2; rw [pj] at j1 j2
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-4-1+32 ∧
      toffoliCount (kgH L ext src dst).Q1c=(raw_kcost 64 32-30)-12-1 ∧ measurementCount (kgH L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4-1) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(LowZero18Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(Z5Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-4-1 ∧
      toffoliCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-32-12-1 ∧ measurementCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-4-1 :=
    ⟨j1.1,j1.2,j2.1,by show measurementCount (Z5Diagonal.clear (jregsH L ext src dst))=_; have := j2.2; omega⟩
  have t5 : toffoliCount (kgH L ext src dst).Q5=ksq 65-2 ∧ measurementCount (kgH L ext src dst).Q5=ksq 65-2 ∧
      toffoliCount (kgH L ext src dst).Q5c=ksq 65-3 ∧ measurementCount (kgH L ext src dst).Q5c=ksq 65-2 := by
    have e : (oregs L ext src dst).S.length=65 := by omega
    have f : (oregs L ext src dst).T.length=130 := by omega
    have qm := TrimMid.tsqM_counts_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have q4 := TrimSquare4.tsqcM4_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have k : signedSquareRowsCount 65+130-3=ksq 65-1 := rfl
    rw [e,f] at q
    rw [e,TrimMid.par_65] at qm
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show toffoliCount (TrimSquare4.tsqcM4 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimSquare4.tsqcM4 (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
  have rb : (kgH L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgH L ext src dst).R.h=64 := rfl
  have tk : ¬(kgH L ext src dst).R.trimOK := by
    show ¬(2*(kgH L ext src dst).R.h+1≤(kgH L ext src dst).R.bank.length); rw [rb,rh,h]; norm_num
  rw [if_neg tk,Nat.add_zero] at mk cl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

include hw h128 hsmax hlen he in
theorem kgS_counts (h : src.length=129) :
    toffoliCount (LowZero18KG.make (kgS L ext src dst))=6679 ∧ measurementCount (LowZero18KG.make (kgS L ext src dst))=6797 ∧
    toffoliCount (LowZero18KG.clear (kgS L ext src dst))=6645 ∧ measurementCount (LowZero18KG.clear (kgS L ext src dst))=6797 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := LowZero18KG.make_counts (kgS L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgS L ext src dst) w
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsS L ext src dst).h=33 := rfl
  have pi : DiagSq.parR (iregs L ext src dst)=1 := by rw [DiagSq.parR_eq _ wi,il,ih]; decide
  have pj : DiagSq.parR (jregsS L ext src dst)=2 := by rw [DiagSq.parR_eq _ wj,jl,jh]; decide
  rw [pi] at i1 i2; rw [pj] at j1 j2
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-4-1+32 ∧
      toffoliCount (kgS L ext src dst).Q1c=(raw_kcost 64 32-30)-12-1 ∧ measurementCount (kgS L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4-1) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smk++(LowZero18Diagonal.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]; norm_num [raw_kcost,raw_ksq,signedSquareRowsCount]
    · show measurementCount ((iregs L ext src dst).smk++(Z5Diagonal.clear (iregs L ext src dst)))=_; rw [measurementCount_append,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgS L ext src dst).Q2=ksq 65-2 ∧ measurementCount (kgS L ext src dst).Q2=ksq 65-2 ∧
      toffoliCount (kgS L ext src dst).Q2c=ksq 65-3 ∧ measurementCount (kgS L ext src dst).Q2c=ksq 65-2 := by
    have e : (oregs L ext src dst).hi.length=65 := by omega
    have f : (oregs L ext src dst).dhi.length=130 := by omega
    have qm := TrimMid.tsqM_counts_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have q4 := TrimSquare4.tsqcM4_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have k : signedSquareRowsCount 65+130-3=ksq 65-1 := rfl
    rw [e,f] at q
    rw [e,TrimMid.par_65] at qm
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show toffoliCount (TrimSquare4.tsqcM4 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimSquare4.tsqcM4 (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
  have t5 : toffoliCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-11-2 ∧ measurementCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-4-2 ∧
      toffoliCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-33-12-2 ∧ measurementCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-4-2 :=
    ⟨j1.1,j1.2,j2.1,by show measurementCount (Z5Diagonal.clear (jregsS L ext src dst))=_; have := j2.2; omega⟩
  have rb : (kgS L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgS L ext src dst).R.h=64 := rfl
  have tk : (kgS L ext src dst).R.trimOK := by
    show 2*(kgS L ext src dst).R.h+1≤(kgS L ext src dst).R.bank.length; rw [rb,rh,h]
  rw [if_pos tk] at mk cl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end Inst3
end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

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

def lowkcost2 (n : Nat) : Nat := if n=128 then 6681 else 6797
def lowkcostTMake (n : Nat) : Nat := if n=128 then 6565 else 6679
def lowkcostTClear (n : Nat) : Nat := if n=128 then 6531 else 6645
def lowkcostTPair (n : Nat) : Nat := lowkcostTMake n+lowkcostTClear n

include hw h128 hsmax hlen he in
theorem kg_counts :
    toffoliCount (LowZero18KG.make (kg L ext src dst))=lowkcostTMake src.length ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))=lowkcost2 src.length ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))=lowkcostTClear src.length ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))=lowkcost2 src.length := by
  by_cases c : src.length=128
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_pos c]; exact kgH_counts L hw ext src dst h128 hsmax hlen he c
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,if_neg c]; exact kgS_counts L hw ext src dst h128 hsmax hlen he (by omega)

include hw h128 hsmax hlen he in
theorem kg_support :
    ECDSAAdd.wires (LowZero18KG.make (kg L ext src dst))⊆(kg L ext src dst).all.toFinset ∧
    ECDSAAdd.wires (LowZero18KG.clear (kg L ext src dst))⊆(kg L ext src dst).all.toFinset := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (oregs L ext src dst).piece_support w
  have ip := (iregs L ext src dst).piece_support wi
  have is := LowZero18Diagonal.steps_support (iregs L ext src dst) wi
  have isc := (iregs L ext src dst).scl1591_support wi
  have tr {P : Program} {A B : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : A⊆B) : ECDSAAdd.wires P⊆B := h1.trans h2
  have ap {P Q : Program} {A : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : ECDSAAdd.wires Q⊆A) :
      ECDSAAdd.wires (P++Q)⊆A := by rw [wires_append]; exact Finset.union_subset h1 h2
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have js := LowZero18Diagonal.steps_support (jregsH L ext src dst) wj
    have iK := sub_of_count (kgH_iall L ext src dst)
    have jK := sub_of_count (kgH_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgH L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr js.1 jK) (tr js.2 jK) (tr ((TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.2.2.1) rK) (tr (((TrimSquare4.tsqcM4_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).trans (TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2).trans rp.2.2.2.2.2.2.2) rK)
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have js := LowZero18Diagonal.steps_support (jregsS L ext src dst) wj
    have iK := sub_of_count (kgS_iall L ext src dst)
    have jK := sub_of_count (kgS_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgS L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr ((TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.1) rK) (tr (((TrimSquare4.tsqcM4_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).trans (TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).2).trans rp.2.2.2.2.2.1) rK) (tr js.1 jK) (tr js.2 jK)

include hw h128 hsmax hlen he in
theorem kg_physical (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (LowZero18KG.make (kg L ext src dst)) ∧ GatePhysical (LowZero18KG.clear (kg L ext src dst)) := by
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  by_cases h : src.length=128
  · rw [kg,if_pos h] at hall ⊢
    have wj := jregsH_W L hw ext src dst h hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgH_iall L ext src dst)
    have nj := knd hall (kgH_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsH L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) js.1 js.2 (TrimMid.tsqM_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).1 (TrimSquare4.tsqcM4_physical (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (TrimMid.tsqM_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).2)
  · rw [kg,if_neg h] at hall ⊢
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgS_iall L ext src dst)
    have nj := knd hall (kgS_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsS L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ip.1 is.2) (TrimMid.tsqM_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).1 (TrimSquare4.tsqcM4_physical (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (TrimMid.tsqM_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).2) js.1 js.2

include hw h128 hsmax hlen he in
theorem kg_slots :
    Challenge.gateSlots (LowZero18KG.make (kg L ext src dst))+Challenge.gateSlots (LowZero18KG.clear (kg L ext src dst))≤1200000 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have ol := oregs_lens L hw ext src dst h128 hsmax
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T
  have ad := (oregs L ext src dst).adder_slots w rfl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have it := LowZero18Diagonal.tiny_slots (iregs L ext src dst) wi (by rw [il,ih]) (by rw [ih]; omega)
  simp only [LowZero18Diagonal.clear] at it
  have oldit := (iregs L ext src dst).tiny_slots wi (by rw [ih]; omega) (by rw [il,ih]; omega) (by omega)
  have isb := (iregs L ext src dst).make_sub_slots wi
  have isc := (iregs L ext src dst).scl1591_slots
  have g2 := TrimMid.tsqM_gateSlots_le (oregs L ext src dst).hi (oregs L ext src dst).dhi
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g2' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5 := TrimMid.tsqM_gateSlots_le (oregs L ext src dst).S (oregs L ext src dst).T
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have x2 : (oregs L ext src dst).hi.length*(12*((oregs L ext src dst).hi.length+1)+6*(oregs L ext src dst).dhi.length) ≤ 65*(12*66+6*130) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : (oregs L ext src dst).S.length*(12*((oregs L ext src dst).S.length+1)+6*(oregs L ext src dst).T.length) ≤ 66*(12*67+6*132) :=
    Nat.mul_le_mul (by omega) (by omega)
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
    have jh : (jregsH L ext src dst).h=32 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsH L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgH L ext src dst) w
    simp only [kgH,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,Z5Diagonal.clearC,KRegs.m5,KRegs.c5,Challenge.gateSlots_append] at st ad ⊢
    omega
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
    have jh : (jregsS L ext src dst).h=33 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsS L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgS L ext src dst) w
    simp only [kgS,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,Z5Diagonal.clearC,KRegs.m2,KRegs.c2,Challenge.gateSlots_append] at st ad ⊢
    omega

end Inst4
end ECDSAAdd.Entrant.LowZero18LowK


namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem kg_metadata (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (kg L ext src dst).R=(FrontierSumCleanup1591LowK.kg L ext src dst).R ∧
    (kg L ext src dst).X1=(FrontierSumCleanup1591LowK.kg L ext src dst).X1 ∧
    (kg L ext src dst).X=(FrontierSumCleanup1591LowK.kg L ext src dst).X ∧
    (kg L ext src dst).all=(FrontierSumCleanup1591LowK.kg L ext src dst).all := by
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true];exact ⟨rfl,rfl,rfl,rfl⟩
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false];exact ⟨rfl,rfl,rfl,rfl⟩

theorem kg_Q1c_subset (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    wires (kg L ext src dst).Q1c⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1c := by
  have a := LowZero18Diagonal.clearC_support_subset (iregs L ext src dst)
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_Q1_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (kg L ext src dst).Q1⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1 := by
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have a := LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18KG.make (kg L ext src dst))+32+3*(if src.length=128 then 0 else 1)=
      toffoliCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))+12+2*(if src.length=128 then 0 else 1)=
      measurementCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))+34+2*(if src.length=128 then 0 else 1)=
      toffoliCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))+12+2*(if src.length=128 then 0 else 1)=
      measurementCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have a := kg_counts L hw ext src dst h128 h129 hd he
  have b := FrontierSumCleanup1591LowK.kg_counts L hw ext src dst h128 h129 hd he
  by_cases h : src.length=128
  all_goals simp only [lowkcostTMake,lowkcostTClear,lowkcost2,FrontierSumCleanup1591LowK.lowkcostTMake,
    FrontierSumCleanup1591LowK.lowkcostTClear,FrontierSumCleanup1591LowK.lowkcost2,h,ite_true,ite_false] at a b ⊢
  all_goals exact ⟨by omega,by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.LowZero18LowK

end


namespace ECDSAAdd.Entrant.CodexBorrowedUnion

/-- The borrowed controls of E already occur in the retained C segment. -/
theorem eight {α : Type} [DecidableEq α]
    {a b c d e f g h A B D E F G : Finset α}
    (ha : a ⊆ A) (hb : b ⊆ B) (hd : d ⊆ D)
    (he : e ⊆ E ∪ c) (hf : f ⊆ F) (hg : g ⊆ G) :
    a ∪ b ∪ c ∪ d ∪ e ∪ f ∪ g ∪ h ⊆
      A ∪ B ∪ c ∪ D ∪ E ∪ F ∪ G ∪ h := by
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (ha h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hb h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hd h)))))
  · rcases Finset.mem_union.mp (he h) with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inr (hf h)))
  · exact Or.inl (Or.inr (hg h))
  · exact Or.inr h

theorem seven {α : Type} [DecidableEq α]
    {b c d e f g h B D E F G : Finset α}
    (hb : b ⊆ B) (hd : d ⊆ D)
    (he : e ⊆ E ∪ c) (hf : f ⊆ F) (hg : g ⊆ G) :
    b ∪ c ∪ d ∪ e ∪ f ∪ g ∪ h ⊆
      B ∪ c ∪ D ∪ E ∪ F ∪ G ∪ h := by
  simpa only [Finset.union_self] using
    eight (a := b) (A := B) (h := h) hb hb hd he hf hg

end ECDSAAdd.Entrant.CodexBorrowedUnion

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

theorem loan_make_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi)
  have ro : FrontierSumCleanup1591LowK.oregs L ext src dst = oregs L ext src dst := rfl
  have ri : FrontierSumCleanup1591LowK.iregs L ext src dst = iregs L ext src dst := rfl
  have a6 := (oregs L ext src dst).m6h_wires_smk w
  have a7 := (oregs L ext src dst).m7k_wires w
  have a8 := (oregs L ext src dst).m8z_wires w
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_support_subset (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    have rj : FrontierSumCleanup1591LowK.jregsH L ext src dst = jregsH L ext src dst := rfl
    have q5 := (TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append,ro,ri,rj]
    exact CodexBorrowedUnion.eight ip jp q5 a6 a7 a8
  · have jp := LowZero18Diagonal.make_support_subset (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    have rj : FrontierSumCleanup1591LowK.jregsS L ext src dst = jregsS L ext src dst := rfl
    have q2 := (TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append,ro,ri,rj]
    exact CodexBorrowedUnion.eight ip q2 jp a6 a7 a8

theorem loan_clear_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have ipc := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.clearC_support_subset (iregs L ext src dst))
  have jhc := LowZero18Diagonal.clear_support_subset (jregsH L ext src dst)
  have jsc := LowZero18Diagonal.clear_support_subset (jregsS L ext src dst)
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.c5,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ipc | exact jhc | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (TrimSquare4.tsqcM4_wires_le _ _ _ _ _).trans (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7t_wires | exact (oregs L ext src dst).c6h_wires w | exact Finset.Subset.refl _
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.c2,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact ipc | exact jsc | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (TrimSquare4.tsqcM4_wires_le _ _ _ _ _).trans (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7t_wires | exact (oregs L ext src dst).c6h_wires w | exact Finset.Subset.refl _

theorem loan_make_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := LowZero18Diagonal.makeC_slots_old (iregs L ext src dst) wi
  have a := (oregs L ext src dst).m7t_slots
  have a7 := (oregs L ext src dst).m7k_slots w
  have b := (oregs L ext src dst).m8z_slots w
  have c6 := ((oregs L ext src dst).m6h_slots w).trans ((oregs L ext src dst).m6k_slots w)
  have q5 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_slots_le (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    have rj : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a a7 b c6 jp q5 ⊢
    omega
  · have jp := LowZero18Diagonal.make_slots_le (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    have rj : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a a7 b c6 jp q2 ⊢
    omega

theorem loan_clear_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have a := (oregs L ext src dst).c8z_slots w
  have b := (oregs L ext src dst).c7t_slots
  have c6 := (oregs L ext src dst).c6h_slots w
  have q5 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q5' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2' := TrimSquare4.tsqcM4_slots (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have i1 := LowZero18Diagonal.clearC_slots_old (iregs L ext src dst)
  have jh := LowZero18Diagonal.clear_slots_old (jregsH L ext src dst)
  have js := LowZero18Diagonal.clear_slots_old (jregsS L ext src dst)
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  have rh : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
  have rs : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
  by_cases h : src.length=128
  all_goals simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,LowZero18KG.clear,
    SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
    kgH,kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
    LowZero18Diagonal.clearC,LowZero18Diagonal.clear,KRegs.c5,KRegs.c2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
  all_goals simp only [LowZero18Diagonal.clearC,LowZero18Diagonal.clear,ro,ri,rh,rs] at a b c6 q5 q2 q5' q2' i1 jh js ⊢
  all_goals omega

end ECDSAAdd.Entrant.LowZero18LowK
end -- original module boundary


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProgram =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18LowK

/-! The checked675/BF719 square with only the18 carry-free low-bit changes. -/
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

abbrev target := SquareCarryLoan719.target
abbrev earlyHost := SquareCarryLoan719.earlyHost
abbrev earlyPerm := SquareCarryLoan719.earlyPerm
abbrev foldPerm := SquareCarryLoan719.foldPerm
abbrev patchKG := SquareCarryLoan719.patchKG
abbrev K : Nat := ControlLoan1589BFFold.K

def make (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.make (patchKG L R)

def clear (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.clear (patchKG L R)

def clearPrefix (R : KG) : Program :=
  R.R.smk++R.R.c8z++R.R.c7t++R.R.c6h++R.Q5c++R.R.scl1591++R.Q2c

def withLowK2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program) : Program :=
  let R := LowZero18LowK.kg L ext src dst
  copyRegister (some control) src (L.inputBank.take src.length)++make L R++
    eraseMask control src (L.inputBank.take src.length)++
    renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)++clear L R++
    eraseMask control src (L.inputBank.take src.length)

def branchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)++
    OwnDiagAll12Square.gClear L

set_option maxHeartbeats 4000000 in
theorem withLowK2_bodyCK (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) :
    toffoliCount (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))+31=
      toffoliCount (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    measurementCount (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))=
      measurementCount (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    wires (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))⊆
      wires (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    Challenge.gateSlots (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))≤
      Challenge.gateSlots (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) := by
  have r := CodexCKAccTail.bodyCTail_rel L hw control
  refine ⟨?_,?_,?_,?_⟩
  · simp only [withLowK2,toffoliCount_append,(renameProgram_counts _ _).1]; omega
  · simp only [withLowK2,measurementCount_append,(renameProgram_counts _ _).2]; omega
  · simp only [withLowK2,wires_append,renameProgram_support]
    repeat' apply Finset.union_subset_union
    all_goals first | exact Finset.image_subset_image r.2.2.1 | exact Finset.Subset.refl _
  · simp only [withLowK2,Challenge.gateSlots_append,Baselines.rename_gateSlots]; omega

def branchBF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.high (L.core.product.take 256) (ControlLoan1589BFFold.bBodyTq L control)

def branchAF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.low (L.core.product.take 256) (ControlLoan1589BFFold.aBodyTq L control)

def reflection (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Program :=
  renameProgram (foldPerm L ext) L.reflectOutput

def raw (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control++reflection L ext

def fastCandidate (L : ControlledPointLayout) : Program :=
  raw L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def place (L : ControlledPointLayout) (P : Program) : Program :=
  let p0 := renameProgram (Square5Placement.blockPerm L 202) P
  let p1 := renameProgram (OwnPlusSquare.swap L) p0
  let p2 := renameProgram (OwnGuardSquare.swap L) p1
  let p3 := renameProgram (OwnQ4Square.swap L) p2
  let p4 := renameProgram (OwnQ5Square.swap L) p3
  let p5 := renameProgram (OwnDiagAll12PlacedQ6.swap L) p4
  let p6 := renameProgram (OwnDiagAll12PlacedQ7.swap L) p5
  let p7 := renameProgram (PrefixFrontierSquare1591.swap L) p6
  let p8 := renameProgram (Prefix1590Square.swap L) p7
  renameProgram (ControlLoan1589Square.swap L) p8

def program (L : ControlledPointLayout) : Program := place L (fastCandidate L)

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareSupport =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProgram

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18SquareSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout LowZero18Square
attribute [local irreducible] wires

theorem kg_X1_eq (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (LowZero18LowK.kg L ext src dst).X1=(OwnDiagLowK.kg L ext src dst).X1 :=
  (LowZero18LowK.kg_metadata L ext src dst).2.1.trans
    (SquareCarryLoan719BFSupport.kg_X1_eq L ext src dst)

section Normal
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hw in
theorem target_mem_X1 : target L∈(LowZero18LowK.kg L ext src dst).X1 := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).2.1]
  exact SquareCarryLoan719BFSupport.target_mem_X1 L hw ext src dst

include hw h128 in
theorem earlyHost_mem_outer : earlyHost L∈(LowZero18LowK.kg L ext src dst).R.S := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).1]
  exact SquareCarryLoan719BFSupport.earlyHost_mem_outer L hw ext src dst h128

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem earlyHost_Q1_free :
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1 ∧
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1c := by
  have old := SquareCarryLoan719BFSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  exact ⟨fun used=>old.1 (LowZero18LowK.kg_Q1_subset L hw ext src dst h128 hsmax hlen he used),
    fun used=>old.2 (LowZero18LowK.kg_Q1c_subset L ext src dst used)⟩

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem target_clearPrefix_free :
    target L∉wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst)) := by
  have old := SquareCarryLoan719BFSupport.target_clearPrefix_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))⊆
      wires (SquareCarryLoan719BF.clearPrefix (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
    by_cases h : src.length=128
    all_goals simp only [LowZero18Square.clearPrefix,SquareCarryLoan719BF.clearPrefix,
      LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,
      LowZero18LowK.kgH,LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
      KRegs.c5,KRegs.c2,wires_append]
    all_goals repeat' apply Finset.union_subset_union
    all_goals first | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact (TrimSquare4.tsqcM4_wires_le _ _ _ _ _).trans (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact LowZero18Diagonal.clear_support_subset _ |
      exact (LowZero18LowK.oregs L ext src dst).c8z_wires w |
      exact (LowZero18LowK.oregs L ext src dst).c7t_wires | exact (LowZero18LowK.oregs L ext src dst).c6h_wires w |
      exact Finset.Subset.refl _
  exact fun used=>old (sub used)

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem make_tail_free :
    target L∉wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6h++(LowZero18LowK.kg L ext src dst).R.m7k++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591) := by
  have old := SquareCarryLoan719BFSupport.make_tail_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6h++(LowZero18LowK.kg L ext src dst).R.m7k++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591)⊆
    wires ((FrontierSumCleanup1591LowK.kg L ext src dst).Q2++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.smk++(FrontierSumCleanup1591LowK.kg L ext src dst).Q5++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m6++(FrontierSumCleanup1591LowK.kg L ext src dst).R.m7++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m8++(FrontierSumCleanup1591LowK.kg L ext src dst).R.scl1591) := by
    have ro : FrontierSumCleanup1591LowK.oregs L ext src dst = LowZero18LowK.oregs L ext src dst := rfl
    have a6 := (LowZero18LowK.oregs L ext src dst).m6h_wires_smk w
    have a7 := (LowZero18LowK.oregs L ext src dst).m7k_wires w
    have a8 := (LowZero18LowK.oregs L ext src dst).m8z_wires w
    by_cases h : src.length=128
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsH L ext src dst)
        (LowZero18LowK.jregsH_W L hw ext src dst h hlen he)
      have rj : FrontierSumCleanup1591LowK.jregsH L ext src dst = LowZero18LowK.jregsH L ext src dst := rfl
      have q5 := (TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).S (LowZero18LowK.oregs L ext src dst).T (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).1
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,
        LowZero18LowK.kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append,ro,rj]
      exact CodexBorrowedUnion.seven jp q5 a6 a7 a8
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsS L ext src dst)
        (LowZero18LowK.jregsS_W L hw ext src dst (by omega) hlen he)
      have rj : FrontierSumCleanup1591LowK.jregsS L ext src dst = LowZero18LowK.jregsS L ext src dst := rfl
      have q2 := (TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).hi (LowZero18LowK.oregs L ext src dst).dhi (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).1
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_false,
        LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append,ro,rj]
      exact CodexBorrowedUnion.seven q2 jp a6 a7 a8
  exact fun used=>old (sub used)

end Normal
end ECDSAAdd.Entrant.LowZero18SquareSupport
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareSupport

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] run wires

abbrev fold_run_eq := SquareCarryLoan719.fold_run_eq

theorem patchKG_make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (K : KG)
    (sp : K.Spec) (targetX1 : target L∈K.X1) (hostS : earlyHost L∈K.R.S)
    (hostFree : earlyHost L∉wires K.Q1)
    (innerZero : ∀v t,K.I1 v t → t (target L)=false) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hX0 : regValue K.X s.basis=0) (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    run (LowZero18Square.make L K) m s=run (LowZero18KG.make K) m s := by
  have dlo0 : regValue K.R.dlo s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hd0 q (List.mem_of_mem_take hq))
  have x10 : regValue K.X1 s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hX0 q (by simp only [KG.X,List.mem_append];tauto))
  have headEq (records : List Bool) := SquareCarryLoan719.q1_run_eq L hw K sp targetX1 hostFree innerZero
    s records dlo0 x10 hp0 hc0 hz0 hi0 ((regValue_zero _ _).mp hS0 _ hostS)
  let tail := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
  have oldShape : LowZero18KG.make K=K.Q1++tail := by simp only [LowZero18KG.make,tail,List.append_assoc]
  have newShape : LowZero18Square.make L K=renameProgram (earlyPerm L) K.Q1++tail := by
    simp only [LowZero18Square.make,SquareCarryLoan719.patchKG,LowZero18KG.make,tail,List.append_assoc]
  simp only [newShape,oldShape,run_append,(renameProgram_counts _ _).2]
  rw [headEq]

theorem make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (sp : (LowZero18LowK.kg L ext src dst).Spec) (s : State) (m : List Bool)
    (hd0 : regValue (LowZero18LowK.kg L ext src dst).R.dst s.basis=0)
    (hS0 : regValue (LowZero18LowK.kg L ext src dst).R.S s.basis=0)
    (hX0 : regValue (LowZero18LowK.kg L ext src dst).X s.basis=0)
    (hz0 : regValue (LowZero18LowK.kg L ext src dst).R.z s.basis=0)
    (hp0 : regValue (LowZero18LowK.kg L ext src dst).R.pad s.basis=0)
    (hc0 : regValue (LowZero18LowK.kg L ext src dst).R.carry s.basis=0)
    (hi0 : s.basis (LowZero18LowK.kg L ext src dst).R.cin=false) :
    run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) m s=
      run (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) m s := by
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  apply patchKG_make_run_eq L hw (LowZero18LowK.kg L ext src dst) sp
    (LowZero18SquareSupport.target_mem_X1 L hw ext src dst)
    (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128) free.1
    ?_ s m hd0 hS0 hX0 hz0 hp0 hc0 hi0
  intro v t inv
  rw [LowZero18LowK.kg_I1] at inv
  exact (regValue_zero _ _).mp inv.1 _
    (SquareCarryLoan719Support.target_mem_inner L hw ext src dst)

theorem clear_run_eq_of_boundaries (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (K : KG) (s : State) (m : List Bool)
    (prefixFree : target L∉wires (clearPrefix K))
    (hostFree : earlyHost L∉wires K.Q1c)
    (targetIn : s.basis (target L)=false)
    (targetOut : (run (LowZero18KG.clear K) m s).basis (target L)=false)
    (hostOut : (run (LowZero18KG.clear K) m s).basis (earlyHost L)=false) :
    run (LowZero18Square.clear L K) m s=run (LowZero18KG.clear K) m s := by
  let middle := run (clearPrefix K) (m.take (measurementCount (clearPrefix K))) s
  let records := m.drop (measurementCount (clearPrefix K))
  have oldShape : LowZero18KG.clear K=clearPrefix K++K.Q1c := by
    simp only [LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have newShape : LowZero18Square.clear L K=clearPrefix K++renameProgram (earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,SquareCarryLoan719.patchKG,LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have oldRun : run (LowZero18KG.clear K) m s=run K.Q1c records middle := by rw [oldShape,run_append]
  have targetMid : middle.basis (target L)=false :=
    (run_preserves_outside _ _ s _ prefixFree).trans targetIn
  rw [oldRun] at targetOut hostOut
  have hostMid : middle.basis (earlyHost L)=false :=
    (run_preserves_outside _ records middle _ hostFree).symm.trans hostOut
  have lastEq := NewFieldFrameOB5.rebind_swap_run (target L) (earlyHost L) K.Q1c
    middle records targetMid hostMid targetOut hostOut
  rw [←SquareCarryLoan719.earlyPerm_eq L hw] at lastEq
  rw [newShape,oldShape,run_append,run_append]
  exact lastEq

theorem cross_host_zero (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)
    (h128 : 128≤src.length) (he : 300≤ext.length) (s : BasisState) (a b : Nat)
    (value : regValue (LowZero18LowK.oregs L ext src dst).T s=2*a*b) :
    s (ext.getD 0 0)=false :=
  SquareCarryLoan719.cross_host_zero L ext src dst h128 he s a b value

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProof =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff

/-! The checked BF719 state proof with only the LowZero producer/cleanup constructors changed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

private theorem k2_xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
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
    (run (LowZero18Square.withLowK2 L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
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
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  let P := if s.basis control then regValue src s.basis else 0
  obtain ⟨a6,r7,e7⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) records s
  obtain ⟨a5,r6,e6⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    copyRegister (some control) src (L.inputBank.take src.length)) (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body)
    (copyRegister (some control) src (L.inputBank.take src.length)) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)) (renameProgram (foldPerm L ext) body) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)) (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) a2 s
  rw [show LowZero18Square.withLowK2 L ext control src dst body=copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length) from rfl,e7,e6,e5,e4,e3,e2]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
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
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
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
  generalize hv : run body r4 u2=v at loc
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r4 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r4 u2 q hb,run_preserves_outside body r4 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply k2_xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r4 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r4 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
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
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r6
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
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
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r6
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r6 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
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
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX,cf2 q hb,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx


theorem reflection_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (O : Nat) (hO : O<SquareReduction.p)
    (s : State) (m : List Bool) (ho : regValue L.core.out s.basis=O)
    (hc : L.PairClean s.basis) (hz : regValue ext s.basis=0) :
    (run (reflection L ext) m s).phase=s.phase ∧
    regValue L.core.out (run (reflection L ext) m s).basis=SquareReduction.p-1-O ∧
    ∀q,q∉L.core.out → (run (reflection L ext) m s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have old := L.reflectOutput_correct hw nd O hO s m ho hc
  have len := OwnDiagLowK.ktmp_length L hw
  have member : target L∈OwnDiagLowK.ktmp L := DiagSq.getD_in _ 67 (by omega)
  have pad : target L∈L.foldPad := List.mem_of_mem_drop member
  have away : target L∉L.core.out :=
    (L.pairAuxAway nd _ (by simp only [List.mem_append];tauto)).2
  have tin : s.basis (target L)=false := (regValue_zero _ _).mp hc.pad _ pad
  have tout : (run L.reflectOutput m s).basis (target L)=false := (old.2.2 _ away).trans tin
  have host : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by have h:=he.len;omega)
  have hin : s.basis (ext.getD 0 0)=false := (regValue_zero _ _).mp hz _ host
  have free : ext.getD 0 0∉wires L.reflectOutput := fun used=>
    he.away _ host (List.mem_toFinset.mp (ControlLoan1589BFFold.reflect_support L control used))
  have eq := SquareCarryLoan719.fold_run_eq L hw ext L.reflectOutput s m tin tout hin free
  simpa only [reflection,eq] using old

def middleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)

theorem middleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (middleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (middleCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (middleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (OwnDiagAll12Square.bodyCKTq L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (OwnDiagAll12Square.bodyCK_supportTq L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (OwnDiagAll12Square.bodyCKTq L control) hbody
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
  have r := OwnDiagAll12Square.accMiddleCFK_bodyTq L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem branchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (LowZero18Square.branchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.branchCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.branchCK L ext control) records s).basis q=s.basis q := by
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
  let middle := middleCK L ext control
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let rest := records.drop mp
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (OwnDiagAll12Square.gClear L) (rest.drop (measurementCount middle)) v
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
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
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (OwnDiagAll12Square.sum_in L control q bad)))).trans hz
  have used := middleCK_correct L hw ext control hn (A+B) O hO u
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
  have cleared := OwnDiagAll12Square.gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [LowZero18Square.branchCK,middleCK,middle,u,v,out,rest,mp,run_append] using final


theorem branchBF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchBF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchBF L ext control) records s).basis=
      ControlLoan1589BFFold.resBF ((if s.basis control then B else 0)^2) O (s.basis control) ∧
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
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ControlLoan1589BFFold.bBodyTq L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ControlLoan1589BFFold.bBody_supportTq L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len
    (ControlLoan1589BFFold.bBodyTq L control) hbody s records hc dstZero hz
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
  have frame := ControlLoan1589BFFold.bBody_frameTq L hw nd control hcw t.basis M mb full clean O hO t m ⟨outO,fun _ _ => rfl⟩
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  rw [ControlLoan1589BFFold.bO4_eq M O (t.basis control) mb hg hO,ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

theorem branchAF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchAF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchAF L ext control) records s).basis=
      ControlLoan1589BFFold.resAF ((if s.basis control then A else 0)^2) O (s.basis control) ∧
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
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ControlLoan1589BFFold.aBodyTq L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ControlLoan1589BFFold.aBody_supportTq L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len
    (ControlLoan1589BFFold.aBodyTq L control) hbody s records hc dstZero hz
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
  have frame := ControlLoan1589BFFold.aBody_frameTq L hw nd control hcw t.basis M mb full clean O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩


theorem raw_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (raw L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (raw L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (raw L ext control) records s).basis q=s.basis q := by
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
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
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
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
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
  have stepR : Triple (SquareFrame L.core.out s.basis OA) (reflection L ext)
      (SquareFrame L.core.out s.basis (SquareReduction.p-1-OA)) := by
    intro t m hf
    have h := reflection_correct L hw control hn ext he OA (ofCast_lt _ _) t m hf.1
      (L.squareFrame_clean nd s.basis t.basis OA hf hc) (extZ _ _ hf)
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := ((stepC.seq stepB).seq stepA).seq stepR
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  exact ⟨phase,value.trans exactResult,frame⟩


theorem raw_state_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (m mOld : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) (he : ECDSAAdd.Entrant.ExtOK L control ext)
    (hz : regValue ext s.basis=0) :
    run (raw L ext control) m s=run (ControlLoan1589BFFold.program L ext control) mOld s := by
  have fresh := raw_correct L hw ext control hn Y O hO s m hy ho hp0 hs0 hc he hz
  have prior := ControlLoan1589BFFold.correct L hw ext control hn Y O hO s mOld hy ho hp0 hs0 hc he hz
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases inside : q∈L.core.out
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q inside
    · exact (fresh.2.2 q inside).trans (prior.2.2 q inside).symm

open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCandidate_state_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (hX : X<p) (s : State) (m mOld : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (fastCandidate L) m s=run (ControlLoan1589BFSquare.fastCandidate L) mOld s := by
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
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_state_eq K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m mOld hy hx prod0 sum0 clean
    (ECDSAAdd.Entrant.kext_ok L hw hn) hz
  simpa only [fastCandidate,ControlLoan1589BFSquare.fastCandidate] using kernel

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (fastCandidate L) := by
  intro X Y G origin s m v
  have old := ControlLoan1589BFSquare.candidate_correct L hw hn X Y G origin s m v
  have eq := fastCandidate_state_eq L hw hn X.val Y.val X.isLt s m m v.x v.y v.clean
  simpa only [eq] using old

private theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (old : ControlLoan1589BFSquare.SquareCorrectK L K P) :
    ControlLoan1589BFSquare.SquareCorrectK L K (renameProgram e P) := by
  intro X Y G origin s m v
  have result := old X Y G origin s m v
  have eq := Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean result.2.clean
  simpa only [eq] using result

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (program L) := by
  have a0 := relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have a1 := relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw) _ a0
  have a2 := relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw) _ a1
  have a3 := relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw) _ a2
  have a4 := relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw) _ a3
  have a5 := relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw) (OwnDiagAll12PlacedQ6.outside L hw) _ a4
  have a6 := relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw) (OwnDiagAll12PlacedQ7.outside L hw) _ a5
  have a7 := relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw) (PrefixFrontierSquare1591.outside L hw) _ a6
  have a8 := relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw) (Prefix1590Square.outside L hw) _ a7
  have a9 := relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw) (ControlLoan1589Square.outside L hw) _ a8
  exact a9

theorem step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (K:Fp) else 0)) Y G origin) :=
  correct L hw hn X Y G origin

private theorem values_unique {L : ControlledPointLayout} {X Y : Fp} {G : Bool}
    {origin a b : BasisState} (ha : PointDialogValues L X Y G origin a)
    (hb : PointDialogValues L X Y G origin b) : a=b := by
  funext q
  by_cases hx : q∈L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ha.x.trans hb.x.symm) q hx
  · by_cases hy : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp (ha.y.trans hb.y.symm) q hy
    · have away : q∉L.point.x++L.point.y := by
        simpa only [List.mem_append,not_or] using And.intro hx hy
      exact (ha.rest q away).trans (hb.rest q away).symm

theorem state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (ControlLoan1589BFSquare.program L) mOld s := by
  have fresh := correct L hw hn X Y G origin s m v
  have prior := ControlLoan1589BFSquare.correct L hw hn X Y G origin s mOld v
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · exact values_unique fresh.2 prior.2

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 :=
  (correct L hw hn X Y G origin s m v).2.clean

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareResources =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProof

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

private theorem source_counts (L : CuccaroStreamedSquareWideLayout) :
    (∀q,L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,(L.core.product.take 256).count q≤L.core.product.count q) := by
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans ((List.drop_sublist 128 L.core.y).count_le q)
  refine ⟨?_,?_,?_,fun q=>(List.take_sublist 256 L.core.product).count_le q⟩
  · intro q
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢;omega
  · intro q;have h := hh q;simp only [List.count_append];omega
  · intro q;have h := hh q;simp only [CuccaroStreamedSquareLayout.sum,List.count_append];omega

theorem patchKG_counts (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    toffoliCount (LowZero18Square.make L R)=toffoliCount (LowZero18KG.make R) ∧
    measurementCount (LowZero18Square.make L R)=measurementCount (LowZero18KG.make R) ∧
    toffoliCount (LowZero18Square.clear L R)=toffoliCount (LowZero18KG.clear R) ∧
    measurementCount (LowZero18Square.clear L R)=measurementCount (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem patchKG_slots (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    Challenge.gateSlots (LowZero18Square.make L R)=Challenge.gateSlots (LowZero18KG.make R) ∧
    Challenge.gateSlots (LowZero18Square.clear L R)=Challenge.gateSlots (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,Challenge.gateSlots_append,
    Baselines.rename_gateSlots,and_self]

theorem withLowK2_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (withLowK2 L ext control src dst body)+66+5*(if src.length=128 then 0 else 1)=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (withLowK2 L ext control src dst body)+24+4*(if src.length=128 then 0 else 1)=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have d := LowZero18LowK.kg_counts_diff L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,toffoliCount_append,measurementCount_append,
    (patchKG_counts L _).1,(patchKG_counts L _).2.1,(patchKG_counts L _).2.2.1,(patchKG_counts L _).2.2.2,
    (SquareCarryLoan719BF.patchKG_counts L _).1,(SquareCarryLoan719BF.patchKG_counts L _).2.1,
    (SquareCarryLoan719BF.patchKG_counts L _).2.2.1,(SquareCarryLoan719BF.patchKG_counts L _).2.2.2,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem withLowK2_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have m := LowZero18LowK.loan_make_support_subset L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_support_subset L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,make,clear,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact m | exact c | exact Finset.Subset.refl _

theorem withLowK2_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have m := LowZero18LowK.loan_make_slots_le L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_slots_le L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,make,clear,patchKG,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

/-- Replacing the body of `withLowK2` by a statically refining body with known count savings. -/
theorem withLowK2_body_rel (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body body0 : Program) (dT dM : Nat)
    (hT : toffoliCount body+dT=toffoliCount body0) (hM : measurementCount body+dM=measurementCount body0)
    (hle : QRel.Le body body0) :
    toffoliCount (withLowK2 L ext control src dst body)+dT=toffoliCount (withLowK2 L ext control src dst body0) ∧
    measurementCount (withLowK2 L ext control src dst body)+dM=
      measurementCount (withLowK2 L ext control src dst body0) ∧
    wires (withLowK2 L ext control src dst body)⊆wires (withLowK2 L ext control src dst body0) ∧
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (withLowK2 L ext control src dst body0) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [withLowK2,toffoliCount_append,(renameProgram_counts _ _).1]; omega
  · simp only [withLowK2,measurementCount_append,(renameProgram_counts _ _).2]; omega
  · simp only [withLowK2,wires_append,renameProgram_support]
    repeat' apply Finset.union_subset_union
    all_goals first | exact Finset.image_subset_image hle.1 | exact Finset.Subset.refl _
  · have := hle.2
    simp only [withLowK2,Challenge.gateSlots_append,Baselines.rename_gateSlots]; omega

theorem raw_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (raw L ext control)+243=toffoliCount (SquareCarryLoan719BF.raw L ext control) ∧
    measurementCount (raw L ext control)+85=measurementCount (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_counts_diff L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_counts_diff L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_counts_diff L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  rw [if_neg (show ¬L.core.sum.length=128 by omega)] at c
  rw [if_pos high] at b
  rw [if_pos low] at a
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,
    toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem raw_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (raw L ext control)⊆wires (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_support_subset L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_support_subset L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_support_subset L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  have k3 := q3.trans k3
  have b := b3.trans b
  have a := a3.trans a
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,wires_append]
  repeat' apply Finset.union_subset_union
  all_goals first | exact k3.trans c | exact c | exact b | exact a | exact Finset.Subset.refl _

theorem raw_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (raw L ext control)≤Challenge.gateSlots (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_slots_le L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_slots_le L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_slots_le L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 2 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := withLowK2_body_rel L ext control L.core.high (L.core.product.take 256) _ _ 4 4
    (QRel.bBody_rel L hw control).1 (QRel.bBody_rel L hw control).2.1 (QRel.bBody_rel L hw control).2.2
  obtain ⟨a1,a2,a3,a4⟩ := withLowK2_body_rel L ext control L.core.low (L.core.product.take 256) _ _ 3 3
    (QRel.aBody_rel L hw control).1 (QRel.aBody_rel L hw control).2.1 (QRel.aBody_rel L hw control).2.2
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

private theorem tRename (f : Wire→Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem mRename (f : Wire→Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+243=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+85=measurementCount (SquareCarryLoan719BF.program L) := by
  have h := raw_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,tRename,mRename] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52016 ∧ measurementCount (program L)=52990 := by
  have a := counts_diff L hw
  have b := SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  have h := raw_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,Baselines.rename_gateSlots] using h

theorem slots (L : ControlledPointLayout) (hw : L.Widths) : Challenge.gateSlots (program L)≤8000000 :=
  (slots_le L hw).trans (SquareCarryLoan719BF.slots L hw)

private theorem place_support_mono (L : ControlledPointLayout) (P Q : Program) (sub : wires P⊆wires Q) :
    wires (place L P)⊆wires (SquareCarryLoan719BF.place L Q) := by
  unfold place SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact sub

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  apply place_support_mono
  exact raw_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (SquareCarryLoan719BF.support L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire k∉wires (program L) :=
  fun used=>SquareCarryLoan719BF.square_free L hw hn k hk (support_subset L hw used)

theorem retired_free719 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 719∉wires (program L) := square_free L hw hn 719 (by simp)
theorem retired_free768 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 768∉wires (program L) := square_free L hw hn 768 (by simp)
theorem retired_free718 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (program L) := square_free L hw hn 718 (by simp)

private theorem patchKG_physical (L : CuccaroStreamedSquareWideLayout) (R : KG)
    (hm : GatePhysical (LowZero18KG.make R))
    (hc : GatePhysical (LowZero18KG.clear R)) :
    GatePhysical (LowZero18Square.make L R) ∧ GatePhysical (LowZero18Square.clear L R) := by
  simp only [LowZero18KG.make,gatePhysical_append] at hm
  simp only [LowZero18KG.clear,gatePhysical_append] at hc
  have first : GatePhysical (renameProgram (earlyPerm L) R.Q1) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  have last : GatePhysical (renameProgram (earlyPerm L) R.Q1c) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,gatePhysical_append]
  tauto

private theorem withLowK2_physical_of_old (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (src dst : List Wire) (body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hlen : dst.length=2*src.length)
    (old : GatePhysical (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst body)) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  simp only [FrontierSumCleanup1591LowK.withLowK2,gatePhysical_append] at old
  have nd := LowZero18LowK.kg_nodup L control hn ext src dst hs hd he.nodup he.away
  have ph := LowZero18LowK.kg_physical L hw ext src dst h128 h129 hlen he.len nd
  have kernels := patchKG_physical L (LowZero18LowK.kg L ext src dst) ph.1 ph.2
  have bodyNew : GatePhysical (renameProgram (foldPerm L ext) body) :=
    gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ (by tauto)
  simp only [withLowK2,gatePhysical_append]
  tauto

private theorem withLowK2_physical_of_old2 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (src dst : List Wire) (body0 body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hlen : dst.length=2*src.length)
    (old : GatePhysical (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst body0))
    (hb : GatePhysical body) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  simp only [FrontierSumCleanup1591LowK.withLowK2,gatePhysical_append] at old
  have nd := LowZero18LowK.kg_nodup L control hn ext src dst hs hd he.nodup he.away
  have ph := LowZero18LowK.kg_physical L hw ext src dst h128 h129 hlen he.len nd
  have kernels := patchKG_physical L (LowZero18LowK.kg L ext src dst) ph.1 ph.2
  have bodyNew : GatePhysical (renameProgram (foldPerm L ext) body) :=
    gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ hb
  simp only [withLowK2,gatePhysical_append]
  tauto

private theorem raw_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) : GatePhysical (raw L ext control) := by
  have old := ControlLoan1589BFFold.physical L hw ext control hn he
  simp only [ControlLoan1589BFFold.program,FrontierSumCleanup1591Raw.accBranchCK,
    FrontierSumCleanup1591Raw.accMiddleCK,ControlLoan1589BFFold.branchBF,
    ControlLoan1589BFFold.branchAF,gatePhysical_append] at old
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sc := source_counts L
  have c := withLowK2_physical_of_old L hw ext control hn he L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) sc.2.2.1 (fun _=>le_rfl)
    (by omega) (by omega) (by rw [hw.core.product,sum]) old.1.1.1.1.2
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have c : GatePhysical (withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)) := by
    have pb := OwnDiagAll12Square.bodyCK_physicalTq L hw (List.nodup_cons.mp hn).2 control (List.nodup_cons.mp hn).1
    have pr := gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ pb
    simp only [withLowK2,gatePhysical_append] at c ⊢
    tauto
  have b := withLowK2_physical_of_old2 L hw ext control hn he L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (ControlLoan1589BFFold.bBodyTq L control) sc.2.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.1.2 (ControlLoan1589BFFold.bBody_physicalTq L hw control hn)
  have a := withLowK2_physical_of_old2 L hw ext control hn he L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (ControlLoan1589BFFold.aBodyTq L control) sc.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.2 (ControlLoan1589BFFold.aBody_physicalTq L hw control hn)
  have r := gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ old.2
  simp only [raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,reflection,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨old.1.1.1.1.1,c⟩,old.1.1.1.2⟩,b⟩,a⟩,r⟩

private theorem control_nd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢
  omega

private theorem place_physical (L : ControlledPointLayout) (P : Program) (hp : GatePhysical P) :
    GatePhysical (place L P) := by
  unfold place
  apply gatePhysical_rename (ControlLoan1589Square.swap L) (ControlLoan1589Square.swap L).injective
  apply gatePhysical_rename (Prefix1590Square.swap L) (Prefix1590Square.swap L).injective
  apply gatePhysical_rename (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.swap L).injective
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202) (Square5Placement.blockPerm L 202).injective _ hp

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (program L) :=
  place_physical L _ (raw_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (control_nd L hw hn) (ECDSAAdd.Entrant.kext_ok L hw hn))

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588LowZeroFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588BFFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588LowZeroFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
  ControlLoan1589BFFinal
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  Offset.gen L (division Rolling1588.entryKernel L) (LowZero18Square.program L)
    (exit Rolling1588.exitKernel L) cx cy

private def Metrics (P Q : Program) : Prop :=
  toffoliCount P+243=toffoliCount Q ∧ measurementCount P+85=measurementCount Q ∧
    gateSlots P≤gateSlots Q

private theorem gen_metrics_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : Metrics S Old) : Metrics G G0 := by
  subst G G0
  simp only [Metrics,Offset.gen,Offset.mid,Offset.generic,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at hs ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Metrics (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) := by
  have counts:=LowZero18Square.counts_diff L hw
  exact gen_metrics_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    ⟨counts.1,counts.2,LowZero18Square.slots_le L hw⟩

theorem gen_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+243=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+85=measurementCount (Rolling1588BFFinal.gen L cx cy) :=
  ⟨(gen_metrics L hw cx cy).1,(gen_metrics L hw cx cy).2.1⟩

private theorem wrapper_metrics (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Metrics P Q) :
    Metrics (Edges.wrapper L C cy P) (Edges.wrapper L C cy Q) := by
  simp only [Metrics,Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at h ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_subset_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : wires S⊆wires Old) : wires G⊆wires G0 := by
  subst G G0
  simp only [Offset.gen,Offset.mid,Offset.generic,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact hs | exact Finset.Subset.refl _

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (Rolling1588BFFinal.gen L cx cy) :=
  gen_subset_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    (LowZero18Square.support_subset L hw)

private theorem wrapper_subset (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P⊆wires Q) :
    wires (Edges.wrapper L C cy P)⊆wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact h | exact Finset.Subset.refl _

private theorem qubits_mono (P Q : Program) (h : wires P⊆wires Q) : qubits P≤qubits Q := by
  change (ioWires∪wires P).card≤(ioWires∪wires Q).card
  exact Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _) h)

theorem gen_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  exact Offset.genFFused_ok L hw hn _ _ _
    (FrontierEntry1591Callers.exit_correct Rolling1588.exitKernel
      Rolling1588.exitKernel_support Rolling1588.exit_correct L hw hn)
    (FrontierEntry1591Callers.division_step Rolling1588.entryKernel
      Rolling1588.entryKernel_support Rolling1588.entry_correct
      L hw hn config.1 above config.2.1 config.2.2)
    (LowZero18Square.step L hw hn) hc

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (Rolling1588BFFinal.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) :=
  Offset.gen_physical L hw hn _ _ _
    (division_physical Rolling1588.entryKernel Rolling1588.entryKernel_support
      Rolling1588.entryKernel_physical L hw hn)
    (LowZero18Square.physical L hw hn)
    (placed_physical Rolling1588.exitKernel Rolling1588.exitKernel_support
      Rolling1588.exitKernel_physical L hw hn) cx cy

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 :=
  (qubits_mono _ _ (wrapper_subset layout C cy _ _
    (gen_support_subset layout layout_widths cx cy))).trans
    (Rolling1588BFFinal.wrapper_qubits C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2152252 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).1
  have old:=Rolling1588BFFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499935 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).2.1
  have old:=Rolling1588BFFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50139199+Rolling1588.slotGrowth :=
  (wrapper_metrics layout C cy _ _ (gen_metrics layout layout_widths cx cy)).2.2.trans
    (Rolling1588BFFinal.wrapper_slots C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2152252,1499935,1588,50139199+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (gen_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2152252 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1499935 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50139199+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499935
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50139199+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.Rolling1588LowZeroFinal
end -- original module boundary

-- Selected checked E1 branch follows; the audited LowZero18 branch is omitted.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.SquareCarryLoan719BFProof

/-! Remove only the BF square's final reflection. All719 loans stay intact. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  SquareCarryLoan719BF
attribute [local irreducible] run wires

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program := place L (fastCore L)

def reflectedTail (L : ControlledPointLayout) : Program :=
  place L (reflection L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    raw L ext control=core L ext control++reflection L ext := rfl

theorem place_append (L : ControlledPointLayout) (P Q : Program) :
    place L (P++Q)=place L P++place L Q := by
  simp only [place,renameProgram,List.map_append]

theorem program_split (L : ControlledPointLayout) :
    SquareCarryLoan719BF.program L=program L++reflectedTail L := by
  simp only [SquareCarryLoan719BF.program,SquareCarryLoan719BF.fastCandidate,
    raw_split,place_append,program,fastCore,reflectedTail]

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
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
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
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
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (SquareCarryLoan719BF.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := SquareCarryLoan719BF.branchCK_correct L hw ext control hn A B O hO t m
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
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
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
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  have prior:=ControlLoan1589BFSquare.fastCandidate_correct L hw hn X.val Y.val G X.isLt s []
    v.generic v.x v.y v.clean
  have canonical:=SquareCarryLoan719BF.candidate_correct L hw hn X Y G origin s [] v
  have eq:=SquareCarryLoan719BF.fastCandidate_state_eq L hw hn X.val Y.val X.isLt s [] []
    v.x v.y v.clean
  rw [eq] at canonical
  have value:=prior.2.1.symm.trans canonical.2.x
  rw [value] at fresh
  exact fresh

private theorem place_relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (renameProgram e P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L e hp hf P s m before after

/-- Transport the complete State before taking any projection. -/
theorem place_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (place L P) m s=run P m s := by
  have a0:=place_relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) P s m before after
  have a1:=place_relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw)
    _ s m before (by rw [a0];exact after)
  have a2:=place_relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw)
    _ s m before (by rw [a1,a0];exact after)
  have a3:=place_relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw)
    _ s m before (by rw [a2,a1,a0];exact after)
  have a4:=place_relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw)
    _ s m before (by rw [a3,a2,a1,a0];exact after)
  have a5:=place_relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw)
    (OwnDiagAll12PlacedQ6.outside L hw) _ s m before (by rw [a4,a3,a2,a1,a0];exact after)
  have a6:=place_relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw)
    (OwnDiagAll12PlacedQ7.outside L hw) _ s m before (by rw [a5,a4,a3,a2,a1,a0];exact after)
  have a7:=place_relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw)
    (PrefixFrontierSquare1591.outside L hw) _ s m before (by rw [a6,a5,a4,a3,a2,a1,a0];exact after)
  have a8:=place_relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw)
    (Prefix1590Square.outside L hw) _ s m before (by rw [a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  have a9:=place_relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw)
    (ControlLoan1589Square.outside L hw) _ s m before (by rw [a8,a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  simpa only [place,a8,a7,a6,a5,a4,a3,a2,a1,a0] using a9


private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem support_subset (L : ControlledPointLayout) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  rw [program_split,wires_append]
  exact Finset.subset_union_left

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L).trans (SquareCarryLoan719BF.support L hw hn)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have old:=SquareCarryLoan719BF.physical L hw hn
  rw [program_split,gatePhysical_append] at old
  exact old.1

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) := by
  by_cases h : i=719
  · subst i;exact fun used=>SquareCarryLoan719BF.retired_free719 L hw hn (support_subset L used)
  · exact fun used=>SquareCarryLoan719BF.square_free L hw hn i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto) (support_subset L used)

theorem place_counts (L : ControlledPointLayout) (P : Program) :
    toffoliCount (place L P)=toffoliCount P ∧ measurementCount (place L P)=measurementCount P := by
  simp only [place,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem reflectedTail_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (reflectedTail L)=255 ∧ measurementCount (reflectedTail L)=255 := by
  have r:=(L.dialogStreamedSquareWide.measured_small_operation_counts
    (L.dialogStreamedSquareWide_widths hw)).2.2
  simpa only [reflectedTail,(place_counts _ _).1,(place_counts _ _).2,reflection,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using r

theorem counts_delta (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+255=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+255=measurementCount (SquareCarryLoan719BF.program L) := by
  rw [program_split,toffoliCount_append,measurementCount_append,
    (reflectedTail_counts L hw).1,(reflectedTail_counts L hw).2]
  exact ⟨rfl,rfl⟩

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52004 ∧ measurementCount (program L)=52820 := by
  have d:=counts_delta L hw
  have c:=SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  rw [program_split,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.ReflectionE1Square
end -- original module boundary



-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
end
